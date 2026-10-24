package com.pusherhub.sdk;

import android.Manifest;
import android.app.Activity;
import android.app.Application;
import android.app.Dialog;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.content.pm.PackageManager;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.location.Address;
import android.location.Geocoder;
import android.location.Location;
import android.location.LocationListener;
import android.location.LocationManager;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.util.Log;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.view.Window;
import android.webkit.JavascriptInterface;
import android.webkit.WebView;
import android.widget.Button;
import android.widget.FrameLayout;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.TextView;
import androidx.core.app.ActivityCompat;
import androidx.core.app.NotificationCompat;
import androidx.core.app.NotificationManagerCompat;
import androidx.core.content.ContextCompat;
import com.google.firebase.messaging.FirebaseMessaging;
import com.google.firebase.messaging.FirebaseMessagingService;
import com.google.firebase.messaging.RemoteMessage;
import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;
import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.lang.ref.WeakReference;
import java.net.HttpURLConnection;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TimeZone;
import java.util.UUID;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * PusherHub push notification + in-app messaging client for native Android (Java).
 *
 * Required setup (this is the whole "core" tier — everything else on this
 * class is optional), called from an Activity (see {@link #initialize}'s doc
 * for why):
 *
 *   PusherHub.initialize(this, appKey, publicKey, baseUrl);
 *   PusherHub.registerDevice();
 *
 * You also need {@link PusherHubMessagingService} declared in your manifest
 * (see the SDK Integration tab in the PusherHub dashboard for the exact
 * snippet) so incoming pushes and token refreshes reach this class.
 *
 * This whole SDK is one file (this one) — drop it straight into your
 * project's source tree, e.g. app/src/main/java/com/pusherhub/sdk/PusherHub.java.
 */
public final class PusherHub {

    private PusherHub() {
    }

    private static final String TAG = "PusherHub";
    private static final String PREFS_NAME = "pushhub_prefs";
    private static final String ANONYMOUS_ID_KEY = "pushhub_anonymous_id_v2";

    // The signed-in user's ID from login() (or registerDevice(externalId)),
    // kept across restarts until logout(): without it, the next launch's
    // plain registerDevice() quietly turned the device anonymous again.
    private static final String EXTERNAL_ID_KEY = "pushhub_external_id";

    // Survives restarts so a denial stays distinguishable from a fresh
    // install that has never been asked — see notificationPermissionStatus().
    private static final String PERMISSION_PROMPTED_KEY = "pushhub_notification_permission_prompted";

    // The last value the backend successfully accepted, so a resume that
    // found nothing changed costs nothing.
    private static final String LAST_REPORTED_PERMISSION_KEY = "pushhub_last_reported_notification_permission";

    // The last FCM token the backend accepted. FCM rotates tokens without a
    // reinstall; reporting the one being replaced lets the backend keep this
    // install as the same device rather than counting a new install plus,
    // later, an uninstall. Cleared with the app's data on reinstall, which is
    // exactly when a new device row is the right answer.
    private static final String LAST_REGISTERED_TOKEN_KEY = "pushhub_last_registered_token";

    // The last tapped notification handled. An Activity re-created with its
    // original Intent (rotation, or the app restored after Android stopped
    // it) brings the same tap back to handleIntent() — it's handled once.
    private static final String LAST_OPENED_MESSAGE_KEY = "pushhub_last_opened_message";

    // What PusherHub itself puts in a push's data next to the Custom Data —
    // left out of what onNotificationOpened gets.
    static final Set<String> OWN_DATA_KEYS = new HashSet<>(Arrays.asList("notification_id", "click_action", "deep_link"));

    // Firebase's own keys on the tap Intent of a notification Android showed
    // itself, next to the push's data.
    private static final Set<String> FIREBASE_INTENT_KEYS = new HashSet<>(Arrays.asList("from", "collapse_key", "message_type"));

    /**
     * The action PusherHub's backend hardcodes into every FCM payload's
     * android.notification.click_action (a holdover from the Flutter SDK,
     * where it's required — see FcmService::deliver() server-side). A native
     * app's launcher Activity needs an intent-filter matching this same
     * action, or a background/killed-state notification tap won't reach it.
     * See {@link #handleIntent}.
     */
    public static final String ACTION_NOTIFICATION_CLICK = "FLUTTER_NOTIFICATION_CLICK";

    // Matches the window the backend's Realtime tab buckets by. Anything
    // faster just upserts the same minute row for no extra information.
    private static final long HEARTBEAT_INTERVAL_MS = 60_000L;

    private static final int REQUEST_CODE_NOTIFICATIONS = 9427;
    private static final int REQUEST_CODE_LOCATION = 9428;

    private static Context appContext;
    private static String appKey;
    private static String publicKey;
    private static String baseUrl;
    private static OnNotificationClickListener onNotificationClick;
    private static OnNotificationOpenedListener onNotificationOpened;
    private static boolean initialized = false;

    // Opens reported before this launch had its FCM token — a tap that
    // launched the app is handled in onCreate(), before the token arrives —
    // sent once the device is registered instead of being dropped.
    private static final List<String[]> pendingEvents = new ArrayList<>();

    // Only set when initialize() was called with an Activity (e.g. from
    // MainActivity.onCreate(), not an Application subclass) — used solely to
    // show the POST_NOTIFICATIONS permission prompt, and held weakly so this
    // singleton can never be the reason that Activity leaks.
    private static WeakReference<Activity> activityRef;

    private static volatile String currentToken;
    private static volatile String currentExternalId;

    // Collected once (collectDeviceMetadata) and re-sent on every later
    // registration — the backend's register-device endpoint replaces these
    // fields wholesale, so omitting them on a later call would wipe out
    // whatever was already stored server-side.
    private static String deviceModel;
    private static String deviceBrand;
    private static String appVersion;
    private static String language;
    private static String country;
    private static String timezone;
    private static String state;
    private static String city;

    private static Runnable pendingAfterLocationPermission;

    // True from the moment the POST_NOTIFICATIONS prompt is shown until its
    // outcome is observed. Notifications read as disabled while the dialog is
    // still up, which would otherwise be reported as a denial the user hasn't
    // actually made yet.
    private static volatile boolean notificationPromptInFlight = false;

    // The system prompt is a translucent Activity stacked on the host's, so
    // the host is paused for as long as it's up — on every Android version.
    // That makes "resumed, having been paused since the prompt went out" the
    // reliable signal that the user has answered, and distinguishes it from
    // the host Activity's own first onResume, which arrives moments after
    // registerDevice() asked for the prompt and before the dialog is even on
    // screen.
    private static volatile boolean pausedSinceNotificationPrompt = false;

    private static boolean lifecycleCallbacksRegistered = false;

    // Counts started (not resumed) Activities, so a rotation or a push from
    // one screen to another never looks like the app went to the background.
    // Zero means the app genuinely isn't on screen and the heartbeat stops.
    private static int foregroundActivityCount = 0;

    private static final Runnable heartbeatRunnable = new Runnable() {
        @Override
        public void run() {
            sendHeartbeat();
            mainHandler.postDelayed(this, HEARTBEAT_INTERVAL_MS);
        }
    };

    private static final ExecutorService executor = Executors.newCachedThreadPool();
    private static final Handler mainHandler = new Handler(Looper.getMainLooper());

    private static SharedPreferences prefs() {
        return appContext.getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE);
    }

    /** Called instead of the SDK's default deep-link handling when a tapped notification carries one. */
    public interface OnNotificationClickListener {
        void onNotificationClick(String deepLink);
    }

    /**
     * Called from {@link #handleIntent} on every tap of a PusherHub
     * notification — whether the app was open, in the background or closed —
     * with the Custom Data it was sent with (empty if it had none). Open the
     * right screen from it, e.g. {@code data.get("campaign_id")}. Values
     * arrive as text — {@code {"campaign_id": 232}} gives "232" — and a nested
     * object or list as its JSON.
     */
    public interface OnNotificationOpenedListener {
        void onNotificationOpened(Map<String, String> data);
    }

    /** Receives the result of {@link #fetchInAppMessages}. */
    public interface InAppMessagesCallback {
        void onResult(List<InAppMessage> messages);
    }

    /** The identity currently registered with the backend — null until {@link #registerDevice} completes. */
    public static String getExternalId() {
        return currentExternalId;
    }

    /**
     * Call once, as early as possible — from MainActivity.onCreate() (or
     * whichever Activity launches first), not an Application subclass:
     * {@link #registerDevice} needs an Activity in hand to show the
     * notification permission prompt, and there isn't one yet inside
     * Application.onCreate().
     *
     * @param baseUrl your PusherHub server's API base URL:
     *   "https://pusherhub.com/api" for apps on pusherhub.com — the
     *   dashboard's SDK Integration tab shows it filled in. There's
     *   deliberately no default — a guessed one would silently point at
     *   the wrong server and registerDevice() would fail with nothing
     *   obviously wrong in your own code.
     */
    public static void initialize(Context context, String appKey, String publicKey, String baseUrl) {
        initialize(context, appKey, publicKey, baseUrl, null);
    }

    /**
     * Same as {@link #initialize(Context, String, String, String)}, plus an
     * optional listener called instead of the SDK's default behavior
     * (opening the link via ACTION_VIEW) when a tapped notification carries
     * a deep link.
     */
    public static void initialize(
            Context context,
            String appKey,
            String publicKey,
            String baseUrl,
            OnNotificationClickListener onNotificationClick) {
        initialize(context, appKey, publicKey, baseUrl, onNotificationClick, null);
    }

    /**
     * Same as {@link #initialize(Context, String, String, String, OnNotificationClickListener)}
     * (pass null for no click listener), plus an optional listener given
     * every tapped notification's Custom Data — see
     * {@link OnNotificationOpenedListener}.
     */
    public static void initialize(
            Context context,
            String appKey,
            String publicKey,
            String baseUrl,
            OnNotificationClickListener onNotificationClick,
            OnNotificationOpenedListener onNotificationOpened) {
        PusherHub.appContext = context.getApplicationContext();
        PusherHub.appKey = appKey;
        PusherHub.publicKey = publicKey;
        PusherHub.baseUrl = baseUrl;
        PusherHub.onNotificationClick = onNotificationClick;
        PusherHub.onNotificationOpened = onNotificationOpened;
        PusherHub.initialized = true;
        if (context instanceof Activity) {
            activityRef = new WeakReference<>((Activity) context);
        }
        observeForegroundForPermissionChanges(context);
        createNotificationChannel();
    }

    /** Requests the FCM token and registers this device as the signed-in user (see {@link #login}), or an auto-generated anonymous id. */
    public static void registerDevice() {
        registerDevice(null, null);
    }

    /** Same as {@link #registerDevice()}, registering under this externalId — the same as calling {@link #login} with it. */
    public static void registerDevice(String externalId) {
        registerDevice(externalId, null);
    }

    /**
     * Same as {@link #registerDevice()}, running onComplete once registration
     * finishes — e.g. {@code PusherHub.registerDevice(() -> PusherHub.collectDeviceMetadata());}
     * — since registration is asynchronous (it needs the FCM token first).
     */
    public static void registerDevice(Runnable onComplete) {
        registerDevice(null, onComplete);
    }

    /**
     * Requests the FCM token and registers this device with the PusherHub
     * backend, as the user last signed in with {@link #login} — remembered
     * across restarts until {@link #logout} — or, with nobody signed in, a
     * persistent anonymous ID generated on first launch (matching
     * OneSignal's default anonymous-subscription behavior). A non-null
     * externalId is the same as calling {@link #login} with it.
     *
     * Registration finishes asynchronously (it needs the FCM token first),
     * so pass onComplete if you need to sequence something after it rather
     * than calling that right after this returns.
     */
    public static void registerDevice(String externalId, Runnable onComplete) {
        if (!requireInitialized()) return;

        requestNotificationPermissionIfNeeded();

        if (externalId != null) rememberExternalId(externalId);

        FirebaseMessaging firebaseMessaging;
        try {
            // Throws IllegalStateException (not a checked exception, so it's
            // easy to miss) if FirebaseApp hasn't been initialized yet — the
            // most common cause is google-services.json not being present
            // for this build, or the com.google.gms.google-services plugin
            // not being applied. Caught here so a missing/incomplete
            // Firebase setup logs a clear, actionable message instead of
            // crashing the whole host app on this call.
            firebaseMessaging = FirebaseMessaging.getInstance();
        } catch (IllegalStateException e) {
            Log.e(TAG, "FirebaseApp isn't initialized — add google-services.json and apply the "
                    + "com.google.gms.google-services plugin (see the SDK Integration tab), then rebuild.", e);
            return;
        }

        firebaseMessaging.getToken().addOnCompleteListener(task -> {
            if (!task.isSuccessful()) {
                Log.w(TAG, "Failed to retrieve FCM token", task.getException());
                return;
            }
            String token = task.getResult();
            if (token == null) return;
            currentToken = token;
            // Read now, not when registerDevice() was called: a login() or
            // logout() while the token was on its way counts.
            registerToken(resolvedExternalId(), token);
            if (onComplete != null) onComplete.run();
        });
    }

    /**
     * Call this from your FirebaseMessagingService.onNewToken(token) — see
     * {@link PusherHubMessagingService}, which already does this for you if
     * you use it directly instead of your own service class.
     */
    public static void handleNewToken(String token) {
        if (!initialized) return;
        currentToken = token;
        registerToken(resolvedExternalId(), token);
    }

    /**
     * Aliases this device to a real signed-in user — equivalent to
     * {@code OneSignal.login(externalId)} — and remembers it on the device,
     * so every later launch registers as this user too, until
     * {@link #logout}. Re-registers the same FCM token under the new
     * external_id, so the backend re-links the existing device row instead
     * of creating a duplicate. Called before {@link #registerDevice} has
     * finished, the ID is still remembered and used as soon as it does.
     */
    public static void login(String externalId) {
        if (!requireInitialized() || externalId == null) return;
        rememberExternalId(externalId);
        String token = currentToken;
        if (token == null) return;
        registerToken(externalId, token);
    }

    /** Reverts this device back to its anonymous identity, and forgets the signed-in user — call this on sign-out. */
    public static void logout() {
        if (!requireInitialized()) return;
        prefs().edit().remove(EXTERNAL_ID_KEY).apply();
        String token = currentToken;
        if (token == null) return;
        registerToken(getOrCreateAnonymousId(), token);
    }

    private static void rememberExternalId(String externalId) {
        prefs().edit().putString(EXTERNAL_ID_KEY, externalId).apply();
    }

    /** Who this device registers as: the signed-in user (see {@link #login}), or the anonymous ID. */
    private static String resolvedExternalId() {
        String signedIn = prefs().getString(EXTERNAL_ID_KEY, null);
        return signedIn != null ? signedIn : getOrCreateAnonymousId();
    }

    /**
     * Optional: enriches this device's record with brand, model, app
     * version, language, country, timezone, state, and city.
     *
     * Brand/model/version/language/timezone are read directly from the OS —
     * no permission needed for those. State and city additionally need a
     * GPS fix + reverse geocoding: this prompts for ACCESS_COARSE_LOCATION
     * (needs the Activity captured in {@link #initialize} — same requirement
     * as the notification permission) and uses Android's own built-in
     * Geocoder, so no extra dependency or API key is needed for this
     * either. If location is denied, unavailable, or there's no Activity to
     * prompt from, this fails quietly and state/city simply stay unset — it
     * never blocks the rest of registration.
     *
     * Forward your Activity's onRequestPermissionsResult() to
     * {@link #onRequestPermissionsResult} or the location prompt's result
     * will never reach this call.
     *
     * Safe to call any time after {@link #registerDevice} has completed.
     */
    public static void collectDeviceMetadata() {
        String token = currentToken;
        if (token == null) {
            Log.w(TAG, "collectDeviceMetadata() called before registerDevice() completed.");
            return;
        }
        // The same identity registerDevice() registered with — not
        // currentExternalId, which is only set once registerToken()'s own
        // background network call finishes: calling this from
        // registerDevice()'s onComplete (the documented, recommended way)
        // races ahead of that.
        String externalId = resolvedExternalId();

        deviceBrand = Build.MANUFACTURER;
        deviceModel = Build.MODEL;
        String resolvedVersion;
        try {
            PackageManager pm = appContext.getPackageManager();
            resolvedVersion = pm.getPackageInfo(appContext.getPackageName(), 0).versionName;
        } catch (Exception e) {
            resolvedVersion = null;
        }
        appVersion = resolvedVersion;
        language = Locale.getDefault().getLanguage();
        country = Locale.getDefault().getCountry();
        timezone = TimeZone.getDefault().getID();

        String finalExternalId = externalId;
        String finalToken = token;
        resolveStateAndCity(() -> registerToken(finalExternalId, finalToken));
    }

    /**
     * Forward your Activity's
     * onRequestPermissionsResult(requestCode, permissions, grantResults)
     * here.
     *
     * <p>Required if you call {@link #collectDeviceMetadata} (which may
     * prompt for location). Optional for the notification permission:
     * forwarding just reports the user's answer to the backend the instant
     * they tap Allow/Don't allow instead of on the app's next foreground.
     */
    public static void onRequestPermissionsResult(int requestCode) {
        if (requestCode == REQUEST_CODE_NOTIFICATIONS) {
            syncNotificationPermissionIfChanged();
            return;
        }
        if (requestCode != REQUEST_CODE_LOCATION) return;
        Runnable callback = pendingAfterLocationPermission;
        pendingAfterLocationPermission = null;
        if (callback != null) callback.run();
    }

    /**
     * Resolves state/city (and overrides country with the geocoded value,
     * more trustworthy than the locale-based guess) via GPS + Android's
     * built-in Geocoder, then always calls onComplete — whether resolution
     * succeeded, failed, or was skipped entirely.
     */
    private static void resolveStateAndCity(Runnable onComplete) {
        boolean hasPermission = ContextCompat.checkSelfPermission(appContext, Manifest.permission.ACCESS_COARSE_LOCATION)
                == PackageManager.PERMISSION_GRANTED;
        if (hasPermission) {
            fetchLocationAndGeocode(onComplete);
            return;
        }

        Activity activity = activityRef != null ? activityRef.get() : null;
        if (activity == null) {
            Log.w(TAG, "Location permission not granted and no Activity available to request it — skipping state/city resolution.");
            onComplete.run();
            return;
        }

        pendingAfterLocationPermission = () -> {
            if (ContextCompat.checkSelfPermission(appContext, Manifest.permission.ACCESS_COARSE_LOCATION) == PackageManager.PERMISSION_GRANTED) {
                fetchLocationAndGeocode(onComplete);
            } else {
                Log.w(TAG, "Location permission denied — skipping state/city resolution.");
                onComplete.run();
            }
        };
        ActivityCompat.requestPermissions(activity, new String[]{Manifest.permission.ACCESS_COARSE_LOCATION}, REQUEST_CODE_LOCATION);
    }

    private static void fetchLocationAndGeocode(Runnable onComplete) {
        executor.execute(() -> {
            Location cached;
            try {
                cached = bestLastKnownLocation();
            } catch (SecurityException e) {
                cached = null;
            }

            if (cached != null) {
                geocodeAndComplete(cached, onComplete);
                return;
            }

            // No cached fix (e.g. no other app on this device has used
            // location recently) — request a fresh one instead of giving up,
            // since that's the common case on a freshly-installed app.
            mainHandler.post(() -> requestFreshLocation(onComplete));
        });
    }

    /**
     * The freshest cached fix from whichever location provider has one —
     * good enough for state/city-level accuracy without the latency (or
     * battery cost) of requesting a brand-new GPS fix just for this.
     */
    private static Location bestLastKnownLocation() {
        LocationManager locationManager = (LocationManager) appContext.getSystemService(Context.LOCATION_SERVICE);
        if (locationManager == null) return null;

        Location best = null;
        for (String provider : new String[]{LocationManager.GPS_PROVIDER, LocationManager.NETWORK_PROVIDER, LocationManager.PASSIVE_PROVIDER}) {
            try {
                if (!locationManager.isProviderEnabled(provider)) continue;
                Location location = locationManager.getLastKnownLocation(provider);
                if (location != null && (best == null || location.getTime() > best.getTime())) {
                    best = location;
                }
            } catch (SecurityException e) {
                // Skip this provider.
            }
        }
        return best;
    }

    /**
     * Asks for a single fresh fix (network provider preferred — faster and
     * plenty precise for state/city) and waits up to 10s. Must run on a
     * thread with a Looper, since LocationManager delivers its callback
     * there — called via mainHandler for that reason.
     */
    private static void requestFreshLocation(Runnable onComplete) {
        LocationManager locationManager = (LocationManager) appContext.getSystemService(Context.LOCATION_SERVICE);
        String provider = null;
        if (locationManager != null) {
            for (String candidate : new String[]{LocationManager.NETWORK_PROVIDER, LocationManager.GPS_PROVIDER}) {
                boolean enabled;
                try {
                    enabled = locationManager.isProviderEnabled(candidate);
                } catch (Exception e) {
                    enabled = false;
                }
                if (enabled) {
                    provider = candidate;
                    break;
                }
            }
        }

        if (locationManager == null || provider == null) {
            Log.w(TAG, "No location provider available — skipping state/city resolution.");
            onComplete.run();
            return;
        }

        LocationManager finalLocationManager = locationManager;
        boolean[] completed = {false};
        LocationListener listener = new LocationListener() {
            @Override
            public void onLocationChanged(Location location) {
                if (completed[0]) return;
                completed[0] = true;
                finalLocationManager.removeUpdates(this);
                executor.execute(() -> geocodeAndComplete(location, onComplete));
            }
        };

        try {
            // requestSingleUpdate still works on every supported version and needs no extra dependency (unlike the fused location API).
            locationManager.requestSingleUpdate(provider, listener, Looper.getMainLooper());
        } catch (Exception e) {
            Log.w(TAG, "Failed to request a location update — skipping state/city resolution.", e);
            onComplete.run();
            return;
        }

        mainHandler.postDelayed(() -> {
            if (!completed[0]) {
                completed[0] = true;
                finalLocationManager.removeUpdates(listener);
                Log.w(TAG, "Timed out waiting for a location fix — skipping state/city resolution.");
                onComplete.run();
            }
        }, 10_000L);
    }

    private static void geocodeAndComplete(Location location, Runnable onComplete) {
        try {
            // The listener-based API is Android 33+ only; this synchronous one still works on every version and is simplest for a single one-off lookup.
            List<Address> addresses = new Geocoder(appContext, Locale.getDefault())
                    .getFromLocation(location.getLatitude(), location.getLongitude(), 1);
            Address address = (addresses != null && !addresses.isEmpty()) ? addresses.get(0) : null;
            if (address != null) {
                state = address.getAdminArea();
                city = address.getLocality();
                if (address.getCountryName() != null && !address.getCountryName().isEmpty()) {
                    country = address.getCountryName();
                }
            }
        } catch (Exception e) {
            Log.w(TAG, "Failed to resolve state/city via geocoding", e);
        }

        mainHandler.post(onComplete);
    }

    /**
     * Fetches the in-app messages currently eligible for this device —
     * active, within their display window, matching this device's audience,
     * and not already shown once (for messages set to display only once).
     * Prefer {@link #checkForInAppMessages} if you just want the SDK's own
     * rendering — call this instead only if you want to build entirely
     * custom UI from the raw data, then call {@link #trackInAppShown}/
     * {@link #trackInAppClick}/{@link #trackInAppDismiss} yourself as
     * appropriate.
     */
    public static void fetchInAppMessages(InAppMessagesCallback callback) {
        String token = currentToken;
        if (token == null) {
            Log.w(TAG, "Skipping fetchInAppMessages — no FCM token registered yet.");
            callback.onResult(new ArrayList<>());
            return;
        }

        executor.execute(() -> {
            try {
                JSONObject body = new JSONObject();
                body.put("app_key", appKey);
                body.put("token", token);
                JSONObject response = postJson(baseUrl + "/fetch-in-app-messages", body);
                if (response == null) {
                    callback.onResult(new ArrayList<>());
                    return;
                }
                JSONArray messagesJson = response.optJSONArray("messages");
                if (messagesJson == null) messagesJson = new JSONArray();
                List<InAppMessage> messages = new ArrayList<>();
                for (int i = 0; i < messagesJson.length(); i++) {
                    try {
                        messages.add(InAppMessage.fromJson(messagesJson.getJSONObject(i)));
                    } catch (Exception ignored) {
                        // Skip a malformed message rather than failing the whole fetch.
                    }
                }
                callback.onResult(messages);
            } catch (Exception e) {
                Log.w(TAG, "Error fetching in-app messages", e);
                callback.onResult(new ArrayList<>());
            }
        });
    }

    /** Reports that message was actually displayed to the user. */
    public static void trackInAppShown(InAppMessage message) {
        trackInAppEvent("track-in-app-shown", message.id);
    }

    /** Reports that the user tapped message's button. */
    public static void trackInAppClick(InAppMessage message) {
        trackInAppEvent("track-in-app-click", message.id);
    }

    /** Reports that message was closed without the button being tapped. */
    public static void trackInAppDismiss(InAppMessage message) {
        trackInAppEvent("track-in-app-dismiss", message.id);
    }

    private static void trackInAppEvent(String endpoint, int inAppMessageId) {
        String token = currentToken;
        if (token == null) {
            Log.w(TAG, "Skipping " + endpoint + " — no FCM token registered yet.");
            return;
        }
        executor.execute(() -> {
            try {
                JSONObject body = new JSONObject();
                body.put("app_key", appKey);
                body.put("in_app_message_id", inAppMessageId);
                body.put("token", token);
                postJson(baseUrl + "/" + endpoint, body);
            } catch (JSONException e) {
                Log.w(TAG, "Failed to build " + endpoint + " request", e);
            }
        });
    }

    // ---------------------------------------------------------------------
    // In-app message rendering — the native equivalent of the Flutter SDK's
    // PusherHubMessageHost widget. Built with plain Android views (no
    // Compose, no Material Components library, no image-loading library)
    // so it works in any Android app regardless of UI toolkit, keeping this
    // SDK's only real dependency as Firebase Messaging itself.
    // ---------------------------------------------------------------------

    /**
     * Fetches in-app messages and, if one is eligible, displays it as a
     * Dialog styled to match its configured display type (banner/modal/
     * fullscreen/center_popup/bottom_sheet) and content mode (simple/
     * blocks/html) — the same content an admin authors on the PusherHub
     * dashboard. Automatically tracks shown/click/dismiss.
     *
     * Call this from your launcher Activity's onResume() — the closest
     * native equivalent to wrapping your app in the Flutter SDK's
     * PusherHubMessageHost, which checks on every app open/resume the same
     * way:
     *
     *   {@literal @}Override
     *   protected void onResume() {
     *       super.onResume();
     *       PusherHub.checkForInAppMessages(this);
     *   }
     */
    public static void checkForInAppMessages(Activity activity) {
        fetchInAppMessages(messages -> {
            if (messages.isEmpty()) return;
            InAppMessage message = messages.get(0);
            mainHandler.post(() -> {
                if (!activity.isFinishing() && !activity.isDestroyed()) {
                    showInAppMessage(activity, message);
                }
            });
        });
    }

    private interface InAppActionListener {
        void onAction(InAppAction action);
    }

    private abstract static class InAppAction {
        private static final class Close extends InAppAction {
        }

        private static final class OpenUrl extends InAppAction {
            final String url;

            OpenUrl(String url) {
                this.url = url;
            }
        }
    }

    private static void showInAppMessage(Activity activity, InAppMessage message) {
        trackInAppShown(message);

        // Set once the dialog is closed via a click or the close button, so
        // the dismiss listener below doesn't also report a plain dismiss —
        // matching the Flutter SDK's semantics, where a click and a dismiss
        // are mutually exclusive outcomes for the same message.
        boolean[] actedOn = {false};

        Dialog dialog = new Dialog(activity, android.R.style.Theme_Translucent_NoTitleBar);
        boolean isFullscreen = "fullscreen".equals(message.type);
        dialog.setCancelable(!isFullscreen);
        dialog.setCanceledOnTouchOutside(!isFullscreen);

        View contentView = buildMessageView(activity, message, action -> {
            if (action instanceof InAppAction.Close) {
                actedOn[0] = true;
                dialog.dismiss();
            } else if (action instanceof InAppAction.OpenUrl) {
                actedOn[0] = true;
                trackInAppClick(message);
                openDeepLink(((InAppAction.OpenUrl) action).url);
                dialog.dismiss();
            }
        });
        dialog.setContentView(contentView);
        dialog.setOnDismissListener(d -> {
            if (!actedOn[0]) trackInAppDismiss(message);
        });

        Window window = dialog.getWindow();
        if (window != null) {
            window.setBackgroundDrawableResource(android.R.color.transparent);
            int gravity;
            int width;
            int height;
            switch (message.type) {
                case "banner":
                    gravity = Gravity.TOP;
                    width = ViewGroup.LayoutParams.MATCH_PARENT;
                    height = ViewGroup.LayoutParams.WRAP_CONTENT;
                    break;
                case "bottom_sheet":
                    gravity = Gravity.BOTTOM;
                    width = ViewGroup.LayoutParams.MATCH_PARENT;
                    height = ViewGroup.LayoutParams.WRAP_CONTENT;
                    break;
                case "fullscreen":
                    gravity = Gravity.CENTER;
                    width = ViewGroup.LayoutParams.MATCH_PARENT;
                    height = ViewGroup.LayoutParams.MATCH_PARENT;
                    break;
                default: // modal / center_popup
                    gravity = Gravity.CENTER;
                    width = ViewGroup.LayoutParams.MATCH_PARENT;
                    height = ViewGroup.LayoutParams.WRAP_CONTENT;
            }
            window.setGravity(gravity);
            window.setLayout(width, height);
        }

        dialog.show();

        Integer dismissAfter = message.dismissAfterSeconds;
        if (dismissAfter != null && dismissAfter > 0) {
            mainHandler.postDelayed(() -> {
                if (dialog.isShowing()) dialog.dismiss();
            }, dismissAfter * 1000L);
        }
    }

    private static View buildMessageView(Context context, InAppMessage message, InAppActionListener onAction) {
        if ("html".equals(message.contentMode) && message.htmlContent != null && !message.htmlContent.isEmpty()) {
            return buildHtmlView(context, message, onAction);
        }

        float density = context.getResources().getDisplayMetrics().density;

        FrameLayout outer = new FrameLayout(context);
        int outerMargin = "fullscreen".equals(message.type) ? 0 : dp(8, density);
        outer.setPadding(outerMargin, outerMargin, outerMargin, outerMargin);

        LinearLayout card = new LinearLayout(context);
        card.setOrientation(LinearLayout.VERTICAL);
        int pad = dp(message.padding != null ? message.padding : 16, density);
        card.setPadding(pad, pad, pad, pad);
        GradientDrawable cardBackground = new GradientDrawable();
        cardBackground.setCornerRadius("fullscreen".equals(message.type) ? 0f : dp(16, density));
        cardBackground.setColor(parseColorOrDefault(message.backgroundColor, "#FFFFFF"));
        card.setBackground(cardBackground);

        if (message.backgroundImage != null && !message.backgroundImage.isEmpty()) {
            ImageView bgImage = new ImageView(context);
            bgImage.setScaleType(ImageView.ScaleType.CENTER_CROP);
            loadImageAsync(message.backgroundImage, bgImage);
            card.addView(
                    bgImage,
                    0,
                    new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        }

        int textColor = parseColorOrDefault(message.textColor, "#0F172A");
        if ("blocks".equals(message.contentMode)) {
            buildBlocksContent(context, card, message.blocks, textColor, onAction);
        } else {
            buildSimpleContent(context, card, message, textColor, onAction);
        }

        outer.addView(card, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));

        if (message.showCloseButton) {
            TextView closeButton = new TextView(context);
            closeButton.setText("✕");
            closeButton.setTextColor(textColor);
            closeButton.setTextSize(16f);
            int closePad = dp(12, density);
            closeButton.setPadding(closePad, closePad, closePad, closePad);
            closeButton.setOnClickListener(v -> onAction.onAction(new InAppAction.Close()));
            FrameLayout.LayoutParams lp =
                    new FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
            lp.gravity = Gravity.TOP | Gravity.END;
            outer.addView(closeButton, lp);
        }

        return outer;
    }

    private static int dp(int value, float density) {
        return (int) (value * density);
    }

    private static void buildSimpleContent(Context context, LinearLayout container, InAppMessage message, int textColor, InAppActionListener onAction) {
        float density = context.getResources().getDisplayMetrics().density;

        if (message.image != null && !message.image.isEmpty()) {
            ImageView image = new ImageView(context);
            image.setScaleType(ImageView.ScaleType.CENTER_CROP);
            loadImageAsync(message.image, image);
            container.addView(image, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(140, density)));
        }

        if (message.heading != null && !message.heading.isEmpty()) {
            TextView heading = new TextView(context);
            heading.setText(message.heading);
            heading.setTextColor(textColor);
            heading.setTextSize(18f);
            heading.setTypeface(heading.getTypeface(), Typeface.BOLD);
            heading.setPadding(0, dp(8, density), 0, 0);
            container.addView(heading);
        }

        if (message.body != null && !message.body.isEmpty()) {
            TextView body = new TextView(context);
            body.setText(message.body);
            body.setTextColor(textColor);
            body.setAlpha(0.85f);
            body.setTextSize(14f);
            body.setPadding(0, dp(4, density), 0, 0);
            container.addView(body);
        }

        if (message.buttonText != null && !message.buttonText.isEmpty()) {
            Button button = new Button(context);
            button.setText(message.buttonText);
            button.setOnClickListener(v -> {
                String link = message.buttonDeepLink;
                if (link != null && !link.isEmpty()) {
                    onAction.onAction(new InAppAction.OpenUrl(link));
                } else {
                    onAction.onAction(new InAppAction.Close());
                }
            });
            LinearLayout.LayoutParams lp =
                    new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
            lp.topMargin = dp(12, density);
            container.addView(button, lp);
        }
    }

    private static void buildBlocksContent(Context context, LinearLayout container, List<Map<String, Object>> blocks, int textColor, InAppActionListener onAction) {
        float density = context.getResources().getDisplayMetrics().density;

        for (Map<String, Object> block : blocks) {
            Object typeObj = block.get("type");
            String type = typeObj instanceof String ? (String) typeObj : null;

            if ("text".equals(type)) {
                TextView tv = new TextView(context);
                Object textObj = block.get("text");
                tv.setText(textObj instanceof String ? (String) textObj : "");
                Object colorObj = block.get("color");
                tv.setTextColor(colorObj instanceof String ? parseColorOrDefault((String) colorObj, "#000000") : textColor);
                Object fontSizeObj = block.get("font_size");
                tv.setTextSize(fontSizeObj instanceof Number ? ((Number) fontSizeObj).floatValue() : 16f);
                boolean bold = Boolean.TRUE.equals(block.get("bold"));
                boolean italic = Boolean.TRUE.equals(block.get("italic"));
                int style;
                if (bold && italic) {
                    style = Typeface.BOLD_ITALIC;
                } else if (bold) {
                    style = Typeface.BOLD;
                } else if (italic) {
                    style = Typeface.ITALIC;
                } else {
                    style = Typeface.NORMAL;
                }
                tv.setTypeface(tv.getTypeface(), style);
                if (Boolean.TRUE.equals(block.get("underline"))) {
                    tv.setPaintFlags(tv.getPaintFlags() | Paint.UNDERLINE_TEXT_FLAG);
                }
                Object alignObj = block.get("align");
                if ("left".equals(alignObj)) {
                    tv.setGravity(Gravity.START);
                } else if ("right".equals(alignObj)) {
                    tv.setGravity(Gravity.END);
                } else {
                    tv.setGravity(Gravity.CENTER);
                }
                LinearLayout.LayoutParams lp =
                        new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
                lp.topMargin = dp(4, density);
                lp.bottomMargin = dp(4, density);
                container.addView(tv, lp);

            } else if ("image".equals(type)) {
                Object urlObj = block.get("image");
                String url = urlObj instanceof String ? (String) urlObj : null;
                if (url != null && !url.isEmpty()) {
                    ImageView image = new ImageView(context);
                    image.setScaleType(ImageView.ScaleType.CENTER_CROP);
                    loadImageAsync(url, image);
                    image.setOnClickListener(v -> handleBlockClick(block, onAction));
                    LinearLayout.LayoutParams lp =
                            new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(120, density));
                    lp.topMargin = dp(4, density);
                    lp.bottomMargin = dp(4, density);
                    container.addView(image, lp);
                }

            } else if ("button".equals(type)) {
                Button button = new Button(context);
                Object textObj = block.get("text");
                button.setText(textObj instanceof String ? (String) textObj : "Button");
                Object fontColorObj = block.get("font_color");
                button.setTextColor(parseColorOrDefault(fontColorObj instanceof String ? (String) fontColorObj : null, "#FFFFFF"));
                GradientDrawable buttonBackground = new GradientDrawable();
                Object backgroundColorObj = block.get("background_color");
                buttonBackground.setColor(parseColorOrDefault(backgroundColorObj instanceof String ? (String) backgroundColorObj : null, "#051B2C"));
                Object cornerObj = block.get("corner_radius");
                float corner = cornerObj instanceof Number ? ((Number) cornerObj).floatValue() : 8f;
                buttonBackground.setCornerRadius(corner * density);
                button.setBackground(buttonBackground);
                button.setOnClickListener(v -> handleBlockClick(block, onAction));
                LinearLayout.LayoutParams lp =
                        new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
                lp.topMargin = dp(4, density);
                container.addView(button, lp);
            }
        }
    }

    @SuppressWarnings("unchecked")
    private static void handleBlockClick(Map<String, Object> block, InAppActionListener onAction) {
        Object clickActionObj = block.get("click_action");
        Map<String, Object> clickAction = clickActionObj instanceof Map ? (Map<String, Object>) clickActionObj : null;
        Object valueObj = clickAction != null ? clickAction.get("value") : null;
        String value = valueObj instanceof String ? (String) valueObj : null;
        Object typeObj = clickAction != null ? clickAction.get("type") : null;

        if ("open_url".equals(typeObj) || "deep_link".equals(typeObj)) {
            if (value != null && !value.isEmpty()) {
                onAction.onAction(new InAppAction.OpenUrl(value));
            }
        } else if ("close".equals(typeObj)) {
            onAction.onAction(new InAppAction.Close());
        }
    }

    /**
     * A WebView pre-wired with the same PushHubIamApi JavaScript bridge
     * documented on the dashboard's HTML in-app message editor —
     * PushHubIamApi.close(), .openUrl(url), and .trackClick() all work
     * exactly as an admin authoring HTML content there expects.
     */
    private static View buildHtmlView(Context context, InAppMessage message, InAppActionListener onAction) {
        WebView webView = new WebView(context);
        webView.getSettings().setJavaScriptEnabled(true);
        webView.addJavascriptInterface(new Object() {
            @JavascriptInterface
            public void close() {
                mainHandler.post(() -> onAction.onAction(new InAppAction.Close()));
            }

            @JavascriptInterface
            public void openUrl(String url) {
                mainHandler.post(() -> onAction.onAction(new InAppAction.OpenUrl(url)));
            }

            @JavascriptInterface
            public void trackClick() {
                trackInAppClick(message);
            }
        }, "PushHubIamApi");
        webView.loadDataWithBaseURL(null, message.htmlContent != null ? message.htmlContent : "", "text/html", "UTF-8", null);
        return webView;
    }

    private static void loadImageAsync(String url, ImageView into) {
        executor.execute(() -> {
            try {
                HttpURLConnection connection = (HttpURLConnection) new URL(url).openConnection();
                connection.setConnectTimeout(15_000);
                connection.setReadTimeout(15_000);
                connection.setDoInput(true);
                Bitmap bitmap = BitmapFactory.decodeStream(connection.getInputStream());
                connection.disconnect();
                if (bitmap != null) {
                    mainHandler.post(() -> into.setImageBitmap(bitmap));
                }
            } catch (Exception e) {
                Log.w(TAG, "Failed to load image: " + url, e);
            }
        });
    }

    private static int parseColorOrDefault(String hex, String defaultColor) {
        try {
            String value = (hex != null && !hex.trim().isEmpty()) ? hex : defaultColor;
            return Color.parseColor(value);
        } catch (Exception e) {
            return Color.parseColor(defaultColor);
        }
    }

    /**
     * Call this from your launcher Activity's onCreate(intent) and
     * onNewIntent(intent) — handles the case where the app was backgrounded
     * or fully killed and the user tapped a PusherHub notification to
     * (re)launch it. Reports the open (and click-through, if the
     * notification carried a deep link), hands its Custom Data to the
     * onNotificationOpened listener, and opens the deep link.
     *
     * (A tap on a notification that arrived while the app was open comes
     * through here too: {@link PusherHubMessagingService}'s own PendingIntent
     * relaunches this same Activity with it. It's safe to call
     * unconditionally — each tap is handled once.)
     */
    public static void handleIntent(Intent intent) {
        if (intent == null) return;
        if (!requireInitialized()) return;
        // The prefixed extra is only present when PusherHub itself built the tap
        // PendingIntent (app was in the foreground when the push arrived). For a
        // backgrounded/killed app, Android auto-displays the notification from the
        // FCM payload and constructs the tap intent itself, carrying the payload's
        // raw data keys instead — so that's what's actually on the intent then.
        String notificationId = intent.getStringExtra(PusherHubMessagingService.EXTRA_NOTIFICATION_ID);
        if (notificationId == null) notificationId = intent.getStringExtra("notification_id");
        if (notificationId == null) return;
        String deepLink = intent.getStringExtra(PusherHubMessagingService.EXTRA_DEEP_LINK);
        if (deepLink == null) deepLink = intent.getStringExtra("deep_link");

        String messageId = intent.getStringExtra(PusherHubMessagingService.EXTRA_MESSAGE_ID);
        if (messageId == null) messageId = intent.getStringExtra("google.message_id");
        if (messageId != null) {
            if (messageId.equals(prefs().getString(LAST_OPENED_MESSAGE_KEY, null))) return;
            prefs().edit().putString(LAST_OPENED_MESSAGE_KEY, messageId).apply();
        }

        handleNotificationOpened(notificationId, deepLink, customDataOf(intent));
    }

    /**
     * A tapped notification's Custom Data: the bundle PusherHub's own
     * notification puts on its tap, or — for one Android showed itself — the
     * push's data keys on the Intent, without PusherHub's and Firebase's own.
     */
    private static Map<String, String> customDataOf(Intent intent) {
        Map<String, String> data = new HashMap<>();
        Bundle bundle = intent.getBundleExtra(PusherHubMessagingService.EXTRA_CUSTOM_DATA);
        boolean fromIntent = bundle == null;
        if (fromIntent) bundle = intent.getExtras();
        if (bundle == null) return data;

        for (String key : bundle.keySet()) {
            if (fromIntent && (OWN_DATA_KEYS.contains(key) || FIREBASE_INTENT_KEYS.contains(key)
                    || key.startsWith("google.") || key.startsWith("gcm."))) {
                continue;
            }
            String value = bundle.getString(key);
            if (value != null) data.put(key, value);
        }
        return data;
    }

    private static void handleNotificationOpened(String notificationId, String deepLink, Map<String, String> data) {
        trackEvent("track-open", notificationId);
        OnNotificationOpenedListener opened = onNotificationOpened;
        if (opened != null) opened.onNotificationOpened(data);
        if (deepLink != null && !deepLink.isEmpty()) {
            trackEvent("track-click", notificationId);
            openDeepLink(deepLink);
        }
    }

    private static void openDeepLink(String deepLink) {
        OnNotificationClickListener callback = onNotificationClick;
        if (callback != null) {
            callback.onNotificationClick(deepLink);
            return;
        }

        try {
            Intent intent = new Intent(Intent.ACTION_VIEW, Uri.parse(deepLink));
            intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
            appContext.startActivity(intent);
        } catch (Exception e) {
            Log.w(TAG, "No handler available to open deep link: " + deepLink, e);
        }
    }

    private static void trackEvent(String endpoint, String notificationId) {
        String token = currentToken;
        if (token == null) {
            synchronized (pendingEvents) {
                pendingEvents.add(new String[] {endpoint, notificationId});
            }
            return;
        }
        executor.execute(() -> {
            try {
                JSONObject body = new JSONObject();
                body.put("app_key", appKey);
                Object idValue;
                try {
                    idValue = Integer.parseInt(notificationId);
                } catch (NumberFormatException e) {
                    idValue = notificationId;
                }
                body.put("notification_id", idValue);
                body.put("token", token);
                postJson(baseUrl + "/" + endpoint, body);
            } catch (JSONException e) {
                Log.w(TAG, "Failed to build " + endpoint + " request", e);
            }
        });
    }

    private static void flushPendingEvents() {
        List<String[]> pending;
        synchronized (pendingEvents) {
            pending = new ArrayList<>(pendingEvents);
            pendingEvents.clear();
        }
        for (String[] event : pending) {
            trackEvent(event[0], event[1]);
        }
    }

    private static void registerToken(String externalId, String token) {
        final String permission = notificationPermissionStatus();
        executor.execute(() -> {
            try {
                String previousToken = prefs().getString(LAST_REGISTERED_TOKEN_KEY, null);
                JSONObject body = new JSONObject();
                body.put("app_key", appKey);
                body.put("external_id", externalId);
                body.put("token", token);
                // Covers both ways a rotation arrives: onNewToken while
                // running, and getToken() returning a different token on a
                // later launch.
                if (previousToken != null && !previousToken.equals(token)) {
                    body.put("previous_token", previousToken);
                }
                body.put("platform", "android");
                body.put("device", deviceModel);
                body.put("brand", deviceBrand);
                body.put("version", appVersion);
                body.put("language", language);
                body.put("country", country);
                body.put("state", state);
                body.put("city", city);
                body.put("timezone", timezone);
                body.put("notification_permission", permission);

                JSONObject response = postJson(baseUrl + "/register-device", body);
                if (response != null) {
                    currentExternalId = externalId;
                    // Only cached once the backend has actually taken it —
                    // caching a value a failed request never delivered would
                    // suppress the retry on the next resume. The token
                    // likewise: if this request failed, the next attempt must
                    // still report the old token as the one being replaced.
                    prefs().edit()
                            .putString(LAST_REPORTED_PERMISSION_KEY, permission)
                            .putString(LAST_REGISTERED_TOKEN_KEY, token)
                            .apply();
                    Log.i(TAG, "Device registered successfully.");
                    flushPendingEvents();
                } else {
                    Log.w(TAG, "Failed to register device.");
                }
            } catch (JSONException e) {
                Log.w(TAG, "Failed to build register-device request", e);
            }
        });
    }

    /** Returns the parsed JSON response body, or null on any failure (network, non-2xx, bad JSON). */
    private static JSONObject postJson(String urlString, JSONObject body) {
        HttpURLConnection connection = null;
        try {
            URL url = new URL(urlString);
            connection = (HttpURLConnection) url.openConnection();
            connection.setRequestMethod("POST");
            connection.setRequestProperty("Content-Type", "application/json");
            connection.setRequestProperty("Authorization", "Bearer " + publicKey);
            // Harmless against a real server; needed only when baseUrl points
            // at a free-tier ngrok tunnel — without it, ngrok returns an HTML
            // "visit site" warning page instead of forwarding to PusherHub.
            connection.setRequestProperty("ngrok-skip-browser-warning", "true");
            connection.setDoOutput(true);
            connection.setConnectTimeout(15_000);
            connection.setReadTimeout(15_000);

            try (OutputStreamWriter writer = new OutputStreamWriter(connection.getOutputStream())) {
                writer.write(body.toString());
            }

            int code = connection.getResponseCode();
            InputStream stream = (code >= 200 && code < 300) ? connection.getInputStream() : connection.getErrorStream();
            String text = "";
            if (stream != null) {
                StringBuilder sb = new StringBuilder();
                try (BufferedReader reader = new BufferedReader(new InputStreamReader(stream))) {
                    String line;
                    while ((line = reader.readLine()) != null) {
                        sb.append(line);
                    }
                }
                text = sb.toString();
            }

            if (code < 200 || code >= 300) {
                Log.w(TAG, urlString + " failed: HTTP " + code + " " + text);
                return null;
            }

            return text.trim().isEmpty() ? new JSONObject() : new JSONObject(text);
        } catch (Exception e) {
            Log.w(TAG, "Request to " + urlString + " failed", e);
            return null;
        } finally {
            if (connection != null) connection.disconnect();
        }
    }

    private static String getOrCreateAnonymousId() {
        String existing = prefs().getString(ANONYMOUS_ID_KEY, null);
        if (existing != null) return existing;

        String id = UUID.randomUUID().toString();
        prefs().edit().putString(ANONYMOUS_ID_KEY, id).apply();
        return id;
    }

    private static boolean requireInitialized() {
        if (!initialized) {
            Log.e(TAG, "PusherHub.initialize() must be called before this.");
        }
        return initialized;
    }

    /**
     * Shows the system POST_NOTIFICATIONS prompt on Android 13+ if it hasn't
     * been granted (or denied) yet — a no-op below API 33, where the
     * permission doesn't exist and notifications just work. Needs the
     * Activity captured in {@link #initialize} (see that method's doc) — if
     * initialize() was called from an Application subclass instead, this
     * logs a warning and does nothing, same as if you'd never called it;
     * request the permission yourself in that case.
     */
    private static void requestNotificationPermissionIfNeeded() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU) return;
        if (ContextCompat.checkSelfPermission(appContext, Manifest.permission.POST_NOTIFICATIONS) == PackageManager.PERMISSION_GRANTED) return;

        Activity activity = activityRef != null ? activityRef.get() : null;
        if (activity == null) {
            Log.w(
                    TAG,
                    "POST_NOTIFICATIONS isn't granted and no Activity is available to prompt for it "
                            + "(PusherHub.initialize() was called without one — see its doc comment). "
                            + "Notifications won't display until this permission is granted.");
            return;
        }

        notificationPromptInFlight = true;
        pausedSinceNotificationPrompt = false;
        prefs().edit().putBoolean(PERMISSION_PROMPTED_KEY, true).apply();
        ActivityCompat.requestPermissions(activity, new String[]{Manifest.permission.POST_NOTIFICATIONS}, REQUEST_CODE_NOTIFICATIONS);
    }

    /**
     * This device's notification permission as the backend records it:
     * "granted", "denied", or "not_determined".
     *
     * Built on NotificationManagerCompat.areNotificationsEnabled() rather
     * than only checking POST_NOTIFICATIONS, because that permission doesn't
     * exist below API 33 while a user on any version can still switch the
     * app's notifications off in system settings — and the question the
     * dashboard answers is "will a push actually reach this device", not
     * "was a runtime permission granted".
     */
    private static String notificationPermissionStatus() {
        if (NotificationManagerCompat.from(appContext).areNotificationsEnabled()) return "granted";

        // Off — but on API 33+ that's also the state of an install nobody has
        // asked yet, which isn't the same signal as a refusal.
        boolean neverAnswered = notificationPromptInFlight || !prefs().getBoolean(PERMISSION_PROMPTED_KEY, false);
        return Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU && neverAnswered ? "not_determined" : "denied";
    }

    /**
     * Re-reports the notification permission when it no longer matches what
     * the backend was last told — the user answering the prompt, or turning
     * notifications off (or back on) in system settings weeks later, which
     * produces no callback of any kind.
     *
     * A no-op with no network call in the overwhelmingly common case where
     * nothing changed, so it's safe on every foreground.
     */
    private static void syncNotificationPermissionIfChanged() {
        if (!initialized) return;

        // Every caller reaches here only once the prompt has resolved, so
        // what we read now is the user's actual answer.
        notificationPromptInFlight = false;

        String token = currentToken;
        if (token == null) return;

        String permission = notificationPermissionStatus();
        if (permission.equals(prefs().getString(LAST_REPORTED_PERMISSION_KEY, null))) return;

        registerToken(resolvedExternalId(), token);
    }

    /**
     * Tells the backend this device has the app open right now — the signal
     * behind the dashboard's Realtime tab, and the only thing separating
     * "using the app" from register-device's "launched it at some point".
     *
     * <p>Silently skipped before registration completes; the next tick picks
     * it up once a token exists.
     */
    private static void sendHeartbeat() {
        final String token = currentToken;
        if (token == null) return;

        executor.execute(() -> {
            try {
                JSONObject body = new JSONObject();
                body.put("app_key", appKey);
                body.put("token", token);
                postJson(baseUrl + "/heartbeat", body);
            } catch (JSONException e) {
                Log.w(TAG, "Failed to build heartbeat request", e);
            }
        });
    }

    private static void startHeartbeat() {
        if (!initialized) return;
        mainHandler.removeCallbacks(heartbeatRunnable);
        mainHandler.post(heartbeatRunnable);
    }

    private static void stopHeartbeat() {
        mainHandler.removeCallbacks(heartbeatRunnable);
    }

    /**
     * Catches permission changes made while the app was away — the system
     * prompt, or Android's own notification settings — without the host app
     * having to wire anything up.
     */
    private static void observeForegroundForPermissionChanges(Context context) {
        if (lifecycleCallbacksRegistered) return;
        Context applicationContext = context.getApplicationContext();
        if (!(applicationContext instanceof Application)) return;
        lifecycleCallbacksRegistered = true;

        ((Application) applicationContext).registerActivityLifecycleCallbacks(new Application.ActivityLifecycleCallbacks() {
            @Override
            public void onActivityResumed(Activity activity) {
                // Still waiting on an unanswered prompt — reading the
                // permission now would report a denial the user hasn't made.
                if (notificationPromptInFlight && !pausedSinceNotificationPrompt) return;
                syncNotificationPermissionIfChanged();
            }

            @Override
            public void onActivityPaused(Activity activity) {
                if (notificationPromptInFlight) pausedSinceNotificationPrompt = true;
            }

            @Override
            public void onActivityCreated(Activity activity, Bundle savedInstanceState) {
            }

            @Override
            public void onActivityStarted(Activity activity) {
                if (foregroundActivityCount++ == 0) startHeartbeat();
            }

            @Override
            public void onActivityStopped(Activity activity) {
                foregroundActivityCount = Math.max(0, foregroundActivityCount - 1);
                if (foregroundActivityCount == 0) stopHeartbeat();
            }

            @Override
            public void onActivitySaveInstanceState(Activity activity, Bundle outState) {
            }

            @Override
            public void onActivityDestroyed(Activity activity) {
            }
        });
    }

    private static void createNotificationChannel() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.O) return;

        NotificationChannel channel = new NotificationChannel(
                PusherHubMessagingService.CHANNEL_ID,
                "Notifications",
                NotificationManager.IMPORTANCE_HIGH);
        NotificationManager manager = (NotificationManager) appContext.getSystemService(Context.NOTIFICATION_SERVICE);
        if (manager != null) manager.createNotificationChannel(channel);
    }

    /**
     * Declare this directly in your manifest (as
     * {@code {yourpackage}.PusherHub$PusherHubMessagingService} — nested classes
     * use a $ in their manifest name) and you're done — see the SDK
     * Integration tab in the PusherHub dashboard for the exact snippet.
     *
     * Nested (rather than top-level, like the Kotlin SDK's equivalent
     * class) only because Java allows a single public top-level type per
     * file, and this SDK is deliberately one file — nesting it here as
     * {@code public static} keeps it a real public class Android's
     * reflection-based component loader can instantiate, without splitting
     * the SDK into two files.
     *
     * If you already have your own FirebaseMessagingService for other
     * purposes, don't use this class — instead call PusherHub.handleNewToken
     * from your own onNewToken(), and build/show the notification yourself
     * in your own onMessageReceived() using buildAndShowNotification (or
     * copy its body — it's a small, self-contained method).
     */
    public static class PusherHubMessagingService extends FirebaseMessagingService {

        static final String CHANNEL_ID = "pushhub_default";
        static final String EXTRA_NOTIFICATION_ID = "pushhub_notification_id";
        static final String EXTRA_DEEP_LINK = "pushhub_deep_link";
        static final String EXTRA_MESSAGE_ID = "pushhub_message_id";
        static final String EXTRA_CUSTOM_DATA = "pushhub_custom_data";

        @Override
        public void onNewToken(String token) {
        PusherHub.handleNewToken(token);
    }

    @Override
    public void onMessageReceived(RemoteMessage message) {
        // Only reaches here while the app is in the foreground — for a
        // backgrounded or killed app, Android shows the notification.notification
        // block automatically and this method never fires (see FcmService::deliver()
        // server-side, which always sends both blocks). The tap is handled by
        // PusherHub.handleIntent() from your launcher Activity in that case.
        buildAndShowNotification(this, message);
    }

    /**
     * Builds and displays a system notification from an FCM RemoteMessage,
     * with a tap action wired to PusherHub.handleIntent via the same
     * extras/action a background-delivered notification's tap carries —
     * exposed as a standalone method so a host app with its own
     * FirebaseMessagingService can still get PusherHub's notification
     * handling without using PusherHubMessagingService itself.
     */
    void buildAndShowNotification(Context context, RemoteMessage message) {
        RemoteMessage.Notification notification = message.getNotification();
        String title = notification != null ? notification.getTitle() : message.getData().get("title");
        String body = notification != null ? notification.getBody() : message.getData().get("body");
        String notificationId = message.getData().get("notification_id");
        String deepLink = message.getData().get("deep_link");

        Intent launchIntent = context.getPackageManager().getLaunchIntentForPackage(context.getPackageName());
        if (launchIntent == null) launchIntent = new Intent();
        launchIntent.setAction(PusherHub.ACTION_NOTIFICATION_CLICK);
        launchIntent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_CLEAR_TOP);
        if (notificationId != null) launchIntent.putExtra(EXTRA_NOTIFICATION_ID, notificationId);
        if (deepLink != null) launchIntent.putExtra(EXTRA_DEEP_LINK, deepLink);
        if (message.getMessageId() != null) launchIntent.putExtra(EXTRA_MESSAGE_ID, message.getMessageId());
        // The Custom Data, for onNotificationOpened — a notification Android
        // shows itself carries the push's data keys on its tap already.
        Bundle customData = new Bundle();
        for (Map.Entry<String, String> entry : message.getData().entrySet()) {
            if (!OWN_DATA_KEYS.contains(entry.getKey())) customData.putString(entry.getKey(), entry.getValue());
        }
        launchIntent.putExtra(EXTRA_CUSTOM_DATA, customData);

        PendingIntent pendingIntent = PendingIntent.getActivity(
                context,
                notificationId != null ? notificationId.hashCode() : 0,
                launchIntent,
                PendingIntent.FLAG_UPDATE_CURRENT | PendingIntent.FLAG_IMMUTABLE);

        NotificationCompat.Builder builder = new NotificationCompat.Builder(context, CHANNEL_ID)
                .setContentTitle(title)
                .setContentText(body)
                .setAutoCancel(true)
                .setContentIntent(pendingIntent)
                .setPriority(NotificationCompat.PRIORITY_HIGH)
                // Replace with your own app icon — a launcher/notification icon
                // is required and there's no safe generic default to fall back
                // to here (unlike title/body, this can't come from the payload).
                .setSmallIcon(context.getApplicationInfo().icon);

        // message.getNotification().getImageUrl() / message.getData().get("image")
        // carries the notification image, if any — showing it needs a
        // BigPictureStyle with the bitmap already downloaded, which needs an
        // image-loading library (Coil/Glide). Deliberately not bundled here
        // to keep this SDK dependency-free; add one yourself and call
        // .setStyle(new NotificationCompat.BigPictureStyle()...) if you want that.

        // Required on Android 13+ (API 33) — posting without this granted
        // throws a SecurityException that would otherwise crash this
        // service's process the first time a push arrives after the user
        // denies (or hasn't yet granted) the runtime permission.
        boolean canPost = Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU
                || ContextCompat.checkSelfPermission(context, Manifest.permission.POST_NOTIFICATIONS) == PackageManager.PERMISSION_GRANTED;
        if (!canPost) return;

        NotificationManagerCompat.from(context).notify(
                notificationId != null ? notificationId.hashCode() : (int) System.currentTimeMillis(),
                builder.build());
    }
}

    /**
     * One in-app message returned by {@link #fetchInAppMessages} — a
     * banner, modal, fullscreen, center-popup, or bottom-sheet message the
     * backend decided this device is currently eligible to see.
     *
     * contentMode picks how it's meant to be rendered: "simple" uses
     * heading/body/image/buttonText (the fixed fields below); "blocks" uses
     * blocks, a list of {@code {type: text|image|button, ...}} maps
     * rendered in order; "html" uses htmlContent (render in a WebView).
     *
     * This SDK only fetches and tracks these — it doesn't include a
     * bundled rendering UI (unlike the Flutter SDK's PusherHubMessageHost).
     * Build your own banner/dialog from this data.
     *
     * Nested (rather than top-level, like the Kotlin SDK's equivalent
     * class) for the same single-file reason as
     * {@link PusherHubMessagingService} — nesting as {@code public static}
     * keeps it usable from outside this SDK's own package without
     * splitting the SDK into two files.
     */
    public static final class InAppMessage {
        public final int id;
        public final String type;
        public final String contentMode;
        public final String heading;
        public final String body;
        public final List<Map<String, Object>> blocks;
        public final String htmlContent;
        public final String image;
        public final String buttonText;
        public final String buttonDeepLink;
        public final String backgroundColor;
        public final String textColor;
        public final boolean showCloseButton;
        public final String closeIconUrl;
        public final String backgroundImage;
        public final Integer padding;
        public final Integer dismissAfterSeconds;
        public final Map<String, Object> customData;

        InAppMessage(
                int id,
                String type,
                String contentMode,
                String heading,
                String body,
                List<Map<String, Object>> blocks,
                String htmlContent,
                String image,
                String buttonText,
                String buttonDeepLink,
                String backgroundColor,
                String textColor,
                boolean showCloseButton,
                String closeIconUrl,
                String backgroundImage,
                Integer padding,
                Integer dismissAfterSeconds,
                Map<String, Object> customData) {
            this.id = id;
            this.type = type;
            this.contentMode = contentMode;
            this.heading = heading;
            this.body = body;
            this.blocks = blocks;
            this.htmlContent = htmlContent;
            this.image = image;
            this.buttonText = buttonText;
            this.buttonDeepLink = buttonDeepLink;
            this.backgroundColor = backgroundColor;
            this.textColor = textColor;
            this.showCloseButton = showCloseButton;
            this.closeIconUrl = closeIconUrl;
            this.backgroundImage = backgroundImage;
            this.padding = padding;
            this.dismissAfterSeconds = dismissAfterSeconds;
            this.customData = customData;
        }

        static InAppMessage fromJson(JSONObject json) throws JSONException {
            List<Map<String, Object>> blocks = new ArrayList<>();
            JSONArray blocksJson = json.optJSONArray("blocks");
            if (blocksJson != null) {
                for (int i = 0; i < blocksJson.length(); i++) {
                    blocks.add(toMap(blocksJson.getJSONObject(i)));
                }
            }
            JSONObject customDataJson = json.optJSONObject("custom_data");

            return new InAppMessage(
                    json.getInt("id"),
                    json.getString("type"),
                    json.optString("content_mode", "simple"),
                    optStringOrNull(json, "heading"),
                    optStringOrNull(json, "body"),
                    blocks,
                    optStringOrNull(json, "html_content"),
                    optStringOrNull(json, "image"),
                    optStringOrNull(json, "button_text"),
                    optStringOrNull(json, "button_deep_link"),
                    optStringOrNull(json, "background_color"),
                    optStringOrNull(json, "text_color"),
                    json.optBoolean("show_close_button", true),
                    optStringOrNull(json, "close_icon_url"),
                    optStringOrNull(json, "background_image"),
                    (json.has("padding") && !json.isNull("padding")) ? json.optInt("padding") : null,
                    (json.has("dismiss_after_seconds") && !json.isNull("dismiss_after_seconds")) ? json.optInt("dismiss_after_seconds") : null,
                    customDataJson != null ? toMap(customDataJson) : null);
        }

        private static String optStringOrNull(JSONObject json, String key) {
            return (json.has(key) && !json.isNull(key)) ? json.optString(key) : null;
        }

        // JSONObject.get() returns nested objects/arrays as raw org.json
        // types, not a plain Map/List — without this, a block's
        // "click_action" (itself a nested JSON object) would come back as
        // a JSONObject that a Map cast silently fails on, breaking every
        // block click handler with no error.
        private static Map<String, Object> toMap(JSONObject json) {
            Map<String, Object> map = new HashMap<>();
            Iterator<String> keys = json.keys();
            while (keys.hasNext()) {
                String key = keys.next();
                map.put(key, toJavaValue(json.opt(key)));
            }
            return map;
        }

        private static Object toJavaValue(Object value) {
            if (value instanceof JSONObject) {
                return toMap((JSONObject) value);
            } else if (value instanceof JSONArray) {
                JSONArray array = (JSONArray) value;
                List<Object> list = new ArrayList<>();
                for (int i = 0; i < array.length(); i++) {
                    list.add(toJavaValue(array.opt(i)));
                }
                return list;
            } else if (value == JSONObject.NULL) {
                return null;
            }
            return value;
        }
    }
}
