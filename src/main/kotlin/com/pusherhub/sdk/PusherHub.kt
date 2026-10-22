package com.pusherhub.sdk

import android.Manifest
import android.app.Activity
import android.app.Application
import android.app.Dialog
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.content.pm.PackageManager
import android.graphics.BitmapFactory
import android.graphics.Color
import android.graphics.Paint
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.location.Geocoder
import android.location.Location
import android.location.LocationManager
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.util.Log
import android.view.Gravity
import android.view.View
import android.view.ViewGroup
import android.view.ViewTreeObserver
import android.webkit.JavascriptInterface
import android.webkit.WebView
import android.widget.Button
import android.widget.FrameLayout
import android.widget.ImageView
import android.widget.LinearLayout
import android.widget.TextView
import androidx.core.app.ActivityCompat
import androidx.core.app.NotificationCompat
import androidx.core.app.NotificationManagerCompat
import androidx.core.content.ContextCompat
import com.google.firebase.messaging.FirebaseMessaging
import com.google.firebase.messaging.FirebaseMessagingService
import com.google.firebase.messaging.RemoteMessage
import org.json.JSONArray
import org.json.JSONObject
import java.io.OutputStreamWriter
import java.lang.ref.WeakReference
import java.net.HttpURLConnection
import java.net.URL
import java.util.Locale
import java.util.TimeZone
import java.util.UUID
import java.util.concurrent.Executors

/**
 * PusherHub push notification + in-app messaging client for native Android.
 *
 * Required setup (this is the whole "core" tier — everything else on this
 * object is optional), called from an Activity (see [initialize]'s doc for
 * why):
 *
 *   PusherHub.initialize(this, appKey = "...", publicKey = "...", baseUrl = "...")
 *   PusherHub.registerDevice()
 *
 * You also need [PusherHubMessagingService] declared in your manifest (see the
 * SDK Integration tab in the PusherHub dashboard for the exact snippet) so
 * incoming pushes and token refreshes reach this object.
 *
 * This whole SDK is one file (this one) — drop it straight into your
 * project's source tree, e.g. app/src/main/java/com/pusherhub/sdk/PusherHub.kt.
 */
object PusherHub {

    private const val TAG = "PusherHub"
    private const val PREFS_NAME = "pushhub_prefs"
    private const val ANONYMOUS_ID_KEY = "pushhub_anonymous_id_v2"

    // The signed-in user's ID from login() (or registerDevice(externalId)),
    // kept across restarts until logout(): without it, the next launch's
    // plain registerDevice() quietly turned the device anonymous again.
    private const val EXTERNAL_ID_KEY = "pushhub_external_id"

    // Survives restarts so a denial stays distinguishable from a fresh
    // install that has never been asked — see [notificationPermissionStatus].
    private const val PERMISSION_PROMPTED_KEY = "pushhub_notification_permission_prompted"

    // The last value the backend successfully accepted, so a resume that
    // found nothing changed costs nothing.
    private const val LAST_REPORTED_PERMISSION_KEY = "pushhub_last_reported_notification_permission"

    // The last FCM token the backend accepted. FCM rotates tokens without a
    // reinstall; reporting the one being replaced lets the backend keep this
    // install as the same device rather than counting a new install plus,
    // later, an uninstall. Cleared with the app's data on reinstall, which is
    // exactly when a new device row is the right answer.
    private const val LAST_REGISTERED_TOKEN_KEY = "pushhub_last_registered_token"

    /**
     * The action PusherHub's backend hardcodes into every FCM payload's
     * android.notification.click_action (a holdover from the Flutter SDK,
     * where it's required — see FcmService::deliver() server-side). A native
     * app's launcher Activity needs an <intent-filter> matching this same
     * action, or a background/killed-state notification tap won't reach it.
     * See PusherHub.handleIntent().
     */
    const val ACTION_NOTIFICATION_CLICK = "FLUTTER_NOTIFICATION_CLICK"

    // Matches the window the backend's Realtime tab buckets by. Anything
    // faster just upserts the same minute row for no extra information.
    private const val HEARTBEAT_INTERVAL_MS = 60_000L

    private const val REQUEST_CODE_NOTIFICATIONS = 9427
    private const val REQUEST_CODE_LOCATION = 9428

    private lateinit var appContext: Context
    private lateinit var appKey: String
    private lateinit var publicKey: String
    private lateinit var baseUrl: String
    private var onNotificationClick: ((String) -> Unit)? = null
    private var initialized = false

    // Only set when initialize() was called with an Activity (e.g. from
    // MainActivity.onCreate(), not an Application subclass) — used solely to
    // show the POST_NOTIFICATIONS permission prompt, and held weakly so this
    // singleton can never be the reason that Activity leaks.
    private var activityRef: WeakReference<Activity>? = null

    @Volatile private var currentToken: String? = null
    @Volatile private var currentExternalId: String? = null

    // Collected once (collectDeviceMetadata) and re-sent on every later
    // registration — the backend's register-device endpoint replaces these
    // fields wholesale, so omitting them on a later call would wipe out
    // whatever was already stored server-side.
    private var deviceModel: String? = null
    private var deviceBrand: String? = null
    private var appVersion: String? = null
    private var language: String? = null
    private var country: String? = null
    private var timezone: String? = null
    private var state: String? = null
    private var city: String? = null

    private var pendingAfterLocationPermission: (() -> Unit)? = null

    // True from the moment the POST_NOTIFICATIONS prompt is shown until its
    // outcome is observed. Notifications read as disabled while the dialog
    // is still up, which would otherwise be reported as a denial the user
    // hasn't actually made yet.
    @Volatile private var notificationPromptInFlight = false

    // The system prompt is a translucent Activity stacked on the host's, so
    // the host is paused for as long as it's up — on every Android version.
    // That makes "resumed, having been paused since the prompt went out" the
    // reliable signal that the user has answered, and distinguishes it from
    // the host Activity's own first onResume, which arrives moments after
    // registerDevice() asked for the prompt and before the dialog is even
    // on screen.
    @Volatile private var pausedSinceNotificationPrompt = false

    private var lifecycleCallbacksRegistered = false

    // Counts started (not resumed) Activities, so a rotation or a push from
    // one screen to another never looks like the app went to the background.
    // Zero means the app genuinely isn't on screen and the heartbeat stops.
    private var foregroundActivityCount = 0

    private val heartbeatRunnable = object : Runnable {
        override fun run() {
            sendHeartbeat()
            mainHandler.postDelayed(this, HEARTBEAT_INTERVAL_MS)
        }
    }

    private val executor = Executors.newCachedThreadPool()
    private val mainHandler = Handler(Looper.getMainLooper())

    private val prefs: SharedPreferences
        get() = appContext.getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE)

    /** The identity currently registered with the backend — null until [registerDevice] completes. */
    val externalId: String? get() = currentExternalId

    /**
     * Call once, as early as possible — from MainActivity.onCreate() (or
     * whichever Activity launches first), not an Application subclass:
     * [registerDevice] needs an Activity in hand to show the notification
     * permission prompt, and there isn't one yet inside Application.onCreate().
     *
     * @param baseUrl your PusherHub server's API base URL:
     *   "https://pusherhub.com/api" for apps on pusherhub.com — the
     *   dashboard's SDK Integration tab shows it filled in. There's
     *   deliberately no default — a guessed one would silently point at
     *   the wrong server and registerDevice() would fail with nothing
     *   obviously wrong in your own code.
     * @param onNotificationClick optional — called instead of the SDK's
     *   default behavior (opening the link via ACTION_VIEW) when a tapped
     *   notification carries a deep link.
     */
    @JvmStatic
    @JvmOverloads
    fun initialize(
        context: Context,
        appKey: String,
        publicKey: String,
        baseUrl: String,
        onNotificationClick: ((String) -> Unit)? = null,
    ) {
        this.appContext = context.applicationContext
        this.appKey = appKey
        this.publicKey = publicKey
        this.baseUrl = baseUrl
        this.onNotificationClick = onNotificationClick
        this.initialized = true
        if (context is Activity) {
            activityRef = WeakReference(context)
        }
        observeForegroundForPermissionChanges(context)
        createNotificationChannel()
    }

    /**
     * Requests the FCM token and registers this device with the PusherHub
     * backend, as the user last signed in with [login] — remembered across
     * restarts until [logout] — or, with nobody signed in, a persistent
     * anonymous ID generated on first launch (matching OneSignal's default
     * anonymous-subscription behavior). Passing [externalId] here is the
     * same as calling [login] with it.
     *
     * Registration finishes asynchronously (it needs the FCM token first),
     * so pass [onComplete] if you need to sequence something after it —
     * e.g. `PusherHub.registerDevice { PusherHub.collectDeviceMetadata() }` —
     * rather than calling that right after this returns.
     */
    @JvmStatic
    @JvmOverloads
    fun registerDevice(externalId: String? = null, onComplete: (() -> Unit)? = null) {
        if (!requireInitialized()) return

        requestNotificationPermissionIfNeeded()

        if (externalId != null) rememberExternalId(externalId)

        // Throws IllegalStateException if FirebaseApp hasn't been
        // initialized yet — the most common cause is google-services.json
        // not being present for this build, or the
        // com.google.gms.google-services plugin not being applied. Caught
        // here so a missing/incomplete Firebase setup logs a clear,
        // actionable message instead of crashing the whole host app on
        // this call.
        val firebaseMessaging = try {
            FirebaseMessaging.getInstance()
        } catch (e: IllegalStateException) {
            Log.e(TAG, "FirebaseApp isn't initialized — add google-services.json and apply the " +
                "com.google.gms.google-services plugin (see the SDK Integration tab), then rebuild.", e)
            return
        }

        firebaseMessaging.token.addOnCompleteListener { task ->
            if (!task.isSuccessful) {
                Log.w(TAG, "Failed to retrieve FCM token", task.exception)
                return@addOnCompleteListener
            }
            val token = task.result ?: return@addOnCompleteListener
            currentToken = token
            // Read now, not when registerDevice() was called: a login() or
            // logout() while the token was on its way counts.
            registerToken(resolvedExternalId(), token)
            onComplete?.invoke()
        }
    }

    /**
     * Call this from your FirebaseMessagingService.onNewToken(token) — see
     * [PusherHubMessagingService], which already does this for you if you use
     * it directly instead of your own service class.
     */
    @JvmStatic
    fun handleNewToken(token: String) {
        if (!initialized) return
        currentToken = token
        registerToken(resolvedExternalId(), token)
    }

    /**
     * Aliases this device to a real signed-in user — equivalent to
     * `OneSignal.login(externalId)` — and remembers it on the device, so
     * every later launch registers as this user too, until [logout].
     * Re-registers the same FCM token under the new external_id, so the
     * backend re-links the existing device row instead of creating a
     * duplicate. Called before [registerDevice] has finished, the ID is
     * still remembered and used as soon as it does.
     */
    @JvmStatic
    fun login(externalId: String) {
        if (!requireInitialized()) return
        rememberExternalId(externalId)
        val token = currentToken ?: return
        registerToken(externalId, token)
    }

    /** Reverts this device back to its anonymous identity, and forgets the signed-in user — call this on sign-out. */
    @JvmStatic
    fun logout() {
        if (!requireInitialized()) return
        prefs.edit().remove(EXTERNAL_ID_KEY).apply()
        val token = currentToken ?: return
        registerToken(getOrCreateAnonymousId(), token)
    }

    private fun rememberExternalId(externalId: String) {
        prefs.edit().putString(EXTERNAL_ID_KEY, externalId).apply()
    }

    /** Who this device registers as: the signed-in user (see [login]), or the anonymous ID. */
    private fun resolvedExternalId(): String =
        prefs.getString(EXTERNAL_ID_KEY, null) ?: getOrCreateAnonymousId()

    /**
     * Optional: enriches this device's record with brand, model, app
     * version, language, country, timezone, state, and city.
     *
     * Brand/model/version/language/timezone are read directly from the OS —
     * no permission needed for those. State and city additionally need a
     * GPS fix + reverse geocoding: this prompts for ACCESS_COARSE_LOCATION
     * (needs the Activity captured in [initialize] — same requirement as
     * the notification permission) and uses Android's own built-in
     * Geocoder, so no extra dependency or API key is needed for this
     * either. If location is denied, unavailable, or there's no Activity to
     * prompt from, this fails quietly and state/city simply stay unset —
     * it never blocks the rest of registration.
     *
     * Forward your Activity's onRequestPermissionsResult() to
     * [PusherHub.onRequestPermissionsResult] or the location prompt's result
     * will never reach this call.
     *
     * Safe to call any time after [registerDevice] has completed.
     */
    @JvmStatic
    fun collectDeviceMetadata() {
        val token = currentToken
        if (token == null) {
            Log.w(TAG, "collectDeviceMetadata() called before registerDevice() completed.")
            return
        }
        // The same identity registerDevice() registered with — not
        // currentExternalId, which is only set once registerToken()'s own
        // background network call finishes: calling this from
        // registerDevice()'s onComplete (the documented, recommended way)
        // races ahead of that.
        val externalId = resolvedExternalId()

        deviceBrand = Build.MANUFACTURER
        deviceModel = Build.MODEL
        appVersion = try {
            val pm = appContext.packageManager
            pm.getPackageInfo(appContext.packageName, 0).versionName
        } catch (e: Exception) {
            null
        }
        language = Locale.getDefault().language
        country = Locale.getDefault().country
        timezone = TimeZone.getDefault().id

        resolveStateAndCity {
            registerToken(externalId, token)
        }
    }

    /**
     * Forward your Activity's
     * onRequestPermissionsResult(requestCode, permissions, grantResults)
     * here.
     *
     * Required if you call [collectDeviceMetadata] (which may prompt for
     * location). Optional for the notification permission: forwarding just
     * reports the user's answer to the backend the instant they tap
     * Allow/Don't allow instead of on the app's next foreground.
     */
    @JvmStatic
    fun onRequestPermissionsResult(requestCode: Int) {
        if (requestCode == REQUEST_CODE_NOTIFICATIONS) {
            syncNotificationPermissionIfChanged()
            return
        }
        if (requestCode != REQUEST_CODE_LOCATION) return
        val callback = pendingAfterLocationPermission
        pendingAfterLocationPermission = null
        callback?.invoke()
    }

    /**
     * Resolves [state]/[city] (and overrides [country] with the geocoded
     * value, more trustworthy than the locale-based guess) via GPS + Android's
     * built-in Geocoder, then always calls [onComplete] — whether resolution
     * succeeded, failed, or was skipped entirely.
     */
    private fun resolveStateAndCity(onComplete: () -> Unit) {
        val hasPermission = ContextCompat.checkSelfPermission(appContext, Manifest.permission.ACCESS_COARSE_LOCATION) == PackageManager.PERMISSION_GRANTED
        if (hasPermission) {
            fetchLocationAndGeocode(onComplete)
            return
        }

        val activity = activityRef?.get()
        if (activity == null) {
            Log.w(TAG, "Location permission not granted and no Activity available to request it — skipping state/city resolution.")
            onComplete()
            return
        }

        pendingAfterLocationPermission = {
            if (ContextCompat.checkSelfPermission(appContext, Manifest.permission.ACCESS_COARSE_LOCATION) == PackageManager.PERMISSION_GRANTED) {
                fetchLocationAndGeocode(onComplete)
            } else {
                Log.w(TAG, "Location permission denied — skipping state/city resolution.")
                onComplete()
            }
        }
        ActivityCompat.requestPermissions(activity, arrayOf(Manifest.permission.ACCESS_COARSE_LOCATION), REQUEST_CODE_LOCATION)
    }

    private fun fetchLocationAndGeocode(onComplete: () -> Unit) {
        executor.execute {
            val cached = try {
                @Suppress("MissingPermission")
                bestLastKnownLocation()
            } catch (e: SecurityException) {
                null
            }

            if (cached != null) {
                geocodeAndComplete(cached, onComplete)
                return@execute
            }

            // No cached fix (e.g. no other app on this device has used
            // location recently) — request a fresh one instead of giving up,
            // since that's the common case on a freshly-installed app.
            mainHandler.post { requestFreshLocation(onComplete) }
        }
    }

    /**
     * The freshest cached fix from whichever location provider has one —
     * good enough for state/city-level accuracy without the latency (or
     * battery cost) of requesting a brand-new GPS fix just for this.
     */
    private fun bestLastKnownLocation(): Location? {
        val locationManager = appContext.getSystemService(Context.LOCATION_SERVICE) as? LocationManager ?: return null
        return listOf(LocationManager.GPS_PROVIDER, LocationManager.NETWORK_PROVIDER, LocationManager.PASSIVE_PROVIDER)
            .mapNotNull { provider ->
                try {
                    if (locationManager.isProviderEnabled(provider)) locationManager.getLastKnownLocation(provider) else null
                } catch (e: SecurityException) {
                    null
                }
            }
            .maxByOrNull { it.time }
    }

    /**
     * Asks for a single fresh fix (network provider preferred — faster and
     * plenty precise for state/city) and waits up to 10s. Must run on a
     * thread with a Looper, since [LocationManager] delivers its callback
     * there — called via [mainHandler] for that reason.
     */
    @Suppress("MissingPermission")
    private fun requestFreshLocation(onComplete: () -> Unit) {
        val locationManager = appContext.getSystemService(Context.LOCATION_SERVICE) as? LocationManager
        val provider = listOf(LocationManager.NETWORK_PROVIDER, LocationManager.GPS_PROVIDER)
            .firstOrNull { p -> runCatching { locationManager?.isProviderEnabled(p) }.getOrDefault(false) == true }

        if (locationManager == null || provider == null) {
            Log.w(TAG, "No location provider available — skipping state/city resolution.")
            onComplete()
            return
        }

        var completed = false
        val listener = object : android.location.LocationListener {
            override fun onLocationChanged(location: Location) {
                if (completed) return
                completed = true
                locationManager.removeUpdates(this)
                executor.execute { geocodeAndComplete(location, onComplete) }
            }
        }

        try {
            @Suppress("DEPRECATION") // requestSingleUpdate still works on every supported version and needs no extra dependency (unlike the fused location API).
            locationManager.requestSingleUpdate(provider, listener, Looper.getMainLooper())
        } catch (e: Exception) {
            Log.w(TAG, "Failed to request a location update — skipping state/city resolution.", e)
            onComplete()
            return
        }

        mainHandler.postDelayed({
            if (!completed) {
                completed = true
                locationManager.removeUpdates(listener)
                Log.w(TAG, "Timed out waiting for a location fix — skipping state/city resolution.")
                onComplete()
            }
        }, 10_000L)
    }

    private fun geocodeAndComplete(location: Location, onComplete: () -> Unit) {
        try {
            @Suppress("DEPRECATION") // The listener-based API is Android 33+ only; this synchronous one still works on every version and is simplest for a single one-off lookup.
            val addresses = Geocoder(appContext, Locale.getDefault()).getFromLocation(location.latitude, location.longitude, 1)
            val address = addresses?.firstOrNull()
            if (address != null) {
                state = address.adminArea
                city = address.locality
                if (!address.countryName.isNullOrEmpty()) {
                    country = address.countryName
                }
            }
        } catch (e: Exception) {
            Log.w(TAG, "Failed to resolve state/city via geocoding", e)
        }

        mainHandler.post { onComplete() }
    }

    /**
     * Fetches the in-app messages currently eligible for this device —
     * active, within their display window, matching this device's audience,
     * and not already shown once (for messages set to display only once).
     * Prefer [checkForInAppMessages] if you just want the SDK's own
     * rendering — call this instead only if you want to build entirely
     * custom UI from the raw data, then call [trackInAppShown]/
     * [trackInAppClick]/[trackInAppDismiss] yourself as appropriate.
     */
    @JvmStatic
    fun fetchInAppMessages(callback: (List<InAppMessage>) -> Unit) {
        val token = currentToken
        if (token == null) {
            Log.w(TAG, "Skipping fetchInAppMessages — no FCM token registered yet.")
            callback(emptyList())
            return
        }

        executor.execute {
            try {
                val body = JSONObject().apply {
                    put("app_key", appKey)
                    put("token", token)
                }
                val response = postJson("$baseUrl/fetch-in-app-messages", body)
                if (response == null) {
                    callback(emptyList())
                    return@execute
                }
                val messagesJson = response.optJSONArray("messages") ?: JSONArray()
                val messages = (0 until messagesJson.length()).mapNotNull { i ->
                    runCatching { InAppMessage.fromJson(messagesJson.getJSONObject(i)) }.getOrNull()
                }
                callback(messages)
            } catch (e: Exception) {
                Log.w(TAG, "Error fetching in-app messages", e)
                callback(emptyList())
            }
        }
    }

    /** Reports that [message] was actually displayed to the user. */
    @JvmStatic
    fun trackInAppShown(message: InAppMessage) = trackInAppEvent("track-in-app-shown", message.id)

    /** Reports that the user tapped [message]'s button. */
    @JvmStatic
    fun trackInAppClick(message: InAppMessage) = trackInAppEvent("track-in-app-click", message.id)

    /** Reports that [message] was closed without the button being tapped. */
    @JvmStatic
    fun trackInAppDismiss(message: InAppMessage) = trackInAppEvent("track-in-app-dismiss", message.id)

    private fun trackInAppEvent(endpoint: String, inAppMessageId: Int) {
        val token = currentToken
        if (token == null) {
            Log.w(TAG, "Skipping $endpoint — no FCM token registered yet.")
            return
        }
        executor.execute {
            val body = JSONObject().apply {
                put("app_key", appKey)
                put("in_app_message_id", inAppMessageId)
                put("token", token)
            }
            postJson("$baseUrl/$endpoint", body)
        }
    }

    // ---------------------------------------------------------------------
    // In-app message rendering — the native equivalent of the Flutter SDK's
    // PusherHubMessageHost widget. Built with plain Android views (no Compose,
    // no Material Components library, no image-loading library) so it works
    // in any Android app regardless of UI toolkit, keeping this SDK's only
    // real dependency as Firebase Messaging itself.
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
     * PusherHubMessageHost, which checks on every app open/resume the same way:
     *
     *   override fun onResume() {
     *       super.onResume()
     *       PusherHub.checkForInAppMessages(this)
     *   }
     */
    @JvmStatic
    fun checkForInAppMessages(activity: Activity) {
        fetchInAppMessages { messages ->
            val message = messages.firstOrNull() ?: return@fetchInAppMessages
            mainHandler.post {
                if (!activity.isFinishing && !activity.isDestroyed) {
                    showInAppMessage(activity, message)
                }
            }
        }
    }

    private sealed class InAppAction {
        data object Close : InAppAction()
        data class OpenUrl(val url: String) : InAppAction()
    }

    private fun showInAppMessage(activity: Activity, message: InAppMessage) {
        trackInAppShown(message)

        // Set once the dialog is closed via a click or the close button, so
        // the dismiss listener below doesn't also report a plain dismiss —
        // matching the Flutter SDK's semantics, where a click and a dismiss
        // are mutually exclusive outcomes for the same message.
        var actedOn = false

        val dialog = Dialog(activity, android.R.style.Theme_Translucent_NoTitleBar)
        val isFullscreen = message.type == "fullscreen"
        dialog.setCancelable(!isFullscreen)
        dialog.setCanceledOnTouchOutside(!isFullscreen)

        val contentView = buildMessageView(activity, message) { action ->
            when (action) {
                is InAppAction.Close -> {
                    actedOn = true
                    dialog.dismiss()
                }
                is InAppAction.OpenUrl -> {
                    actedOn = true
                    trackInAppClick(message)
                    openDeepLink(action.url)
                    dialog.dismiss()
                }
            }
        }
        dialog.setContentView(contentView)
        dialog.setOnDismissListener { if (!actedOn) trackInAppDismiss(message) }

        dialog.window?.apply {
            setBackgroundDrawableResource(android.R.color.transparent)
            val (gravity, width, height) = when (message.type) {
                "banner" -> Triple(Gravity.TOP, ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
                "bottom_sheet" -> Triple(Gravity.BOTTOM, ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
                "fullscreen" -> Triple(Gravity.CENTER, ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT)
                else -> Triple(Gravity.CENTER, ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT) // modal / center_popup
            }
            setGravity(gravity)
            setLayout(width, height)
        }

        dialog.show()

        val dismissAfter = message.dismissAfterSeconds
        if (dismissAfter != null && dismissAfter > 0) {
            mainHandler.postDelayed({ if (dialog.isShowing) dialog.dismiss() }, dismissAfter * 1000L)
        }
    }

    private fun buildMessageView(context: Context, message: InAppMessage, onAction: (InAppAction) -> Unit): View {
        if (message.contentMode == "html" && !message.htmlContent.isNullOrEmpty()) {
            return buildHtmlView(context, message, onAction)
        }

        val density = context.resources.displayMetrics.density
        fun dp(value: Int) = (value * density).toInt()

        val outer = FrameLayout(context)
        val outerMargin = if (message.type == "fullscreen") 0 else dp(8)
        outer.setPadding(outerMargin, outerMargin, outerMargin, outerMargin)

        // `card` is a FrameLayout (not the LinearLayout it used to be) so an
        // optional background image can sit behind `content` without taking
        // up flow space of its own. Giving that image MATCH_PARENT height as
        // a normal LinearLayout child of a WRAP_CONTENT card made it balloon
        // to fill the entire (also WRAP_CONTENT) dialog window — up to
        // screen height — pushing text down into whatever was left, instead
        // of a content-sized card with the image behind it (matching the
        // dashboard preview's CSS background-image, which paints behind
        // content rather than occupying its own box in the flow).
        val card = FrameLayout(context).apply {
            background = GradientDrawable().apply {
                cornerRadius = if (message.type == "fullscreen") 0f else dp(16).toFloat()
                setColor(parseColorOrDefault(message.backgroundColor, "#FFFFFF"))
            }
            clipToOutline = true
        }

        val content = LinearLayout(context).apply {
            orientation = LinearLayout.VERTICAL
            val pad = dp(message.padding ?: 16)
            setPadding(pad, pad, pad, pad)
        }

        val textColor = parseColorOrDefault(message.textColor, "#0F172A")
        if (message.contentMode == "blocks") {
            buildBlocksContent(context, content, message.blocks, textColor, onAction)
        } else {
            buildSimpleContent(context, content, message, textColor, onAction)
        }

        card.addView(content, FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))

        if (!message.backgroundImage.isNullOrEmpty()) {
            val bgImage = ImageView(context).apply { scaleType = ImageView.ScaleType.CENTER_CROP }
            loadImageAsync(message.backgroundImage, bgImage)
            // Starts at 0×0 so it can't inflate card's own (content-driven)
            // size during measurement, then gets resized to card's actual
            // final pixel bounds once known post-layout — an exact number,
            // not the ambiguous MATCH_PARENT that caused the bug above.
            card.addView(bgImage, 0, FrameLayout.LayoutParams(0, 0))
            card.viewTreeObserver.addOnGlobalLayoutListener(object : ViewTreeObserver.OnGlobalLayoutListener {
                override fun onGlobalLayout() {
                    card.viewTreeObserver.removeOnGlobalLayoutListener(this)
                    bgImage.layoutParams = FrameLayout.LayoutParams(card.width, card.height)
                }
            })
        }

        outer.addView(card, FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))

        if (message.showCloseButton) {
            outer.addView(
                TextView(context).apply {
                    text = "✕"
                    setTextColor(textColor)
                    textSize = 16f
                    setPadding(dp(12), dp(12), dp(12), dp(12))
                    setOnClickListener { onAction(InAppAction.Close) }
                },
                FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT).apply {
                    gravity = Gravity.TOP or Gravity.END
                },
            )
        }

        return outer
    }

    private fun buildSimpleContent(context: Context, container: LinearLayout, message: InAppMessage, textColor: Int, onAction: (InAppAction) -> Unit) {
        val density = context.resources.displayMetrics.density
        fun dp(value: Int) = (value * density).toInt()

        if (!message.image.isNullOrEmpty()) {
            // FIT_CENTER + adjustViewBounds + WRAP_CONTENT height shows the
            // whole image at its natural aspect ratio (matches the
            // dashboard preview's <img class="w-full"> — no crop, no
            // letterboxing) instead of cropping it to a fixed box.
            val image = ImageView(context).apply {
                scaleType = ImageView.ScaleType.FIT_CENTER
                adjustViewBounds = true
            }
            loadImageAsync(message.image, image)
            container.addView(image, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT))
        }

        if (!message.heading.isNullOrEmpty()) {
            container.addView(
                TextView(context).apply {
                    text = message.heading
                    setTextColor(textColor)
                    textSize = 18f
                    setTypeface(typeface, Typeface.BOLD)
                    setPadding(0, dp(8), 0, 0)
                },
            )
        }

        if (!message.body.isNullOrEmpty()) {
            container.addView(
                TextView(context).apply {
                    text = message.body
                    setTextColor(textColor)
                    alpha = 0.85f
                    textSize = 14f
                    setPadding(0, dp(4), 0, 0)
                },
            )
        }

        if (!message.buttonText.isNullOrEmpty()) {
            container.addView(
                Button(context).apply {
                    text = message.buttonText
                    setOnClickListener {
                        val link = message.buttonDeepLink
                        onAction(if (!link.isNullOrEmpty()) InAppAction.OpenUrl(link) else InAppAction.Close)
                    }
                },
                LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT).apply { topMargin = dp(12) },
            )
        }
    }

    private fun buildBlocksContent(context: Context, container: LinearLayout, blocks: List<Map<String, Any?>>, textColor: Int, onAction: (InAppAction) -> Unit) {
        val density = context.resources.displayMetrics.density
        fun dp(value: Int) = (value * density).toInt()

        blocks.forEach { block ->
            when (block["type"] as? String) {
                "text" -> container.addView(
                    TextView(context).apply {
                        text = block["text"] as? String ?: ""
                        setTextColor((block["color"] as? String)?.let { parseColorOrDefault(it, "#000000") } ?: textColor)
                        textSize = (block["font_size"] as? Number)?.toFloat() ?: 16f
                        val bold = block["bold"] == true
                        val italic = block["italic"] == true
                        setTypeface(
                            typeface,
                            when {
                                bold && italic -> Typeface.BOLD_ITALIC
                                bold -> Typeface.BOLD
                                italic -> Typeface.ITALIC
                                else -> Typeface.NORMAL
                            },
                        )
                        if (block["underline"] == true) paintFlags = paintFlags or Paint.UNDERLINE_TEXT_FLAG
                        gravity = when (block["align"] as? String) {
                            "left" -> Gravity.START
                            "right" -> Gravity.END
                            else -> Gravity.CENTER
                        }
                    },
                    LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT).apply { topMargin = dp(4); bottomMargin = dp(4) },
                )

                "image" -> {
                    val url = block["image"] as? String
                    if (!url.isNullOrEmpty()) {
                        // See buildSimpleContent's image for why FIT_CENTER +
                        // adjustViewBounds + WRAP_CONTENT (no crop, matches preview).
                        val image = ImageView(context).apply {
                            scaleType = ImageView.ScaleType.FIT_CENTER
                            adjustViewBounds = true
                        }
                        loadImageAsync(url, image)
                        image.setOnClickListener { handleBlockClick(block, onAction) }
                        container.addView(image, LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT).apply { topMargin = dp(4); bottomMargin = dp(4) })
                    }
                }

                "button" -> container.addView(
                    Button(context).apply {
                        text = block["text"] as? String ?: "Button"
                        setTextColor(parseColorOrDefault(block["font_color"] as? String, "#FFFFFF"))
                        background = GradientDrawable().apply {
                            setColor(parseColorOrDefault(block["background_color"] as? String, "#051B2C"))
                            cornerRadius = ((block["corner_radius"] as? Number)?.toFloat() ?: 8f) * density
                        }
                        setOnClickListener { handleBlockClick(block, onAction) }
                    },
                    LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT).apply { topMargin = dp(4) },
                )
            }
        }
    }

    private fun handleBlockClick(block: Map<String, Any?>, onAction: (InAppAction) -> Unit) {
        @Suppress("UNCHECKED_CAST")
        val clickAction = block["click_action"] as? Map<String, Any?>
        val value = clickAction?.get("value") as? String
        when (clickAction?.get("type") as? String) {
            "open_url", "deep_link" -> if (!value.isNullOrEmpty()) onAction(InAppAction.OpenUrl(value))
            "close" -> onAction(InAppAction.Close)
        }
    }

    /**
     * A WebView pre-wired with the same `PushHubIamApi` JavaScript bridge
     * documented on the dashboard's HTML in-app message editor —
     * `PushHubIamApi.close()`, `.openUrl(url)`, and `.trackClick()` all work
     * exactly as an admin authoring HTML content there expects.
     */
    private fun buildHtmlView(context: Context, message: InAppMessage, onAction: (InAppAction) -> Unit): View {
        val webView = WebView(context)
        webView.settings.javaScriptEnabled = true
        webView.addJavascriptInterface(
            object {
                @JavascriptInterface
                fun close() {
                    mainHandler.post { onAction(InAppAction.Close) }
                }

                @JavascriptInterface
                fun openUrl(url: String) {
                    mainHandler.post { onAction(InAppAction.OpenUrl(url)) }
                }

                @JavascriptInterface
                fun trackClick() {
                    trackInAppClick(message)
                }
            },
            "PushHubIamApi",
        )
        webView.loadDataWithBaseURL(null, message.htmlContent ?: "", "text/html", "UTF-8", null)
        return webView
    }

    private fun loadImageAsync(url: String, into: ImageView) {
        executor.execute {
            try {
                val connection = URL(url).openConnection() as HttpURLConnection
                connection.connectTimeout = 15_000
                connection.readTimeout = 15_000
                connection.doInput = true
                val bitmap = BitmapFactory.decodeStream(connection.inputStream)
                connection.disconnect()
                if (bitmap != null) {
                    mainHandler.post { into.setImageBitmap(bitmap) }
                }
            } catch (e: Exception) {
                Log.w(TAG, "Failed to load image: $url", e)
            }
        }
    }

    private fun parseColorOrDefault(hex: String?, default: String): Int {
        return try {
            Color.parseColor(hex?.takeIf { it.isNotBlank() } ?: default)
        } catch (e: Exception) {
            Color.parseColor(default)
        }
    }

    /**
     * Call this from your launcher Activity's onCreate(intent) and
     * onNewIntent(intent) — handles the case where the app was
     * backgrounded or fully killed and the user tapped a PusherHub
     * notification to (re)launch it. Reports the open (and click-through,
     * if the notification carried a deep link) and opens the deep link.
     *
     * (The "already in foreground" tap case is handled automatically by
     * [PusherHubMessagingService]'s own PendingIntent — you don't need to call
     * this for that path, but it's harmless to call unconditionally.)
     */
    @JvmStatic
    fun handleIntent(intent: Intent?) {
        intent ?: return
        // The prefixed extra is only present when PusherHub itself built the tap
        // PendingIntent (app was in the foreground when the push arrived). For a
        // backgrounded/killed app, Android auto-displays the notification from the
        // FCM payload and constructs the tap intent itself, carrying the payload's
        // raw data keys instead — so that's what's actually on the intent then.
        val notificationId = intent.getStringExtra(PusherHubMessagingService.EXTRA_NOTIFICATION_ID)
            ?: intent.getStringExtra("notification_id")
            ?: return
        val deepLink = intent.getStringExtra(PusherHubMessagingService.EXTRA_DEEP_LINK)
            ?: intent.getStringExtra("deep_link")
        handleNotificationOpened(notificationId, deepLink)
    }

    internal fun handleNotificationOpened(notificationId: String, deepLink: String?) {
        trackEvent("track-open", notificationId)
        if (!deepLink.isNullOrEmpty()) {
            trackEvent("track-click", notificationId)
            openDeepLink(deepLink)
        }
    }

    private fun openDeepLink(deepLink: String) {
        val callback = onNotificationClick
        if (callback != null) {
            callback(deepLink)
            return
        }

        try {
            val intent = Intent(Intent.ACTION_VIEW, Uri.parse(deepLink))
            intent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            appContext.startActivity(intent)
        } catch (e: Exception) {
            Log.w(TAG, "No handler available to open deep link: $deepLink", e)
        }
    }

    private fun trackEvent(endpoint: String, notificationId: String) {
        val token = currentToken
        if (token == null) {
            Log.w(TAG, "Skipping $endpoint — no FCM token registered yet.")
            return
        }
        executor.execute {
            val body = JSONObject().apply {
                put("app_key", appKey)
                put("notification_id", notificationId.toIntOrNull() ?: notificationId)
                put("token", token)
            }
            postJson("$baseUrl/$endpoint", body)
        }
    }

    private fun registerToken(externalId: String, token: String) {
        val permission = notificationPermissionStatus()
        executor.execute {
            val previousToken = prefs.getString(LAST_REGISTERED_TOKEN_KEY, null)
            val body = JSONObject().apply {
                put("app_key", appKey)
                put("external_id", externalId)
                put("token", token)
                // Covers both ways a rotation arrives: onNewToken while
                // running, and getToken() returning a different token on a
                // later launch.
                if (previousToken != null && previousToken != token) {
                    put("previous_token", previousToken)
                }
                put("platform", "android")
                put("device", deviceModel)
                put("brand", deviceBrand)
                put("version", appVersion)
                put("language", language)
                put("country", country)
                put("state", state)
                put("city", city)
                put("timezone", timezone)
                put("notification_permission", permission)
            }

            val response = postJson("$baseUrl/register-device", body)
            if (response != null) {
                currentExternalId = externalId
                // Only cached once the backend has actually taken it —
                // caching a value a failed request never delivered would
                // suppress the retry on the next resume. The token likewise:
                // if this request failed, the next attempt must still report
                // the old token as the one being replaced.
                prefs.edit()
                    .putString(LAST_REPORTED_PERMISSION_KEY, permission)
                    .putString(LAST_REGISTERED_TOKEN_KEY, token)
                    .apply()
                Log.i(TAG, "Device registered successfully.")
            } else {
                Log.w(TAG, "Failed to register device.")
            }
        }
    }

    /** Returns the parsed JSON response body, or null on any failure (network, non-2xx, bad JSON). */
    private fun postJson(urlString: String, body: JSONObject): JSONObject? {
        return try {
            val url = URL(urlString)
            val connection = url.openConnection() as HttpURLConnection
            connection.requestMethod = "POST"
            connection.setRequestProperty("Content-Type", "application/json")
            connection.setRequestProperty("Authorization", "Bearer $publicKey")
            // Harmless against a real server; needed only when baseUrl points
            // at a free-tier ngrok tunnel — without it, ngrok returns an HTML
            // "visit site" warning page instead of forwarding to PusherHub.
            connection.setRequestProperty("ngrok-skip-browser-warning", "true")
            connection.doOutput = true
            connection.connectTimeout = 15_000
            connection.readTimeout = 15_000

            OutputStreamWriter(connection.outputStream).use { it.write(body.toString()) }

            val code = connection.responseCode
            val stream = if (code in 200..299) connection.inputStream else connection.errorStream
            val text = stream?.bufferedReader()?.use { it.readText() } ?: ""
            connection.disconnect()

            if (code !in 200..299) {
                Log.w(TAG, "$urlString failed: HTTP $code $text")
                return null
            }

            if (text.isBlank()) JSONObject() else JSONObject(text)
        } catch (e: Exception) {
            Log.w(TAG, "Request to $urlString failed", e)
            null
        }
    }

    private fun getOrCreateAnonymousId(): String {
        prefs.getString(ANONYMOUS_ID_KEY, null)?.let { return it }

        val id = UUID.randomUUID().toString()
        prefs.edit().putString(ANONYMOUS_ID_KEY, id).apply()
        return id
    }

    private fun requireInitialized(): Boolean {
        if (!initialized) {
            Log.e(TAG, "PusherHub.initialize() must be called before this.")
        }
        return initialized
    }

    /**
     * Shows the system POST_NOTIFICATIONS prompt on Android 13+ if it
     * hasn't been granted (or denied) yet — a no-op below API 33, where the
     * permission doesn't exist and notifications just work. Needs the
     * Activity captured in [initialize] (see that function's doc) — if
     * initialize() was called from an Application subclass instead, this
     * logs a warning and does nothing, same as if you'd never called it;
     * request the permission yourself in that case.
     */
    private fun requestNotificationPermissionIfNeeded() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU) return
        if (ContextCompat.checkSelfPermission(appContext, Manifest.permission.POST_NOTIFICATIONS) == PackageManager.PERMISSION_GRANTED) return

        val activity = activityRef?.get()
        if (activity == null) {
            Log.w(
                TAG,
                "POST_NOTIFICATIONS isn't granted and no Activity is available to prompt for it " +
                    "(PusherHub.initialize() was called without one — see its doc comment). " +
                    "Notifications won't display until this permission is granted.",
            )
            return
        }

        notificationPromptInFlight = true
        pausedSinceNotificationPrompt = false
        prefs.edit().putBoolean(PERMISSION_PROMPTED_KEY, true).apply()
        ActivityCompat.requestPermissions(activity, arrayOf(Manifest.permission.POST_NOTIFICATIONS), REQUEST_CODE_NOTIFICATIONS)
    }

    /**
     * This device's notification permission as the backend records it:
     * "granted", "denied", or "not_determined".
     *
     * Built on NotificationManagerCompat.areNotificationsEnabled() rather
     * than only checking POST_NOTIFICATIONS, because that permission
     * doesn't exist below API 33 while a user on any version can still
     * switch the app's notifications off in system settings — and the
     * question the dashboard answers is "will a push actually reach this
     * device", not "was a runtime permission granted".
     */
    private fun notificationPermissionStatus(): String {
        if (NotificationManagerCompat.from(appContext).areNotificationsEnabled()) return "granted"

        // Off — but on API 33+ that's also the state of an install nobody
        // has asked yet, which isn't the same signal as a refusal.
        val neverAnswered = notificationPromptInFlight || !prefs.getBoolean(PERMISSION_PROMPTED_KEY, false)
        return if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU && neverAnswered) "not_determined" else "denied"
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
    private fun syncNotificationPermissionIfChanged() {
        if (!initialized) return

        // Every caller reaches here only once the prompt has resolved, so
        // what we read now is the user's actual answer.
        notificationPromptInFlight = false

        val token = currentToken ?: return
        if (notificationPermissionStatus() == prefs.getString(LAST_REPORTED_PERMISSION_KEY, null)) return

        registerToken(resolvedExternalId(), token)
    }

    /**
     * Tells the backend this device has the app open right now — the signal
     * behind the dashboard's Realtime tab, and the only thing separating
     * "using the app" from register-device's "launched it at some point".
     *
     * Silently skipped before registration completes; the next tick picks it
     * up once a token exists.
     */
    private fun sendHeartbeat() {
        val token = currentToken ?: return
        executor.execute {
            val body = JSONObject().apply {
                put("app_key", appKey)
                put("token", token)
            }
            postJson("$baseUrl/heartbeat", body)
        }
    }

    private fun startHeartbeat() {
        if (!initialized) return
        mainHandler.removeCallbacks(heartbeatRunnable)
        mainHandler.post(heartbeatRunnable)
    }

    private fun stopHeartbeat() {
        mainHandler.removeCallbacks(heartbeatRunnable)
    }

    /**
     * Catches permission changes made while the app was away — the system
     * prompt, or Android's own notification settings — without the host app
     * having to wire anything up.
     */
    private fun observeForegroundForPermissionChanges(context: Context) {
        if (lifecycleCallbacksRegistered) return
        val application = context.applicationContext as? Application ?: return
        lifecycleCallbacksRegistered = true

        application.registerActivityLifecycleCallbacks(object : Application.ActivityLifecycleCallbacks {
            override fun onActivityResumed(activity: Activity) {
                // Still waiting on an unanswered prompt — reading the
                // permission now would report a denial the user hasn't made.
                if (notificationPromptInFlight && !pausedSinceNotificationPrompt) return
                syncNotificationPermissionIfChanged()
            }

            override fun onActivityPaused(activity: Activity) {
                if (notificationPromptInFlight) pausedSinceNotificationPrompt = true
            }

            override fun onActivityStarted(activity: Activity) {
                if (foregroundActivityCount++ == 0) startHeartbeat()
            }

            override fun onActivityStopped(activity: Activity) {
                foregroundActivityCount = (foregroundActivityCount - 1).coerceAtLeast(0)
                if (foregroundActivityCount == 0) stopHeartbeat()
            }

            override fun onActivityCreated(activity: Activity, savedInstanceState: Bundle?) = Unit
            override fun onActivitySaveInstanceState(activity: Activity, outState: Bundle) = Unit
            override fun onActivityDestroyed(activity: Activity) = Unit
        })
    }

    private fun createNotificationChannel() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.O) return

        val channel = NotificationChannel(
            PusherHubMessagingService.CHANNEL_ID,
            "Notifications",
            NotificationManager.IMPORTANCE_HIGH,
        )
        val manager = appContext.getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
        manager.createNotificationChannel(channel)
    }
}

/**
 * Declare this directly in your manifest and you're done — see the SDK
 * Integration tab in the PusherHub dashboard for the exact snippet.
 *
 * If you already have your own FirebaseMessagingService for other purposes,
 * don't use this class — instead call [PusherHub.handleNewToken] from your own
 * onNewToken(), and build/show the notification yourself in your own
 * onMessageReceived() using [buildAndShowNotification] (or copy its body —
 * it's a small, self-contained function).
 */
class PusherHubMessagingService : FirebaseMessagingService() {

    companion object {
        const val CHANNEL_ID = "pushhub_default"
        const val EXTRA_NOTIFICATION_ID = "pushhub_notification_id"
        const val EXTRA_DEEP_LINK = "pushhub_deep_link"
    }

    override fun onNewToken(token: String) {
        PusherHub.handleNewToken(token)
    }

    override fun onMessageReceived(message: RemoteMessage) {
        // Only reaches here while the app is in the foreground — for a
        // backgrounded or killed app, Android shows the notification.notification
        // block automatically and this method never fires (see FcmService::deliver()
        // server-side, which always sends both blocks). The tap is handled by
        // PusherHub.handleIntent() from your launcher Activity in that case.
        buildAndShowNotification(this, message)
    }

    /**
     * Builds and displays a system notification from an FCM RemoteMessage,
     * with a tap action wired to [PusherHub.handleIntent] via the same
     * extras/action a background-delivered notification's tap carries —
     * exposed as a standalone function so a host app with its own
     * FirebaseMessagingService can still get PusherHub's notification
     * handling without using [PusherHubMessagingService] itself.
     */
    fun buildAndShowNotification(context: Context, message: RemoteMessage) {
        val title = message.notification?.title ?: message.data["title"]
        val body = message.notification?.body ?: message.data["body"]
        val notificationId = message.data["notification_id"]
        val deepLink = message.data["deep_link"]

        val launchIntent = context.packageManager.getLaunchIntentForPackage(context.packageName)
            ?: Intent()
        launchIntent.action = PusherHub.ACTION_NOTIFICATION_CLICK
        launchIntent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK or Intent.FLAG_ACTIVITY_CLEAR_TOP)
        if (notificationId != null) launchIntent.putExtra(EXTRA_NOTIFICATION_ID, notificationId)
        if (deepLink != null) launchIntent.putExtra(EXTRA_DEEP_LINK, deepLink)

        val pendingIntent = PendingIntent.getActivity(
            context,
            notificationId?.hashCode() ?: 0,
            launchIntent,
            PendingIntent.FLAG_UPDATE_CURRENT or PendingIntent.FLAG_IMMUTABLE,
        )

        val builder = NotificationCompat.Builder(context, CHANNEL_ID)
            .setContentTitle(title)
            .setContentText(body)
            .setAutoCancel(true)
            .setContentIntent(pendingIntent)
            .setPriority(NotificationCompat.PRIORITY_HIGH)
            // Replace with your own app icon — a launcher/notification icon
            // is required and there's no safe generic default to fall back
            // to here (unlike title/body, this can't come from the payload).
            .setSmallIcon(context.applicationInfo.icon)

        // message.notification?.imageUrl / message.data["image"] carries the
        // notification image, if any — showing it needs a BigPictureStyle
        // with the bitmap already downloaded, which needs an image-loading
        // library (Coil/Glide). Deliberately not bundled here to keep this
        // SDK dependency-free; add one yourself and set
        // .setStyle(NotificationCompat.BigPictureStyle()...) if you want that.

        // Required on Android 13+ (API 33) — posting without this granted
        // throws a SecurityException that would otherwise crash this
        // service's process the first time a push arrives after the user
        // denies (or hasn't yet granted) the runtime permission.
        val canPost = Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU ||
            ContextCompat.checkSelfPermission(context, Manifest.permission.POST_NOTIFICATIONS) == PackageManager.PERMISSION_GRANTED
        if (!canPost) return

        NotificationManagerCompat.from(context).notify(
            notificationId?.hashCode() ?: System.currentTimeMillis().toInt(),
            builder.build(),
        )
    }
}

/**
 * One in-app message returned by [PusherHub.fetchInAppMessages] — a banner,
 * modal, fullscreen, center-popup, or bottom-sheet message the backend
 * decided this device is currently eligible to see.
 *
 * [contentMode] picks how it's meant to be rendered: "simple" uses
 * [heading]/[body]/[image]/[buttonText] (the fixed fields below); "blocks"
 * uses [blocks], a list of `{type: text|image|button, ...}` maps rendered in
 * order; "html" uses [htmlContent] (render in a WebView).
 *
 * This SDK only fetches and tracks these — it doesn't include a bundled
 * rendering UI (unlike the Flutter SDK's PusherHubMessageHost). Build your own
 * banner/dialog from this data.
 */
data class InAppMessage(
    val id: Int,
    val type: String,
    val contentMode: String,
    val heading: String?,
    val body: String?,
    val blocks: List<Map<String, Any?>>,
    val htmlContent: String?,
    val image: String?,
    val buttonText: String?,
    val buttonDeepLink: String?,
    val backgroundColor: String?,
    val textColor: String?,
    val showCloseButton: Boolean,
    val closeIconUrl: String?,
    val backgroundImage: String?,
    val padding: Int?,
    val dismissAfterSeconds: Int?,
    val customData: Map<String, Any?>?,
) {
    companion object {
        fun fromJson(json: JSONObject): InAppMessage {
            return InAppMessage(
                id = json.getInt("id"),
                type = json.getString("type"),
                contentMode = json.optString("content_mode", "simple"),
                heading = json.optStringOrNull("heading"),
                body = json.optStringOrNull("body"),
                blocks = json.optJSONArray("blocks")?.let { array ->
                    (0 until array.length()).map { i -> array.getJSONObject(i).toMap() }
                } ?: emptyList(),
                htmlContent = json.optStringOrNull("html_content"),
                image = json.optStringOrNull("image"),
                buttonText = json.optStringOrNull("button_text"),
                buttonDeepLink = json.optStringOrNull("button_deep_link"),
                backgroundColor = json.optStringOrNull("background_color"),
                textColor = json.optStringOrNull("text_color"),
                showCloseButton = json.optBoolean("show_close_button", true),
                closeIconUrl = json.optStringOrNull("close_icon_url"),
                backgroundImage = json.optStringOrNull("background_image"),
                padding = if (json.has("padding") && !json.isNull("padding")) json.optInt("padding") else null,
                dismissAfterSeconds = if (json.has("dismiss_after_seconds") && !json.isNull("dismiss_after_seconds")) {
                    json.optInt("dismiss_after_seconds")
                } else {
                    null
                },
                customData = json.optJSONObject("custom_data")?.toMap(),
            )
        }
    }
}

private fun JSONObject.optStringOrNull(key: String): String? {
    return if (has(key) && !isNull(key)) getString(key) else null
}

private fun JSONObject.toMap(): Map<String, Any?> {
    val map = mutableMapOf<String, Any?>()
    keys().forEach { key -> map[key] = get(key).toKotlinValue() }
    return map
}

// JSONObject.get() returns nested objects/arrays as raw org.json types, not
// Kotlin Map/List — without this, a block's `click_action` (itself a nested
// JSON object) would come back as a JSONObject that `as? Map<String, Any?>`
// silently fails to cast, breaking every block click handler with no error.
private fun Any?.toKotlinValue(): Any? = when (this) {
    is JSONObject -> toMap()
    is JSONArray -> (0 until length()).map { get(it).toKotlinValue() }
    JSONObject.NULL -> null
    else -> this
}
