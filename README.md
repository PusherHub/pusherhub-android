# PusherHub Android SDK (Kotlin and Java)

Push notifications and in-app messages for your native Android app, sent through your own Firebase project with [PusherHub](https://pusherhub.com).

[Website](https://pusherhub.com) · [Guides](https://pusherhub.com/docs) · [Pricing](https://pusherhub.com/pricing)

## What it does

- Registers each phone with PusherHub, asks for the notification permission, and keeps its FCM token up to date
- Links a phone to your own user id with `login()` — remembered across restarts until `logout()`
- Reports notification opens and clicks, and follows a notification's deep link
- Shows in-app messages (banner, modal, full screen, center popup, bottom sheet) with plain Android views — works with Compose and classic Views
- Optional device details, and state and city if you add the location permission

One file, two languages — use whichever your app is written in:

| Language | File |
|---|---|
| Kotlin | [`src/main/kotlin/com/pusherhub/sdk/PusherHub.kt`](src/main/kotlin/com/pusherhub/sdk/PusherHub.kt) |
| Java | [`src/main/java/com/pusherhub/sdk/PusherHub.java`](src/main/java/com/pusherhub/sdk/PusherHub.java) |

No extra libraries: the SDK uses Android's built-in `HttpURLConnection` and `org.json`.

## Before you start

1. A PusherHub account with your app added — it's free to start at [pusherhub.com](https://pusherhub.com).
2. Your app added to a Firebase project (`google-services.json` in your app module, Google services Gradle plugin applied), with the Firebase service account key uploaded to your app in PusherHub. See the [getting-started guide](https://pusherhub.com/docs/getting-started).
3. Your **app key** and **public key** — on your app's **SDK Integration** tab in PusherHub, which also shows every step below with your keys filled in.

## Install

1. Add Firebase Messaging to your app module:

   ```kotlin
   // app/build.gradle.kts
   dependencies {
       implementation(platform("com.google.firebase:firebase-bom:34.4.0"))
       implementation("com.google.firebase:firebase-messaging")
   }
   ```

   ```groovy
   // or app/build.gradle (Java projects)
   dependencies {
       implementation platform('com.google.firebase:firebase-bom:34.4.0')
       implementation 'com.google.firebase:firebase-messaging'
   }
   ```

2. Copy the SDK file into your app, and change its first line to a package inside your app — for example `package com.example.myapp.pusherhub`.
   *Easier:* download it from your app's SDK Integration tab in PusherHub — that copy already has your app's package.

3. Add to `AndroidManifest.xml`, inside your existing manifest (replace `com.example.myapp.pusherhub` with the package from step 2):

   ```xml
   <uses-permission android:name="android.permission.INTERNET"/>
   <uses-permission android:name="android.permission.POST_NOTIFICATIONS"/>
   <!-- Only if you want state and city from collectDeviceMetadata() -->
   <uses-permission android:name="android.permission.ACCESS_COARSE_LOCATION"/>

   <application ...>
       <activity android:name=".MainActivity" ...>
           <!-- Lets a notification tap reach your app when it's in the background or closed -->
           <intent-filter>
               <action android:name="FLUTTER_NOTIFICATION_CLICK"/>
               <category android:name="android.intent.category.DEFAULT"/>
           </intent-filter>
       </activity>

       <!-- Kotlin -->
       <service
           android:name="com.example.myapp.pusherhub.PusherHubMessagingService"
           android:exported="false">
           <intent-filter>
               <action android:name="com.google.firebase.MESSAGING_EVENT"/>
           </intent-filter>
       </service>
       <!-- Java: android:name="com.example.myapp.pusherhub.PusherHub$PusherHubMessagingService" -->
   </application>
   ```

   The action name `FLUTTER_NOTIFICATION_CLICK` is what PusherHub puts on every notification, so native apps match it too.

## Quick start (Kotlin)

Call it from your Activity — not an Application subclass — so it can ask for the notification permission.

```kotlin
class MainActivity : ComponentActivity() {
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        PusherHub.initialize(
            context = this,
            appKey = "YOUR_APP_KEY",
            publicKey = "YOUR_PUBLIC_KEY",
            baseUrl = "https://pusherhub.com/api",
        )

        // Required: registers this phone. Optional details once that's done.
        PusherHub.registerDevice {
            PusherHub.collectDeviceMetadata()
        }

        // A notification tap that launched the app.
        PusherHub.handleIntent(intent)
    }

    override fun onNewIntent(intent: Intent) {
        super.onNewIntent(intent)
        PusherHub.handleIntent(intent)
    }

    override fun onRequestPermissionsResult(requestCode: Int, permissions: Array<String>, grantResults: IntArray) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        PusherHub.onRequestPermissionsResult(requestCode)
    }

    override fun onResume() {
        super.onResume()
        // Optional: shows in-app messages on open and resume.
        PusherHub.checkForInAppMessages(this)
    }
}
```

## Quick start (Java)

```java
public class MainActivity extends AppCompatActivity {
    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        PusherHub.initialize(this, "YOUR_APP_KEY", "YOUR_PUBLIC_KEY", "https://pusherhub.com/api");

        PusherHub.registerDevice(() -> PusherHub.collectDeviceMetadata());

        PusherHub.handleIntent(getIntent());
    }

    @Override
    protected void onNewIntent(Intent intent) {
        super.onNewIntent(intent);
        PusherHub.handleIntent(intent);
    }

    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        PusherHub.onRequestPermissionsResult(requestCode);
    }

    @Override
    protected void onResume() {
        super.onResume();
        PusherHub.checkForInAppMessages(this);
    }
}
```

## Signed-in users

```kotlin
PusherHub.login(currentUserId)   // when someone signs in
PusherHub.logout()               // when they sign out
```

## Keys

The **public key** is meant to be built into your app. Never put your **secret key** in an app — it's only for your own server, with PusherHub's REST API.

## Help

- Step-by-step guides: [pusherhub.com/docs](https://pusherhub.com/docs)
- Your app's **SDK Integration** tab in PusherHub has every step with your keys filled in.

## License

[MIT](LICENSE)
