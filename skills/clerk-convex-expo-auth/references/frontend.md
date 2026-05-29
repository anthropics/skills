# Frontend Implementation Reference

## Auth Provider (`components/auth/index.tsx`)

```typescript
import { ClerkProvider, useAuth } from "@clerk/clerk-expo";
import { ConvexReactClient } from "convex/react";
import { ConvexProviderWithClerk } from "convex/react-clerk";
import * as SecureStore from "expo-secure-store";

const convex = new ConvexReactClient(
  process.env.EXPO_PUBLIC_CONVEX_URL as string
);

const tokenCache = {
  async getToken(key: string) {
    return SecureStore.getItemAsync(key);
  },
  async saveToken(key: string, value: string) {
    return SecureStore.setItemAsync(key, value);
  },
};

export default function AuthProvider({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <ClerkProvider
      tokenCache={tokenCache}
      publishableKey={process.env.EXPO_PUBLIC_CLERK_PUBLISHABLE_KEY!}
    >
      <ConvexProviderWithClerk client={convex} useAuth={useAuth}>
        {children}
      </ConvexProviderWithClerk>
    </ClerkProvider>
  );
}
```

## Root Layout (`app/_layout.tsx`)

```typescript
import AuthProvider from "@/components/auth";

export default function RootLayout() {
  return (
    <KeyboardProvider>
      <AuthProvider>
        <GestureHandlerRootView>
          <Stack screenOptions={{ headerShown: false }}>
            <Stack.Screen name="index" />
            <Stack.Screen name="Auth/sign-in" />
            <Stack.Screen name="Auth/verification" />
            <Stack.Screen name="Auth/nickname" />
          </Stack>
        </GestureHandlerRootView>
      </AuthProvider>
    </KeyboardProvider>
  );
}
```

## Route Protection (`app/index.tsx`)

### Option A: Imperative (useAuth)

```typescript
import { useAuth } from "@clerk/clerk-expo";
import { useQuery } from "convex/react";
import { Redirect } from "expo-router";
import { api } from "@/convex/_generated/api";

const Index = () => {
  const { isLoaded, isSignedIn } = useAuth();

  if (!isLoaded) return <LoadingScreen />;
  if (!isSignedIn) return <UnauthenticatedMenu />;

  return <AuthenticatedContent />;
};

const AuthenticatedContent = () => {
  const hasCompletedOnboarding = useQuery(api.onboarding.hasCompletedOnboarding);

  if (hasCompletedOnboarding === undefined) return <LoadingScreen />;
  if (!hasCompletedOnboarding) return <Redirect href="/Auth/nickname" />;

  return <MainApp />;
};
```

### Option B: Declarative (Convex components)

```typescript
import { Authenticated, Unauthenticated } from "convex/react";

const Index = () => (
  <>
    <Unauthenticated>
      <UnauthenticatedMenu />
    </Unauthenticated>
    <Authenticated>
      <AuthenticatedContent />
    </Authenticated>
  </>
);
```

Both approaches are equivalent -- `ConvexProviderWithClerk` uses Clerk's `useAuth` internally.

## Sign-In / Sign-Up Form

```typescript
import { useSignIn, useSignUp } from "@clerk/clerk-expo";

interface SignInFormProps {
  onSignInComplete: () => void;
  onSignUpNeedsVerification: (email: string) => void;
}

export default function SignInForm({
  onSignInComplete,
  onSignUpNeedsVerification,
}: SignInFormProps) {
  const { signIn, setActive: setSignInActive, isLoaded: isSignInLoaded } = useSignIn();
  const { signUp, setActive: setSignUpActive, isLoaded: isSignUpLoaded } = useSignUp();
  const [email, setEmail] = useState("");
  const [password, setPassword] = useState("");

  const handleSignIn = async () => {
    const signInAttempt = await signIn.create({
      identifier: email.trim(),
      password: password.trim(),
    });
    if (signInAttempt.status === "complete") {
      await setSignInActive({ session: signInAttempt.createdSessionId });
      onSignInComplete();
    }
  };

  const handleSignUp = async () => {
    await signUp.create({
      emailAddress: email.trim(),
      password: password.trim(),
    });
    await signUp.prepareEmailAddressVerification({ strategy: "email_code" });
    onSignUpNeedsVerification(email.trim());
  };

  // ... render email input, password input, sign-in/sign-up buttons
}
```

## Email Verification Form

```typescript
import { useSignUp } from "@clerk/clerk-expo";

interface VerificationFormProps {
  email: string;
  onVerificationComplete: () => void;
  onBack: () => void;
}

export default function VerificationForm({
  email,
  onVerificationComplete,
  onBack,
}: VerificationFormProps) {
  const { signUp, setActive } = useSignUp();
  const [code, setCode] = useState("");

  const handleVerifyCode = async () => {
    const signUpAttempt = await signUp.attemptEmailAddressVerification({
      code: code.trim(),
    });
    if (signUpAttempt.status === "complete") {
      await setActive({ session: signUpAttempt.createdSessionId });
      onVerificationComplete();
    }
  };

  const handleResendCode = async () => {
    await signUp.prepareEmailAddressVerification({ strategy: "email_code" });
  };

  // ... render code input, verify button, resend button
}
```

## Nickname / Onboarding Form

```typescript
import { useMutation } from "convex/react";
import { api } from "@/convex/_generated/api";

export default function NicknameForm({ onComplete }: { onComplete: () => void }) {
  const setNickname = useMutation(api.onboarding.setNickname);
  const skipNickname = useMutation(api.onboarding.skipNickname);
  const [nickname, setNicknameValue] = useState("");

  const handleSubmit = async () => {
    if (!/^[a-zA-Z0-9_]+$/.test(nickname) || nickname.length < 3) return;
    await setNickname({ nickname });
    onComplete();
  };

  const handleSkip = async () => {
    await skipNickname();
    onComplete();
  };

  // ... render nickname input, submit button, skip button
}
```

## Apple Sign-In (iOS Only)

```typescript
import { useSignInWithApple } from "@clerk/clerk-expo";
import * as AppleAuthentication from "expo-apple-authentication";
import { Platform } from "react-native";

export function AppleSignInButton({ onSignInComplete }: { onSignInComplete?: () => void }) {
  const { startAppleAuthenticationFlow } = useSignInWithApple();

  const handleAppleSignIn = async () => {
    try {
      const { createdSessionId, setActive } = await startAppleAuthenticationFlow();
      if (createdSessionId && setActive) {
        await setActive({ session: createdSessionId });
        onSignInComplete?.();
      }
    } catch (err: any) {
      if (err.code === "ERR_REQUEST_CANCELED") return;
      Alert.alert("Error", err.message);
    }
  };

  if (Platform.OS !== "ios") return null;

  return (
    <AppleAuthentication.AppleAuthenticationButton
      buttonType={AppleAuthentication.AppleAuthenticationButtonType.SIGN_IN}
      buttonStyle={
        colorScheme === "dark"
          ? AppleAuthentication.AppleAuthenticationButtonStyle.WHITE
          : AppleAuthentication.AppleAuthenticationButtonStyle.BLACK
      }
      cornerRadius={20}
      style={{ width: "100%", height: 55 }}
      onPress={handleAppleSignIn}
    />
  );
}
```

## Auth Modal (Multi-Step Flow)

```typescript
export function AuthModal({ visible, onClose }: AuthModalProps) {
  const [currentScreen, setCurrentScreen] = useState<
    "signIn" | "verification" | "nickname"
  >("signIn");
  const [email, setEmail] = useState("");

  return (
    <Modal visible={visible} animationType="slide" presentationStyle="pageSheet">
      {currentScreen === "signIn" && (
        <SignInForm
          onSignInComplete={onClose}
          onSignUpNeedsVerification={(email) => {
            setEmail(email);
            setCurrentScreen("verification");
          }}
        />
      )}
      {currentScreen === "verification" && (
        <VerificationForm
          email={email}
          onVerificationComplete={() => setCurrentScreen("nickname")}
          onBack={() => setCurrentScreen("signIn")}
        />
      )}
      {currentScreen === "nickname" && (
        <NicknameForm onComplete={onClose} />
      )}
    </Modal>
  );
}
```

**Flow:** Sign In/Up -> Email Verification -> Nickname Setup -> Done

## Sign-Out & Account Deletion

```typescript
import { useAuth, useUser } from "@clerk/clerk-expo";

const { signOut } = useAuth();
const { user: clerkUser } = useUser();

// Sign out
const handleSignOut = async () => {
  await signOut();
};

// Delete account (triggers webhook cascade)
const handleDeleteAccount = async () => {
  await clerkUser?.delete();
};
```

## User Online/Offline Status Hook

```typescript
import { useConvexAuth } from "convex/react";
import { AppState } from "react-native";

export const useUserStatus = () => {
  const setUserStatus = useMutation(api.users.setUserStatus);
  const { isAuthenticated } = useConvexAuth();

  useEffect(() => {
    if (isAuthenticated) {
      setUserStatus({ status: "online" });
    }

    const subscription = AppState.addEventListener("change", (nextAppState) => {
      if (isAuthenticated) {
        setUserStatus({
          status: nextAppState === "active" ? "online" : "offline",
        });
      }
    });

    return () => {
      if (isAuthenticated) setUserStatus({ status: "offline" });
      subscription.remove();
    };
  }, [isAuthenticated]);
};
```
