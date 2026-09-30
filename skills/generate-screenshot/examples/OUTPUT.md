# Example Output

## Basic single page (`/`)

```
screenshots/
├── home--desktop--light.png
├── home--desktop--dark.png
├── home--tablet--light.png
├── home--tablet--dark.png
├── home--mobile--light.png
└── home--mobile--dark.png
```

6 screenshots (1 route x 3 viewports x 2 modes)

## Multi-route (`/`, `/login`, `/dashboard`, `/settings`)

```
screenshots/
├── home--desktop--light.png
├── home--desktop--dark.png
├── home--tablet--light.png
├── home--tablet--dark.png
├── home--mobile--light.png
├── home--mobile--dark.png
├── login--desktop--light.png
├── login--desktop--dark.png
├── login--tablet--light.png
├── login--tablet--dark.png
├── login--mobile--light.png
├── login--mobile--dark.png
├── dashboard--desktop--light.png
├── dashboard--desktop--dark.png
├── dashboard--tablet--light.png
├── dashboard--tablet--dark.png
├── dashboard--mobile--light.png
├── dashboard--mobile--dark.png
├── settings--desktop--light.png
├── settings--desktop--dark.png
├── settings--tablet--light.png
├── settings--tablet--dark.png
├── settings--mobile--light.png
└── settings--mobile--dark.png
```

24 screenshots (4 routes x 3 viewports x 2 modes)

## Single viewport — desktop light only

```
screenshots/
├── home--desktop--light.png
├── login--desktop--light.png
├── dashboard--desktop--light.png
└── settings--desktop--light.png
```

4 screenshots (4 routes x 1 viewport x 1 mode)

## Authenticated pages (`/dashboard`, `/settings`, `/profile`)

```
screenshots/
├── dashboard--desktop--light.png
├── dashboard--desktop--dark.png
├── dashboard--tablet--light.png
├── dashboard--tablet--dark.png
├── dashboard--mobile--light.png
├── dashboard--mobile--dark.png
├── settings--desktop--light.png
├── settings--desktop--dark.png
├── settings--tablet--light.png
├── settings--tablet--dark.png
├── settings--mobile--light.png
├── settings--mobile--dark.png
├── profile--desktop--light.png
├── profile--desktop--dark.png
├── profile--tablet--light.png
├── profile--tablet--dark.png
├── profile--mobile--light.png
└── profile--mobile--dark.png
```

18 screenshots (3 routes x 3 viewports x 2 modes)

## Naming convention

```
{route}--{viewport}--{mode}.png
```

| Segment | Values |
|---------|--------|
| route | `home` for `/`, otherwise path with `/` replaced by `-` |
| viewport | `desktop`, `tablet`, `mobile` |
| mode | `light`, `dark` |
