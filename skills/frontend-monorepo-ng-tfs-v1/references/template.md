# Technical Functional Specification (TFS)

**Purpose**: Translate an approved **PRD** into a concrete, frontend-oriented technical plan. This document defines _how the feature will be built_ in our Nx + Angular workspace, which libraries are required, and what **public contracts** (methods, inputs, outputs, and etc.) each library must expose.

---

- **TFS Status** (Draft / Reviewed / Approved): …
- **Last Updated** (YYYY‑MM‑DD): …
- **Owner**: …

---

<!--
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
-->

&nbsp;

## Overview

### Functionality Name

> kebab-case name of the functionality, with prefix such as 'ng-' (which stands for Angular), if it's a technology-specific fun.

{name}

### Functionality Classification

Choose **exactly one** type.

- **Hybrid** – Uses `map`, `data-access`, `ui`, and `feature` libs
- **Abstract** – Uses `map` and `data-access` libs only
- **Visual** – Uses `ui` and `feature` libs only

**Selected type**: …

### Rationale

> Explain _why_ this classification applies (data fetching, UI presentation, reuse of existing APIs, etc.).

…

<!--
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
-->

&nbsp;

## Existing Dependencies & Reuse

> List the libs that are already available in the workspace and will be reused in this functionality. Mention the libs' name (i.e., the one which is mentioned in `project.json` file of the lib).
> You can also specify more detailed info to specify what class and what method of the lib is used.  
> e.g., "`shared-util-ng-services` lib: `V1FormatterService` class: `formatNumFractionDigits`, `getUnitCost` methods".
>
> Reuse decisions are based on developer knowledge of the workspace.

### Used map / data-access libs

- 'map' libs:
  - …

- 'data-access' libs:
  - …

### Used ui / feature libs

- 'ui' libs:
  - …

- 'feature' libs:
  - …

### Used util libs

> Functionalities **must not create their own 'util' libs**. Instead they reuse existing 'util' libs. And if something should be built that is NOT already existed in a 'util' lib, then again the developer must mention that 'util' lib name here and build it later.

**What are 'util' libs?** These are libs that contain low-level utilities used by many libs and apps. They can contain services or non-technology (e.g., not Angular specific) related vanilla JS/TS utility functions.

For 'util' libs, explain briefly _why_ reuse is appropriate.

- 'util' libs:
  - …

<!--
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
-->

&nbsp;

## Library Breakdown

Include **only** libs relevant to the selected functionality classification.

- **What are 'map' libs?** These are libs that contain codes for interacting with backend or external resources. **Constraints:** They can import 'util', and 'map' types.
- **What are 'data-access' libs?** These are the libs that hold state management codes. **Constraints:** They can import 'util', 'map', and 'data-access' types.
- **What are 'ui' libs?** These are stupid libs! They only contain stylesheets, presentational components, directives, and pipes. **Constraints:** They can import 'util', 'map', and 'ui' types.
- **What are 'feature' libs?** These are smart (with access to data sources) libs! They are some smart components (which present an independent functionality) that can also access data sources through 'data-access' libs. They are the last piece of the puzzle to complete the logic of a functionality. **Constraints:** They can import 'util', 'map', 'data-access', 'ui', and other 'feature' libs (if necessarily).

<!--
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
-->

&nbsp;

---

### 'map' Library Specification

#### Lib Name

`{scope}-map-{name}`

#### Exported Class

```ts
export class V1Name {}
```

#### Methods (API Endpoints)

> Note!
>
> - One method = one type of data to be returned (in most cases an API endpoint is called, but the data can also come from a SQLite or Local Storage)
> - Interface **names matter**, structures are defined later

> Tip!
>
> A 'map' lib that needs to do CRUD operation, should have methods such as:
>
> - `getAll(url: string, lib = 'any'): Observable<V1Name_MapEntityName[]>`
> - `addOne(url: string, entityName: V1Name_MapEntityName, lib = 'any'): Observable<V1Name_MapEntityName>`
> - `addMany(url: string, entitiesName: V1Name_MapEntityName[], lib = 'any'): Observable<V1Name_MapEntityName[]>`
> - `updateOne(url: string, entityName: V1Name_MapEntityName, lib = 'any'): Observable<V1Name_MapEntityName>`
> - `updateMany(url: string, entitiesName: V1Name_MapEntityName[], lib = 'any'): Observable<V1Name_MapEntityName[]>`
> - `removeOne(url: string, id: number, lib = 'any'): Observable<number>`
> - `removeMany(url: string, ids: number[], lib = 'any'): Observable<number[]>`
> - `removeAll(url: string, lib = 'any'): Observable<void>`

| Method                              | Returns                      | Description            |
| ----------------------------------- | ---------------------------- | ---------------------- |
| `getInfo(url: string, lib = 'any')` | `Observable<V1Name_MapInfo>` | Get app's generic info |

&nbsp;

For **each method**, specify:

> If data is coming from other resources (e.g., SQLite) and there's no API endpoint to call, **include only** 'Authentication', 'Sample Response', and 'Error Handling' sections.

&nbsp;

#### Method: `getInfo(url: string, lib = 'any')`

- **HTTP Method**: `GET`

- **Endpoint**: `{url}/info`

- **Authentication**:
  - Protected endpoint
  - `Authorization: Bearer <TOKEN>` required

- **Headers**:

```http
Authorization: Bearer <TOKEN>
Content-Type: application/json
```

- **Request Body**:

```json
N/A
```

- **Sample Response** (illustrative only):

```json
// Scenario #1
{
  id: number;
  name: string;
  preview: string;
}
```

- **Error Handling**

  When fetching data, errors may happen, and 'map' lib can log them. Here, we mention the errors that should be exceptions (not get logged).
  - `ERROR_CODE_SOMETHING`

&nbsp;

#### Method: `getData(url: string, lib = 'any')`

_(Repeat the same structure for each method)_

<!--
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
-->

&nbsp;

---

### 'data-access' Library Specification

#### Lib Name

`{scope}-data-access-{name}`

#### Exported Facade Class

```ts
export class V1NameFacade {}
```

#### 'State object structure' type

Based on how this 'data-access' lib is going to be used, its 'state object structure' can be different. In general, there are 3 'state object structure' types:

- _'single-instance'_ — It is suitable for storing one single data at the same time.  
  **Example:** You call a single API endpoint to fetch a response, so you would use a 'single-instance' state object to just simply store the response in the state object. If you call the API endpoint again, the response will replace the previous fetched data.  
  **Useful for:** The time that the lib is initialized by one single 'feature' lib, or multiple 'feature' libs, but NOT at the same time (e.g., in the same page).
- _'multi-instance'_ — It is suitable for storing multiple variation of data at the same time.  
  **Example:** You call a single API endpoint with different URL query parameters to fetch different responses, so you would use a 'multi-instance' state object to store each response in a separate instance of the same state object.  
  **Useful for:** The time that the lib is initialized by multiple 'feature' libs at the same time (e.g., in the same page).
- _'entity'_ — It is suitable for CRUD operations.  
  **Example:** You have 'users-all', 'users-edit', 'users-new', 'users-one' pages, and initialize 4 different exported components from a 'feature' lib in each page. And you have 4 different API endpoints to do CRUD operation, so you would use a 'entity' state object to update the stored entities properly.
  **Useful for:** The time that the lib is initialized by a 'feature' lib that is suppose to do a CRUD operation.

**Selected type**: …

#### Public Methods

> Some methods call map APIs via effects; others mutate local state or storage only.

> Tip!
>
> 'State object structure' with 'entity' type:
>
> Should have methods to do their CRUD operation properly. Methods such as:
>
> - `getAll(url: string, lib = 'any')`
> - `setSelectedId(id: number)`
> - `addOne(url: string, entityName: V1Name_MapEntityName, lib = 'any')`
> - `addMany(url: string, entitiesName: V1Name_MapEntityName[], lib = 'any')`
> - `updateOne(url: string, entityName: V1Name_MapEntityName, lib = 'any')`
> - `updateMany(url: string, entitiesName: V1Name_MapEntityName[], lib = 'any')`
> - `removeOne(url: string, id: number, lib = 'any')`
> - `removeMany(url: string, ids: number[], lib = 'any')`
> - `removeAll(url: string, lib = 'any')`
>
> Should also have observables to do their CRUD operation properly. observables such as:
>
> - `state$: Observable<reducer.V1Name_State>`
> - `allEntities$: Observable<V1Name_MapEntityName[]>`
> - `selectedEntity$: Observable<V1Name_MapEntityName | undefined>`
> - `crudActionLatest$: Observable<"getAll" | "addOne" | "addMany" | "updateOne" | "updateMany" | "removeOne" | "removeMany" | "removeAll" | undefined>`
> - `loaded$: Observable<boolean>`
> - `error$: Observable<string | undefined>`

| Method                                        | Description                                        |
| --------------------------------------------- | -------------------------------------------------- |
| `getInfo(url: string, id = 'g', lib = 'any')` | Triggers API call via 'map' lib                    |
| `reset(id: string)`                           | Clears one instance object to its initial state    |
| `resetAll()`                                  | Clears the whole state object to its initial state |

#### Public Observables

| Observable        | Type                                  | Description            |
| ----------------- | ------------------------------------- | ---------------------- |
| state$            | `Observable<reducer.V1Name_State>`    | The whole state object |
| allEntities$      | `Observable<reducer.V1Name_Entity[]>` | Entities array         |
| entity$(id = 'g') | `Observable<reducer.V1Name_Entity>`   | One entity             |

<!--
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
-->

&nbsp;

---

### 'ui' Library Specification

#### Lib Name

`{scope}-ui-{name}`

#### Exported Components

> A 'ui' lib may export **multiple components** according to PRD 'User Experience & Flows' section.  
> In general, complex functionalities MUST export more than 1 components, but simple ones should export only 1 component.
>
> **What's a complex functionality?** In most cases, if the functionality requires more than 1 screens/pages to display its content, or requires to show a list of something which each item in the list is clickable/selectable... Then such functionality should be considered as a complex one! For building the 'ui' lib of such functionalities, it's better to have 2 components for each screen/page, instead of implementing everything in one single component that needs to change its `dataType` input based on other inputs to switch between screens/pages.
>
> **What's a simple functionality?** In most cases, if the functionality doesn't need to navigate/switch between different contents, then it's a simple functionality. When building the 'ui' lib of such functionalities, the `dataType` input NEVER changes.
>
> **How to decide whether the functionality is simple or complex?** It's up to the developer to choose how they want to organize their UI, lib's content, and components. This decision affects how other libs (e.g., the 'feature' lib that is going to initialize this 'ui' lib) interact with this lib.

> **Note!** Component's input/output/property/method/ descriptions will be used as part of their JSDoc description.

&nbsp;

##### Component: `V1Name1Component`

```ts
@Component(...)
export class V1Name1Component {}
```

###### Responsibility

…

###### Inputs

**Required**

- `data: InputSignal<V1Name_MapData>` — …
- `dataType: InputSignal<UiDataType>` — …

**Optional**

- `state: InputSignal<UiState>`
  Default: `'loading'` — …
- `iconInfo: InputSignal<string>`
  Default: `'./assets/images/libs/shared/icon-info.svg'` — …
- `showBtnReadMore: InputSignal<boolean>`
  Default: `true` — …

###### Outputs

- `clickedDetails: OutputEmitterRef<void>` — …

###### Externally Read Properties

- `isUpdateNeeded: boolean` — …

###### Externally Callable Methods

| Method    | Returns | Description                                          |
| --------- | ------- | ---------------------------------------------------- |
| `reset()` | `void`  | Resets all inputs/properties to their default values |

##### Rendering Rules

Define what should be rendered in HTML template based on `state` and `dataType`.

- `state` defines what elements should be shown in general, based on the value of the component's inputs: `"loading" | "empty" | "data" | "success" | "failure"`
- `dataType` defines what type of data should be shown, when `state = data`: `"all" | "one" | "new" | "edit"`

> Complementing PRD 'User Experience & Flows'.

- `state = loading` (whatever `dataType`)
  - Loader / skeleton only

- `state = empty`
  - Heading + `[data-cy="empty"]`

- `state = data`
  - `dataType = all`: Heading + `[data-cy="data-list"]` + `button[aria-label="View details"]`
  - `dataType = one`: Heading + `[data-cy="data-item"]`

###### Functional Requirements & Business Rule Breakdown (Technical & Frontend Perspective)

> 'Functional Requirements' (e.g., NAME-FR-01) is complementing PRD 'Functional Requirements'. Typically map to **unit tests `describe()` blocks**.  
> 'Business Rule Breakdown' (e.g., NAME-BR-01) is complementing PRD 'Business Rule Breakdown'. Each item should map to **unit tests `it`**.
>
> Based on this component's responsibility, read PRD and do the following:
>
> 1. Pick the most related 'Functional Requirement' & 'Business Rule' for this component.
> 2. Put the picked 'Business Rule' items under the most related picked 'Functional Requirement' items.
> 3. Re-phrase 'Functional Requirement' & 'Business Rule' items to reflect to the correct rendered UI elements, input, outputs, and methods.

- **NAME-FR-01**: Test 'state'; component SHALL render elements correctly.
  - **NAME-BR-01**: Given none/some required inputs _(Arrange)_; When `state = loading` _(Act)_; no interactive elements are rendered _(Negative & boundary)_.
  - **NAME-BR-02**: Given ALL required inputs _(Arrange)_; When `state = empty` _(Act)_; `[data-cy="empty"]` must be displayed _(Negative & boundary)_.
- **NAME-FR-02**: Test 'dataType = all'; component SHALL render elements correctly.
  - **NAME-BR-03**: Given ALL required inputs _(Arrange)_; When `state = data` & `dataType = all` _(Act)_; `[data-cy="data-list"]` must be displayed _(Assert)_.
- **NAME-FR-03**: Test 'dataType = all'; clicked 'View details'; component MUST emit 'clickedDetails'.
  - **NAME-BR-04**: Given ALL required inputs _(Arrange)_; When `state = data` & `dataType = all` _(Act)_; clicking `button[aria-label="View details"]` must call `onClickedDetails` and emit `clickedDetails` _(Assert)_.

###### Analytics & Tracking

> These help in defining Analytics logs (e.g., Firebase Analytics).
>
> **Tip!** Components can simply have a `log` method to prepare logging to different analytic services, which can be implemented later.

- Events to be tracked
  - When user clicks `button[aria-label="View details"]`; log `{name: 'clicked_view_details', params: {com: 'V1Name1Component'}}`
  - …

###### Error Handling & Edge Cases

In 'ui' components, we mention the edge case scenarios which lead to showing an empty state or a message in the UI.

- When `showBtnReadMore = false`; then `[data-cy="data-btn-placeholder"]` is shown.

&nbsp;

##### Component: `V1Name2Component`

_(Repeat the same structure for each component)_

<!--
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
-->

&nbsp;

---

### 'feature' Library Specification

#### Lib Name

`{scope}-feature-{name}`

#### Exported Components

> A 'feature' lib may export **multiple components** according to the exported components of the 'ui' lib.  
> In most cases, if the 'ui' exports more than 1 components, then the 'feature' lib will also export the same number of components and initialize the corresponding 'ui' component in each of those components.
>
> **How to decide whether the 'feature' lib should export more than 1 component?** It's up to the developer to choose how they want to initialize and interact with the 'ui' components in their 'feature' lib. This decision affects how other libs (e.g., the 'page' lib that is going to initialize this 'feature' lib) interact with this lib.

> **Note!** Component's input/output/property/method/ descriptions will be used as part of their JSDoc description.

&nbsp;

##### Component: `V1Name1FeaComponent`

```ts
@Component(...)
export class V1Name1FeaComponent {}
```

###### Responsibility

…

###### Inputs

**Required**

- `userId: InputSignal<number>` — …

**Optional**

- `showErrors: InputSignal<boolean>`
  Default: `true` — …
- `showBtnReadMore: InputSignal<boolean>`
  Default: `true` — …

###### Outputs

- `ready: OutputEmitterRef<void>` — …
- `allDataIsReady: OutputEmitterRef<void>` — …
- `hasError: OutputEmitterRef<{ key: string; value: string; }>` — …
- `clickedDetails: OutputEmitterRef<void>` — …

###### Externally Read Properties

- `isUpdateNeeded: boolean` — …

###### Externally Callable Methods

| Method    | Returns | Description                                          |
| --------- | ------- | ---------------------------------------------------- |
| `reset()` | `void`  | Resets all inputs/properties to their default values |

###### Analytics & Tracking

> These help in defining Analytics logs (e.g., Firebase Analytics).
>
> **Tip!** Components can simply have a `log` method to prepare logging to different analytic services, which can be implemented later.

- Events to be tracked
  - When `reset` method is called (externally); log `{name: 'called_reset', params: {com: 'V1Name1FeaComponent'}}`
- Success / failure signals
  - `_xInitOrUpdateAfterAllDataReady` is called (internally), i.e., facade method(s) call(s) succeeds; log `{name: 'all_data_is_ready', params: {com: 'V1Name1FeaComponent'}}`
  - …

###### Error Handling & Edge Cases

In 'feature' components, `hasError` output will be emitted, whenever an error is detected in the state object of the initialized 'data-access' libs (in `_xFacadesAddErrorListeners`). So API calls error handling will happen by default. Here, we mention the state object errors that should be exceptions (not get emitted), and the edge case scenarios which lead to showing an empty state or a message in the UI.

- Consider the following as error exceptions:
  - When listening to `V1NameFacade.entity$(id = 'V1NameFeaComponent_main')`; if `state.errors.info = 'ERROR_CODE_SOMETHING'`.
- Consider the following as edge cases
  - When `showBtnReadMore = false`; then `[data-cy="data-btn-placeholder"]` is shown.

&nbsp;

##### Component: `V1Name2FeaComponent`

_(Repeat the same structure for each component)_

<!--
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
-->

&nbsp;

## User Experience & Flows (Technical & Frontend Perspective)

> Complementing PRD 'User Experience & Flows'. Describes **how the functionality executes technically**.

### Primary flow

1. Trigger (navigation, input, lifecycle) — lifecycle:

- Whenever ALL required inputs of 'feature' lib are defined for the **very first time**, `_xInit` is called.
- Whenever an input of 'feature' lib is updated, `_xUpdate` is called.

2. 'feature' lib calls 'data-access' facade methods — The following methods will be called:

- …

3. 'feature' lib is listening (waiting) for object state changes in 'data-access' — Listening to the following properties:

- …

4. 'data-access' facade methods invoke 'map' methods to call API — The following methods will be called:

- …

5. 'data-access' effect is listening (waiting) for 'map' observable.
6. 'map' methods call API and wait for response/error.
7. As soon as API response/error is ready, 'map' invokes 'data-access' effect, which leads to state object change that 'feature' is listening to.
8. 'feature' updates 'ui' component's inputs based on state object changes — The following inputs will be updated:

- If … state object property is changed, … input is updated.
- …

9. Whenever ALL required inputs of 'ui' lib are defined, its `state` is changed from 'loading' to something else:

- If … input is defined and equal to …, `state` is …, and `dataType` is ….
- …

10. Now data fetching is done, and UI's state is defined based on it, so user can do the following:

- Click `button[aria-label="View details"]`: Emits `clickedViewDetails: OutputEmitterRef<void>`.
- …

&nbsp;

### Flow when `button[aria-label="View details"]` is clicked (user interaction)

Side effect of this output (button click) is 'routing' but it will happen **outside of the functionality**.  
How? 'feature' lib is listening to this output, and emits the same output, and eventually the page that initialized the 'feature' lib is listening to the output and in its handler, takes care of the routing.

&nbsp;

### Flow when 'ui' lib's … input is … (i.e., `state = data` & `dataType = one`)

We show the data, but also show `[data-cy="data-msg-warning"]`.

&nbsp;

### Flow when …

_(Repeat the same structure for each non-primary flow)_

<!--
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
-->

&nbsp;

## Open Technical Questions

- …
- …
