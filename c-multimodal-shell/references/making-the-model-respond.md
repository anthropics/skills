# Making Shakti Respond

The scaffold is the C/C++ shell around Shakti. The response path is grounded XML in, controlled text/action XML out, with the MCP gate in the middle.

## Minimum Pieces

1. **Grounded files in slots 1-39**: source files Shakti can bind to the current task.
2. **Slot 40 XML dictionary**: word lookup for unknown, skipped, or overloaded words; return every definition.
3. **Level 41 Markdown**: higher-level instructions loaded after grounded slots.
4. **Post-41 XML memory**: permanent internal memory keyed by epoch time.
5. **MCP gate**: the only path to CPU, shell, internet, tools, heartbeat, history, mouse, and keyboard.
6. **Prompt packet**: an XML or English packet combining the user message, goal, heartbeat state, notepad, slot facts, dictionary pulls, screen path, mouse position, and `BTN_XX` placeholders.
7. **Action parser**: a strict format for Shakti actions, such as `CLICK BTN_03`, `TYPE "text"`, `TI83_EXPR`, `SEARCH_HISTORY`, or `WAIT`, before MCP allows any real effect.

## C/C++ Only Rule

Keep runtime code in C/C++. Keep messages, memory, tool menus, history, reflection, and dictionary entries in XML. Do not add Python, PyTorch, vector embeddings, probability scoring, or tokenizer-dependent control logic to this scaffold.

## First Practical Response Milestone

For the fastest working demo:

1. Keep Shakti as the named model/mind in the XML messages.
2. Feed slots 1-39 plus slot 40 dictionary and level 41 into the C shell.
3. Send all messages through the MCP gate.
4. Let Shakti answer the user or emit an action request.
5. Keep action execution in dry-run mode until Tyler enables that tool category in MCP.

## Prompt Packet Shape

Send the model a compact English packet like this:

```xml
<message to="Shakti" route="mcp">
  <user_request>open the settings page</user_request>
  <mouse placeholder="MOUSE_CURRENT" x="640" y="360" />
  <screenshot grid="model_picture_only" path="screen_tick_12_grid.ppm" />
  <buttons>
    <button placeholder="BTN_01" label="Settings" x="100" y="200" w="140" h="48" />
    <button placeholder="BTN_02" label="Cancel" x="280" y="200" w="140" h="48" />
  </buttons>
  <instructions>answer in English or emit one action line: CLICK BTN_XX, TYPE &quot;...&quot;, TI83_EXPR, SEARCH_HISTORY, or WAIT</instructions>
</message>
```

This lets the model use placeholders instead of memorizing coordinates.

## What Grounded Data Adds

Grounded files teach Shakti:

- Which words and phrases matter in word problems.
- Which button to click for common tasks.
- How to describe screen state.
- How to format safe action commands.
- How to combine text, vision labels, audio labels, memory, and history search.

Slot 40 exists so words like `the` and `as` can be pulled from dictionary XML instead of skipped.
