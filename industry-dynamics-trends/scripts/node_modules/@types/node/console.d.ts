/**
 * The `node:console` module provides a simple debugging console that is similar to
 * the JavaScript console mechanism provided by web browsers.
 *
 * The module exports two specific components:
 *
 * * A `Console` class with methods such as `console.log()`, `console.error()`, and `console.warn()` that can be used to write to any Node.js stream.
 * * A global `console` instance configured to write to [`process.stdout`](https://nodejs.org/docs/latest-v25.x/api/process.html#processstdout) and
 * [`process.stderr`](https://nodejs.org/docs/latest-v25.x/api/process.html#processstderr). The global `console` can be used without importing the `node:console` module.
 *
 * _**Warning**_: The global console object's methods are neither consistently
 * synchronous like the browser APIs they resemble, nor are they consistently
 * asynchronous like all other Node.js streams. See the [`note on process I/O`](https://nodejs.org/docs/latest-v25.x/api/process.html#a-note-on-process-io) for
 * more information.
 *
 * Example using the global `console`:
 *
 * ```js
 * console.log('hello world');
 * // Prints: hello world, to stdout
 * console.log('hello %s', 'world');
 * // Prints: hello world, to stdout
 * console.error(new Error('Whoops, something bad happened'));
 * // Prints error message and stack trace to stderr:
 * //   Error: Whoops, something bad happened
 * //     at [eval]:5:15
 * //     at Script.runInThisContext (node:vm:132:18)
 * //     at Object.runInThisContext (node:vm:309:38)
 * //     at node:internal/process/execution:77:19
 * //     at [eval]-wrapper:6:22
 * //     at evalScript (node:internal/process/execution:76:60)
 * //     at node:internal/main/eval_string:23:3
 *
 * const name = 'Will Robinson';
 * console.warn(`Danger ${name}! Danger!`);
 * // Prints: Danger Will Robinson! Danger!, to stderr
 * ```
 *
 * Example using the `Console` class:
 *
 * ```js
 * const out = getStreamSomehow();
 * const err = getStreamSomehow();
 * const myConsole = new console.Console(out, err);
 *
 * myConsole.log('hello world');
 * // Prints: hello world, to out
 * myConsole.log('hello %s', 'world');
 * // Prints: hello world, to out
 * myConsole.error(new Error('Whoops, something bad happened'));
 * // Prints: [Error: Whoops, something bad happened], to err
 *
 * const name = 'Will Robinson';
 * myConsole.warn(`Danger ${name}! Danger!`);
 * // Prints: Danger Will Robinson! Danger!, to err
 * ```
 * @see [source](https://github.com/nodejs/node/blob/v25.x/lib/console.js)
 */
declare module "node:console" {
    import { InspectOptions } from "node:util";
    namespace console {
        interface ConsoleOptions {
            stdout: NodeJS.WritableStream;
            stderr?: NodeJS.WritableStream | undefined;
            /**
             * Ignore errors when writing to the underlying streams.
             * @default true
             */
            ignoreErrors?: boolean | undefined;
            /**
             * Set color support for this `Console` instance. Setting to true enables coloring while inspecting
             * values. Setting to `false` disables coloring while inspecting values. Setting to `'auto'` makes color
             * support depend on the value of the `isTTY` property and the value returned by `getColorDepth()` on the
             * respective stream. This option can not be used, if `inspectOptions.colors` is set as well.
             * @default 'auto'
             */
            colorMode?: boolean | "auto" | undefined;
            /**
             * Specifies options that are passed along to
             * [`util.inspect()`](https://nodejs.org/docs/latest-v25.x/api/util.html#utilinspectobject-options).
             */
            inspectOptions?: InspectOptions | ReadonlyMap<NodeJS.WritableStream, InspectOptions> | undefined;
            /**
             * Set group indentation.
             * @default 2
             */
            groupIndentation?: number | undefined;
        }
        interface Console {
            readonly Console: {
                prototype: Console;
                new(stdout: NodeJS.WritableStream, stderr?: NodeJS.WritableStream, ignoreErrors?: boolean): Console;
                new(options: ConsoleOptions): Console;
            };
            assert(condition?: unknown, ...data: any[]): void;
            clear(): void;
            count(label?: string): void;
            countReset(label?: string): void;
            debug(...data: any[]): void;
            dir(item?: any, options?: InspectOptions): void;
            dirxml(...data: any[]): void;
            error(...data: any[]): void;
            group(...data: any[]): void;
            groupCollapsed(...data: any[]): void;
            groupEnd(): void;
            info(...data: any[]): void;
            log(...data: any[]): void;
            table(tabularData?: any, properties?: string[]): void;
            time(label?: string): void;
            timeEnd(label?: string): void;
            timeLog(label?: string, ...data: any[]): void;
            trace(...data: any[]): void;
            warn(...data: any[]): void;
            /**
             * This method does not display anything unless used in the inspector. The `console.profile()`
             * method starts a JavaScript CPU profile with an optional label until {@link profileEnd}
             * is called. The profile is then added to the Profile panel of the inspector.
             *
             * ```js
             * console.profile('MyLabel');
             * // Some code
             * console.profileEnd('MyLabel');
             * // Adds the profile 'MyLabel' to the Profiles panel of the inspector.
             * ```
             * @since v8.0.0
             */
            profile(label?: string): void;
            /**
             * This method does not display anything unless used in the inspector. Stops the current
             * JavaScript CPU profiling session if one has been started and prints the report to the
             * Profiles panel of the inspector. See {@link profile} for an example.
             *
             * If this method is called without a label, the most recently started profile is stopped.
             * @since v8.0.0
             */
            profileEnd(label?: string): void;
            /**
             * This method does not display anything unless used in the inspector. The `console.timeStamp()`
             * method adds an event with the label `'label'` to the Timeline panel of the inspector.
             * @since v8.0.0
             */
            timeStamp(label?: string): void;
        }
    }
    var console: console.Console;
    export = console;
}
declare module "console" {
    import console = require("node:console");
    export = console;
}
