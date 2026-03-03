export type DegeneratorName = string | RegExp;
export type DegeneratorNames = DegeneratorName[];
/**
 * Compiles sync JavaScript code into JavaScript with async Functions.
 *
 * @param {String} code JavaScript string to convert
 * @param {Array} names Array of function names to add `await` operators to
 * @return {String} Converted JavaScript string with async/await injected
 * @api public
 */
export declare function degenerator(code: string, _names: DegeneratorNames): string;
//# sourceMappingURL=degenerator.d.ts.map