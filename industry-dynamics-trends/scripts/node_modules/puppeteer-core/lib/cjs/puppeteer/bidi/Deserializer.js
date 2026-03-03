"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.BidiDeserializer = void 0;
const util_js_1 = require("../common/util.js");
/**
 * @internal
 */
class BidiDeserializer {
    static deserialize(result) {
        if (!result) {
            (0, util_js_1.debugError)('Service did not produce a result.');
            return undefined;
        }
        switch (result.type) {
            case 'array':
                return result.value?.map(value => {
                    return this.deserialize(value);
                });
            case 'set':
                return result.value?.reduce((acc, value) => {
                    return acc.add(this.deserialize(value));
                }, new Set());
            case 'object':
                return result.value?.reduce((acc, tuple) => {
                    const { key, value } = this.#deserializeTuple(tuple);
                    acc[key] = value;
                    return acc;
                }, {});
            case 'map':
                return result.value?.reduce((acc, tuple) => {
                    const { key, value } = this.#deserializeTuple(tuple);
                    return acc.set(key, value);
                }, new Map());
            case 'promise':
                return {};
            case 'regexp':
                return new RegExp(result.value.pattern, result.value.flags);
            case 'date':
                return new Date(result.value);
            case 'undefined':
                return undefined;
            case 'null':
                return null;
            case 'number':
                return this.#deserializeNumber(result.value);
            case 'bigint':
                return BigInt(result.value);
            case 'boolean':
                return Boolean(result.value);
            case 'string':
                return result.value;
        }
        (0, util_js_1.debugError)(`Deserialization of type ${result.type} not supported.`);
        return undefined;
    }
    static #deserializeNumber(value) {
        switch (value) {
            case '-0':
                return -0;
            case 'NaN':
                return NaN;
            case 'Infinity':
                return Infinity;
            case '-Infinity':
                return -Infinity;
            default:
                return value;
        }
    }
    static #deserializeTuple([serializedKey, serializedValue]) {
        const key = typeof serializedKey === 'string'
            ? serializedKey
            : this.deserialize(serializedKey);
        const value = this.deserialize(serializedValue);
        return { key, value };
    }
}
exports.BidiDeserializer = BidiDeserializer;
//# sourceMappingURL=Deserializer.js.map