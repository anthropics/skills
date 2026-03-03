import { ASTNode, Type, AnyType, Field } from "./lib/types";
import { NodePath } from "./lib/node-path";
import { namedTypes } from "./gen/namedTypes";
import { builders } from "./gen/builders";
import { Visitor } from "./gen/visitor";
declare const astNodesAreEquivalent: {
    (a: any, b: any, problemPath?: any): boolean;
    assert(a: any, b: any): void;
}, builders: builders, builtInTypes: {
    string: Type<string>;
    function: Type<Function>;
    array: Type<any[]>;
    object: Type<{
        [key: string]: any;
    }>;
    RegExp: Type<RegExp>;
    Date: Type<Date>;
    number: Type<number>;
    boolean: Type<boolean>;
    null: Type<null>;
    undefined: Type<undefined>;
}, defineMethod: (name: any, func?: Function | undefined) => Function, eachField: (object: any, callback: (name: any, value: any) => any, context?: any) => void, finalize: () => void, getBuilderName: (typeName: any) => any, getFieldNames: (object: any) => string[], getFieldValue: (object: any, fieldName: any) => any, getSupertypeNames: (typeName: string) => string[], NodePath: import("./lib/node-path").NodePathConstructor, Path: import("./lib/path").PathConstructor, PathVisitor: import("./lib/path-visitor").PathVisitorConstructor, someField: (object: any, callback: (name: any, value: any) => any, context?: any) => boolean, Type: {
    or(...types: any[]): Type<any>;
    from<T>(value: any, name?: string | undefined): Type<T>;
    def(typeName: string): import("./lib/types").Def<any>;
    hasDef(typeName: string): boolean;
}, use: <T>(plugin: import("./types").Plugin<T>) => T, visit: <M = {}>(node: ASTNode, methods?: Visitor<M> | undefined) => any;
export { AnyType, ASTNode, astNodesAreEquivalent, builders, builtInTypes, defineMethod, eachField, Field, finalize, getBuilderName, getFieldNames, getFieldValue, getSupertypeNames, namedTypes, NodePath, Path, PathVisitor, someField, Type, use, visit, Visitor, };
