import * as K from "./kinds";
import { namedTypes } from "./namedTypes";
export interface FileBuilder {
    (program: K.ProgramKind, name?: string | null): namedTypes.File;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        name?: string | null;
        program: K.ProgramKind;
    }): namedTypes.File;
}
export interface ProgramBuilder {
    (body: K.StatementKind[]): namedTypes.Program;
    from(params: {
        body: K.StatementKind[];
        comments?: K.CommentKind[] | null;
        directives?: K.DirectiveKind[];
        interpreter?: K.InterpreterDirectiveKind | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.Program;
}
export interface IdentifierBuilder {
    (name: string): namedTypes.Identifier;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        name: string;
        optional?: boolean;
        typeAnnotation?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
    }): namedTypes.Identifier;
}
export interface BlockStatementBuilder {
    (body: K.StatementKind[]): namedTypes.BlockStatement;
    from(params: {
        body: K.StatementKind[];
        comments?: K.CommentKind[] | null;
        directives?: K.DirectiveKind[];
        loc?: K.SourceLocationKind | null;
    }): namedTypes.BlockStatement;
}
export interface EmptyStatementBuilder {
    (): namedTypes.EmptyStatement;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.EmptyStatement;
}
export interface ExpressionStatementBuilder {
    (expression: K.ExpressionKind): namedTypes.ExpressionStatement;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ExpressionStatement;
}
export interface IfStatementBuilder {
    (test: K.ExpressionKind, consequent: K.StatementKind, alternate?: K.StatementKind | null): namedTypes.IfStatement;
    from(params: {
        alternate?: K.StatementKind | null;
        comments?: K.CommentKind[] | null;
        consequent: K.StatementKind;
        loc?: K.SourceLocationKind | null;
        test: K.ExpressionKind;
    }): namedTypes.IfStatement;
}
export interface LabeledStatementBuilder {
    (label: K.IdentifierKind, body: K.StatementKind): namedTypes.LabeledStatement;
    from(params: {
        body: K.StatementKind;
        comments?: K.CommentKind[] | null;
        label: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.LabeledStatement;
}
export interface BreakStatementBuilder {
    (label?: K.IdentifierKind | null): namedTypes.BreakStatement;
    from(params: {
        comments?: K.CommentKind[] | null;
        label?: K.IdentifierKind | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.BreakStatement;
}
export interface ContinueStatementBuilder {
    (label?: K.IdentifierKind | null): namedTypes.ContinueStatement;
    from(params: {
        comments?: K.CommentKind[] | null;
        label?: K.IdentifierKind | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ContinueStatement;
}
export interface WithStatementBuilder {
    (object: K.ExpressionKind, body: K.StatementKind): namedTypes.WithStatement;
    from(params: {
        body: K.StatementKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        object: K.ExpressionKind;
    }): namedTypes.WithStatement;
}
export interface SwitchStatementBuilder {
    (discriminant: K.ExpressionKind, cases: K.SwitchCaseKind[], lexical?: boolean): namedTypes.SwitchStatement;
    from(params: {
        cases: K.SwitchCaseKind[];
        comments?: K.CommentKind[] | null;
        discriminant: K.ExpressionKind;
        lexical?: boolean;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.SwitchStatement;
}
export interface SwitchCaseBuilder {
    (test: K.ExpressionKind | null, consequent: K.StatementKind[]): namedTypes.SwitchCase;
    from(params: {
        comments?: K.CommentKind[] | null;
        consequent: K.StatementKind[];
        loc?: K.SourceLocationKind | null;
        test: K.ExpressionKind | null;
    }): namedTypes.SwitchCase;
}
export interface ReturnStatementBuilder {
    (argument: K.ExpressionKind | null): namedTypes.ReturnStatement;
    from(params: {
        argument: K.ExpressionKind | null;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ReturnStatement;
}
export interface ThrowStatementBuilder {
    (argument: K.ExpressionKind): namedTypes.ThrowStatement;
    from(params: {
        argument: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ThrowStatement;
}
export interface TryStatementBuilder {
    (block: K.BlockStatementKind, handler?: K.CatchClauseKind | null, finalizer?: K.BlockStatementKind | null): namedTypes.TryStatement;
    from(params: {
        block: K.BlockStatementKind;
        comments?: K.CommentKind[] | null;
        finalizer?: K.BlockStatementKind | null;
        guardedHandlers?: K.CatchClauseKind[];
        handler?: K.CatchClauseKind | null;
        handlers?: K.CatchClauseKind[];
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TryStatement;
}
export interface CatchClauseBuilder {
    (param: K.PatternKind | null | undefined, guard: K.ExpressionKind | null | undefined, body: K.BlockStatementKind): namedTypes.CatchClause;
    from(params: {
        body: K.BlockStatementKind;
        comments?: K.CommentKind[] | null;
        guard?: K.ExpressionKind | null;
        loc?: K.SourceLocationKind | null;
        param?: K.PatternKind | null;
    }): namedTypes.CatchClause;
}
export interface WhileStatementBuilder {
    (test: K.ExpressionKind, body: K.StatementKind): namedTypes.WhileStatement;
    from(params: {
        body: K.StatementKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        test: K.ExpressionKind;
    }): namedTypes.WhileStatement;
}
export interface DoWhileStatementBuilder {
    (body: K.StatementKind, test: K.ExpressionKind): namedTypes.DoWhileStatement;
    from(params: {
        body: K.StatementKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        test: K.ExpressionKind;
    }): namedTypes.DoWhileStatement;
}
export interface ForStatementBuilder {
    (init: K.VariableDeclarationKind | K.ExpressionKind | null, test: K.ExpressionKind | null, update: K.ExpressionKind | null, body: K.StatementKind): namedTypes.ForStatement;
    from(params: {
        body: K.StatementKind;
        comments?: K.CommentKind[] | null;
        init: K.VariableDeclarationKind | K.ExpressionKind | null;
        loc?: K.SourceLocationKind | null;
        test: K.ExpressionKind | null;
        update: K.ExpressionKind | null;
    }): namedTypes.ForStatement;
}
export interface VariableDeclarationBuilder {
    (kind: "var" | "let" | "const", declarations: (K.VariableDeclaratorKind | K.IdentifierKind)[]): namedTypes.VariableDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        declarations: (K.VariableDeclaratorKind | K.IdentifierKind)[];
        kind: "var" | "let" | "const";
        loc?: K.SourceLocationKind | null;
    }): namedTypes.VariableDeclaration;
}
export interface ForInStatementBuilder {
    (left: K.VariableDeclarationKind | K.ExpressionKind, right: K.ExpressionKind, body: K.StatementKind): namedTypes.ForInStatement;
    from(params: {
        body: K.StatementKind;
        comments?: K.CommentKind[] | null;
        left: K.VariableDeclarationKind | K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        right: K.ExpressionKind;
    }): namedTypes.ForInStatement;
}
export interface DebuggerStatementBuilder {
    (): namedTypes.DebuggerStatement;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.DebuggerStatement;
}
export interface FunctionDeclarationBuilder {
    (id: K.IdentifierKind, params: K.PatternKind[], body: K.BlockStatementKind, generator?: boolean, expression?: boolean): namedTypes.FunctionDeclaration;
    from(params: {
        async?: boolean;
        body: K.BlockStatementKind;
        comments?: K.CommentKind[] | null;
        defaults?: (K.ExpressionKind | null)[];
        expression?: boolean;
        generator?: boolean;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        params: K.PatternKind[];
        rest?: K.IdentifierKind | null;
        returnType?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
        typeParameters?: K.TypeParameterDeclarationKind | K.TSTypeParameterDeclarationKind | null;
    }): namedTypes.FunctionDeclaration;
}
export interface FunctionExpressionBuilder {
    (id: K.IdentifierKind | null | undefined, params: K.PatternKind[], body: K.BlockStatementKind, generator?: boolean, expression?: boolean): namedTypes.FunctionExpression;
    from(params: {
        async?: boolean;
        body: K.BlockStatementKind;
        comments?: K.CommentKind[] | null;
        defaults?: (K.ExpressionKind | null)[];
        expression?: boolean;
        generator?: boolean;
        id?: K.IdentifierKind | null;
        loc?: K.SourceLocationKind | null;
        params: K.PatternKind[];
        rest?: K.IdentifierKind | null;
        returnType?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
        typeParameters?: K.TypeParameterDeclarationKind | K.TSTypeParameterDeclarationKind | null;
    }): namedTypes.FunctionExpression;
}
export interface VariableDeclaratorBuilder {
    (id: K.PatternKind, init?: K.ExpressionKind | null): namedTypes.VariableDeclarator;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.PatternKind;
        init?: K.ExpressionKind | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.VariableDeclarator;
}
export interface ThisExpressionBuilder {
    (): namedTypes.ThisExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ThisExpression;
}
export interface ArrayExpressionBuilder {
    (elements: (K.ExpressionKind | K.SpreadElementKind | K.RestElementKind | null)[]): namedTypes.ArrayExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        elements: (K.ExpressionKind | K.SpreadElementKind | K.RestElementKind | null)[];
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ArrayExpression;
}
export interface ObjectExpressionBuilder {
    (properties: (K.PropertyKind | K.ObjectMethodKind | K.ObjectPropertyKind | K.SpreadPropertyKind | K.SpreadElementKind)[]): namedTypes.ObjectExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        properties: (K.PropertyKind | K.ObjectMethodKind | K.ObjectPropertyKind | K.SpreadPropertyKind | K.SpreadElementKind)[];
    }): namedTypes.ObjectExpression;
}
export interface PropertyBuilder {
    (kind: "init" | "get" | "set", key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind, value: K.ExpressionKind | K.PatternKind): namedTypes.Property;
    from(params: {
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        decorators?: K.DecoratorKind[] | null;
        key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind;
        kind: "init" | "get" | "set";
        loc?: K.SourceLocationKind | null;
        method?: boolean;
        shorthand?: boolean;
        value: K.ExpressionKind | K.PatternKind;
    }): namedTypes.Property;
}
export interface LiteralBuilder {
    (value: string | boolean | null | number | RegExp): namedTypes.Literal;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        regex?: {
            pattern: string;
            flags: string;
        } | null;
        value: string | boolean | null | number | RegExp;
    }): namedTypes.Literal;
}
export interface SequenceExpressionBuilder {
    (expressions: K.ExpressionKind[]): namedTypes.SequenceExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        expressions: K.ExpressionKind[];
        loc?: K.SourceLocationKind | null;
    }): namedTypes.SequenceExpression;
}
export interface UnaryExpressionBuilder {
    (operator: "-" | "+" | "!" | "~" | "typeof" | "void" | "delete", argument: K.ExpressionKind, prefix?: boolean): namedTypes.UnaryExpression;
    from(params: {
        argument: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        operator: "-" | "+" | "!" | "~" | "typeof" | "void" | "delete";
        prefix?: boolean;
    }): namedTypes.UnaryExpression;
}
export interface BinaryExpressionBuilder {
    (operator: "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">=" | "<<" | ">>" | ">>>" | "+" | "-" | "*" | "/" | "%" | "**" | "&" | "|" | "^" | "in" | "instanceof", left: K.ExpressionKind, right: K.ExpressionKind): namedTypes.BinaryExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        left: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        operator: "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">=" | "<<" | ">>" | ">>>" | "+" | "-" | "*" | "/" | "%" | "**" | "&" | "|" | "^" | "in" | "instanceof";
        right: K.ExpressionKind;
    }): namedTypes.BinaryExpression;
}
export interface AssignmentExpressionBuilder {
    (operator: "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "<<=" | ">>=" | ">>>=" | "|=" | "^=" | "&=", left: K.PatternKind | K.MemberExpressionKind, right: K.ExpressionKind): namedTypes.AssignmentExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        left: K.PatternKind | K.MemberExpressionKind;
        loc?: K.SourceLocationKind | null;
        operator: "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "<<=" | ">>=" | ">>>=" | "|=" | "^=" | "&=";
        right: K.ExpressionKind;
    }): namedTypes.AssignmentExpression;
}
export interface MemberExpressionBuilder {
    (object: K.ExpressionKind, property: K.IdentifierKind | K.ExpressionKind, computed?: boolean): namedTypes.MemberExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        loc?: K.SourceLocationKind | null;
        object: K.ExpressionKind;
        property: K.IdentifierKind | K.ExpressionKind;
    }): namedTypes.MemberExpression;
}
export interface UpdateExpressionBuilder {
    (operator: "++" | "--", argument: K.ExpressionKind, prefix: boolean): namedTypes.UpdateExpression;
    from(params: {
        argument: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        operator: "++" | "--";
        prefix: boolean;
    }): namedTypes.UpdateExpression;
}
export interface LogicalExpressionBuilder {
    (operator: "||" | "&&" | "??", left: K.ExpressionKind, right: K.ExpressionKind): namedTypes.LogicalExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        left: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        operator: "||" | "&&" | "??";
        right: K.ExpressionKind;
    }): namedTypes.LogicalExpression;
}
export interface ConditionalExpressionBuilder {
    (test: K.ExpressionKind, consequent: K.ExpressionKind, alternate: K.ExpressionKind): namedTypes.ConditionalExpression;
    from(params: {
        alternate: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        consequent: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        test: K.ExpressionKind;
    }): namedTypes.ConditionalExpression;
}
export interface NewExpressionBuilder {
    (callee: K.ExpressionKind, argumentsParam: (K.ExpressionKind | K.SpreadElementKind)[]): namedTypes.NewExpression;
    from(params: {
        arguments: (K.ExpressionKind | K.SpreadElementKind)[];
        callee: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeArguments?: null | K.TypeParameterInstantiationKind;
    }): namedTypes.NewExpression;
}
export interface CallExpressionBuilder {
    (callee: K.ExpressionKind, argumentsParam: (K.ExpressionKind | K.SpreadElementKind)[]): namedTypes.CallExpression;
    from(params: {
        arguments: (K.ExpressionKind | K.SpreadElementKind)[];
        callee: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeArguments?: null | K.TypeParameterInstantiationKind;
    }): namedTypes.CallExpression;
}
export interface RestElementBuilder {
    (argument: K.PatternKind): namedTypes.RestElement;
    from(params: {
        argument: K.PatternKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeAnnotation?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
    }): namedTypes.RestElement;
}
export interface TypeAnnotationBuilder {
    (typeAnnotation: K.FlowTypeKind): namedTypes.TypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.FlowTypeKind;
    }): namedTypes.TypeAnnotation;
}
export interface TSTypeAnnotationBuilder {
    (typeAnnotation: K.TSTypeKind | K.TSTypeAnnotationKind): namedTypes.TSTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.TSTypeKind | K.TSTypeAnnotationKind;
    }): namedTypes.TSTypeAnnotation;
}
export interface SpreadElementPatternBuilder {
    (argument: K.PatternKind): namedTypes.SpreadElementPattern;
    from(params: {
        argument: K.PatternKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.SpreadElementPattern;
}
export interface ArrowFunctionExpressionBuilder {
    (params: K.PatternKind[], body: K.BlockStatementKind | K.ExpressionKind, expression?: boolean): namedTypes.ArrowFunctionExpression;
    from(params: {
        async?: boolean;
        body: K.BlockStatementKind | K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        defaults?: (K.ExpressionKind | null)[];
        expression?: boolean;
        generator?: false;
        id?: null;
        loc?: K.SourceLocationKind | null;
        params: K.PatternKind[];
        rest?: K.IdentifierKind | null;
        returnType?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
        typeParameters?: K.TypeParameterDeclarationKind | K.TSTypeParameterDeclarationKind | null;
    }): namedTypes.ArrowFunctionExpression;
}
export interface ForOfStatementBuilder {
    (left: K.VariableDeclarationKind | K.PatternKind, right: K.ExpressionKind, body: K.StatementKind): namedTypes.ForOfStatement;
    from(params: {
        body: K.StatementKind;
        comments?: K.CommentKind[] | null;
        left: K.VariableDeclarationKind | K.PatternKind;
        loc?: K.SourceLocationKind | null;
        right: K.ExpressionKind;
    }): namedTypes.ForOfStatement;
}
export interface YieldExpressionBuilder {
    (argument: K.ExpressionKind | null, delegate?: boolean): namedTypes.YieldExpression;
    from(params: {
        argument: K.ExpressionKind | null;
        comments?: K.CommentKind[] | null;
        delegate?: boolean;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.YieldExpression;
}
export interface GeneratorExpressionBuilder {
    (body: K.ExpressionKind, blocks: K.ComprehensionBlockKind[], filter: K.ExpressionKind | null): namedTypes.GeneratorExpression;
    from(params: {
        blocks: K.ComprehensionBlockKind[];
        body: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        filter: K.ExpressionKind | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.GeneratorExpression;
}
export interface ComprehensionBlockBuilder {
    (left: K.PatternKind, right: K.ExpressionKind, each: boolean): namedTypes.ComprehensionBlock;
    from(params: {
        comments?: K.CommentKind[] | null;
        each: boolean;
        left: K.PatternKind;
        loc?: K.SourceLocationKind | null;
        right: K.ExpressionKind;
    }): namedTypes.ComprehensionBlock;
}
export interface ComprehensionExpressionBuilder {
    (body: K.ExpressionKind, blocks: K.ComprehensionBlockKind[], filter: K.ExpressionKind | null): namedTypes.ComprehensionExpression;
    from(params: {
        blocks: K.ComprehensionBlockKind[];
        body: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        filter: K.ExpressionKind | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ComprehensionExpression;
}
export interface ObjectPropertyBuilder {
    (key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind, value: K.ExpressionKind | K.PatternKind): namedTypes.ObjectProperty;
    from(params: {
        accessibility?: K.LiteralKind | null;
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        shorthand?: boolean;
        value: K.ExpressionKind | K.PatternKind;
    }): namedTypes.ObjectProperty;
}
export interface PropertyPatternBuilder {
    (key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind, pattern: K.PatternKind): namedTypes.PropertyPattern;
    from(params: {
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        pattern: K.PatternKind;
    }): namedTypes.PropertyPattern;
}
export interface ObjectPatternBuilder {
    (properties: (K.PropertyKind | K.PropertyPatternKind | K.SpreadPropertyPatternKind | K.SpreadPropertyKind | K.ObjectPropertyKind | K.RestPropertyKind)[]): namedTypes.ObjectPattern;
    from(params: {
        comments?: K.CommentKind[] | null;
        decorators?: K.DecoratorKind[] | null;
        loc?: K.SourceLocationKind | null;
        properties: (K.PropertyKind | K.PropertyPatternKind | K.SpreadPropertyPatternKind | K.SpreadPropertyKind | K.ObjectPropertyKind | K.RestPropertyKind)[];
        typeAnnotation?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
    }): namedTypes.ObjectPattern;
}
export interface ArrayPatternBuilder {
    (elements: (K.PatternKind | K.SpreadElementKind | null)[]): namedTypes.ArrayPattern;
    from(params: {
        comments?: K.CommentKind[] | null;
        elements: (K.PatternKind | K.SpreadElementKind | null)[];
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ArrayPattern;
}
export interface MethodDefinitionBuilder {
    (kind: "constructor" | "method" | "get" | "set", key: K.ExpressionKind, value: K.FunctionKind, staticParam?: boolean): namedTypes.MethodDefinition;
    from(params: {
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        decorators?: K.DecoratorKind[] | null;
        key: K.ExpressionKind;
        kind: "constructor" | "method" | "get" | "set";
        loc?: K.SourceLocationKind | null;
        static?: boolean;
        value: K.FunctionKind;
    }): namedTypes.MethodDefinition;
}
export interface SpreadElementBuilder {
    (argument: K.ExpressionKind): namedTypes.SpreadElement;
    from(params: {
        argument: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.SpreadElement;
}
export interface AssignmentPatternBuilder {
    (left: K.PatternKind, right: K.ExpressionKind): namedTypes.AssignmentPattern;
    from(params: {
        comments?: K.CommentKind[] | null;
        left: K.PatternKind;
        loc?: K.SourceLocationKind | null;
        right: K.ExpressionKind;
    }): namedTypes.AssignmentPattern;
}
export interface ClassPropertyDefinitionBuilder {
    (definition: K.MethodDefinitionKind | K.VariableDeclaratorKind | K.ClassPropertyDefinitionKind | K.ClassPropertyKind): namedTypes.ClassPropertyDefinition;
    from(params: {
        comments?: K.CommentKind[] | null;
        definition: K.MethodDefinitionKind | K.VariableDeclaratorKind | K.ClassPropertyDefinitionKind | K.ClassPropertyKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ClassPropertyDefinition;
}
export interface ClassPropertyBuilder {
    (key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind, value: K.ExpressionKind | null, typeAnnotation?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null, staticParam?: boolean): namedTypes.ClassProperty;
    from(params: {
        access?: "public" | "private" | "protected" | undefined;
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        static?: boolean;
        typeAnnotation?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
        value: K.ExpressionKind | null;
        variance?: K.VarianceKind | "plus" | "minus" | null;
    }): namedTypes.ClassProperty;
}
export interface ClassBodyBuilder {
    (body: (K.MethodDefinitionKind | K.VariableDeclaratorKind | K.ClassPropertyDefinitionKind | K.ClassPropertyKind | K.ClassPrivatePropertyKind | K.ClassMethodKind | K.ClassPrivateMethodKind | K.TSDeclareMethodKind | K.TSCallSignatureDeclarationKind | K.TSConstructSignatureDeclarationKind | K.TSIndexSignatureKind | K.TSMethodSignatureKind | K.TSPropertySignatureKind)[]): namedTypes.ClassBody;
    from(params: {
        body: (K.MethodDefinitionKind | K.VariableDeclaratorKind | K.ClassPropertyDefinitionKind | K.ClassPropertyKind | K.ClassPrivatePropertyKind | K.ClassMethodKind | K.ClassPrivateMethodKind | K.TSDeclareMethodKind | K.TSCallSignatureDeclarationKind | K.TSConstructSignatureDeclarationKind | K.TSIndexSignatureKind | K.TSMethodSignatureKind | K.TSPropertySignatureKind)[];
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ClassBody;
}
export interface ClassDeclarationBuilder {
    (id: K.IdentifierKind | null, body: K.ClassBodyKind, superClass?: K.ExpressionKind | null): namedTypes.ClassDeclaration;
    from(params: {
        body: K.ClassBodyKind;
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind | null;
        implements?: K.ClassImplementsKind[] | K.TSExpressionWithTypeArgumentsKind[];
        loc?: K.SourceLocationKind | null;
        superClass?: K.ExpressionKind | null;
        superTypeParameters?: K.TypeParameterInstantiationKind | K.TSTypeParameterInstantiationKind | null;
        typeParameters?: K.TypeParameterDeclarationKind | K.TSTypeParameterDeclarationKind | null;
    }): namedTypes.ClassDeclaration;
}
export interface ClassExpressionBuilder {
    (id: K.IdentifierKind | null | undefined, body: K.ClassBodyKind, superClass?: K.ExpressionKind | null): namedTypes.ClassExpression;
    from(params: {
        body: K.ClassBodyKind;
        comments?: K.CommentKind[] | null;
        id?: K.IdentifierKind | null;
        implements?: K.ClassImplementsKind[] | K.TSExpressionWithTypeArgumentsKind[];
        loc?: K.SourceLocationKind | null;
        superClass?: K.ExpressionKind | null;
        superTypeParameters?: K.TypeParameterInstantiationKind | K.TSTypeParameterInstantiationKind | null;
        typeParameters?: K.TypeParameterDeclarationKind | K.TSTypeParameterDeclarationKind | null;
    }): namedTypes.ClassExpression;
}
export interface ImportSpecifierBuilder {
    (imported: K.IdentifierKind, local?: K.IdentifierKind | null): namedTypes.ImportSpecifier;
    from(params: {
        comments?: K.CommentKind[] | null;
        id?: K.IdentifierKind | null;
        imported: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        local?: K.IdentifierKind | null;
        name?: K.IdentifierKind | null;
    }): namedTypes.ImportSpecifier;
}
export interface ImportNamespaceSpecifierBuilder {
    (local?: K.IdentifierKind | null): namedTypes.ImportNamespaceSpecifier;
    from(params: {
        comments?: K.CommentKind[] | null;
        id?: K.IdentifierKind | null;
        loc?: K.SourceLocationKind | null;
        local?: K.IdentifierKind | null;
        name?: K.IdentifierKind | null;
    }): namedTypes.ImportNamespaceSpecifier;
}
export interface ImportDefaultSpecifierBuilder {
    (local?: K.IdentifierKind | null): namedTypes.ImportDefaultSpecifier;
    from(params: {
        comments?: K.CommentKind[] | null;
        id?: K.IdentifierKind | null;
        loc?: K.SourceLocationKind | null;
        local?: K.IdentifierKind | null;
        name?: K.IdentifierKind | null;
    }): namedTypes.ImportDefaultSpecifier;
}
export interface ImportDeclarationBuilder {
    (specifiers: (K.ImportSpecifierKind | K.ImportNamespaceSpecifierKind | K.ImportDefaultSpecifierKind)[] | undefined, source: K.LiteralKind, importKind?: "value" | "type"): namedTypes.ImportDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        importKind?: "value" | "type";
        loc?: K.SourceLocationKind | null;
        source: K.LiteralKind;
        specifiers?: (K.ImportSpecifierKind | K.ImportNamespaceSpecifierKind | K.ImportDefaultSpecifierKind)[];
    }): namedTypes.ImportDeclaration;
}
export interface TaggedTemplateExpressionBuilder {
    (tag: K.ExpressionKind, quasi: K.TemplateLiteralKind): namedTypes.TaggedTemplateExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        quasi: K.TemplateLiteralKind;
        tag: K.ExpressionKind;
    }): namedTypes.TaggedTemplateExpression;
}
export interface TemplateLiteralBuilder {
    (quasis: K.TemplateElementKind[], expressions: K.ExpressionKind[]): namedTypes.TemplateLiteral;
    from(params: {
        comments?: K.CommentKind[] | null;
        expressions: K.ExpressionKind[];
        loc?: K.SourceLocationKind | null;
        quasis: K.TemplateElementKind[];
    }): namedTypes.TemplateLiteral;
}
export interface TemplateElementBuilder {
    (value: {
        cooked: string;
        raw: string;
    }, tail: boolean): namedTypes.TemplateElement;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        tail: boolean;
        value: {
            cooked: string;
            raw: string;
        };
    }): namedTypes.TemplateElement;
}
export interface SpreadPropertyBuilder {
    (argument: K.ExpressionKind): namedTypes.SpreadProperty;
    from(params: {
        argument: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.SpreadProperty;
}
export interface SpreadPropertyPatternBuilder {
    (argument: K.PatternKind): namedTypes.SpreadPropertyPattern;
    from(params: {
        argument: K.PatternKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.SpreadPropertyPattern;
}
export interface AwaitExpressionBuilder {
    (argument: K.ExpressionKind | null, all?: boolean): namedTypes.AwaitExpression;
    from(params: {
        all?: boolean;
        argument: K.ExpressionKind | null;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.AwaitExpression;
}
export interface ImportExpressionBuilder {
    (source: K.ExpressionKind): namedTypes.ImportExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        source: K.ExpressionKind;
    }): namedTypes.ImportExpression;
}
export interface JSXAttributeBuilder {
    (name: K.JSXIdentifierKind | K.JSXNamespacedNameKind, value?: K.LiteralKind | K.JSXExpressionContainerKind | null): namedTypes.JSXAttribute;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        name: K.JSXIdentifierKind | K.JSXNamespacedNameKind;
        value?: K.LiteralKind | K.JSXExpressionContainerKind | null;
    }): namedTypes.JSXAttribute;
}
export interface JSXIdentifierBuilder {
    (name: string): namedTypes.JSXIdentifier;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        name: string;
        optional?: boolean;
        typeAnnotation?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
    }): namedTypes.JSXIdentifier;
}
export interface JSXNamespacedNameBuilder {
    (namespace: K.JSXIdentifierKind, name: K.JSXIdentifierKind): namedTypes.JSXNamespacedName;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        name: K.JSXIdentifierKind;
        namespace: K.JSXIdentifierKind;
    }): namedTypes.JSXNamespacedName;
}
export interface JSXExpressionContainerBuilder {
    (expression: K.ExpressionKind): namedTypes.JSXExpressionContainer;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.JSXExpressionContainer;
}
export interface JSXMemberExpressionBuilder {
    (object: K.JSXIdentifierKind | K.JSXMemberExpressionKind, property: K.JSXIdentifierKind): namedTypes.JSXMemberExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        loc?: K.SourceLocationKind | null;
        object: K.JSXIdentifierKind | K.JSXMemberExpressionKind;
        property: K.JSXIdentifierKind;
    }): namedTypes.JSXMemberExpression;
}
export interface JSXSpreadAttributeBuilder {
    (argument: K.ExpressionKind): namedTypes.JSXSpreadAttribute;
    from(params: {
        argument: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.JSXSpreadAttribute;
}
export interface JSXElementBuilder {
    (openingElement: K.JSXOpeningElementKind, closingElement?: K.JSXClosingElementKind | null, children?: (K.JSXElementKind | K.JSXExpressionContainerKind | K.JSXFragmentKind | K.JSXTextKind | K.LiteralKind)[]): namedTypes.JSXElement;
    from(params: {
        attributes?: (K.JSXAttributeKind | K.JSXSpreadAttributeKind)[];
        children?: (K.JSXElementKind | K.JSXExpressionContainerKind | K.JSXFragmentKind | K.JSXTextKind | K.LiteralKind)[];
        closingElement?: K.JSXClosingElementKind | null;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        name?: K.JSXIdentifierKind | K.JSXNamespacedNameKind | K.JSXMemberExpressionKind;
        openingElement: K.JSXOpeningElementKind;
        selfClosing?: boolean;
    }): namedTypes.JSXElement;
}
export interface JSXOpeningElementBuilder {
    (name: K.JSXIdentifierKind | K.JSXNamespacedNameKind | K.JSXMemberExpressionKind, attributes?: (K.JSXAttributeKind | K.JSXSpreadAttributeKind)[], selfClosing?: boolean): namedTypes.JSXOpeningElement;
    from(params: {
        attributes?: (K.JSXAttributeKind | K.JSXSpreadAttributeKind)[];
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        name: K.JSXIdentifierKind | K.JSXNamespacedNameKind | K.JSXMemberExpressionKind;
        selfClosing?: boolean;
    }): namedTypes.JSXOpeningElement;
}
export interface JSXClosingElementBuilder {
    (name: K.JSXIdentifierKind | K.JSXNamespacedNameKind | K.JSXMemberExpressionKind): namedTypes.JSXClosingElement;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        name: K.JSXIdentifierKind | K.JSXNamespacedNameKind | K.JSXMemberExpressionKind;
    }): namedTypes.JSXClosingElement;
}
export interface JSXFragmentBuilder {
    (openingElement: K.JSXOpeningFragmentKind, closingElement: K.JSXClosingFragmentKind, children?: (K.JSXElementKind | K.JSXExpressionContainerKind | K.JSXFragmentKind | K.JSXTextKind | K.LiteralKind)[]): namedTypes.JSXFragment;
    from(params: {
        children?: (K.JSXElementKind | K.JSXExpressionContainerKind | K.JSXFragmentKind | K.JSXTextKind | K.LiteralKind)[];
        closingElement: K.JSXClosingFragmentKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        openingElement: K.JSXOpeningFragmentKind;
    }): namedTypes.JSXFragment;
}
export interface JSXTextBuilder {
    (value: string): namedTypes.JSXText;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        regex?: {
            pattern: string;
            flags: string;
        } | null;
        value: string;
    }): namedTypes.JSXText;
}
export interface JSXOpeningFragmentBuilder {
    (): namedTypes.JSXOpeningFragment;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.JSXOpeningFragment;
}
export interface JSXClosingFragmentBuilder {
    (): namedTypes.JSXClosingFragment;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.JSXClosingFragment;
}
export interface JSXEmptyExpressionBuilder {
    (): namedTypes.JSXEmptyExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.JSXEmptyExpression;
}
export interface JSXSpreadChildBuilder {
    (expression: K.ExpressionKind): namedTypes.JSXSpreadChild;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.JSXSpreadChild;
}
export interface TypeParameterDeclarationBuilder {
    (params: K.TypeParameterKind[]): namedTypes.TypeParameterDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        params: K.TypeParameterKind[];
    }): namedTypes.TypeParameterDeclaration;
}
export interface TSTypeParameterDeclarationBuilder {
    (params: K.TSTypeParameterKind[]): namedTypes.TSTypeParameterDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        params: K.TSTypeParameterKind[];
    }): namedTypes.TSTypeParameterDeclaration;
}
export interface TypeParameterInstantiationBuilder {
    (params: K.FlowTypeKind[]): namedTypes.TypeParameterInstantiation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        params: K.FlowTypeKind[];
    }): namedTypes.TypeParameterInstantiation;
}
export interface TSTypeParameterInstantiationBuilder {
    (params: K.TSTypeKind[]): namedTypes.TSTypeParameterInstantiation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        params: K.TSTypeKind[];
    }): namedTypes.TSTypeParameterInstantiation;
}
export interface ClassImplementsBuilder {
    (id: K.IdentifierKind): namedTypes.ClassImplements;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        superClass?: K.ExpressionKind | null;
        typeParameters?: K.TypeParameterInstantiationKind | null;
    }): namedTypes.ClassImplements;
}
export interface TSExpressionWithTypeArgumentsBuilder {
    (expression: K.IdentifierKind | K.TSQualifiedNameKind, typeParameters?: K.TSTypeParameterInstantiationKind | null): namedTypes.TSExpressionWithTypeArguments;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.IdentifierKind | K.TSQualifiedNameKind;
        loc?: K.SourceLocationKind | null;
        typeParameters?: K.TSTypeParameterInstantiationKind | null;
    }): namedTypes.TSExpressionWithTypeArguments;
}
export interface AnyTypeAnnotationBuilder {
    (): namedTypes.AnyTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.AnyTypeAnnotation;
}
export interface EmptyTypeAnnotationBuilder {
    (): namedTypes.EmptyTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.EmptyTypeAnnotation;
}
export interface MixedTypeAnnotationBuilder {
    (): namedTypes.MixedTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.MixedTypeAnnotation;
}
export interface VoidTypeAnnotationBuilder {
    (): namedTypes.VoidTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.VoidTypeAnnotation;
}
export interface NumberTypeAnnotationBuilder {
    (): namedTypes.NumberTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.NumberTypeAnnotation;
}
export interface NumberLiteralTypeAnnotationBuilder {
    (value: number, raw: string): namedTypes.NumberLiteralTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        raw: string;
        value: number;
    }): namedTypes.NumberLiteralTypeAnnotation;
}
export interface NumericLiteralTypeAnnotationBuilder {
    (value: number, raw: string): namedTypes.NumericLiteralTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        raw: string;
        value: number;
    }): namedTypes.NumericLiteralTypeAnnotation;
}
export interface StringTypeAnnotationBuilder {
    (): namedTypes.StringTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.StringTypeAnnotation;
}
export interface StringLiteralTypeAnnotationBuilder {
    (value: string, raw: string): namedTypes.StringLiteralTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        raw: string;
        value: string;
    }): namedTypes.StringLiteralTypeAnnotation;
}
export interface BooleanTypeAnnotationBuilder {
    (): namedTypes.BooleanTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.BooleanTypeAnnotation;
}
export interface BooleanLiteralTypeAnnotationBuilder {
    (value: boolean, raw: string): namedTypes.BooleanLiteralTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        raw: string;
        value: boolean;
    }): namedTypes.BooleanLiteralTypeAnnotation;
}
export interface NullableTypeAnnotationBuilder {
    (typeAnnotation: K.FlowTypeKind): namedTypes.NullableTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.FlowTypeKind;
    }): namedTypes.NullableTypeAnnotation;
}
export interface NullLiteralTypeAnnotationBuilder {
    (): namedTypes.NullLiteralTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.NullLiteralTypeAnnotation;
}
export interface NullTypeAnnotationBuilder {
    (): namedTypes.NullTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.NullTypeAnnotation;
}
export interface ThisTypeAnnotationBuilder {
    (): namedTypes.ThisTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ThisTypeAnnotation;
}
export interface ExistsTypeAnnotationBuilder {
    (): namedTypes.ExistsTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ExistsTypeAnnotation;
}
export interface ExistentialTypeParamBuilder {
    (): namedTypes.ExistentialTypeParam;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ExistentialTypeParam;
}
export interface FunctionTypeAnnotationBuilder {
    (params: K.FunctionTypeParamKind[], returnType: K.FlowTypeKind, rest: K.FunctionTypeParamKind | null, typeParameters: K.TypeParameterDeclarationKind | null): namedTypes.FunctionTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        params: K.FunctionTypeParamKind[];
        rest: K.FunctionTypeParamKind | null;
        returnType: K.FlowTypeKind;
        typeParameters: K.TypeParameterDeclarationKind | null;
    }): namedTypes.FunctionTypeAnnotation;
}
export interface FunctionTypeParamBuilder {
    (name: K.IdentifierKind, typeAnnotation: K.FlowTypeKind, optional: boolean): namedTypes.FunctionTypeParam;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        name: K.IdentifierKind;
        optional: boolean;
        typeAnnotation: K.FlowTypeKind;
    }): namedTypes.FunctionTypeParam;
}
export interface ArrayTypeAnnotationBuilder {
    (elementType: K.FlowTypeKind): namedTypes.ArrayTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        elementType: K.FlowTypeKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ArrayTypeAnnotation;
}
export interface ObjectTypeAnnotationBuilder {
    (properties: (K.ObjectTypePropertyKind | K.ObjectTypeSpreadPropertyKind)[], indexers?: K.ObjectTypeIndexerKind[], callProperties?: K.ObjectTypeCallPropertyKind[]): namedTypes.ObjectTypeAnnotation;
    from(params: {
        callProperties?: K.ObjectTypeCallPropertyKind[];
        comments?: K.CommentKind[] | null;
        exact?: boolean;
        indexers?: K.ObjectTypeIndexerKind[];
        inexact?: boolean | undefined;
        internalSlots?: K.ObjectTypeInternalSlotKind[];
        loc?: K.SourceLocationKind | null;
        properties: (K.ObjectTypePropertyKind | K.ObjectTypeSpreadPropertyKind)[];
    }): namedTypes.ObjectTypeAnnotation;
}
export interface ObjectTypePropertyBuilder {
    (key: K.LiteralKind | K.IdentifierKind, value: K.FlowTypeKind, optional: boolean): namedTypes.ObjectTypeProperty;
    from(params: {
        comments?: K.CommentKind[] | null;
        key: K.LiteralKind | K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        optional: boolean;
        value: K.FlowTypeKind;
        variance?: K.VarianceKind | "plus" | "minus" | null;
    }): namedTypes.ObjectTypeProperty;
}
export interface ObjectTypeSpreadPropertyBuilder {
    (argument: K.FlowTypeKind): namedTypes.ObjectTypeSpreadProperty;
    from(params: {
        argument: K.FlowTypeKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ObjectTypeSpreadProperty;
}
export interface ObjectTypeIndexerBuilder {
    (id: K.IdentifierKind, key: K.FlowTypeKind, value: K.FlowTypeKind): namedTypes.ObjectTypeIndexer;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        key: K.FlowTypeKind;
        loc?: K.SourceLocationKind | null;
        value: K.FlowTypeKind;
        variance?: K.VarianceKind | "plus" | "minus" | null;
    }): namedTypes.ObjectTypeIndexer;
}
export interface ObjectTypeCallPropertyBuilder {
    (value: K.FunctionTypeAnnotationKind): namedTypes.ObjectTypeCallProperty;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        static?: boolean;
        value: K.FunctionTypeAnnotationKind;
    }): namedTypes.ObjectTypeCallProperty;
}
export interface ObjectTypeInternalSlotBuilder {
    (id: K.IdentifierKind, value: K.FlowTypeKind, optional: boolean, staticParam: boolean, method: boolean): namedTypes.ObjectTypeInternalSlot;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        method: boolean;
        optional: boolean;
        static: boolean;
        value: K.FlowTypeKind;
    }): namedTypes.ObjectTypeInternalSlot;
}
export interface VarianceBuilder {
    (kind: "plus" | "minus"): namedTypes.Variance;
    from(params: {
        comments?: K.CommentKind[] | null;
        kind: "plus" | "minus";
        loc?: K.SourceLocationKind | null;
    }): namedTypes.Variance;
}
export interface QualifiedTypeIdentifierBuilder {
    (qualification: K.IdentifierKind | K.QualifiedTypeIdentifierKind, id: K.IdentifierKind): namedTypes.QualifiedTypeIdentifier;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        qualification: K.IdentifierKind | K.QualifiedTypeIdentifierKind;
    }): namedTypes.QualifiedTypeIdentifier;
}
export interface GenericTypeAnnotationBuilder {
    (id: K.IdentifierKind | K.QualifiedTypeIdentifierKind, typeParameters: K.TypeParameterInstantiationKind | null): namedTypes.GenericTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind | K.QualifiedTypeIdentifierKind;
        loc?: K.SourceLocationKind | null;
        typeParameters: K.TypeParameterInstantiationKind | null;
    }): namedTypes.GenericTypeAnnotation;
}
export interface MemberTypeAnnotationBuilder {
    (object: K.IdentifierKind, property: K.MemberTypeAnnotationKind | K.GenericTypeAnnotationKind): namedTypes.MemberTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        object: K.IdentifierKind;
        property: K.MemberTypeAnnotationKind | K.GenericTypeAnnotationKind;
    }): namedTypes.MemberTypeAnnotation;
}
export interface UnionTypeAnnotationBuilder {
    (types: K.FlowTypeKind[]): namedTypes.UnionTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        types: K.FlowTypeKind[];
    }): namedTypes.UnionTypeAnnotation;
}
export interface IntersectionTypeAnnotationBuilder {
    (types: K.FlowTypeKind[]): namedTypes.IntersectionTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        types: K.FlowTypeKind[];
    }): namedTypes.IntersectionTypeAnnotation;
}
export interface TypeofTypeAnnotationBuilder {
    (argument: K.FlowTypeKind): namedTypes.TypeofTypeAnnotation;
    from(params: {
        argument: K.FlowTypeKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TypeofTypeAnnotation;
}
export interface TypeParameterBuilder {
    (name: string, variance?: K.VarianceKind | "plus" | "minus" | null, bound?: K.TypeAnnotationKind | null): namedTypes.TypeParameter;
    from(params: {
        bound?: K.TypeAnnotationKind | null;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        name: string;
        variance?: K.VarianceKind | "plus" | "minus" | null;
    }): namedTypes.TypeParameter;
}
export interface InterfaceTypeAnnotationBuilder {
    (body: K.ObjectTypeAnnotationKind, extendsParam?: K.InterfaceExtendsKind[] | null): namedTypes.InterfaceTypeAnnotation;
    from(params: {
        body: K.ObjectTypeAnnotationKind;
        comments?: K.CommentKind[] | null;
        extends?: K.InterfaceExtendsKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.InterfaceTypeAnnotation;
}
export interface InterfaceExtendsBuilder {
    (id: K.IdentifierKind): namedTypes.InterfaceExtends;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        typeParameters?: K.TypeParameterInstantiationKind | null;
    }): namedTypes.InterfaceExtends;
}
export interface InterfaceDeclarationBuilder {
    (id: K.IdentifierKind, body: K.ObjectTypeAnnotationKind, extendsParam: K.InterfaceExtendsKind[]): namedTypes.InterfaceDeclaration;
    from(params: {
        body: K.ObjectTypeAnnotationKind;
        comments?: K.CommentKind[] | null;
        extends: K.InterfaceExtendsKind[];
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        typeParameters?: K.TypeParameterDeclarationKind | null;
    }): namedTypes.InterfaceDeclaration;
}
export interface DeclareInterfaceBuilder {
    (id: K.IdentifierKind, body: K.ObjectTypeAnnotationKind, extendsParam: K.InterfaceExtendsKind[]): namedTypes.DeclareInterface;
    from(params: {
        body: K.ObjectTypeAnnotationKind;
        comments?: K.CommentKind[] | null;
        extends: K.InterfaceExtendsKind[];
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        typeParameters?: K.TypeParameterDeclarationKind | null;
    }): namedTypes.DeclareInterface;
}
export interface TypeAliasBuilder {
    (id: K.IdentifierKind, typeParameters: K.TypeParameterDeclarationKind | null, right: K.FlowTypeKind): namedTypes.TypeAlias;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        right: K.FlowTypeKind;
        typeParameters: K.TypeParameterDeclarationKind | null;
    }): namedTypes.TypeAlias;
}
export interface OpaqueTypeBuilder {
    (id: K.IdentifierKind, typeParameters: K.TypeParameterDeclarationKind | null, impltype: K.FlowTypeKind, supertype: K.FlowTypeKind): namedTypes.OpaqueType;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        impltype: K.FlowTypeKind;
        loc?: K.SourceLocationKind | null;
        supertype: K.FlowTypeKind;
        typeParameters: K.TypeParameterDeclarationKind | null;
    }): namedTypes.OpaqueType;
}
export interface DeclareTypeAliasBuilder {
    (id: K.IdentifierKind, typeParameters: K.TypeParameterDeclarationKind | null, right: K.FlowTypeKind): namedTypes.DeclareTypeAlias;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        right: K.FlowTypeKind;
        typeParameters: K.TypeParameterDeclarationKind | null;
    }): namedTypes.DeclareTypeAlias;
}
export interface DeclareOpaqueTypeBuilder {
    (id: K.IdentifierKind, typeParameters: K.TypeParameterDeclarationKind | null): namedTypes.DeclareOpaqueType;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        right: K.FlowTypeKind;
        typeParameters: K.TypeParameterDeclarationKind | null;
    }): namedTypes.DeclareOpaqueType;
}
export interface TypeCastExpressionBuilder {
    (expression: K.ExpressionKind, typeAnnotation: K.TypeAnnotationKind): namedTypes.TypeCastExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.TypeAnnotationKind;
    }): namedTypes.TypeCastExpression;
}
export interface TupleTypeAnnotationBuilder {
    (types: K.FlowTypeKind[]): namedTypes.TupleTypeAnnotation;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        types: K.FlowTypeKind[];
    }): namedTypes.TupleTypeAnnotation;
}
export interface DeclareVariableBuilder {
    (id: K.IdentifierKind): namedTypes.DeclareVariable;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.DeclareVariable;
}
export interface DeclareFunctionBuilder {
    (id: K.IdentifierKind): namedTypes.DeclareFunction;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.DeclareFunction;
}
export interface DeclareClassBuilder {
    (id: K.IdentifierKind): namedTypes.DeclareClass;
    from(params: {
        body: K.ObjectTypeAnnotationKind;
        comments?: K.CommentKind[] | null;
        extends: K.InterfaceExtendsKind[];
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        typeParameters?: K.TypeParameterDeclarationKind | null;
    }): namedTypes.DeclareClass;
}
export interface DeclareModuleBuilder {
    (id: K.IdentifierKind | K.LiteralKind, body: K.BlockStatementKind): namedTypes.DeclareModule;
    from(params: {
        body: K.BlockStatementKind;
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind | K.LiteralKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.DeclareModule;
}
export interface DeclareModuleExportsBuilder {
    (typeAnnotation: K.TypeAnnotationKind): namedTypes.DeclareModuleExports;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.TypeAnnotationKind;
    }): namedTypes.DeclareModuleExports;
}
export interface DeclareExportDeclarationBuilder {
    (defaultParam: boolean, declaration: K.DeclareVariableKind | K.DeclareFunctionKind | K.DeclareClassKind | K.FlowTypeKind | null, specifiers?: (K.ExportSpecifierKind | K.ExportBatchSpecifierKind)[], source?: K.LiteralKind | null): namedTypes.DeclareExportDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        declaration: K.DeclareVariableKind | K.DeclareFunctionKind | K.DeclareClassKind | K.FlowTypeKind | null;
        default: boolean;
        loc?: K.SourceLocationKind | null;
        source?: K.LiteralKind | null;
        specifiers?: (K.ExportSpecifierKind | K.ExportBatchSpecifierKind)[];
    }): namedTypes.DeclareExportDeclaration;
}
export interface ExportSpecifierBuilder {
    (local: K.IdentifierKind | null | undefined, exported: K.IdentifierKind): namedTypes.ExportSpecifier;
    from(params: {
        comments?: K.CommentKind[] | null;
        exported: K.IdentifierKind;
        id?: K.IdentifierKind | null;
        loc?: K.SourceLocationKind | null;
        local?: K.IdentifierKind | null;
        name?: K.IdentifierKind | null;
    }): namedTypes.ExportSpecifier;
}
export interface ExportBatchSpecifierBuilder {
    (): namedTypes.ExportBatchSpecifier;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ExportBatchSpecifier;
}
export interface DeclareExportAllDeclarationBuilder {
    (source?: K.LiteralKind | null): namedTypes.DeclareExportAllDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        source?: K.LiteralKind | null;
    }): namedTypes.DeclareExportAllDeclaration;
}
export interface InferredPredicateBuilder {
    (): namedTypes.InferredPredicate;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.InferredPredicate;
}
export interface DeclaredPredicateBuilder {
    (value: K.ExpressionKind): namedTypes.DeclaredPredicate;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        value: K.ExpressionKind;
    }): namedTypes.DeclaredPredicate;
}
export interface ExportDeclarationBuilder {
    (defaultParam: boolean, declaration: K.DeclarationKind | K.ExpressionKind | null, specifiers?: (K.ExportSpecifierKind | K.ExportBatchSpecifierKind)[], source?: K.LiteralKind | null): namedTypes.ExportDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        declaration: K.DeclarationKind | K.ExpressionKind | null;
        default: boolean;
        loc?: K.SourceLocationKind | null;
        source?: K.LiteralKind | null;
        specifiers?: (K.ExportSpecifierKind | K.ExportBatchSpecifierKind)[];
    }): namedTypes.ExportDeclaration;
}
export interface BlockBuilder {
    (value: string, leading?: boolean, trailing?: boolean): namedTypes.Block;
    from(params: {
        leading?: boolean;
        loc?: K.SourceLocationKind | null;
        trailing?: boolean;
        value: string;
    }): namedTypes.Block;
}
export interface LineBuilder {
    (value: string, leading?: boolean, trailing?: boolean): namedTypes.Line;
    from(params: {
        leading?: boolean;
        loc?: K.SourceLocationKind | null;
        trailing?: boolean;
        value: string;
    }): namedTypes.Line;
}
export interface NoopBuilder {
    (): namedTypes.Noop;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.Noop;
}
export interface DoExpressionBuilder {
    (body: K.StatementKind[]): namedTypes.DoExpression;
    from(params: {
        body: K.StatementKind[];
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.DoExpression;
}
export interface SuperBuilder {
    (): namedTypes.Super;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.Super;
}
export interface BindExpressionBuilder {
    (object: K.ExpressionKind | null, callee: K.ExpressionKind): namedTypes.BindExpression;
    from(params: {
        callee: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        object: K.ExpressionKind | null;
    }): namedTypes.BindExpression;
}
export interface DecoratorBuilder {
    (expression: K.ExpressionKind): namedTypes.Decorator;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.Decorator;
}
export interface MetaPropertyBuilder {
    (meta: K.IdentifierKind, property: K.IdentifierKind): namedTypes.MetaProperty;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        meta: K.IdentifierKind;
        property: K.IdentifierKind;
    }): namedTypes.MetaProperty;
}
export interface ParenthesizedExpressionBuilder {
    (expression: K.ExpressionKind): namedTypes.ParenthesizedExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ParenthesizedExpression;
}
export interface ExportDefaultDeclarationBuilder {
    (declaration: K.DeclarationKind | K.ExpressionKind): namedTypes.ExportDefaultDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        declaration: K.DeclarationKind | K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ExportDefaultDeclaration;
}
export interface ExportNamedDeclarationBuilder {
    (declaration: K.DeclarationKind | null, specifiers?: K.ExportSpecifierKind[], source?: K.LiteralKind | null): namedTypes.ExportNamedDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        declaration: K.DeclarationKind | null;
        loc?: K.SourceLocationKind | null;
        source?: K.LiteralKind | null;
        specifiers?: K.ExportSpecifierKind[];
    }): namedTypes.ExportNamedDeclaration;
}
export interface ExportNamespaceSpecifierBuilder {
    (exported: K.IdentifierKind): namedTypes.ExportNamespaceSpecifier;
    from(params: {
        comments?: K.CommentKind[] | null;
        exported: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ExportNamespaceSpecifier;
}
export interface ExportDefaultSpecifierBuilder {
    (exported: K.IdentifierKind): namedTypes.ExportDefaultSpecifier;
    from(params: {
        comments?: K.CommentKind[] | null;
        exported: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.ExportDefaultSpecifier;
}
export interface ExportAllDeclarationBuilder {
    (exported: K.IdentifierKind | null, source: K.LiteralKind): namedTypes.ExportAllDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        exported: K.IdentifierKind | null;
        loc?: K.SourceLocationKind | null;
        source: K.LiteralKind;
    }): namedTypes.ExportAllDeclaration;
}
export interface CommentBlockBuilder {
    (value: string, leading?: boolean, trailing?: boolean): namedTypes.CommentBlock;
    from(params: {
        leading?: boolean;
        loc?: K.SourceLocationKind | null;
        trailing?: boolean;
        value: string;
    }): namedTypes.CommentBlock;
}
export interface CommentLineBuilder {
    (value: string, leading?: boolean, trailing?: boolean): namedTypes.CommentLine;
    from(params: {
        leading?: boolean;
        loc?: K.SourceLocationKind | null;
        trailing?: boolean;
        value: string;
    }): namedTypes.CommentLine;
}
export interface DirectiveBuilder {
    (value: K.DirectiveLiteralKind): namedTypes.Directive;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        value: K.DirectiveLiteralKind;
    }): namedTypes.Directive;
}
export interface DirectiveLiteralBuilder {
    (value?: string): namedTypes.DirectiveLiteral;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        value?: string;
    }): namedTypes.DirectiveLiteral;
}
export interface InterpreterDirectiveBuilder {
    (value: string): namedTypes.InterpreterDirective;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        value: string;
    }): namedTypes.InterpreterDirective;
}
export interface StringLiteralBuilder {
    (value: string): namedTypes.StringLiteral;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        regex?: {
            pattern: string;
            flags: string;
        } | null;
        value: string;
    }): namedTypes.StringLiteral;
}
export interface NumericLiteralBuilder {
    (value: number): namedTypes.NumericLiteral;
    from(params: {
        comments?: K.CommentKind[] | null;
        extra?: {
            rawValue: number;
            raw: string;
        };
        loc?: K.SourceLocationKind | null;
        raw?: string | null;
        regex?: {
            pattern: string;
            flags: string;
        } | null;
        value: number;
    }): namedTypes.NumericLiteral;
}
export interface BigIntLiteralBuilder {
    (value: string | number): namedTypes.BigIntLiteral;
    from(params: {
        comments?: K.CommentKind[] | null;
        extra?: {
            rawValue: string;
            raw: string;
        };
        loc?: K.SourceLocationKind | null;
        regex?: {
            pattern: string;
            flags: string;
        } | null;
        value: string | number;
    }): namedTypes.BigIntLiteral;
}
export interface NullLiteralBuilder {
    (): namedTypes.NullLiteral;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        regex?: {
            pattern: string;
            flags: string;
        } | null;
        value?: null;
    }): namedTypes.NullLiteral;
}
export interface BooleanLiteralBuilder {
    (value: boolean): namedTypes.BooleanLiteral;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        regex?: {
            pattern: string;
            flags: string;
        } | null;
        value: boolean;
    }): namedTypes.BooleanLiteral;
}
export interface RegExpLiteralBuilder {
    (pattern: string, flags: string): namedTypes.RegExpLiteral;
    from(params: {
        comments?: K.CommentKind[] | null;
        flags: string;
        loc?: K.SourceLocationKind | null;
        pattern: string;
        regex?: {
            pattern: string;
            flags: string;
        } | null;
        value?: RegExp;
    }): namedTypes.RegExpLiteral;
}
export interface ObjectMethodBuilder {
    (kind: "method" | "get" | "set", key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind, params: K.PatternKind[], body: K.BlockStatementKind, computed?: boolean): namedTypes.ObjectMethod;
    from(params: {
        accessibility?: K.LiteralKind | null;
        async?: boolean;
        body: K.BlockStatementKind;
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        decorators?: K.DecoratorKind[] | null;
        defaults?: (K.ExpressionKind | null)[];
        expression?: boolean;
        generator?: boolean;
        id?: K.IdentifierKind | null;
        key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind;
        kind: "method" | "get" | "set";
        loc?: K.SourceLocationKind | null;
        params: K.PatternKind[];
        rest?: K.IdentifierKind | null;
        returnType?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
        typeParameters?: K.TypeParameterDeclarationKind | K.TSTypeParameterDeclarationKind | null;
    }): namedTypes.ObjectMethod;
}
export interface ClassPrivatePropertyBuilder {
    (key: K.PrivateNameKind, value?: K.ExpressionKind | null): namedTypes.ClassPrivateProperty;
    from(params: {
        access?: "public" | "private" | "protected" | undefined;
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        key: K.PrivateNameKind;
        loc?: K.SourceLocationKind | null;
        static?: boolean;
        typeAnnotation?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
        value?: K.ExpressionKind | null;
        variance?: K.VarianceKind | "plus" | "minus" | null;
    }): namedTypes.ClassPrivateProperty;
}
export interface ClassMethodBuilder {
    (kind: "get" | "set" | "method" | "constructor" | undefined, key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind, params: K.PatternKind[], body: K.BlockStatementKind, computed?: boolean, staticParam?: boolean | null): namedTypes.ClassMethod;
    from(params: {
        abstract?: boolean | null;
        access?: "public" | "private" | "protected" | null;
        accessibility?: "public" | "private" | "protected" | null;
        async?: boolean;
        body: K.BlockStatementKind;
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        decorators?: K.DecoratorKind[] | null;
        defaults?: (K.ExpressionKind | null)[];
        expression?: boolean;
        generator?: boolean;
        id?: K.IdentifierKind | null;
        key: K.LiteralKind | K.IdentifierKind | K.ExpressionKind;
        kind?: "get" | "set" | "method" | "constructor";
        loc?: K.SourceLocationKind | null;
        optional?: boolean | null;
        params: K.PatternKind[];
        rest?: K.IdentifierKind | null;
        returnType?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
        static?: boolean | null;
        typeParameters?: K.TypeParameterDeclarationKind | K.TSTypeParameterDeclarationKind | null;
    }): namedTypes.ClassMethod;
}
export interface ClassPrivateMethodBuilder {
    (key: K.PrivateNameKind, params: K.PatternKind[], body: K.BlockStatementKind, kind?: "get" | "set" | "method" | "constructor", computed?: boolean, staticParam?: boolean | null): namedTypes.ClassPrivateMethod;
    from(params: {
        abstract?: boolean | null;
        access?: "public" | "private" | "protected" | null;
        accessibility?: "public" | "private" | "protected" | null;
        async?: boolean;
        body: K.BlockStatementKind;
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        decorators?: K.DecoratorKind[] | null;
        defaults?: (K.ExpressionKind | null)[];
        expression?: boolean;
        generator?: boolean;
        id?: K.IdentifierKind | null;
        key: K.PrivateNameKind;
        kind?: "get" | "set" | "method" | "constructor";
        loc?: K.SourceLocationKind | null;
        optional?: boolean | null;
        params: K.PatternKind[];
        rest?: K.IdentifierKind | null;
        returnType?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
        static?: boolean | null;
        typeParameters?: K.TypeParameterDeclarationKind | K.TSTypeParameterDeclarationKind | null;
    }): namedTypes.ClassPrivateMethod;
}
export interface PrivateNameBuilder {
    (id: K.IdentifierKind): namedTypes.PrivateName;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.PrivateName;
}
export interface RestPropertyBuilder {
    (argument: K.ExpressionKind): namedTypes.RestProperty;
    from(params: {
        argument: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.RestProperty;
}
export interface ForAwaitStatementBuilder {
    (left: K.VariableDeclarationKind | K.ExpressionKind, right: K.ExpressionKind, body: K.StatementKind): namedTypes.ForAwaitStatement;
    from(params: {
        body: K.StatementKind;
        comments?: K.CommentKind[] | null;
        left: K.VariableDeclarationKind | K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        right: K.ExpressionKind;
    }): namedTypes.ForAwaitStatement;
}
export interface ImportBuilder {
    (): namedTypes.Import;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.Import;
}
export interface TSQualifiedNameBuilder {
    (left: K.IdentifierKind | K.TSQualifiedNameKind, right: K.IdentifierKind | K.TSQualifiedNameKind): namedTypes.TSQualifiedName;
    from(params: {
        comments?: K.CommentKind[] | null;
        left: K.IdentifierKind | K.TSQualifiedNameKind;
        loc?: K.SourceLocationKind | null;
        right: K.IdentifierKind | K.TSQualifiedNameKind;
    }): namedTypes.TSQualifiedName;
}
export interface TSTypeReferenceBuilder {
    (typeName: K.IdentifierKind | K.TSQualifiedNameKind, typeParameters?: K.TSTypeParameterInstantiationKind | null): namedTypes.TSTypeReference;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeName: K.IdentifierKind | K.TSQualifiedNameKind;
        typeParameters?: K.TSTypeParameterInstantiationKind | null;
    }): namedTypes.TSTypeReference;
}
export interface TSAsExpressionBuilder {
    (expression: K.ExpressionKind, typeAnnotation: K.TSTypeKind): namedTypes.TSAsExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.ExpressionKind;
        extra?: {
            parenthesized: boolean;
        } | null;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.TSTypeKind;
    }): namedTypes.TSAsExpression;
}
export interface TSNonNullExpressionBuilder {
    (expression: K.ExpressionKind): namedTypes.TSNonNullExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSNonNullExpression;
}
export interface TSAnyKeywordBuilder {
    (): namedTypes.TSAnyKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSAnyKeyword;
}
export interface TSBigIntKeywordBuilder {
    (): namedTypes.TSBigIntKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSBigIntKeyword;
}
export interface TSBooleanKeywordBuilder {
    (): namedTypes.TSBooleanKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSBooleanKeyword;
}
export interface TSNeverKeywordBuilder {
    (): namedTypes.TSNeverKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSNeverKeyword;
}
export interface TSNullKeywordBuilder {
    (): namedTypes.TSNullKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSNullKeyword;
}
export interface TSNumberKeywordBuilder {
    (): namedTypes.TSNumberKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSNumberKeyword;
}
export interface TSObjectKeywordBuilder {
    (): namedTypes.TSObjectKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSObjectKeyword;
}
export interface TSStringKeywordBuilder {
    (): namedTypes.TSStringKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSStringKeyword;
}
export interface TSSymbolKeywordBuilder {
    (): namedTypes.TSSymbolKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSSymbolKeyword;
}
export interface TSUndefinedKeywordBuilder {
    (): namedTypes.TSUndefinedKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSUndefinedKeyword;
}
export interface TSUnknownKeywordBuilder {
    (): namedTypes.TSUnknownKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSUnknownKeyword;
}
export interface TSVoidKeywordBuilder {
    (): namedTypes.TSVoidKeyword;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSVoidKeyword;
}
export interface TSThisTypeBuilder {
    (): namedTypes.TSThisType;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSThisType;
}
export interface TSArrayTypeBuilder {
    (elementType: K.TSTypeKind): namedTypes.TSArrayType;
    from(params: {
        comments?: K.CommentKind[] | null;
        elementType: K.TSTypeKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSArrayType;
}
export interface TSLiteralTypeBuilder {
    (literal: K.NumericLiteralKind | K.StringLiteralKind | K.BooleanLiteralKind | K.TemplateLiteralKind | K.UnaryExpressionKind): namedTypes.TSLiteralType;
    from(params: {
        comments?: K.CommentKind[] | null;
        literal: K.NumericLiteralKind | K.StringLiteralKind | K.BooleanLiteralKind | K.TemplateLiteralKind | K.UnaryExpressionKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSLiteralType;
}
export interface TSUnionTypeBuilder {
    (types: K.TSTypeKind[]): namedTypes.TSUnionType;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        types: K.TSTypeKind[];
    }): namedTypes.TSUnionType;
}
export interface TSIntersectionTypeBuilder {
    (types: K.TSTypeKind[]): namedTypes.TSIntersectionType;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        types: K.TSTypeKind[];
    }): namedTypes.TSIntersectionType;
}
export interface TSConditionalTypeBuilder {
    (checkType: K.TSTypeKind, extendsType: K.TSTypeKind, trueType: K.TSTypeKind, falseType: K.TSTypeKind): namedTypes.TSConditionalType;
    from(params: {
        checkType: K.TSTypeKind;
        comments?: K.CommentKind[] | null;
        extendsType: K.TSTypeKind;
        falseType: K.TSTypeKind;
        loc?: K.SourceLocationKind | null;
        trueType: K.TSTypeKind;
    }): namedTypes.TSConditionalType;
}
export interface TSInferTypeBuilder {
    (typeParameter: K.TSTypeParameterKind): namedTypes.TSInferType;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeParameter: K.TSTypeParameterKind;
    }): namedTypes.TSInferType;
}
export interface TSTypeParameterBuilder {
    (name: string, constraint?: K.TSTypeKind | undefined, defaultParam?: K.TSTypeKind | undefined): namedTypes.TSTypeParameter;
    from(params: {
        comments?: K.CommentKind[] | null;
        constraint?: K.TSTypeKind | undefined;
        default?: K.TSTypeKind | undefined;
        loc?: K.SourceLocationKind | null;
        name: string;
        optional?: boolean;
        typeAnnotation?: K.TypeAnnotationKind | K.TSTypeAnnotationKind | null;
    }): namedTypes.TSTypeParameter;
}
export interface TSParenthesizedTypeBuilder {
    (typeAnnotation: K.TSTypeKind): namedTypes.TSParenthesizedType;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.TSTypeKind;
    }): namedTypes.TSParenthesizedType;
}
export interface TSFunctionTypeBuilder {
    (parameters: (K.IdentifierKind | K.RestElementKind | K.ArrayPatternKind | K.ObjectPatternKind)[]): namedTypes.TSFunctionType;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        parameters: (K.IdentifierKind | K.RestElementKind | K.ArrayPatternKind | K.ObjectPatternKind)[];
        typeAnnotation?: K.TSTypeAnnotationKind | null;
        typeParameters?: K.TSTypeParameterDeclarationKind | null | undefined;
    }): namedTypes.TSFunctionType;
}
export interface TSConstructorTypeBuilder {
    (parameters: (K.IdentifierKind | K.RestElementKind | K.ArrayPatternKind | K.ObjectPatternKind)[]): namedTypes.TSConstructorType;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        parameters: (K.IdentifierKind | K.RestElementKind | K.ArrayPatternKind | K.ObjectPatternKind)[];
        typeAnnotation?: K.TSTypeAnnotationKind | null;
        typeParameters?: K.TSTypeParameterDeclarationKind | null | undefined;
    }): namedTypes.TSConstructorType;
}
export interface TSDeclareFunctionBuilder {
    (id: K.IdentifierKind | null | undefined, params: K.PatternKind[], returnType?: K.TSTypeAnnotationKind | K.NoopKind | null): namedTypes.TSDeclareFunction;
    from(params: {
        async?: boolean;
        comments?: K.CommentKind[] | null;
        declare?: boolean;
        generator?: boolean;
        id?: K.IdentifierKind | null;
        loc?: K.SourceLocationKind | null;
        params: K.PatternKind[];
        returnType?: K.TSTypeAnnotationKind | K.NoopKind | null;
        typeParameters?: K.TSTypeParameterDeclarationKind | null | undefined;
    }): namedTypes.TSDeclareFunction;
}
export interface TSDeclareMethodBuilder {
    (key: K.IdentifierKind | K.StringLiteralKind | K.NumericLiteralKind | K.ExpressionKind, params: K.PatternKind[], returnType?: K.TSTypeAnnotationKind | K.NoopKind | null): namedTypes.TSDeclareMethod;
    from(params: {
        abstract?: boolean;
        access?: "public" | "private" | "protected" | undefined;
        accessibility?: "public" | "private" | "protected" | undefined;
        async?: boolean;
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        decorators?: K.DecoratorKind[] | null;
        generator?: boolean;
        key: K.IdentifierKind | K.StringLiteralKind | K.NumericLiteralKind | K.ExpressionKind;
        kind?: "get" | "set" | "method" | "constructor";
        loc?: K.SourceLocationKind | null;
        optional?: boolean;
        params: K.PatternKind[];
        returnType?: K.TSTypeAnnotationKind | K.NoopKind | null;
        static?: boolean;
        typeParameters?: K.TSTypeParameterDeclarationKind | null | undefined;
    }): namedTypes.TSDeclareMethod;
}
export interface TSMappedTypeBuilder {
    (typeParameter: K.TSTypeParameterKind, typeAnnotation?: K.TSTypeKind | null): namedTypes.TSMappedType;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        optional?: boolean | "+" | "-";
        readonly?: boolean | "+" | "-";
        typeAnnotation?: K.TSTypeKind | null;
        typeParameter: K.TSTypeParameterKind;
    }): namedTypes.TSMappedType;
}
export interface TSTupleTypeBuilder {
    (elementTypes: (K.TSTypeKind | K.TSNamedTupleMemberKind)[]): namedTypes.TSTupleType;
    from(params: {
        comments?: K.CommentKind[] | null;
        elementTypes: (K.TSTypeKind | K.TSNamedTupleMemberKind)[];
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSTupleType;
}
export interface TSNamedTupleMemberBuilder {
    (label: K.IdentifierKind, elementType: K.TSTypeKind, optional?: boolean): namedTypes.TSNamedTupleMember;
    from(params: {
        comments?: K.CommentKind[] | null;
        elementType: K.TSTypeKind;
        label: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        optional?: boolean;
    }): namedTypes.TSNamedTupleMember;
}
export interface TSRestTypeBuilder {
    (typeAnnotation: K.TSTypeKind): namedTypes.TSRestType;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.TSTypeKind;
    }): namedTypes.TSRestType;
}
export interface TSOptionalTypeBuilder {
    (typeAnnotation: K.TSTypeKind): namedTypes.TSOptionalType;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.TSTypeKind;
    }): namedTypes.TSOptionalType;
}
export interface TSIndexedAccessTypeBuilder {
    (objectType: K.TSTypeKind, indexType: K.TSTypeKind): namedTypes.TSIndexedAccessType;
    from(params: {
        comments?: K.CommentKind[] | null;
        indexType: K.TSTypeKind;
        loc?: K.SourceLocationKind | null;
        objectType: K.TSTypeKind;
    }): namedTypes.TSIndexedAccessType;
}
export interface TSTypeOperatorBuilder {
    (operator: string): namedTypes.TSTypeOperator;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        operator: string;
        typeAnnotation: K.TSTypeKind;
    }): namedTypes.TSTypeOperator;
}
export interface TSIndexSignatureBuilder {
    (parameters: K.IdentifierKind[], typeAnnotation?: K.TSTypeAnnotationKind | null): namedTypes.TSIndexSignature;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        parameters: K.IdentifierKind[];
        readonly?: boolean;
        typeAnnotation?: K.TSTypeAnnotationKind | null;
    }): namedTypes.TSIndexSignature;
}
export interface TSPropertySignatureBuilder {
    (key: K.ExpressionKind, typeAnnotation?: K.TSTypeAnnotationKind | null, optional?: boolean): namedTypes.TSPropertySignature;
    from(params: {
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        initializer?: K.ExpressionKind | null;
        key: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        optional?: boolean;
        readonly?: boolean;
        typeAnnotation?: K.TSTypeAnnotationKind | null;
    }): namedTypes.TSPropertySignature;
}
export interface TSMethodSignatureBuilder {
    (key: K.ExpressionKind, parameters: (K.IdentifierKind | K.RestElementKind | K.ArrayPatternKind | K.ObjectPatternKind)[], typeAnnotation?: K.TSTypeAnnotationKind | null): namedTypes.TSMethodSignature;
    from(params: {
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        key: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
        optional?: boolean;
        parameters: (K.IdentifierKind | K.RestElementKind | K.ArrayPatternKind | K.ObjectPatternKind)[];
        typeAnnotation?: K.TSTypeAnnotationKind | null;
        typeParameters?: K.TSTypeParameterDeclarationKind | null | undefined;
    }): namedTypes.TSMethodSignature;
}
export interface TSTypePredicateBuilder {
    (parameterName: K.IdentifierKind | K.TSThisTypeKind, typeAnnotation?: K.TSTypeAnnotationKind | null, asserts?: boolean): namedTypes.TSTypePredicate;
    from(params: {
        asserts?: boolean;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        parameterName: K.IdentifierKind | K.TSThisTypeKind;
        typeAnnotation?: K.TSTypeAnnotationKind | null;
    }): namedTypes.TSTypePredicate;
}
export interface TSCallSignatureDeclarationBuilder {
    (parameters: (K.IdentifierKind | K.RestElementKind | K.ArrayPatternKind | K.ObjectPatternKind)[], typeAnnotation?: K.TSTypeAnnotationKind | null): namedTypes.TSCallSignatureDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        parameters: (K.IdentifierKind | K.RestElementKind | K.ArrayPatternKind | K.ObjectPatternKind)[];
        typeAnnotation?: K.TSTypeAnnotationKind | null;
        typeParameters?: K.TSTypeParameterDeclarationKind | null | undefined;
    }): namedTypes.TSCallSignatureDeclaration;
}
export interface TSConstructSignatureDeclarationBuilder {
    (parameters: (K.IdentifierKind | K.RestElementKind | K.ArrayPatternKind | K.ObjectPatternKind)[], typeAnnotation?: K.TSTypeAnnotationKind | null): namedTypes.TSConstructSignatureDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        parameters: (K.IdentifierKind | K.RestElementKind | K.ArrayPatternKind | K.ObjectPatternKind)[];
        typeAnnotation?: K.TSTypeAnnotationKind | null;
        typeParameters?: K.TSTypeParameterDeclarationKind | null | undefined;
    }): namedTypes.TSConstructSignatureDeclaration;
}
export interface TSEnumMemberBuilder {
    (id: K.IdentifierKind | K.StringLiteralKind, initializer?: K.ExpressionKind | null): namedTypes.TSEnumMember;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind | K.StringLiteralKind;
        initializer?: K.ExpressionKind | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSEnumMember;
}
export interface TSTypeQueryBuilder {
    (exprName: K.IdentifierKind | K.TSQualifiedNameKind | K.TSImportTypeKind): namedTypes.TSTypeQuery;
    from(params: {
        comments?: K.CommentKind[] | null;
        exprName: K.IdentifierKind | K.TSQualifiedNameKind | K.TSImportTypeKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSTypeQuery;
}
export interface TSImportTypeBuilder {
    (argument: K.StringLiteralKind, qualifier?: K.IdentifierKind | K.TSQualifiedNameKind | undefined, typeParameters?: K.TSTypeParameterInstantiationKind | null): namedTypes.TSImportType;
    from(params: {
        argument: K.StringLiteralKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        qualifier?: K.IdentifierKind | K.TSQualifiedNameKind | undefined;
        typeParameters?: K.TSTypeParameterInstantiationKind | null;
    }): namedTypes.TSImportType;
}
export interface TSTypeLiteralBuilder {
    (members: (K.TSCallSignatureDeclarationKind | K.TSConstructSignatureDeclarationKind | K.TSIndexSignatureKind | K.TSMethodSignatureKind | K.TSPropertySignatureKind)[]): namedTypes.TSTypeLiteral;
    from(params: {
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        members: (K.TSCallSignatureDeclarationKind | K.TSConstructSignatureDeclarationKind | K.TSIndexSignatureKind | K.TSMethodSignatureKind | K.TSPropertySignatureKind)[];
    }): namedTypes.TSTypeLiteral;
}
export interface TSTypeAssertionBuilder {
    (typeAnnotation: K.TSTypeKind, expression: K.ExpressionKind): namedTypes.TSTypeAssertion;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.ExpressionKind;
        extra?: {
            parenthesized: boolean;
        } | null;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.TSTypeKind;
    }): namedTypes.TSTypeAssertion;
}
export interface TSEnumDeclarationBuilder {
    (id: K.IdentifierKind, members: K.TSEnumMemberKind[]): namedTypes.TSEnumDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        const?: boolean;
        declare?: boolean;
        id: K.IdentifierKind;
        initializer?: K.ExpressionKind | null;
        loc?: K.SourceLocationKind | null;
        members: K.TSEnumMemberKind[];
    }): namedTypes.TSEnumDeclaration;
}
export interface TSTypeAliasDeclarationBuilder {
    (id: K.IdentifierKind, typeAnnotation: K.TSTypeKind): namedTypes.TSTypeAliasDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        declare?: boolean;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
        typeAnnotation: K.TSTypeKind;
        typeParameters?: K.TSTypeParameterDeclarationKind | null | undefined;
    }): namedTypes.TSTypeAliasDeclaration;
}
export interface TSModuleBlockBuilder {
    (body: K.StatementKind[]): namedTypes.TSModuleBlock;
    from(params: {
        body: K.StatementKind[];
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSModuleBlock;
}
export interface TSModuleDeclarationBuilder {
    (id: K.StringLiteralKind | K.IdentifierKind | K.TSQualifiedNameKind, body?: K.TSModuleBlockKind | K.TSModuleDeclarationKind | null): namedTypes.TSModuleDeclaration;
    from(params: {
        body?: K.TSModuleBlockKind | K.TSModuleDeclarationKind | null;
        comments?: K.CommentKind[] | null;
        declare?: boolean;
        global?: boolean;
        id: K.StringLiteralKind | K.IdentifierKind | K.TSQualifiedNameKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSModuleDeclaration;
}
export interface TSImportEqualsDeclarationBuilder {
    (id: K.IdentifierKind, moduleReference: K.IdentifierKind | K.TSQualifiedNameKind | K.TSExternalModuleReferenceKind): namedTypes.TSImportEqualsDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        isExport?: boolean;
        loc?: K.SourceLocationKind | null;
        moduleReference: K.IdentifierKind | K.TSQualifiedNameKind | K.TSExternalModuleReferenceKind;
    }): namedTypes.TSImportEqualsDeclaration;
}
export interface TSExternalModuleReferenceBuilder {
    (expression: K.StringLiteralKind): namedTypes.TSExternalModuleReference;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.StringLiteralKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSExternalModuleReference;
}
export interface TSExportAssignmentBuilder {
    (expression: K.ExpressionKind): namedTypes.TSExportAssignment;
    from(params: {
        comments?: K.CommentKind[] | null;
        expression: K.ExpressionKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSExportAssignment;
}
export interface TSNamespaceExportDeclarationBuilder {
    (id: K.IdentifierKind): namedTypes.TSNamespaceExportDeclaration;
    from(params: {
        comments?: K.CommentKind[] | null;
        id: K.IdentifierKind;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSNamespaceExportDeclaration;
}
export interface TSInterfaceBodyBuilder {
    (body: (K.TSCallSignatureDeclarationKind | K.TSConstructSignatureDeclarationKind | K.TSIndexSignatureKind | K.TSMethodSignatureKind | K.TSPropertySignatureKind)[]): namedTypes.TSInterfaceBody;
    from(params: {
        body: (K.TSCallSignatureDeclarationKind | K.TSConstructSignatureDeclarationKind | K.TSIndexSignatureKind | K.TSMethodSignatureKind | K.TSPropertySignatureKind)[];
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
    }): namedTypes.TSInterfaceBody;
}
export interface TSInterfaceDeclarationBuilder {
    (id: K.IdentifierKind | K.TSQualifiedNameKind, body: K.TSInterfaceBodyKind): namedTypes.TSInterfaceDeclaration;
    from(params: {
        body: K.TSInterfaceBodyKind;
        comments?: K.CommentKind[] | null;
        declare?: boolean;
        extends?: K.TSExpressionWithTypeArgumentsKind[] | null;
        id: K.IdentifierKind | K.TSQualifiedNameKind;
        loc?: K.SourceLocationKind | null;
        typeParameters?: K.TSTypeParameterDeclarationKind | null | undefined;
    }): namedTypes.TSInterfaceDeclaration;
}
export interface TSParameterPropertyBuilder {
    (parameter: K.IdentifierKind | K.AssignmentPatternKind): namedTypes.TSParameterProperty;
    from(params: {
        accessibility?: "public" | "private" | "protected" | undefined;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        parameter: K.IdentifierKind | K.AssignmentPatternKind;
        readonly?: boolean;
    }): namedTypes.TSParameterProperty;
}
export interface OptionalMemberExpressionBuilder {
    (object: K.ExpressionKind, property: K.IdentifierKind | K.ExpressionKind, computed?: boolean, optional?: boolean): namedTypes.OptionalMemberExpression;
    from(params: {
        comments?: K.CommentKind[] | null;
        computed?: boolean;
        loc?: K.SourceLocationKind | null;
        object: K.ExpressionKind;
        optional?: boolean;
        property: K.IdentifierKind | K.ExpressionKind;
    }): namedTypes.OptionalMemberExpression;
}
export interface OptionalCallExpressionBuilder {
    (callee: K.ExpressionKind, argumentsParam: (K.ExpressionKind | K.SpreadElementKind)[], optional?: boolean): namedTypes.OptionalCallExpression;
    from(params: {
        arguments: (K.ExpressionKind | K.SpreadElementKind)[];
        callee: K.ExpressionKind;
        comments?: K.CommentKind[] | null;
        loc?: K.SourceLocationKind | null;
        optional?: boolean;
        typeArguments?: null | K.TypeParameterInstantiationKind;
    }): namedTypes.OptionalCallExpression;
}
export interface builders {
    file: FileBuilder;
    program: ProgramBuilder;
    identifier: IdentifierBuilder;
    blockStatement: BlockStatementBuilder;
    emptyStatement: EmptyStatementBuilder;
    expressionStatement: ExpressionStatementBuilder;
    ifStatement: IfStatementBuilder;
    labeledStatement: LabeledStatementBuilder;
    breakStatement: BreakStatementBuilder;
    continueStatement: ContinueStatementBuilder;
    withStatement: WithStatementBuilder;
    switchStatement: SwitchStatementBuilder;
    switchCase: SwitchCaseBuilder;
    returnStatement: ReturnStatementBuilder;
    throwStatement: ThrowStatementBuilder;
    tryStatement: TryStatementBuilder;
    catchClause: CatchClauseBuilder;
    whileStatement: WhileStatementBuilder;
    doWhileStatement: DoWhileStatementBuilder;
    forStatement: ForStatementBuilder;
    variableDeclaration: VariableDeclarationBuilder;
    forInStatement: ForInStatementBuilder;
    debuggerStatement: DebuggerStatementBuilder;
    functionDeclaration: FunctionDeclarationBuilder;
    functionExpression: FunctionExpressionBuilder;
    variableDeclarator: VariableDeclaratorBuilder;
    thisExpression: ThisExpressionBuilder;
    arrayExpression: ArrayExpressionBuilder;
    objectExpression: ObjectExpressionBuilder;
    property: PropertyBuilder;
    literal: LiteralBuilder;
    sequenceExpression: SequenceExpressionBuilder;
    unaryExpression: UnaryExpressionBuilder;
    binaryExpression: BinaryExpressionBuilder;
    assignmentExpression: AssignmentExpressionBuilder;
    memberExpression: MemberExpressionBuilder;
    updateExpression: UpdateExpressionBuilder;
    logicalExpression: LogicalExpressionBuilder;
    conditionalExpression: ConditionalExpressionBuilder;
    newExpression: NewExpressionBuilder;
    callExpression: CallExpressionBuilder;
    restElement: RestElementBuilder;
    typeAnnotation: TypeAnnotationBuilder;
    tsTypeAnnotation: TSTypeAnnotationBuilder;
    spreadElementPattern: SpreadElementPatternBuilder;
    arrowFunctionExpression: ArrowFunctionExpressionBuilder;
    forOfStatement: ForOfStatementBuilder;
    yieldExpression: YieldExpressionBuilder;
    generatorExpression: GeneratorExpressionBuilder;
    comprehensionBlock: ComprehensionBlockBuilder;
    comprehensionExpression: ComprehensionExpressionBuilder;
    objectProperty: ObjectPropertyBuilder;
    propertyPattern: PropertyPatternBuilder;
    objectPattern: ObjectPatternBuilder;
    arrayPattern: ArrayPatternBuilder;
    methodDefinition: MethodDefinitionBuilder;
    spreadElement: SpreadElementBuilder;
    assignmentPattern: AssignmentPatternBuilder;
    classPropertyDefinition: ClassPropertyDefinitionBuilder;
    classProperty: ClassPropertyBuilder;
    classBody: ClassBodyBuilder;
    classDeclaration: ClassDeclarationBuilder;
    classExpression: ClassExpressionBuilder;
    importSpecifier: ImportSpecifierBuilder;
    importNamespaceSpecifier: ImportNamespaceSpecifierBuilder;
    importDefaultSpecifier: ImportDefaultSpecifierBuilder;
    importDeclaration: ImportDeclarationBuilder;
    taggedTemplateExpression: TaggedTemplateExpressionBuilder;
    templateLiteral: TemplateLiteralBuilder;
    templateElement: TemplateElementBuilder;
    spreadProperty: SpreadPropertyBuilder;
    spreadPropertyPattern: SpreadPropertyPatternBuilder;
    awaitExpression: AwaitExpressionBuilder;
    importExpression: ImportExpressionBuilder;
    jsxAttribute: JSXAttributeBuilder;
    jsxIdentifier: JSXIdentifierBuilder;
    jsxNamespacedName: JSXNamespacedNameBuilder;
    jsxExpressionContainer: JSXExpressionContainerBuilder;
    jsxMemberExpression: JSXMemberExpressionBuilder;
    jsxSpreadAttribute: JSXSpreadAttributeBuilder;
    jsxElement: JSXElementBuilder;
    jsxOpeningElement: JSXOpeningElementBuilder;
    jsxClosingElement: JSXClosingElementBuilder;
    jsxFragment: JSXFragmentBuilder;
    jsxText: JSXTextBuilder;
    jsxOpeningFragment: JSXOpeningFragmentBuilder;
    jsxClosingFragment: JSXClosingFragmentBuilder;
    jsxEmptyExpression: JSXEmptyExpressionBuilder;
    jsxSpreadChild: JSXSpreadChildBuilder;
    typeParameterDeclaration: TypeParameterDeclarationBuilder;
    tsTypeParameterDeclaration: TSTypeParameterDeclarationBuilder;
    typeParameterInstantiation: TypeParameterInstantiationBuilder;
    tsTypeParameterInstantiation: TSTypeParameterInstantiationBuilder;
    classImplements: ClassImplementsBuilder;
    tsExpressionWithTypeArguments: TSExpressionWithTypeArgumentsBuilder;
    anyTypeAnnotation: AnyTypeAnnotationBuilder;
    emptyTypeAnnotation: EmptyTypeAnnotationBuilder;
    mixedTypeAnnotation: MixedTypeAnnotationBuilder;
    voidTypeAnnotation: VoidTypeAnnotationBuilder;
    numberTypeAnnotation: NumberTypeAnnotationBuilder;
    numberLiteralTypeAnnotation: NumberLiteralTypeAnnotationBuilder;
    numericLiteralTypeAnnotation: NumericLiteralTypeAnnotationBuilder;
    stringTypeAnnotation: StringTypeAnnotationBuilder;
    stringLiteralTypeAnnotation: StringLiteralTypeAnnotationBuilder;
    booleanTypeAnnotation: BooleanTypeAnnotationBuilder;
    booleanLiteralTypeAnnotation: BooleanLiteralTypeAnnotationBuilder;
    nullableTypeAnnotation: NullableTypeAnnotationBuilder;
    nullLiteralTypeAnnotation: NullLiteralTypeAnnotationBuilder;
    nullTypeAnnotation: NullTypeAnnotationBuilder;
    thisTypeAnnotation: ThisTypeAnnotationBuilder;
    existsTypeAnnotation: ExistsTypeAnnotationBuilder;
    existentialTypeParam: ExistentialTypeParamBuilder;
    functionTypeAnnotation: FunctionTypeAnnotationBuilder;
    functionTypeParam: FunctionTypeParamBuilder;
    arrayTypeAnnotation: ArrayTypeAnnotationBuilder;
    objectTypeAnnotation: ObjectTypeAnnotationBuilder;
    objectTypeProperty: ObjectTypePropertyBuilder;
    objectTypeSpreadProperty: ObjectTypeSpreadPropertyBuilder;
    objectTypeIndexer: ObjectTypeIndexerBuilder;
    objectTypeCallProperty: ObjectTypeCallPropertyBuilder;
    objectTypeInternalSlot: ObjectTypeInternalSlotBuilder;
    variance: VarianceBuilder;
    qualifiedTypeIdentifier: QualifiedTypeIdentifierBuilder;
    genericTypeAnnotation: GenericTypeAnnotationBuilder;
    memberTypeAnnotation: MemberTypeAnnotationBuilder;
    unionTypeAnnotation: UnionTypeAnnotationBuilder;
    intersectionTypeAnnotation: IntersectionTypeAnnotationBuilder;
    typeofTypeAnnotation: TypeofTypeAnnotationBuilder;
    typeParameter: TypeParameterBuilder;
    interfaceTypeAnnotation: InterfaceTypeAnnotationBuilder;
    interfaceExtends: InterfaceExtendsBuilder;
    interfaceDeclaration: InterfaceDeclarationBuilder;
    declareInterface: DeclareInterfaceBuilder;
    typeAlias: TypeAliasBuilder;
    opaqueType: OpaqueTypeBuilder;
    declareTypeAlias: DeclareTypeAliasBuilder;
    declareOpaqueType: DeclareOpaqueTypeBuilder;
    typeCastExpression: TypeCastExpressionBuilder;
    tupleTypeAnnotation: TupleTypeAnnotationBuilder;
    declareVariable: DeclareVariableBuilder;
    declareFunction: DeclareFunctionBuilder;
    declareClass: DeclareClassBuilder;
    declareModule: DeclareModuleBuilder;
    declareModuleExports: DeclareModuleExportsBuilder;
    declareExportDeclaration: DeclareExportDeclarationBuilder;
    exportSpecifier: ExportSpecifierBuilder;
    exportBatchSpecifier: ExportBatchSpecifierBuilder;
    declareExportAllDeclaration: DeclareExportAllDeclarationBuilder;
    inferredPredicate: InferredPredicateBuilder;
    declaredPredicate: DeclaredPredicateBuilder;
    exportDeclaration: ExportDeclarationBuilder;
    block: BlockBuilder;
    line: LineBuilder;
    noop: NoopBuilder;
    doExpression: DoExpressionBuilder;
    super: SuperBuilder;
    bindExpression: BindExpressionBuilder;
    decorator: DecoratorBuilder;
    metaProperty: MetaPropertyBuilder;
    parenthesizedExpression: ParenthesizedExpressionBuilder;
    exportDefaultDeclaration: ExportDefaultDeclarationBuilder;
    exportNamedDeclaration: ExportNamedDeclarationBuilder;
    exportNamespaceSpecifier: ExportNamespaceSpecifierBuilder;
    exportDefaultSpecifier: ExportDefaultSpecifierBuilder;
    exportAllDeclaration: ExportAllDeclarationBuilder;
    commentBlock: CommentBlockBuilder;
    commentLine: CommentLineBuilder;
    directive: DirectiveBuilder;
    directiveLiteral: DirectiveLiteralBuilder;
    interpreterDirective: InterpreterDirectiveBuilder;
    stringLiteral: StringLiteralBuilder;
    numericLiteral: NumericLiteralBuilder;
    bigIntLiteral: BigIntLiteralBuilder;
    nullLiteral: NullLiteralBuilder;
    booleanLiteral: BooleanLiteralBuilder;
    regExpLiteral: RegExpLiteralBuilder;
    objectMethod: ObjectMethodBuilder;
    classPrivateProperty: ClassPrivatePropertyBuilder;
    classMethod: ClassMethodBuilder;
    classPrivateMethod: ClassPrivateMethodBuilder;
    privateName: PrivateNameBuilder;
    restProperty: RestPropertyBuilder;
    forAwaitStatement: ForAwaitStatementBuilder;
    import: ImportBuilder;
    tsQualifiedName: TSQualifiedNameBuilder;
    tsTypeReference: TSTypeReferenceBuilder;
    tsAsExpression: TSAsExpressionBuilder;
    tsNonNullExpression: TSNonNullExpressionBuilder;
    tsAnyKeyword: TSAnyKeywordBuilder;
    tsBigIntKeyword: TSBigIntKeywordBuilder;
    tsBooleanKeyword: TSBooleanKeywordBuilder;
    tsNeverKeyword: TSNeverKeywordBuilder;
    tsNullKeyword: TSNullKeywordBuilder;
    tsNumberKeyword: TSNumberKeywordBuilder;
    tsObjectKeyword: TSObjectKeywordBuilder;
    tsStringKeyword: TSStringKeywordBuilder;
    tsSymbolKeyword: TSSymbolKeywordBuilder;
    tsUndefinedKeyword: TSUndefinedKeywordBuilder;
    tsUnknownKeyword: TSUnknownKeywordBuilder;
    tsVoidKeyword: TSVoidKeywordBuilder;
    tsThisType: TSThisTypeBuilder;
    tsArrayType: TSArrayTypeBuilder;
    tsLiteralType: TSLiteralTypeBuilder;
    tsUnionType: TSUnionTypeBuilder;
    tsIntersectionType: TSIntersectionTypeBuilder;
    tsConditionalType: TSConditionalTypeBuilder;
    tsInferType: TSInferTypeBuilder;
    tsTypeParameter: TSTypeParameterBuilder;
    tsParenthesizedType: TSParenthesizedTypeBuilder;
    tsFunctionType: TSFunctionTypeBuilder;
    tsConstructorType: TSConstructorTypeBuilder;
    tsDeclareFunction: TSDeclareFunctionBuilder;
    tsDeclareMethod: TSDeclareMethodBuilder;
    tsMappedType: TSMappedTypeBuilder;
    tsTupleType: TSTupleTypeBuilder;
    tsNamedTupleMember: TSNamedTupleMemberBuilder;
    tsRestType: TSRestTypeBuilder;
    tsOptionalType: TSOptionalTypeBuilder;
    tsIndexedAccessType: TSIndexedAccessTypeBuilder;
    tsTypeOperator: TSTypeOperatorBuilder;
    tsIndexSignature: TSIndexSignatureBuilder;
    tsPropertySignature: TSPropertySignatureBuilder;
    tsMethodSignature: TSMethodSignatureBuilder;
    tsTypePredicate: TSTypePredicateBuilder;
    tsCallSignatureDeclaration: TSCallSignatureDeclarationBuilder;
    tsConstructSignatureDeclaration: TSConstructSignatureDeclarationBuilder;
    tsEnumMember: TSEnumMemberBuilder;
    tsTypeQuery: TSTypeQueryBuilder;
    tsImportType: TSImportTypeBuilder;
    tsTypeLiteral: TSTypeLiteralBuilder;
    tsTypeAssertion: TSTypeAssertionBuilder;
    tsEnumDeclaration: TSEnumDeclarationBuilder;
    tsTypeAliasDeclaration: TSTypeAliasDeclarationBuilder;
    tsModuleBlock: TSModuleBlockBuilder;
    tsModuleDeclaration: TSModuleDeclarationBuilder;
    tsImportEqualsDeclaration: TSImportEqualsDeclarationBuilder;
    tsExternalModuleReference: TSExternalModuleReferenceBuilder;
    tsExportAssignment: TSExportAssignmentBuilder;
    tsNamespaceExportDeclaration: TSNamespaceExportDeclarationBuilder;
    tsInterfaceBody: TSInterfaceBodyBuilder;
    tsInterfaceDeclaration: TSInterfaceDeclarationBuilder;
    tsParameterProperty: TSParameterPropertyBuilder;
    optionalMemberExpression: OptionalMemberExpressionBuilder;
    optionalCallExpression: OptionalCallExpressionBuilder;
    [builderName: string]: any;
}
