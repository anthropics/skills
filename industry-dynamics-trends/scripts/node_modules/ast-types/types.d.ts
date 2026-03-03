export declare type Fork = {
    use<T>(plugin: Plugin<T>): T;
};
export declare type Plugin<T> = (fork: Fork) => T;
export declare type Def = Plugin<void>;
export declare type Omit<T, K> = Pick<T, Exclude<keyof T, K>>;
