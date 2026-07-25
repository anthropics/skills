export class Gem {
  constructor(
    public id: string,
    public name: string,
    public description: string | null,
    public prompt: string | null,
    public predefined: boolean,
  ) {}

  toString(): string {
    return `Gem(id='${this.id}', name='${this.name}', description='${this.description}', prompt='${this.prompt}', predefined=${this.predefined})`;
  }
}

export class GemJar implements Iterable<Gem> {
  private m = new Map<string, Gem>();

  constructor(entries?: Iterable<[string, Gem]>) {
    if (entries) for (const [id, gem] of entries) this.m.set(id, gem);
  }

  [Symbol.iterator](): Iterator<Gem> {
    return this.m.values();
  }

  entries(): IterableIterator<[string, Gem]> {
    return this.m.entries();
  }

  values(): IterableIterator<Gem> {
    return this.m.values();
  }

  has(id: string): boolean {
    return this.m.has(id);
  }

  set(id: string, gem: Gem): this {
    this.m.set(id, gem);
    return this;
  }

  get(id?: string | null, name?: string | null, def: Gem | null = null): Gem | null {
    if (id == null && name == null) {
      throw new Error('At least one of gem id or name must be provided.');
    }

    if (id != null) {
      const g = this.m.get(id) ?? null;
      if (!g) return def;
      if (name != null) return g.name === name ? g : def;
      return g;
    }

    if (name != null) {
      for (const g of this.m.values()) {
        if (g.name === name) return g;
      }
      return def;
    }

    return def;
  }

  filter(predefined: boolean | null = null, name: string | null = null): GemJar {
    const out: [string, Gem][] = [];
    for (const [id, gem] of this.m.entries()) {
      if (predefined != null && gem.predefined !== predefined) continue;
      if (name != null && gem.name !== name) continue;
      out.push([id, gem]);
    }
    return new GemJar(out);
  }
}

