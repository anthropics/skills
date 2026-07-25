export class RPCData {
  constructor(
    public rpcid: string,
    public payload: string,
    public identifier: string = 'generic',
  ) {}

  toString(): string {
    return `GRPC(rpcid='${this.rpcid}', payload='${this.payload}', identifier='${this.identifier}')`;
  }

  serialize(): unknown[] {
    return [this.rpcid, this.payload, null, this.identifier];
  }
}

