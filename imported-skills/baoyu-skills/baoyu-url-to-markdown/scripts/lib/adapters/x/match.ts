export function isXHost(hostname: string): boolean {
  return ["x.com", "www.x.com", "twitter.com", "www.twitter.com"].includes(hostname);
}

export function extractStatusId(url: URL): string | undefined {
  const match = url.pathname.match(/\/(?:status|article)\/(\d+)/);
  return match?.[1];
}

