// The worker dials only IP literals, so it never asks a resolver for a name. This decides what
// an IP literal is. IPv4: four decimal octets 0-255, no leading zeros (a leading zero is read
// as octal by some resolvers). IPv6: what the WHATWG URL parser accepts inside brackets, and only
// when it does not change the text except for case and zero compression (no zone id, no IPv4
// tail with leading zeros).
const IPV4 = /^(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)(\.(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)){3}$/;

export function isIpLiteral(s: string): boolean {
  if (IPV4.test(s)) return true;
  if (!s.includes(":") || !/^[0-9a-fA-F:.]+$/.test(s)) return false;
  try {
    // The URL parser refuses anything that is not a valid IPv6 address.
    new URL(`http://[${s}]/`);
    return true;
  } catch {
    return false;
  }
}
