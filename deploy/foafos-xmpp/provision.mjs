// Makes the accounts and the state key on the laptop, for `fly secrets import`.
// Usage: node provision.mjs NEW_PRIVATE_DIRECTORY   (outside the build context)
// It refuses to reuse a directory, and it prints no secret.
import { mkdir, writeFile } from 'node:fs/promises'
import { join, resolve } from 'node:path'
import { randomBytes } from 'node:crypto'

const [directory] = process.argv.slice(2)
if (!directory) throw new Error('usage: node provision.mjs NEW_PRIVATE_DIRECTORY')
const dir = resolve(directory)
process.umask(0o077)
await mkdir(dir, { mode: 0o700 })
const names = ['me', 'foafos', 'foafbot', 'test1', 'test2']
const lines = names.map((name) => `${name}:${randomBytes(24).toString('base64url')}\n`).join('')
await writeFile(join(dir, 'accounts'), lines, { mode: 0o600, flag: 'wx' })
await writeFile(join(dir, 'fly-secrets.env'),
  `XMPP_ACCOUNTS_B64=${Buffer.from(lines).toString('base64')}\nXMPP_STATE_KEY=${randomBytes(32).toString('hex')}\n`,
  { mode: 0o600, flag: 'wx' })
console.log(`made ${names.length} accounts in ${join(dir, 'accounts')}`)
