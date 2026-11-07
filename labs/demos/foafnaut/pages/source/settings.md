# Settings

## Theme

- [NeXT grey](foafnaut:theme/next)
- [Arcade night](foafnaut:theme/arcade)

## Text size

- [Small](foafnaut:zoom/100)
- [Medium](foafnaut:zoom/125)
- [Large](foafnaut:zoom/150)
- [Huge](foafnaut:zoom/200)

## Page scripts

The engine that runs the scripts of a page. The chrome shows which one ran, or why none did.
A new setting applies to the pages you open next.

- [QuickJS-NG](foafnaut:scripts/quickjs) (the default)
- [VerifiedJS](foafnaut:scripts/verifiedjs): it can not run page scripts yet, so a page says why ([issue 1252](https://github.com/danbri/factoidal/issues/1252))
- [None](foafnaut:scripts/none)

## The address bar

Type a URL, or words to search, or a command.

- :back and :forward
- :reload
- :home
- :graph opens the interactive FOAF graph
- :source shows this page's source
- :new and :close
- :zoom 150
- :theme arcade
- :open https://example.org opens your system browser

Settings last until the window closes. Saving them is not built yet.
