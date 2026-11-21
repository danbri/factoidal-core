# Real pages as browser acceptance checks

Use the released desktop browser at its default settings alongside Chrome at the same CSS viewport. Report the visible result and the interaction result. Use focused HTML, CSS layout and JavaScript WPT tests to identify and verify the underlying platform behaviour.

- [Wikipedia: World Wide Web](https://en.wikipedia.org/wiki/World_Wide_Web). Compare the heading, body text, search and top navigation. The desktop had a 200% default while the survey forced 100%, hiding the default behaviour. Set the desktop default and reset to 100% at the backing scale. Preserve saved size preferences.
- [GOV.UK](https://www.gov.uk/). Check the search form and the icons on the popular links, as well as the hero layout.
- [FrogFind](https://frogfind.com/). Check whether the home page loads, whether its search field takes focus and text, and whether submission opens results. A verification interstitial on the live site calls for a separate local form fixture.

The browser shell currently paints 5-by-7 bitmap glyphs. Address text needs an outline font and a common advance for paint, caret, selection and pointer hit testing. Keep a browser screenshot as the visible acceptance check.
