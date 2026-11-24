# Match replay documents to Chrome references

The frozen BBC News capture at 1280 px used a 937,534-byte UK document from the initial plain fetch. Chrome loaded a separate international edition at bbc.com. The Foafnaut and Chrome screenshots showed different headlines, navigation and images. Their image similarity cannot establish layout parity.

Add an explicit Chrome reference mode to the snapshot tool. It uses the main frame and loader's Document response and its recorded HTTP redirects, preserving the original URL for the replay. Responses from embedded frames cannot replace the main document. If the captured HTTP chain or response body is incomplete, capture fails instead of pairing two different documents. Record the reference document URL in the manifest. The default capture continues to collect the Foafnaut host's fetch variant for browser compatibility work.

The browser-backed fixture serves different documents by user agent and checks the redirect, the reference URL, the HTML and cookie stripping. The fixed public BBC capture also needs review for resources the two browsers request differently and for differences caused by scripts.

Related to [desktop acceptance](https://github.com/danbri/factoidal-core/issues/712) and [BBC News](https://github.com/danbri/factoidal-core/issues/833).
