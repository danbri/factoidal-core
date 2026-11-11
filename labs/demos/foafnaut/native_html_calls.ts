// The engine methods a caller may run in the worker. Its own module, with no worker code in it, so
// that the worker and its client share one list: two copies drifted, and the window lost
// printLayout once and encodingChoices later.
export const REMOTE_CALLS=["xmlStylesheet","xslt","inspect","fontRequests","graphStart","graphEvent","graphPage","sourcePage","wasmPage","sparqlPage","selectedText","findInPage","aboutPage","engineBuild","decodeDocument","encodingSetting","encodingChoices","compile","compileLayers","printLayout","imageInfo","imageLoad","imageDrop","frameWork","requestBytes","scriptInfo","scriptLoad","scriptSession","nodeAt","pointerAt","scriptPlan","scriptSetting","scriptChoices","fontFaces","webFontLoad"] as const;
export type RemoteCall=typeof REMOTE_CALLS[number];
