# Video posters

Use the existing document image inventory and decoder for a video's nonempty
`poster` URL. The request is resolved against the document URL and shares the
ordinary image storage and request limits. The video uses the existing replaced
image layout, including intrinsic aspect ratio and authored object fit and position.
The user-agent default for a video is contain.

The full raster-enabled CSS run exposed 45 video-poster cases that used to pass
before the raster reference was painted. In the pinned comparison, exercise all
object-fit and object-position poster cases on the same native renderer. The
end-to-end Lean guards exercise letterboxing, an author override, and the resolved
image key while excluding the media source from image discovery.

This covers static posters. Media playback, lazy poster lifecycle and dynamic poster
events remain separate. [HTML video](https://html.spec.whatwg.org/multipage/media.html#the-video-element)
and [video rendering](https://html.spec.whatwg.org/multipage/rendering.html#video-object-fit).
