# Measure cold graphics preparation

In the [24-page Linux survey](https://github.com/danbri/factoidal-builds/actions/runs/45616968447), graphics preparation for the first page on each runner took 9.88 to 10.29 seconds. The next 20 launches usually spent around 1.4 seconds there. The current native frame trace shows the combined time but leaves out pipeline compilation and asynchronous validation from its detailed steps. Its pipeline count also excludes the layers used by default.

Record the shader module creation, compilation information query, asynchronous pipeline creation, and validation waits in the existing chrome, page, and composite draw steps. Count pipelines built in both the single and layered paths. These measures identify time spent inside the host calls. They do not attribute it to any specific compiler or driver component.

The experiment keeps the draw order, commands, and pipeline cache unchanged. Compare fresh and reused shader caches while checking frame pixels and input on the same native renderer. Tracks [issue 952](https://github.com/danbri/factoidal-core/issues/952).


The [controlled mobile Wikipedia replay](https://github.com/danbri/factoidal-builds/actions/runs/45621104102) compared two fresh caches and their immediate reuse. The graphics phase took 87.71 and 86.88 seconds with empty caches and 1.59 and 1.56 seconds on the repeat launches. All four first screenshots had the same SHA-256 and all four responded to wheel input. The instrumented pipeline and validation calls accounted for less than one second per launch.

The next replay records layer drawing, plan resolution, texture and binding setup, buffer uploads, and surface configuration, acquisition and presentation. The total layer timing contains the per-layer measures.


The [expanded replay](https://github.com/danbri/factoidal-builds/actions/runs/45622247369) found that the page layer resource phase took 8.61 and 8.35 seconds with fresh caches and 27 and 29 milliseconds on reuse. Surface configuration was about 0.34 seconds in every arm, and buffer upload was under 4 milliseconds. All screenshots and visible scroll checks matched in the four arms. The next trace separates texture allocation, buffer allocation, binding layout lookup and bind-group creation.
