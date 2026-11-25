# Measure cold graphics preparation

In the [24-page Linux survey](https://github.com/danbri/factoidal-builds/actions/runs/45616968447), graphics preparation for the first page on each runner took 9.88 to 10.29 seconds. The next 20 launches usually spent around 1.4 seconds there. The current native frame trace shows the combined time but leaves out pipeline compilation and asynchronous validation from its detailed steps. Its pipeline count also excludes the layers used by default.

Record the shader module creation, compilation information query, asynchronous pipeline creation, and validation waits in the existing chrome, page, and composite draw steps. Count pipelines built in both the single and layered paths. These measures identify time spent inside the host calls. They do not attribute it to any specific compiler or driver component.

The experiment keeps the draw order, commands, and pipeline cache unchanged. Compare fresh and reused shader caches while checking frame pixels and input on the same native renderer. Tracks [issue 952](https://github.com/danbri/factoidal-core/issues/952).
