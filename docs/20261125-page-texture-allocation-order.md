# Allocate the page layer before the chrome submission

The fourth timing run measured 82.65 and 87.79 seconds inside the page layer texture allocation on stock lavapipe with fresh shader caches. Cache reuse reduced that call to about 52–54 milliseconds. Render plan and buffer timing were small in both arms. The first painted frame and wheel response were checked on the exact same frozen mobile Wikipedia page.

Move page texture allocation before the first chrome submission when the page needs its initial texture. The plan still checks the requested size before the native call. Chrome and page draw submissions retain their usual order. Compare against the instrumented parent with fresh caches and check whether the latency disappears or shifts to another call. [Timing artifact](https://github.com/danbri/factoidal-builds/actions/runs/45623412497/artifacts/15027906328)
