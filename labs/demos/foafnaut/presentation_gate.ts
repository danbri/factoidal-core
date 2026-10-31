// Visibility is OS transport state, not Lean scene state. A newly visible static
// scene needs repainting even if no input or simulation command marked it dirty.
export class PresentationGate {
  private wasReady=false;
  next(ready:boolean,dirty:boolean) {
    const pending=dirty || (ready && !this.wasReady);
    this.wasReady=ready;
    return {draw:ready&&pending,dirty:pending};
  }
}
