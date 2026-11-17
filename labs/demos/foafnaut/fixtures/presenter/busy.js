// Original test workload. Bounded work; no DOM mutation or renderer-specific page API.
// Repeated turns allow the timing harness to verify overlap after the first frame.
(function () {
  var turns = 0;
  var total = 0;
  function burn() {
    var value = 1;
    for (var i = 0; i < 200000; i++) value = (value * 17 + i) % 65521;
    total += value;
    turns++;
    if (turns < 12) setTimeout(burn, 100);
    else console.log("presenter busy fixture finished " + total);
  }
  setTimeout(burn, 1000);
})();
