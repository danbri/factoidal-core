// Plain recursion: calls, name lookups, small number arithmetic. 392,835 calls.
function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
print(fib(26));
