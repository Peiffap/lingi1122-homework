method find_sum(a: seq<int>, s: int) returns (found: bool, i: int, j: int)
requires sorted(a)
ensures found ==> (0 <= i <= j < |a| && a[i] + a[j] == s)
ensures !found <==> (forall m, n | 0 <= m <= n < |a| :: a[m] + a[n] != s)
{
  i, j := 0, |a| - 1;
  while i <= j
  invariant 0 <= i <= j+1 <= |a|
  invariant forall p, x | 0 <= p < i && 0 <= x < |a| :: a[p] + a[x] != s
  invariant forall q, x | j < q < |a| && 0 <= x < |a| :: a[x] + a[q] != s
  decreases j - i + 1
  {
    var m;
    m := a[i] + a[j];
    if m > s {
      j := j - 1;
    } else if m < s {
      i := i + 1;
    } else {
      found := true;
      return;
    }
  }
  found := false;
}
predicate sorted(a: seq<int>)
{
  forall k, l | 0 <= k <= l < |a| :: a[k] <= a[l]
}
