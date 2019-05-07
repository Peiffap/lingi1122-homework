
function sum(a: seq<int>, i: int, j: int): int
    requires 0 <= i <= j < |a|
    decreases j - i
{
    if i == j then a[j] else sum(a, i, j-1) + a[j]
}

// This is the only allowed `function method`.
// Everything else must be either `function` or `method`.
function method max(x: int, y: int): int
    ensures max(x, y) == x || max(x, y) == y
    ensures max(x, y) >= x && max(x, y) >= y
{
    if x > y then x else y
}

// Three different algorithms to solve the maximum subarray problem.
// The maximum subarray problem is the task of finding a contiguous,
// non-empty subarray with the largest sum.

// An O(n³) implementation, to warm up.

/*
 * For the three algorithms, the preconditions and postconditions are the same.
 *
 * @Pre: as the statement says that the returned maxSum is a non-empty interval,
 * we can require that the sequence `a` is non-empty.
 *
 * @Post: maxSum is greater than or equal to any sum of subsequences of the sequence `a`
* and, maxSum is the sum of a particular subsequence of the sequence `a`.
 */

method maxsumDumb(a: seq<int>) returns (maxSum: int)
    requires |a| > 0
    ensures exists ii, jj | 0 <= ii <= jj < |a| :: maxSum == sum(a, ii, jj)
    ensures forall ii, jj | 0 <= ii <= jj < |a| :: maxSum >= sum(a, ii, jj)
{
    var i := 0;
    maxSum := a[0];
    // We help Danfy here to start.
    assert sum(a, 0, 0) == maxSum;

    while i < |a| 
    // i goes from 0 to |a|, causing the while loop to stop.
    invariant 0 <= i <= |a|
    // We went so far to the start index of the subsequence i.
    // We have checked the sum of all the subsequences starting by indexes up to i.
    invariant exists ii, jj | 0 <= ii <= i && ii <= jj < |a| :: maxSum == sum(a, ii, jj)
    // maxSum is the maximum of all the subsequences checked so far.
    invariant forall ii, jj | 0 <= ii < i && ii <= jj < |a| :: maxSum >= sum(a, ii, jj)

    {
        var j := i;

        while j < |a|
        // Invariant for the values of j.
        invariant i <= j <= |a|
        // The next two invariants are the same as for the outer loop.
        invariant exists ii, jj | 0 <= ii <= i && ii <= jj < |a| :: maxSum == sum(a, ii, jj)
        invariant forall ii, jj | 0 <= ii < i && ii <= jj < |a| :: maxSum >= sum(a, ii, jj)
        // This invariant says that for the current value of i, we have checked 
        // all the subsequences from i to j, not included.
        invariant forall jj | i <= jj < j :: maxSum >= sum(a, i, jj)
        {
            var k := i;
            var currentSum := a[i];

            while k < j
            // Invariant for the values of k.
            invariant i <= k <= j
            // currentSum is currently the sum of all the values from i to k.
            invariant currentSum == sum(a, i, k)
            {
                k := k + 1;
                currentSum := currentSum + a[k];
            }

            maxSum := max(currentSum, maxSum);
            j := j + 1;
        }
        i := i + 1;
    }
}

// An O(n²) implementation, slightly improved over the previous one.
method maxsumImproved(a: seq<int>) returns (maxSum: int)
    requires |a| > 0
    ensures exists ii, jj | 0 <= ii <= jj < |a| :: maxSum == sum(a, ii, jj)
    ensures forall ii, jj | 0 <= ii <= jj < |a| :: maxSum >= sum(a, ii, jj)
{
    var i := 0;
    maxSum := a[0];
    assert maxSum == sum(a, 0, 0);

    while i < |a| 
    invariant 0 <= i <= |a|
    invariant exists ii, jj | 0 <= ii <= i && ii <= jj < |a| :: maxSum == sum(a, ii, jj)
    invariant forall ii, jj | 0 <= ii < i && ii <= jj < |a| :: maxSum >= sum(a, ii, jj)

    {
        var j := i;
        var currentSum := a[i];
        assert currentSum == sum(a, i, i);
        maxSum := max(currentSum, maxSum);

        while j + 1 < |a|
        invariant i <= j < |a| // Could do <= |a|-1.
        invariant exists ii, jj | 0 <= ii <= i && ii <= jj < |a| :: maxSum == sum(a, ii, jj)
        invariant forall ii, jj | 0 <= ii <  i && ii <= jj < |a| :: maxSum >= sum(a, ii, jj)
        invariant currentSum == sum(a, i, j)
        invariant forall jj | i <= jj < j+1 :: maxSum >= sum(a, i, jj)
        
        {
            j := j + 1;
            currentSum := currentSum + a[j];
            assert currentSum == sum(a, i, j);
            maxSum := max(currentSum, maxSum);
        }

        i := i + 1;
    }
}

// `s` is the maximal sum of any subarray of `a` ending with cell `n` included.
// See https://en.wikipedia.org/wiki/Maximum_subarray_problem#Kadane.27s_algorithm
predicate isMaxSumAt(a: seq<int>, s: int, n: int)
    requires 0 <= n < |a|
{
    forall i | 0 <= i <= n :: s >= sum(a, i, n)
}

// An optimal, O(n) implementation. This one is harder to prove.
// You may wish to use the above `isMaxSumAt` predicate.
//
// Dafny may need some carefully crafted asserts to prove this one.
// Edit : Using the Ghost function provided on Moodle by Guillaume Maudoux which is simpler to prove.
method maxsumLinearGhost(a: seq<int>) returns (maxSum: int)
    requires |a| > 0
    ensures exists ii, jj | 0 <= ii <= jj < |a| :: maxSum == sum(a, ii, jj)
    ensures forall ii, jj | 0 <= ii <= jj < |a| :: maxSum >= sum(a, ii, jj)
{
    // Ghost vars are not part of the code, and will be removed during compilation.
    // They can however be used as if they were normal variables for specification purposes.
    ghost var i := 0;
    var j := 0;
    var currentSum := a[0];
    
    maxSum := currentSum;
    
    while j + 1 < |a|
    // Invariant for the values of j: from 0 to |a| excluded, because the while loop
    // breaks when j+1 == |a| ==> j < |a|.
    invariant 0 <= j < |a|
    // Invariant for the values of i: from 0 to j included, because i is the lower bound of the 
    // current maximum subsequence ending at index j.
    invariant 0 <= i <= j
    // Either i is equal to j (the maximum subsequence ending at j is only the value at index j)
    // or i is still the lower bound of the maximum subsequence ending at j-1.
    // In either case, currentSum is equal to the sum of values from i to j included.
    invariant currentSum == sum(a, i, j)
    // Also, we ask currentSum to be the maximum subsequence sum, for all subsequences ending at index j.
    invariant isMaxSumAt(a, currentSum, j)
    invariant exists ii, jj | 0 <= ii <= jj <= j :: maxSum == sum(a, ii, jj)
    invariant forall ii, jj | 0 <= ii <= jj <= j :: maxSum >= sum(a, ii, jj)
    decreases  |a| - (j + 1)
    { 
        
        j := j + 1;

        if (currentSum < 0) {
            i := j;
            currentSum := a[j];
            
            
        } else {
            currentSum := currentSum + a[j];
        }
        

        maxSum := max(currentSum, maxSum);
        
    }
}
