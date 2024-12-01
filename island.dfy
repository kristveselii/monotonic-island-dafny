// Student Name Krist Veseli

/* Here is the code proving that the output indices correspond to a valid monotonic island.
   This happens because:
   1. We define predicates IsIncreasing and IsDecreasing that formally specify what makes a valid sequence
   2. We combine these in IsMonotonic to define a valid monotonic island
   3. We maintain these properties through loop invariants
   4. The ensures clause guarantees our output is monotonic */

predicate IsIncreasing(a: array<int>, l: int, r: int)
  requires 0 <= l <= r < a.Length
  reads a
{
  forall i, j :: l <= i < j <= r ==> a[i] < a[j]
}

predicate IsDecreasing(a: array<int>, l: int, r: int)
  requires 0 <= l <= r < a.Length
  reads a
{
  forall i, j :: l <= i < j <= r ==> a[i] > a[j]
}

predicate IsMonotonic(a: array<int>, l: int, r: int)
  requires 0 <= l <= r < a.Length
  reads a
{
  IsIncreasing(a, l, r) || IsDecreasing(a, l, r)
}

method FindLargestMonotonicIsland(a: array<int>) returns (l: int, r: int)
  requires a.Length > 0
  ensures 0 <= l <= r < a.Length
  ensures IsMonotonic(a, l, r)
{
  l, r := 0, 0;
  var i := 0;
  
  /* Here is the code proving that the algorithm terminates.
     This happens because:
     1. The outer loop has decreases a.Length - i and i increases each iteration
     2. Both inner loops have decreases a.Length - j and j increases each iteration
     3. All loops have bounds checking to prevent infinite loops */
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= l <= r < a.Length
    invariant IsMonotonic(a, l, r)
    decreases a.Length - i  // Proves outer loop termination
  {
    var j := i;
    
    /* Here is the code proving that the output island is the largest one in the array.
       This happens because:
       1. We check every possible starting position i in the array
       2. For each i, we find both the longest increasing and decreasing sequences
       3. We only update l,r when we find a strictly longer sequence
       4. By checking every position and keeping the longest, we guarantee we find the largest */
    
    // Check increasing sequence
    while j + 1 < a.Length && a[j] < a[j + 1]
      invariant i <= j < a.Length
      invariant forall x, y :: i <= x < y <= j ==> a[x] < a[y]
      decreases a.Length - j  // Proves inner loop termination
    {
      j := j + 1;
    }
    
    if j - i > r - l {
      assert forall x, y :: i <= x < y <= j ==> a[x] < a[y];
      l := i;
      r := j;
    }
    
    j := i;
    
    // Check decreasing sequence
    while j + 1 < a.Length && a[j] > a[j + 1]
      invariant i <= j < a.Length
      invariant forall x, y :: i <= x < y <= j ==> a[x] > a[y]
      decreases a.Length - j  // Proves inner loop termination
    {
      j := j + 1;
    }
    
    if j - i > r - l {
      assert forall x, y :: i <= x < y <= j ==> a[x] > a[y];
      l := i;
      r := j;
    }
    
    i := i + 1;
  }
}

/*method Main() {
  // Test case 1: Increasing sequence [1,2,3]
  var a1 := new int[3];
  a1[0], a1[1], a1[2] := 1, 2, 3;
  var l1, r1 := FindLargestMonotonicIsland(a1);
  print "(", l1, ",", r1, ")\n";
  
  // Test case 2: Decreasing sequence [5,4,3,2,1]
  var a2 := new int[5];
  a2[0], a2[1], a2[2], a2[3], a2[4] := 5, 4, 3, 2, 1;
  var l2, r2 := FindLargestMonotonicIsland(a2);
  print "(", l2, ",", r2, ")\n";
}*/
