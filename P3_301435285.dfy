method Find(a: array<int>, v: int) returns (index: int)
  ensures index >= 0 ==> index < a.Length && a[index] == v
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != v
{
  var i: int := 0;

  while i < a.Length
    // We need to make sure that index is not out of bound
    invariant 0 <= i <= a.Length

    // For the part that has been traversed, make sure that there is no number we are looking for.
    invariant forall j :: 0 <= j < i ==> a[j] != v
  {
    if a[i] == v {
      return i;
    }
    i := i + 1;
  }
  return -1;
}

method Sum(n: int) returns (sum: int)
  requires n > 0
  ensures sum == 5 * n * (n + 1)
{
  sum := 0;
  var i: int := n;

  while i > 0
    invariant 0 <= i <= n
    // The sum in the end is 5 * n * (n + 1), the value of the unprocessed part is 5 * i * (i + 1), the difference is the current sum.
    invariant sum == 5 * (n * (n + 1) - i * (i + 1))
  {
    var k: int := 0;
    var j: int := i;

    while j > 0
      invariant 0 <= j <= i
      // Make sure k for each iteration is equal to 10 * (i - j), in the end k is equal to 10i.
      invariant k == 10 * (i - j)
    {
      k := k + 10;
      j := j - 1;
    }

    sum := sum + k;
    i := i - 1;
  }
}

method ArrayMin(a: array<int>) returns (min: int)
  // Precondition is this array must not an empty array
  requires a.Length > 0

  // Make sure the return min is the minimum value in the array
  ensures forall i :: 0 <= i < a.Length ==> min <= a[i]

  // Make sure this min is exists in the array.
  ensures exists j :: 0 <= j < a.Length && min == a[j]
{
  // Let min equal to first element at first
  min := a[0];

  // Index variable
  var i: int:= 1;

  // Using while loop to find the minimum value
  while i < a.Length
    // Make sure index is not out of bound
    invariant 1 <= i <= a.Length

    // For the elements that have been traversed, ensure that min is the smallest one
    invariant forall k :: 0 <= k < i ==> min <= a[k]

    // Make sure min exists in the array
    invariant exists j :: 0 <= j < i && min == a[j]
  {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
}

method SortCoins(a: array<bool>)
    // This method need to modify array a, so we must add this line
    modifies a

    // True represents front, False represents back. If j > i, then a[j] is True, which means a[i] must be True. Conversely, if a[i] is True, a[j] may not be.
    ensures forall i, j :: 0 <= i <= j < a.Length ==> a[j] ==> a[i]

    // This is used to make sure elements in the array remains the same
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    // If the length of array is 1 / 0, no need to do anything
    if a.Length <= 1 {
        return;
    }
    
    // Two pointers one start from the beginning the other start from the end to traverse and modify the array.
    var i: int := 0;
    var j: int := a.Length - 1;

    while i < j
        // Make sure not out of bound
        invariant 0 <= i <= a.Length
        invariant 0 <= j < a.Length

        // This must be j + 1, like: if i is 2, j is 3 and a[i] == false a[j] == true, then i = 3 j = 2.
        invariant i <= j + 1

        // All element before i is true (front)
        invariant forall k :: 0 <= k < i ==> a[k]

        // All element after i is false (back)
        invariant forall k :: j < k < a.Length ==> !a[k]

        // Make sure all Ture come before any False
        invariant forall p, q :: 0 <= p < i && j < q < a.Length ==> a[q] ==> a[p]

        // Make sure elements in the array remains the same
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if a[i] {
            i := i + 1;
        } else if !a[j] {
            j := j - 1;
        } else {
            var temp := a[i];
            a[i] := a[j];
            a[j] := temp;
            i := i + 1;
            j := j - 1;
        }
    }
}