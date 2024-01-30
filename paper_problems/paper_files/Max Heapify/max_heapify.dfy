
predicate maxHeaped(a: array<int>)
    reads a;
{
    forall x :: (0 <= x < a.Length) ==> (
        ((x*2 + 1 < a.Length) ==> (a[x] >= a[x*2 + 1])) && 
        ((x*2 + 2 < a.Length) ==> (a[x] >= a[x*2 + 2]))
    )
}

method maxHeapify(arr: array<int>)
    modifies arr;
    requires arr.Length > 0;
    ensures multiset(arr[..]) == multiset(old(arr[..]));
    ensures maxHeaped(arr);
{
    var i := 0;
    while (i < arr.Length)
        invariant 0 <= i <= arr.Length;
        invariant multiset(arr[..]) == multiset(old(arr[..]));
        invariant (0 <= i-1 < arr.Length) ==> (  // look after a sift.
            ((i*2 + 1 < arr.Length) ==> (arr[i-1] >= arr[(i-1)*2 + 1])) && 
            ((i*2 + 2 < arr.Length) ==> (arr[i-1] >= arr[(i-1)*2 + 2]))
        );
        decreases arr.Length - i;
    {
        var left := 2 * i + 1;
        var right := 2 * i + 2;

        var largest:int;
        if (left < arr.Length && arr[left] > arr[i]) {
            largest := left;
        } else {
            largest := i;
        }

        if (right < arr.Length && arr[right] > arr[largest]) {
            largest := right;
        }

        if (largest != i) {
            arr[i], arr[largest] := arr[largest], arr[i];
            maxHeapify(arr);
        }

        i := i + 1;
    }
}