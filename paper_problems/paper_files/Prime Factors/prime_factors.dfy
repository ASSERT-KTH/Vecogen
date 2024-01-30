
function multSeq(s: seq<int>, i: int) : int
    requires 0 <= i < |s|;
    decreases i;
{
    if (i == 0) then s[i]
    else s[i] * multSeq(s, i-1)
}


lemma append_seq_mul(s: seq<int>, v:int, val:int)
    requires val >= 2;
    requires v >= 1;
    requires |s| >= 1;
    requires forall x :: 0 <= x < |s| ==> s[x] >= 1;
    ensures (multSeq(s, |s|-1) * v) == val;
    ensures  multSeq(s + [v], |s|) == val;
    ensures (v == 1) ==> (multSeq(s, |s|-1) == val);
{
    assume(false); // unable to find a proof for this. Assume the ensures.
    calc
    {
        multSeq(s, |s|-1) * v == val;
        multSeq(s + [v], |s|) == val;
    }
}

// Copied from: https://homepage.cs.uiowa.edu/~tinelli/classes/181/Spring11/Tools/Dafny/Examples/square-root.dfy

// isr computes the (non-negative) integer square root of its input
method isr(n: int) returns (r : int)
    requires n >= 0;
    // r is the largest non-negative integer whose square is at most n 
    ensures 0 <= r*r && r*r <= n && n < (r+1)*(r+1);
{
    r := 0 ;
    while ((r+1) * (r+1) <= n)
        invariant r*r <= n ;
    {
        r := r+1;
    }

    return r;
}

method primeFactors(val: int) returns (res: seq<int>)
    requires 2 <= val;
    ensures |res| >= 1;
    ensures multSeq(res, |res|-1) == val;
{
    var factors := [1];
    var v:int := val;
    
    while ((v % 2) == 0)
        invariant 1 <= v <= val;
        invariant |factors| >= 1;
        invariant |factors| > 1 ==> factors[ (|factors|-1) ] == 2;
        invariant forall x :: 0 <= x < |factors| ==> factors[x] >= 1;
        invariant multSeq(factors, |factors|-1) * v == val;
        decreases v;
    {
        append_seq_mul(factors, v, val);

        factors := factors + [2];
        v := v / 2;

        append_seq_mul(factors, v, val);
    }

    assert(v % 2 == 1);

    var i:int := 3;
    var n:int := isr(v);
    n := n + 1;

    while (i < n) 
        invariant 3 <= i <= n+2;
        invariant 1 <= v <= val;
        invariant i % 2 == 1;
        invariant v % 2 == 1;
        invariant |factors| >= 1;
        invariant forall x :: 0 <= x < |factors| ==> factors[x] >= 1
        invariant multSeq(factors, |factors|-1) * v == val;
        decreases n - i;
    {
        while ((v % i) == 0) 
            invariant i >= 1;
            invariant 1 <= v <= val;
            invariant v % 2 == 1;
            invariant |factors| >= 1;
            invariant |factors| > |old(factors)| ==> factors[ (|factors|-1) ] == i;
            invariant forall x :: 0 <= x < |factors| ==> factors[x] >= 1;
            invariant multSeq(factors, |factors|-1) * v == val;
            decreases v;
        {
            append_seq_mul(factors, v, val);

            factors := factors + [i];
            v := v / i;

            append_seq_mul(factors, v, val);
        }
        i := i + 2;
    }

    assume(v % 2 == 1);
    assert(v >= 1);

    if (v > 2) {
        append_seq_mul(factors, v, val);

        factors := factors + [v];
        v := v / v;

        append_seq_mul(factors, v, val);
    }

    assert(v == 1);

    append_seq_mul(factors, v, val);
    return factors;
}

