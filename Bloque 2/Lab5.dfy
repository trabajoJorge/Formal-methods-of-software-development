predicate sorted (s:seq<nat>)
{
    if |s|<=1 then true 
    else s[0]<=s[1] && sorted(s[1..])
}

method insert2 (x:nat, s:seq<nat>) returns (r:seq<nat>,ghost fr:nat)
    requires sorted(s)
    ensures sorted(r)

    ensures |r| == |s| + 1
    ensures fr == r[0]
    ensures fr == x || (s != [] && fr == s[0])
{
    if s == [] {
        r, fr:=[x], x;
    }
    else if x <= s[0] {
        r, fr:= [x]+s, x;
    }
    else{
        var aux;
        ghost var faux;
        aux, faux:= insert2(x, s[1..]);

        assert |aux| == |s[1..]| + 1;
        assert faux == aux[0];
        assert faux == aux[0] || (s != [] && faux == s[0]);

        r, fr:= [s[0]]+aux, s[0];

        assert |[s[0]]+aux| == |([s[0]]+s[1..])| + 1;
        assert |r| == |s| + 1;
        assert fr == r[0];
        assert fr == x || (s != [] && fr == s[0]);
    }
}

method insert3 (x:nat, s:seq<nat>) returns (r:seq<nat>,ghost fr:nat)
requires sorted(s)
ensures sorted(r)
ensures multiset(r) == multiset(s) + multiset{x}
//GHOST
ensures fr == r[0]
ensures fr == x || (s != [] && fr == s[0]);
{
    if s == [] {
        r, fr := [x], x;
    }
    else if x<=s[0]{
        r, fr := [x]+s, x;
    }
    else{
        var aux;
        ghost var faux;
        aux, faux:= insert3(x, s[1..]);

        calc == {
            multiset([s[0]]+aux);
            multiset{s[0]} + multiset(aux) ;
            multiset{s[0]} + multiset(s[1..]) + multiset{x};
            {
                assert [s[0]] + s[1..] == s;
            }
            multiset(s) + multiset{x};
        }
        assert multiset([s[0]]+aux) == multiset(s) + multiset{x}; // A demostrar
        r, fr:= [s[0]]+aux, s[0];
        assert multiset(r) == multiset(s) + multiset{x};
    }
}


method insert (x:nat, s:seq<nat>) returns (r:seq<nat>)
requires sorted(s)
ensures sorted(r)
ensures multiset(r) == multiset(s) + multiset{x}
{
    ghost var fr;
    r, fr:= insert3(x,s);
}

// TODO: Para sacar nota
method insert_It (x:nat, s:seq<nat>) returns (r:seq<nat>)
requires sorted(s)
ensures sorted(r)
ensures multiset(r) == multiset(s) + multiset{x}
{
    var left:seq<nat>,right := [],s;
    while right != [] && right[0] < x
        invariant left + right == s
        invariant left == [] || right == [] || left[|left|-1] <= right[0];
        invariant sorted(left)
        invariant sorted(right)
        invariant forall i :: 0 <= i < |left| ==> left[i] < x 
        decreases right
    {
        assert left == [] || left[|left|-1] <= right[0];
        sorted_Lemma (left, [right[0]]); 
        left,right := left+[right[0]],right[1..];
        assert sorted(left);
    }
    assert sorted(left) && sorted(right) && !(right != [] && right[0] < x) && (left == [] || left[|left|-1] < x);
    sorted_Lemma(left, [x]);
    assert sorted (left+[x]);
    sorted_Lemma([x], right);
    assert sorted ([x]+right);
    sorted_Lemma(left+[x], right);
    sorted_Lemma(left, [x]+right);
    assert sorted(left+[x]+right);
    calc{
        multiset(left+[x]+right);
        multiset(left+right)+multiset{x};
        {
                assert left+right== s;
        }
        multiset(s)+multiset{x};
    }
    assert multiset(left+[x]+right) == multiset(s)+multiset{x};
    r:= left+[x]+right;
    assert sorted(r);
    assert multiset(r) == multiset(s)+multiset{x};
}


lemma sorted_Lemma (s1:seq<nat>, s2:seq<nat>)
requires sorted(s1) && sorted(s2) && (s1==[] || s2==[] || s1[|s1|-1] <= s2[0]) 
ensures sorted(s1+s2)
{
    if s1==[]{
        assert s1+s2 == s2;
        assert sorted(s2);
    }
    else{
        sorted_Lemma(s1[1..], s2);
        assert sorted(s1[1..]+s2);
        assert s1[1..] == [] || s1[0]<=s1[1];
        assert s1+s2 == [s1[0]] + (s1[1..] + s2);
        assert sorted(s1+s2);
    }
}


