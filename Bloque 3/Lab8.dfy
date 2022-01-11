
// TODO: Este lab me desconcierta un poco.  ¿Debería de saber implementar el quicksort?
datatype List<T> = Nil | Cons(head:T, tail:List)

function length<T> (xs:List<T>):nat
decreases xs
{
    match xs 
        case Nil => 0
        case Cons(h, t) => 1 + length(t)
}

function mset_list<T>(xs:List):multiset<T>
decreases xs
{
    match xs 
        case Nil => multiset {}
        case Cons(h, t) => multiset{h} + mset_list(t)
}

function method append<T> (xs:List,ys:List):List
decreases xs
{
    match xs 
        case Nil => ys
        case Cons(h,t) => Cons(h, append(t, ys))
}

lemma {:induction xs} mset_append_Lemma<T> (xs:List<T>,ys:List<T>)
ensures mset_list(append(xs,ys)) == mset_list(xs) + mset_list(ys)
{
    match xs 
        case Nil => {}
        case Cons(h ,t) => 
        {
            mset_append_Lemma(t, ys);
            assert mset_list(append(t,ys)) == mset_list(t) + mset_list(ys);
            assert mset_list(append(xs.tail,ys)) == mset_list(xs.tail) + mset_list(ys); // HI

            calc == {
                mset_list(xs) + mset_list(ys);
                multiset{xs.head} + mset_list(xs.tail) + mset_list(ys);
                {
                    mset_append_Lemma(t, ys);
                    assert mset_list(append(t,ys)) == mset_list(t) + mset_list(ys);
                    assert mset_list(append(xs.tail,ys)) == mset_list(xs.tail) + mset_list(ys); // HI
                }
                multiset{xs.head} + mset_list(append(xs.tail,ys));
                mset_list(append(xs,ys));
            }
        }
}


predicate sorted (xs:List<int>)
decreases xs
{
    match xs
        case Nil => true
        case Cons(h,t) => 
            if xs.tail.Nil? then true
            else h <= xs.tail.head && sorted(t)
}

//INSERTION SORT

method insert(x:int, xs:List<int>) returns (ys:List<int>, ghost hys:int)
requires sorted(xs)
ensures sorted(ys)
ensures mset_list(ys) == multiset{x} + mset_list(xs)
ensures hys == ys.head && (hys == x || (xs.Cons? && hys == xs.head))
decreases xs
{
    match xs 
        case Nil => 
        {
            ys, hys := Cons(x, Nil), x;
        }
        case Cons(h, t) =>
        {
            if x <= h {
                ys,hys:= Cons(x, Cons(h, t)), x;
            }
            else {
                var aux;
                ghost var haux:int;
                aux,haux := insert(x, t);
                ys, hys := Cons(h, aux), h;
            }
        }

}

//QUICKSORT
method quicksort(xs:List<int>) returns (ys:List<int>)
ensures sorted(ys)
ensures mset_list(ys) == mset_list(xs)
decreases length(xs)
{
match xs 
	case Nil => {return Nil;}
	case Cons(h,t) => 
	{
		var t1,t2 := partition(h,t);
		var ys1 := quicksort(t1);
		var ys2 := quicksort(t2);
		ys := append(ys1,Cons(h,ys2));
		assume sorted(ys);
		assume mset_list(ys) == mset_list(xs);
	}
}

method partition(z:int,xs:List<int>) returns (xs1:List<int>,xs2:List<int>)
ensures length(xs1) <= length(xs) && length(xs2) <= length(xs)
ensures mset_list(xs) == mset_list(xs1) + mset_list(xs2)
ensures forall e :: e in mset_list(xs1) ==> e <= z
ensures forall e :: e in mset_list(xs2) ==> e > z
{
match xs 
	case Nil => { return Nil,Nil;}
	case Cons(h,t) => {
		var t1,t2 := partition(z,t);
		if h <= z { return Cons(h,t1),t2; }
		else {return t1,Cons(h,t2);}
	}
}
