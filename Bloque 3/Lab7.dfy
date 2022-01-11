
datatype List<T> = Nil | Cons(head:T,tail:List<T>)

function method length<T> (xs:List<T>):nat
decreases xs
{
    match xs
    case Nil => 0
    case Cons(x, xs) => 1 + length(xs)
}


// Calcular el número de pares de elementos consecutivos iguales de una lista
function EqPairs<T(==)> (xs:List<T>):nat
{
    match xs
    case Nil => 0
    case Cons(h1, Nil) => 0
    case Cons(h1, Cons(h2, l)) =>
        if h1==h2 then 1 + EqPairs(xs.tail)
        else EqPairs(xs.tail)
}

datatype Tree<T> = Nil | Node(left:Tree<T>,root:T,right:Tree<T>)

function max (a:int,b:int):int
{
if a >= b then a else b
}

function depth<T> (t:Tree<T>):nat
decreases t
{
match t
    case Nil => 0
    case Node(l,_,r) => 1+(max(depth(l), depth(r)))
}


//Decidir si un arbol es "full" (todo nodo tiene 0 o 2 hijos)
predicate full<T>(t:Tree<T>)
decreases t
{
    match t
    case Nil => true
    case Node (left, root, right)=> 
        if ((left.Nil? && right.Nil?) || (!(left.Nil?) && !(right.Nil?))) then true
        else false          
}


lemma {:induction false} EqPairs_Lemma<T(==)> (xs:List<T>)
ensures EqPairs(xs) <= length(xs)
{
match xs
    case Nil => {}
    case Cons(l, ls) =>
    {
        EqPairs_Lemma(ls);
        assert EqPairs(ls) <= length(ls);

        calc == {
            length(xs); ==
            1 + length(ls); >=
            {
                EqPairs_Lemma(ls);
                assert EqPairs(ls) <= length(ls);
            }
            1 + EqPairs(ls); >=
            EqPairs(ls);
        }
    }
}


function method append<T>(xs:List<T>,ys:List<T>):List<T>
{
    if xs.Nil? then ys else Cons(xs.head, append(xs.tail, ys))
}

function rev<T>(xs:List<T>):List<T>
{
    if xs==List.Nil then List.Nil 
    else append(rev(xs.tail), Cons(xs.head, List.Nil))
}

function m_set<T>(xs:List<T>):multiset<T>
{
    if xs.Nil? then multiset{} else  multiset{xs.head}+m_set(xs.tail)
}


lemma {:induction false} append_Lemma<T> (xs:List<T>,ys:List<T>)
ensures m_set(append(xs,ys)) == m_set(xs) + m_set(ys)
{
    match xs 
        case Nil => {}
        case Cons(l, ls) => {
            append_Lemma(ls, ys);
            assert m_set(append(ls,ys)) == m_set(ls) + m_set(ys);

            calc {
                m_set(xs) + m_set(ys);
                multiset{xs.head} + m_set(xs.tail) + m_set(ys);
                {
                    assert ls == xs.tail;
                }
                multiset{xs.head} + m_set(ls) + m_set(ys);
                {
                    append_Lemma(ls, ys);
                    assert m_set(append(ls,ys)) == m_set(ls) + m_set(ys);
                }
                multiset{xs.head} + m_set(append(ls,ys));
                multiset{xs.head} + m_set(append(xs.tail,ys));
                m_set(append(xs,ys));
            }
        }
}

lemma {:induction false} append_length_Lemma<T> (xs:List<T>,ys:List<T>)
ensures length(append(xs,ys)) == length(xs) + length(ys)
{
    if length(xs)==0 { }
    else {
        append_length_Lemma(xs.tail, ys);
        assert length(append(xs.tail,ys)) == length(xs.tail) + length(ys);

        calc {
            length(xs) + length(ys);
            1 + length(xs.tail) + length(ys);
            {
                append_length_Lemma(xs.tail, ys);
                assert length(append(xs.tail,ys)) == length(xs.tail) + length(ys);
            }
            1 + length(append(xs.tail,ys));
            length(append(xs,ys));
        }
    }
}

lemma rev_append_Lemma<T> (xs:List<T>,ys:List<T>)
ensures rev(append(xs,ys)) == append(rev(ys),rev(xs))
{
match xs
    case Nil => {
        assert xs == List.Nil;
        var lv:List<T> := List.Nil;

        calc {
            append(rev(ys),rev(xs));
            append(rev(ys),rev(List.Nil));
            {
                assert append(rev(ys),rev(lv)) == append(rev(ys),lv);
            }
            append(rev(ys), lv);
            {
                lemma_rev_append_nil(rev(ys));
                assert append(rev(ys), lv) == rev(ys);
            }
            rev(ys);
        }
    }
    case Cons(l, ls) => 
    {
        rev_append_Lemma(ls, ys);
        assert rev(append(ls,ys)) == append(rev(ys),rev(ls));
        assert ls == xs.tail;

        calc {
            append(rev(ys),rev(xs));
            append(rev(ys),append(rev(xs.tail), Cons(xs.head, List.Nil)));
            {
                lemma_rev_order(rev(ys), rev(xs.tail), Cons(xs.head, List.Nil));
            }
            append(append(rev(ys), rev(xs.tail)), Cons(xs.head, List.Nil));
            {
                assert xs.tail==ls;
            }
            append(append(rev(ys), rev(ls)), Cons(xs.head, List.Nil));
            append(rev(append(ls,ys)), Cons(xs.head, List.Nil));
            rev(append(xs,ys));
        }
    }
}

// Este lo he creado yo
lemma lemma_rev_append_nil<T> (xs:List<T>)
ensures append(xs, List.Nil) == xs
{
    // Este se verifica solo
}
// Este tambien lo he creado yo 
lemma lemma_rev_order<T> (l1:List<T>, l2:List<T>, l3:List<T>)
ensures append(l1,append(l2, l3)) == append(append(l1, l2), l3)
{
match l1
    case Nil => {}
    case Cons(l,ls) => 
    {
        lemma_rev_order(ls, l2, l3);
        assert append(ls,append(l2, l3)) == append(append(ls, l2), l3);

        calc {
            append(l1,append(l2, l3));
            Cons(l1.head, append(l1.tail, append(l2, l3)));
            {
                assert ls==l1.tail;
            }
            Cons(l1.head, append(ls, append(l2, l3)));
            {
                lemma_rev_order(ls, l2, l3);
                assert append (ls, append(l2, l3)) == append(append(ls, l2), l3);
            }
            Cons(l1.head, append(append(ls, l2), l3));
            Cons(l1.head, append(append(l1.tail, l2), l3));
            append(append(l1, l2), l3);
        }
    }
}

lemma rev_twice_Lemma<T> (xs:List<T>)
ensures rev(rev(xs)) == xs
{
match xs 
    case Nil => {}
    case Cons(h,t) => {

        var hl:=Cons(h,List.Nil);
        var l:=append(rev(t),hl);


        rev_twice_Lemma(t);
        assert rev(rev(t)) == t;
        assert rev(rev(xs.tail)) == xs.tail;

        calc {  
            rev(rev(xs));
            rev(append(rev(t), hl));
            rev(append(rev(t), hl));
            rev(append(rev(t), rev(hl)));
            {
                rev_append_Lemma(rev(t), rev(hl));
                assert rev(append(rev(t),rev(hl))) == append(rev(rev(hl)),rev(rev(t)));
            }
            append(rev(rev(hl)),rev(rev(t)));
            {
                rev_twice_Lemma(t);
                assert rev(rev(t)) == t;
                assert rev(rev(xs.tail)) == xs.tail;
            }
            append(rev(rev(hl)),t);
            {
                assert rev(rev(hl)) == hl;
            }
            append(hl, t);
            append(Cons(h,List.Nil), xs.tail);
            xs;
        }
    }
}


// Funciones de orden superior
function filter<T> (p: T -> bool, xs:List<T>):List<T>
{
    match xs
    case Nil => List.Nil
    case Cons(h,t) => 
        if p(h) then Cons(h, filter(p, t))
        else filter(p, t) 
}

lemma filterConmutes_Lemma<T>(xs:List<T>,p:T->bool,q:T->bool)
ensures filter(p,filter(q,xs)) == filter(q,filter(p,xs))
{
match xs
    case Nil => {}
    case Cons(h, t) => {
        filterConmutes_Lemma(t, p, q);
        assert filter(p,filter(q,xs)) == filter(q,filter(p,xs));

        calc {
            filter(p,filter(q,xs));
            if filter(q,xs).Nil? then List.Nil 
            else if p(h) && q(h) then 
                Cons(h, filter(p,filter(q,t)))
            else 
                filter(p,filter(q,t));
            {
                filterConmutes_Lemma(t, p, q);
                assert filter(p,filter(q,xs)) == filter(q,filter(p,xs));
            }
            if filter(q,xs).Nil? then List.Nil 
            else if p(h) && q(h) then 
                Cons(h, filter(q,filter(p,t)))
            else 
                filter(q,filter(p,t));
        }
    }
}

// ARBOLES
// Un arbol es perfecto cuando todos los nodos tienen 0 o 2 hijos y tienen la misma altura.
predicate perfect<T>(t:Tree<T>)
{
t.Nil? ||
(t.left.Nil? && t.right.Nil?) || 
((t.left.Node?)  && (t.right.Node?) && perfect(t.left) && perfect(t.right) && depth(t.right) == depth(t.left))
}


function numLeaves<T>(t:Tree<T>):nat
{
match t
case Nil => 0
case Node(l,_,r)=>  if l.Nil? && r.Nil? then 1
                    else numLeaves(l)+numLeaves(r)
}

function exp2(n:nat):nat
{
if n== 0 then 1 else 2*exp2(n-1)
}

lemma {:induction false} numLeavesPerf_Lemma<T> (t:Tree<T>)
requires t.Node? && perfect(t)
ensures numLeaves(t) == exp2(depth(t)-1)
{
    match t
    case Node(l,_,r) => {
        calc =={
        numLeaves(t);
        if l.Nil? && r.Nil? then 1 else numLeaves(l) + numLeaves(r);
            {
            if l.Node? {
                numLeavesPerf_Lemma(l);
                assert numLeaves(l)==exp2(depth(l)-1); //HI
            }
            if r.Node?{
                numLeavesPerf_Lemma(r);
                assert numLeaves(r)==exp2(depth(r)-1); //HI
            }
            }
            if l.Nil? && r.Nil? then 1 else exp2(depth(l)-1) + exp2(depth(r)-1);
            exp2(depth(t)-1);
        }
    }
}
