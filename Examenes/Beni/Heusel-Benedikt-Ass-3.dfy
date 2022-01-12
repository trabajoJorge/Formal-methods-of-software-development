//APELLIDOS: Heusel
//NOMBRE: Benedikt

/////// EJERCICIO 1

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

function length<T> (xs:List<T>):nat
decreases xs
{
match xs
case Nil => 0
case Cons(_,t) => 1 + length(t)
}

function elem<T>(xs: List<T>, i: nat): T
requires 0 <= i < length(xs)
requires xs.Cons?
{
if i == 0 then xs.head else elem(xs.tail,i-1)
}

predicate sorted (xs:List<int>)
{
xs == List.Nil  || xs.tail == List.Nil  || (xs.head <= xs.tail.head && sorted(xs.tail))
}

//EJERCICIO 1: Demostrar por inducción el siguiente lema:
lemma sortedR2L_Lemma (xs:List<int>)
requires forall i :: 0 <= i < length(xs)-1 ==> elem(xs,i) <= elem(xs,i+1) 
ensures sorted(xs)
{
	if xs.Nil? || xs.tail.Nil? {
		assert sorted(xs);
	} else {
		calc <==> {
			sorted(xs);
			xs == List.Nil  || xs.tail == List.Nil  || (xs.head <= xs.tail.head && sorted(xs.tail));
			xs.head <= xs.tail.head && sorted(xs.tail);
			{
				assert forall i ::  1 <= i < length(xs)-1 ==>  elem(xs,i) ==  elem(xs.tail,i-1);
				assert forall i :: 0 <= i < length(xs)-1 ==> elem(xs,i) <= elem(xs,i+1); //es el requires del lema, si no se repite aqui, la prueba falla
				assert elem(xs,0) <= elem(xs,1); 
				assert elem(xs,0) == xs.head && elem(xs,1) == xs.tail.head;
				assert xs.head <= xs.tail.head;
			}
			//true && sorted(xs.tail);  //MUY INNECESARIO
			sorted(xs.tail);
			{
				//assert forall i ::  1 <= i < length(xs)-1 ==>  elem(xs,i) ==  elem(xs.tail,i-1);
				//assert forall i :: 0 <= i < length(xs)-1 ==> elem(xs,i) <= elem(xs,i+1); //es el requires del lema, aqui parece que al final no se necesita, pero arriba si!
				assert forall i :: 0 <= i < length(xs.tail)-1 ==> elem(xs.tail,i) == elem(xs, i+1) <= elem(xs, i+2);// == elem(xs.tail,i+1);
				sortedR2L_Lemma(xs.tail);
				//assert sorted(xs.tail); HI
			}
			true;
		}
	}
}
//CREO QUE LO HAS HECHO ALGO MÁS COMPLICADO DE LO NORMAL, MIRA:
lemma sortedR2L_Lemma_version (xs:List<int>)
requires forall i :: 0 <= i < length(xs)-1 ==> elem(xs,i) <= elem(xs,i+1) 
ensures sorted(xs)
{
if xs.Cons? && xs.tail.Cons? {
    assert forall i :: 0 <= i < length(xs)-1 ==> elem(xs.tail,i) == elem(xs,i+1);
    //assert forall i :: 0 <= i < length(xs.tail)-1 ==> elem(xs.tail,i) <= elem(xs.tail,i+1);
    sortedR2L_Lemma_version(xs.tail);
    //assert sorted(xs.tail); //HI
	assert xs.head == elem(xs,0) <= elem(xs,1) == xs.tail.head;
    }
}


////////// EJERCICIO 2

function mset_list<T>(xs:List):multiset<T>
ensures length(xs) == |mset_list(xs)|
{
match xs
case Nil => multiset{}
case Cons(h,t) => multiset{h} + mset_list(t)
}

function append (xs:List<int>,ys:List<int>):List<int>
{
match xs
case Nil => ys
case Cons(h,t) => Cons(h,append(t,ys))
}

//Las siguientes funciones take y drop son como las predefinidas en Haskell 
//take(i,xs) es la lista de los i primeros elementos de xs, si i <= length(xs), en otro caso, es toda la lista xs
//drop(i,xs) es la lista que resulta de eliminar los i primeros elementos de xs, si i<=length(xs), en otro caso, es vacía
function take(i:nat, xs:List<int>):List<int>
{
if i == 0 || xs == Nil then Nil else Cons(xs.head,take(i-1,xs.tail))
}

function drop(i:nat, xs:List<int>):List<int>
{
if i == 0 || xs == Nil then xs else drop(i-1,xs.tail)
}

//EJERCICIO 2: Demostrar por induccion en i y xs el append_Lemma de abajo.
//Dafny lo demuestra automáticamente, pero tu debes dar todos los detalles,
//incluida la hipótesis de inducción y como se usa para probra el lema.

lemma {:induction false} append_Lemma (i:nat, xs:List<int>)
requires i < length(xs)
ensures append(take(i,xs),Cons(elem(xs,i),drop(i+1,xs))) == xs
{
	if i == 0 {
		calc {
			append(take(i,xs),Cons(elem(xs,i),drop(i+1,xs)));
			append(Nil, Cons(xs.head, xs.tail));
			Cons(xs.head, xs.tail);
			xs;
		}
	} else {
		calc {
			append(take(i,xs),Cons(elem(xs,i),drop(i+1,xs)));
			append(Cons(xs.head, take(i-1,xs.tail)),Cons(elem(xs,i),drop(i+1,xs)));
			Cons(xs.head, append(take(i-1,xs.tail),Cons(elem(xs,i),drop(i+1,xs))));
			//TE FALTABA LA DE ABAJO, Y PARA APLICAR LA HI ES RELEVANTE
			//AUNQUE DAFNY LO HACÍA SIN ELLO
			Cons(xs.head, append(take(i-1,xs.tail), Cons(elem(xs.tail,i-1),drop(i,xs.tail))));
			{
				append_Lemma(i-1, xs.tail);
				//assert append(take(i-1,xs.tail),Cons(elem(xs.tail,i-1),drop(i,xs.tail))) == xs.tail; //HI
			}
			Cons(xs.head, xs.tail);
			xs;
		}
	}
}

/////////////////////////EJERCICIO 3: 
//Diseñar un método iterativo verificado que satisfaga la siguiente especificación:
//Indicación: partiendo de las postcondiciones, plantea los invariantes y deriva el programa.

method index_min_from(a:array<int>,j:int) returns (im:int)
requires 0 <= j < a.Length
ensures j <= im < a.Length
ensures forall i :: j <= i < a.Length ==> a[im] <= a[i]
{ //MUY BIEN
	var k := j;
	im := j;

	while k < a.Length
		invariant j <= k <= a.Length
		invariant j <= im < a.Length
		invariant forall i :: j <= i < k ==> a[im] <= a[i]
		decreases a.Length - k
	{
		if a[k] < a[im] {
			im := k;
		}
		k := k+1;
	}
}

////////////////////////EJERCICIO 4

predicate sortedBetween(a:array<int>,lo:int,hi:int)
requires 0 <= lo <= hi <= a.Length
reads a
{
forall i, j :: lo <= i < j < hi ==> a[i] <= a[j] 
}

predicate sortedArray(a:array<int>)
reads a
{
sortedBetween(a,0,a.Length) 
}

predicate perm<T>(s:seq<T>,r:seq<T>)
{
multiset(s) == multiset(r)
}

/*EJERCICIO 4: Utilizando el método index_min_from del ejercicio 3 
   (si no lo has implementado comenta el cuerpo completo, y utiliza su contrato),
   y los predicados definidos arriba "sortedBetween" y "perm", 
   diseñar un método verificado que ordene el array en base a intercambiar el 
   el elemento actual con el mínimo elemento de la parte del array que está aún sin ordenar
   Ejemplo:
	0 1 2 3 4 --index 
	(9 8 5 7 6) index_min_from(a,0) = 2
	===>  Swap a[0] y a[2] 
	(5 8 9 7 6) index_min_from(a,1) = 4  
	===>  Swap a[1] y a[4] 
	(5 6 9 7 8) index_min_from(a,2) = 3
	===>  Swap a[2] y a[3] 
	(5 6 7 9 8) index_min_from(a,3) = 4
	===>  Swap a[3] y a[4] 
	(5 6 7 8 9) 
*/
method min_sort(a:array<int>)
requires a.Length > 0
ensures sortedArray(a)
ensures perm(a[..],old(a[..]))
modifies a
{
	var f := 0;

	while f < a.Length
		invariant 0 <= f <= a.Length
		invariant sortedBetween(a, 0, f)
		invariant forall s, u :: 0 <= s < f && f <= u < a.Length ==> a[s] <= a[u] //MUY BIEN
		invariant perm(a[..],old(a[..]))
	{
		var im := index_min_from(a, f);
		a[f], a[im] := a[im], a[f];
		f := f + 1;
	}
}

///////////////////////////////////////////////////////////////////////////////////////
//// EL SIGUIENTE EJERCICIO ES EXTRA (hazlo sólo si has completado todos los anteriores)

function mapping<T,S> (f:T -> S, xs:List<T>):List<S>
decreases xs
{
match xs
case Nil => Nil
case Cons(h,t) => Cons(f(h),mapping(f,t))    
}

function compose<T,S,U> (f:T -> S, g:S -> U):(T -> U)
{
x => g(f(x))  
}

//Demostrar por inducción en xs el lema compose_Lemma de abajo.
//Dafny lo demuestra automáticamente, pero tu debes dar todos los detalles,
//incluida la hipótesis de inducción y como se usa para probra el lema.
lemma {:induction false} compose_Lemma<T,S,U> (f:T -> S, g:S -> U, xs:List<T>)
ensures mapping(compose(f,g),xs) == mapping(g,mapping(f,xs))
{ //PERFECTO
	match xs
		case Nil => {
			calc {
				mapping(compose(f,g),xs);
				Nil;
				mapping(g, Nil);
				mapping(g, mapping(f, xs));
			}
		}
		case Cons(h, t) => {
			calc {
				mapping(compose(f,g),xs);
				Cons(compose(f, g)(h), mapping(compose(f, g),t));
				{
					compose_Lemma(f, g, t);
					//assert mapping(compose(f,g),t) == mapping(g,mapping(f,t)); //HI
				}
				Cons(compose(f, g)(h), mapping(g,mapping(f,t)));
				Cons(g(f(h)), mapping(g,mapping(f,t)));
				mapping(g,Cons(f(h), mapping(f,t)));
				mapping(g,mapping(f,xs));
			}
		}
}


