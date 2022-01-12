//EJERCICIO 1
function factorial (n:nat):nat
{
if n == 0 then 1 else n * factorial(n-1)
}

function factSeq (n:nat):seq<nat>
ensures |factSeq(n)| == n + 1
{
if n == 0 then [1] else factSeq(n-1) + [n * factorial(n-1)]
}

method compute_Fact_Seq (n: nat) returns (facts: seq<nat>)
ensures facts == factSeq(n)									  
{
	assert 0 <= 0 <= n && [1] == factSeq(0) && 1 == factorial(0);
	var i, f := 0, 1;
	assert 0 <= i <= n && [1] == factSeq(i) && f == factorial(i);
	facts := [1];
	assert 0 <= i <= n && facts == factSeq(i) && f == factorial(i);
		while i < n
		invariant 0 <= i <= n
		invariant facts == factSeq(i)
		invariant f == factorial(i)
			// Poner los invariantes y activar la post
			{
			assert 0 <= i+1 <= n && facts + [f*(i+1)] == factSeq(i+1) && f*(i+1) == factorial(i+1);
			f, i := f*(i+1), i+1;  
			assert 0 <= i <= n && facts + [f] == factSeq(i) && f == factorial(i);
			facts := facts + [f];
			assert 0 <= i <= n && facts == factSeq(i) && f == factorial(i);
			}
		assert facts == factSeq(n);	
	}

	method VCG_compute_Fact_Seq()
	{

		// Escribe aquí las tres condiciones de verificación que
		// hacen que el método compute_Fact_Seq sea verificado
		//VC1: 
		assert forall n:nat :: 0 <= 0 <= n && [1] == factSeq(0) && 1 == factorial(0);
		
		//VC2: se mantiene el invariante
		assert forall i, n, facts, f ::
		i < n && 
		0 <= i <= n && facts == factSeq(i) && f == factorial(i)
		==>
		0 <= i+1 <= n && facts + [f*(i+1)] == factSeq(i+1) && f*(i+1) == factorial(i+1);
		
		//VC3: invariante && !loopCondition ==> post
		assert forall i, n, facts, f ::
		!(i < n) &&
		0 <= i <= n && facts == factSeq(i) && f == factorial(i)
		==>
		facts == factSeq(n);


}

// EJERCICIO 2

function min(a:int, b:int):int
{
if a <= b then a else b
}

function zip<T,S>(r:seq<T>, s:seq<S>): seq<(T,S)>
	ensures |zip(r,s)| == min(|r|,|s|) 
{
if r == [] || s == []  then []
else [(r[0],s[0])] + zip(r[1..],s[1..])
}

function unzip<T,S> (z:seq<(T,S)>):(seq<T>,seq<S>)
{
if z == []  then ([],[])
else ( [z[0].0] + unzip(z[1..]).0, [z[0].1] + unzip(z[1..]).1 )
}

lemma unzip_zip_Lemma<T,S>(r:seq<T>, s:seq<S>)
requires |r| == |s|
ensures unzip(zip(r,s)) == (r,s) 
{
	if r == [] {
		//caso base
	} else {
		var resto: seq<(T, S)> := zip(r[1..], s[1..]);
		assert |resto| == |r|-1;
		calc {
			unzip(zip(r,s));
			unzip([(r[0],s[0])] + zip(r[1..],s[1..]));
			unzip([(r[0],s[0])] + resto);
			([r[0]] + unzip(resto).0,
			 [s[0]] + unzip(resto).1);
			 {
				 unzip_zip_Lemma(r[1..], s[1..]);
				 assert unzip(zip(r[1..],s[1..])) == (r[1..],s[1..]); //HI 
			 }
			 ([r[0]] + r[1..],
			 [s[0]] + s[1..]);
			 {
				 assert [r[0]] + r[1..] == r;
				 assert [s[0]] + s[1..] == s;
			 }
			(r, s);
		}
	}
}
// Demostrar este lema por inducción 

// EJERCICIO 3

lemma sets_size_Lemma<T>(s: set<T>, u: set<T> )
requires s < u 
ensures |s| < |u|
//No demostrar, solo usar más abajo, si necesario

lemma set_Lemma_Directa<T> (s1:set<T>,s2:set<T>, n:nat)
requires s1 < s2 && |s2| <= n 
ensures |s1 * s2| < n
{
	assert s1 * s2 < s2;
	sets_size_Lemma(s1 * s2, s2);
	assert |s1 * s2| < |s2| <= n;
}
//Demostrar este lemma mediante una prueba directa

lemma set_Lemma_Contr<T> (s1:set<T>,s2:set<T>, n:nat)
requires s1 < s2 && |s2| <= n 
ensures |s1 * s2| < n
{
	if |s1 * s2| >= n {
		assert exists x :: x in s2 && !(x in s1);
		var x :| x in s2 && !(x in s1);
		assert !(x in s1 * s2);

		assert |s1 * s2| >= |s2|;
		//assert s1 * s2 == s2;
		
		//assert x in s1 * s2;

		assert forall x :: x in s1 * s2 ==> x in s2;
		assert |s2| >= |s1*s2|;
		
		assert s2 <= s1 * s2;
		//assert s1 * s2 == s2;
		assume false;
} 
//Demostrar el mismo lemma, pero ahora con una prueba por contradicción/contraposición
