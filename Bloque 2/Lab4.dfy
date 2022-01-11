
// ESQUEMA DE VC GENERAL
/*
	1 → invariante sustituyendo las variables inciales
	2 → invariante sustituyendo las variables del while
	3 → !(condiciones del while) && invariante

	VC1 → Requires ==> 1
	VC2 → Condicion while && invarianrte ==> 2
	VC2 → 3 ==> Ensures
*/

// Ejercicio 1
method rootApprox (x:int)  returns (r:int)
	requires x >= 0
	ensures r*r <= x < (r+1)*(r+1) 

{
    assert 0 <= x; // 1
    r := 0;  
    assert r*r <= x;
    while (r+1)*(r+1) <= x
        invariant 0 <= r <= x+1 
        invariant r*r <= x
        decreases x - (r + 1) * (r + 1)
    {
        assert (r+1)*(r+1) <= x; // 2
        r := r+1;
        assert r*r <= x;
    }
    assert  !((r+1)*(r+1) <= x) && r*r <= x; //3
}

method VC_for_rootApprox (){
    assert forall x :: x >= 0 ==> 0 <= x;
    assert forall x, r :: (  (r+1)*(r+1) <= x && r*r <= x ) ==> ( (r+1)*(r+1) <= x );
    assert forall x, r :: ( !((r+1)*(r+1) <= x) && r*r <= x ) ==> ( r*r <= x < (r+1)*(r+1) );
}


function factorial (n:int):int
requires n >= 0
{
    if n==1 || n==0 then 1
    else n*factorial(n-1)
}

method compute_Fact1 (n:int) returns (f:int)
requires n >= 0
ensures f == factorial(n)
{
    assert factorial(n)== factorial(n)*1; //1
    f := 1;
    assert factorial(n)== factorial(n)*f;
    var x := n;
    f := 1;assert factorial(n)== factorial(x)*f;
    while x > 0
        invariant factorial(n)== factorial(x)*f;
    {
        assert factorial(n)== factorial(x-1)*(f* x); //2
        f, x := f* x, x-1;
        assert factorial(n)== factorial(x)*f;
    }
    assert !(x > 0) && factorial(n)== factorial(x)*f; //3
}

method VC_for_compute_Fact1()
{
    assert forall n:: (n >= 0) ==> factorial(n)== factorial(n);
    // TODO: no se porque no funciona
    // assert forall n, f, x:: (x>0 && (factorial(n)== factorial(x)*f)) ==> ( factorial(n)== factorial(x-1)*(f* x) );
    assert forall n,x,f ::  (!(x > 0) &&  0 <= x <= n &&  f * factorial(x) == factorial(n)) ==> f == factorial(n);
}

method compute_Fact2 (n:int) returns (f:int)
requires n >= 0
ensures f == factorial(n)
{
    assert 0 <= 0 <= n && 1== factorial(0); // 1
    var x := 0;
    assert 0 <= x <= n && 1== factorial(x);
    f := 1;
    assert 0 <= x <= n && f== factorial(x);
    while x < n
        invariant 0 <= x <= n
        invariant f== factorial(x)
        decreases n - x
    {
        assert 0 <= x+1 <= n && f*(x+1)== factorial(x+1); // 2
        x, f := x+1, f*(x+1);
        assert 0 <= x <= n && f== factorial(x);
    }
    assert !(x < n) && 0 <= x <= n && f== factorial(x); // 3
}


method VC_for_compute_Fact2()
{
    assert forall n :: (n >= 0) ==> (0 <= 0 <= n && 1== factorial(0));
    assert forall n,x,f :: (x < n && (0 <= x <= n && f== factorial(x))) ==> (0 <= x+1 <= n && f*(x+1)== factorial(x+1));
    assert forall n,x,f :: (!(x < n) && 0 <= x <= n && f== factorial(x)) ==> (f == factorial(n));
}

function power2(e:nat):nat		
{
    if e == 0 then 1 else 2*power2(e-1)
}

function sumPowers(n:nat):int
requires n >= 1
{
    if n == 1 then 1 else sumPowers(n-1) + power2(n-1)
}

method computeSumPowers(n:int) returns (r:int)  
	requires n >= 1
	ensures r == power2(n) - 1 
{
    var k, p;
    assert 1 <= 1 <= 1 && 1==1+(1-1) && 1== power2(1-1);
    k, r, p:= 1, 1, 1;
    assert 1 <= k <= n && r==p+(p-1) && p== power2(k-1);
    while k < n
        invariant 1 <= k <= n
        invariant r==p+(p-1)
        invariant p== power2(k-1)
        decreases n - k
    {
        assert 1 <= (k+1) <= n && (r+2*p)==2*p+(2*p-1) && 2*p== power2((k+1)-1);
        p := 2*p;
        assert 1 <= (k+1) <= n && (r+p)==p+(p-1) && p== power2((k+1)-1);
        r, k := r + p, k+1;
        assert 1 <= k <= n && r==p+(p-1) && p== power2(k-1);
    }
    assert !(k < n) && 1 <= k <= n && r==p+(p-1) && p== power2(k-1);
}


method VC_for_computeSumPowers ()
{
	assert forall n:: (n >= 1) ==> 1 <= 1 && 1 == power2(1)-1;
	assert forall n, k, r, p:: (k < n && 1 <= k <= n && r == p * 2 - 1 == power2(k) - 1) ==> (1 <= k+1 <= n && r+2*p == 2*p * 2 - 1 == power2(k+1) - 1);
	assert forall n, k, r, p:: (!(k < n) && 1 <= k <= n && r == p * 2 - 1 == power2(k) - 1) ==> (r == power2(n) - 1 );
}

method computeFactTuring (n:int) returns (u:int)
requires n >= 1
ensures u == factorial(n)
{
	
	assert (1 <= 1 <= n &&  1 == factorial(1)) == (1 <= n &&  1 == factorial(1)); //1
	var r := 1;
	assert 1 <= r <= n &&  1 == factorial(r);
	u := 1;
	assert 1 <= r <= n &&  u == factorial(r);
	while r < n
		invariant 1 <= r <= n
		invariant u == factorial(r)
	{
		assert 1 <= r <= n && u == factorial(r); //2
		// TODO: No entiendo porque esta es 1 y no la de abajo.
		//assert 1 <= r <= n &&  sig_fact(r,u) == factorial(r); //2
		u := sig_fact(r,u);
		assert 1 <= r+1 <= n &&  u == factorial(r+1); 
		r := r+1;
		assert 1 <= r <= n &&  u == factorial(r);
	}
	assert !(r < n) && 1 <= r <= n &&  u == factorial(r);
}

method VC_for_computeFactTuring ()

method sig_fact(r:int,u:int) returns (v:int)
requires r >= 1 && u == factorial(r)
ensures v == factorial(r+1)
{
    assert 1 <= 1 <= r+1 && v==v*1; //1
    var s := 1;
    assert 1 <= s <= r+1 && v==v*s;
    v := u;
    assert 1 <= s <= r+1 && v==u*s;
    while s < r+1
        invariant 1 <= s <= r+1 
        invariant v==u*s
    {
        assert 1 <= (s+1) <= r+1 && (v+u)==u*(s+1);//2
        s, v := s+1, v+u;
        assert 1 <= s <= r+1 && v==u*s;
    }
    assert !(s < r+1) && 1 <= s <= r+1 && v==u*s;//3
}

method VC_for_sig_fact()
{
    assert forall r,u,v:: (r >= 1 && u == factorial(r)) ==> (1 <= 1 <= r+1 && v==v*1);
    assert forall r,u,v,s:: ( s < r+1 && 1 <= s <= r+1 && v==u*s ) ==> (1 <= (s+1) <= r+1 && (v+u)==u*(s+1));
    
    // Se tiene que poner factorial de r en vez de u para que el forall cumpla con la precondicion de 
    // que u == factorial(r)
    // NO: assert forall r,u,v,s:: !(s < r+1) && 1 <= s <= r+1 && v==u*s ==> v == factorial(r+1);
    assert forall r, s, v:: !(s < r+1) && 1 <= s <= r+1 && v==s*factorial(r) ==> v == factorial(r+1);
}

predicate noDivU(x:int, t:int)
{
forall z :: ( 1 < z < t ==> x % z != 0) 
}

predicate prime(x:int)
{ 
x >= 2  && noDivU(x,x) 
}

predicate noPrimesIn(a:int, b:int)
{
forall z :: a < z < b ==> !prime(z)
}

// TODO: Hacer si quieres sacar nota
method next_prime (x:int) returns (p:int)
	requires prime(x)
	ensures p > x && prime(p) && noPrimesIn(x,p)
	decreases *
{
assert x+1 > x >= 2 && noPrimesIn(x,x+1); //1.1
assert x+1 > x >= 2 && noPrimesIn(x,x+1) && false ==> (p == x+1 && prime(x+1)); 
var next, isPrime := x+1, false;
assert next > x >= 2 && noPrimesIn(x,next) && isPrime ==> (p == next && prime(next));
while !isPrime					
    invariant next > x >= 2
    invariant noPrimesIn(x,next)          
	invariant isPrime ==> (p == next && prime(next))       
	decreases *
	{
	assert 2 <= 2 <= next && noDivU(next,2); //2.1 
	var d := 2;
	assert 2 <= d <= next && noDivU(next,d);
	while next % d != 0 
		invariant 2 <= d <= next
		invariant noDivU(next,d) 
		decreases next-d
		{ 
			assert 2 <= d+1 <= next && noDivU(next,d+1); //2.2
			d := d+1;
			assert 2 <= d <= next && noDivU(next,d);
		}
		assert 	((d == next) && next > x >= 2 && noPrimesIn(x,next) && ((d == next) ==> next == next && prime(next))) || 
				(!(d == next) && next+1 > x >= 2 && noPrimesIn(x,next+1) && ((d == next) ==> p == next+1 && prime(next+1)));
		isPrime := (d == next);
		assert 	(isPrime && next > x >= 2 && noPrimesIn(x,next) && (isPrime ==> next == next && prime(next))) || 
				(!isPrime && next+1 > x >= 2 && noPrimesIn(x,next+1) && (isPrime ==> p == next+1 && prime(next+1)));
		if isPrime { 
			p := next; 
		} 
		else { 
			next := next+1; 
		}
		assert next > x >= 2 && noPrimesIn(x,next) && isPrime ==> (p == next && prime(next));
	}
	assert isPrime && next > x >= 2 && noPrimesIn(x,next) && isPrime ==> (p == next && prime(next)); //3.1 
}


method VC_for_next_prime ()
{
	assert forall x:: prime(x) ==>( x+1 > x >= 2 && noPrimesIn(x,x+1));
	//assert forall x, next, isPrime, p:: (!isPrime && next > x >= 2 && noPrimesIn(x,next) && isPrime ==> (p == next && prime(next))) ==> (2 <= next && noDivU(next,2));
}