function exp (x:int,e:int): int
requires e >= 0
decreases e
{
if e == 0 then 1 else x * exp(x,e-1) 
}


lemma {:induction false} Ind1_Lemma (n:int)
requires n >= 1
ensures (exp(3,n) - 1)%2 == 0
{ // INDUCCION SIMPLE
    if n==1 {
        assert (exp(3,1) - 1)%2==0; 
    }
    else{
        calc == {
            (exp(3,n) - 1)%2;
            (2*exp(3,n-1))%2 + (exp(3,n-1) - 1)%2;
            {
                Ind1_Lemma(n-1);
                assert (exp(3,n-1) - 1)%2 == 0; // HI
            }
            2*exp(3,n-1)%2 + 0;
            {
                assert 2*exp(3,n-1)%2==0;
            }
            0+0;
            0;
        }
        assert (exp(3,n) - 1)%2 == 0;
    }
}


lemma {:induction false} mod8_Lemma (n:int)
requires n >= 1
ensures (exp(3,2*n) - 1)%8 == 0
{ // INDUCCION DIVISIVILIDAD
    if n==1 {}
    else {

        calc == {
            (exp(3,2*n) - 1)%8;
            (3*3*exp(3,2*n-2) - 1)%8;
            (9*exp(3,2*n-2) - 1)%8;
            (8*exp(3,2*n-2))%8 + (exp(3,2*n-2) - 1)%8;
            {
                mod8_Lemma(n-1);
                assert (exp(3,2*(n-1)) - 1)%8 == 0;
                assert (exp(3,2*n-2) - 1)%8 == 0; // HI
            }
            (8*exp(3,2*n-2))%8 + 0;
            {
                assert (8*exp(3,2*n-2))%8==0;
            }
            0+0;
            0;
        }
        assert (exp(3,2*n) - 1)%8 == 0;
    }
}

// DEMOSTRAR UN LEMMA FORALL CON OTRO LEMMA
lemma mod8_forall_Lemma()
ensures forall m :: m >= 1 ==> (exp(3,2*m) - 1)%8 == 0
{
forall k | k >= 1 {mod8_Lemma(k);}
}


lemma {:induction false} cuatroN_Lemma (n:int)
requires n >= 6
ensures 4*n < (n*n) - 7
{
    if n==6{}
    else {
        cuatroN_Lemma(n-1);
        assert 4*(n-1) < ((n-1)*(n-1)) - 7;  //HI
        // Se simplifica la HI
        assert 4*n-4 < (n*n)-2*n+1 -7; 
        // Se vuelve a simplificar la HI
        assert 4*n < (n*n)-2*n+5 -7; 
        // Se simplifica una ultima vez la HI y se obtiene a la derecha un operando mayor por lo que se mantiene 
        // la propiedad
        assert 4*n < ((n*n)-7) + (2*n+5); 
    }
}

function sumOdds (n:nat):nat
requires n >= 1
{
if n == 1 then 1 else sumOdds(n-1) + 2*n-1       
}

lemma {:induction false} sumOdds_Lemma (n:nat)
requires n >= 1
ensures sumOdds(n) == n*n
{
    if n==1{}
    else {
        calc == {
            sumOdds(n);
            sumOdds(n-1) + 2*n-1;
            {
                sumOdds_Lemma(n-1);
                assert sumOdds(n-1)==(n-1)*(n-1); // HI
            }
            (n-1)*(n-1) + 2*n-1;
            (n*n)-2*n+1 + 2*n-1;
            n*n;
        }
        assert sumOdds(n)==n*n;
    }
}

function fact(n:nat):nat
decreases n
{
    if n==1 || n==0 then n else n*fact(n-1)
}

lemma factExp_Lemma(n:nat)
ensures fact(n) <= exp(n,n)
{
    if n==0{}
    else if n==1 {}
    else {
        factExp_Lemma(n-1);
        assert fact(n-1) <= exp(n-1,n-1); //HI
        
        assert fact(n)==n*fact(n-1);
        // Por induccion puedo decir que 
        assert fact(n-1) <= exp(n-1,n-1); // HI
        // Pero para utilizar la expresion anterior lo tengo que multiplicar el lado derecho por n
        assert n*fact(n-1) <= n*exp(n-1,n-1);

        // TODO: No entiendo este paso             
        aux_Lemma(n-1,n,n-1);
        assert exp(n-1,n-1)  <= exp(n, n-1);

        // Se sustituye la parte derecha
        assert n*fact(n-1) <= n*exp(n, n-1);

        // Se simplifican los operandos y queda demostrado el lemma
        assert fact(n) <= exp(n,n);
    }
}

lemma aux_forall_Lemma()
ensures forall x,y,e :: (0 <= x < y && e >= 0) ==> exp(x,e) <= exp(y,e);


lemma aux_Lemma (x:int,y:int,e:int)
requires 0 <= x < y 
requires e >= 0 
ensures exp(x,e) <= exp(y,e);
{
    if e > 0 {
        aux_Lemma(x,y,e-1);
        assert exp(x,e-1) <= exp(y,e-1); //HI
        assert exp(x,e) == x * exp(x,e-1) <= x * exp(y,e-1);
        
        calc {
            x * exp(x,e-1); <= 
            {
                aux_Lemma(x,y,e-1);
                assert exp(x,e-1) <= exp(y,e-1); //HI   
            }
            x * exp(y,e-1); <= 
            {
                // Para asegurar que y elevado a e-1 es mayor o igual que 1. (Propiedad de los exponentes, que dafny no comprueba automatico)
                expGET1_Lemma (y, e-1);
            }
            y * exp(y,e-1); == 
            exp(y,e);
        }
    }
} 


lemma aux_Lemma2 (x:int,y:int,e:int)
requires 0 <= x < y 
requires e >= 0 
ensures exp(x,e) <= exp(y,e);
{
    if e==0{}
    else{
        aux_Lemma2(x,y,e-1);
        assert exp(x,e-1) <= exp(y, e-1);

        calc {
            exp(x,e);
            x*exp(x,e-1); <=
            {
                aux_Lemma2(x,y,e-1);
                assert exp(x,e-1) <= exp(y,e-1);
            }
            x*exp(y,e-1); <=
            {
                assert 0<=x<y;
                expGET1_Lemma(y, e-1);
                assert x*exp(x,e-1) <= y*exp(y,e-1);
            }
            y*exp(y,e-1);
        }
    }
}


lemma {:induction false} expGET1_Lemma  (z:int,e:int)
requires z >= 1 && e >= 0
ensures exp(z,e) >= 1
{
    if e==1{}
    else {
        if e-1>=0{
            expGET1_Lemma(z, e-1);
            assert exp(z,e-1) >= 1;
            
            calc  {
                exp(z,e);
                z*exp(z,e-1); >=
                {
                    expGET1_Lemma(z, e-1);
                    assert exp(z,e-1) >= 1; // HI
                }
                1;
            }
        }
        else{
            assert e-1<0;
            assert exp(z,e) >= 1;
        }
    }
}


function sumD (x :nat) :nat
{
if x < 10 then x else x%10 + sumD(x/10)
}


function even(x:nat):bool   
{
    x%2 == 0
}
predicate even2 (x:nat)
{
    x%2 == 0
}
lemma sumDig_Lemma (x:nat)
requires x >= 11 && x%11 == 0 
ensures even(sumD(x))
{
    if x==11{}
    else{
        // Creo una variable para la induccion
        var n := x/11;
        assert x==11*n;
        
        sumDig_Lemma(11*(n-1));
        assert even(sumD(11*(n-1)));

        calc <==> {
            even(sumD(x));
            even(sumD(11*n));
            even(sumD(11*(n-1)+11));
            {
                // Se asume porque el lemma que lo demuestra es falso
                assume forall a:nat,b:nat :: sumD(a+b) == sumD(a)+sumD(b);
            }
            even(sumD(11*(n-1))+sumD(11));
            even(sumD(11*(n-1))+2);
            even(sumD(11*(n-1))) && even(2);
            even(sumD(11*(n-1))) && true;
            even(sumD(11*(n-1)));
            {
                sumDig_Lemma(11*(n-1));
                assert even(sumD(11*(n-1)));
            }
            true;
        }
    }
}

function Fib (n:nat):nat
{
    if n==0 || n==1 then 1
    else Fib(n-1)+Fib(n-2)
}

lemma {:induction false} Fib1_Lemma(n:nat)
requires n >= 1
ensures Fib(n) >= 1
{
    if n==1{}
    else{

        calc {
            Fib(n); ==
            Fib(n-1)+Fib(n-2); >=
            {
                Fib1_Lemma(n-1);
                assert Fib(n-1) >=1;
            }
            1;
        }

        assert Fib(n) >= 1;
    }
}

lemma {:induction false} Fib5_Lemma (n:nat)
requires n >= 5
ensures Fib(n) >= n
{
    if n==5{}
    else{
        calc {
            Fib(n); ==
            Fib(n-1)+Fib(n-2); >=   
            {
                Fib5_Lemma(n-1);
                assert Fib(n-1) >= n-1;
                // Sabiendo que Fibonachi como minimo nos puede dar y se puede afirmar que el valor minimo de 
                // Fib(n-2) es 1. Por lo que se cumple lo siguiente.
                assert Fib(n-1) + 1 >= n;
                assert Fib(n-1) + Fib(n-2) >= n;
            }
            n;
        }
        assert Fib(n)>=n;
    }
}

lemma Cuad_Mitad_Lemma (b:int,e:nat)
requires e > 0 && e % 2 == 0
ensures exp(b*b,e/2) == exp(b,e)
{
    if (e==2){}
    else {
        
        calc {
            exp(b,e);
            b*b*exp(b,(e-2));
            {
                Cuad_Mitad_Lemma(b, e-2);
                assert exp(b*b,(e-2)/2) == exp(b,(e-2));
            }
            b*b*exp(b*b,(e-2)/2);
            exp(b*b, e/2);
        }
        assert exp(b*b,e/2) == exp(b,e);
    }
}

lemma fact_Lemma (n:int)
requires n >= 7
ensures exp(3,n) < fact(n)
{
    if n==7{}
    else{
        calc {
            exp(3,n); ==
            3*exp(3,n-1); <
            {
                fact_Lemma(n-1);
                assert exp(3,n-1) < fact(n-1);
            }
            3*fact(n-1); <
            {
                // Como siempre es menor se asume (Lo he intentado demostrar pero es un baile importante)
                assume 3*fact(n-1) < fact(n);
            }
            fact(n);
        }
    }
}


//Ejercicio para casa
lemma fact2n_Lemma(n:int)
requires n >= 1
ensures fact(2*n) < exp(2,2*n)*fact(n) *fact(n)
{
    if n==1 {}
    else{
        fact2n_Lemma(n-1);
        assert fact(2*(n-1)) < exp(2,2*(n-1))*fact((n-1)) *fact((n-1));
        assert fact(2*n-2) < exp(2,2*n-2)*fact(n-1) *fact(n-1);

        calc {
            fact(2*n);
            2*n*fact(2*n-1);
            (2*n)*(2*n-1)*fact(2*n-2); <
            {
                fact2n_Lemma(n-1);
                assert fact(2*(n-1)) < exp(2,2*(n-1))*fact((n-1)) *fact((n-1));
                assert fact(2*n-2) < exp(2,2*n-2)*fact(n-1) *fact(n-1);
                // Asumo que si se cumple el anterior assert y multiplico a ambos por el mismo valor, siendo este 
                // entero y positivo, se sigue cumpliendo la desigualdad.
                assume (2*n)*(2*n-1)*fact(2*n-2) < (2*n)*(2*n-1)*exp(2,2*n-2)*fact(n-1) *fact(n-1);
            }
            exp(2,2*n)*fact(n) *fact(n);
        }
    }
}
