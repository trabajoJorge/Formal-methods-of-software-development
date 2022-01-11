//Direct Proof by Cases
predicate div2(n:nat)
{ 
n%2 == 0 
}

lemma cuadEven_Lemma(x:nat)
ensures div2(3*x*x + x + 14)
// INDUCCION POR CASOS
{
    if div2(x){
        var n:= x/2;
        assert x== 2*n;
        assert 3*x*x + x + 14 == 2*(6*n*n+n+7);
        assert div2(2*(6*n*n+n+7));
    }
    else{
        var n:=(x-1)/2;
        assert x== 2*n+1;

        calc{
            3*x*x + x + 14;
            3*(2*n+1)*(2*n+1) + (2*n+1) + 14;
            12*n*n+14*n+18;
            2*(6*n*n+7*n+9);
        }

        assert 3*x*x + x + 14 == 2*(6*n*n+7*n+9);
        assert div2(2*(6*n*n+7*n+9));
    }
}
predicate div3 (n:nat)
{ n%3 == 0}

lemma notDiv3_Lemma (x:nat)
ensures !div3(2*x*x + x + 1)
{
    if (x%3==0){
        var n:= x/3;
        assert x==3*n;

        calc {
            2*x*x + x + 1;
            2*(3*n)*(3*n) + (3*n) + 1;
            18*n*n+3*n+1;
            3*(6*n*n+n)+1;
        }
        assert 2*x*x + x + 1 == 3*(6*n*n+n)+1;
        assert !div3(3*(6*n*n+n)+1);
    }
    else if (x%3==1){
        var n:= (x-1)/3;
        assert x==3*n+1;

        calc {
            2*x*x + x + 1;
            2*(3*n+1)*(3*n+1) + (3*n+1) + 1;
            18*n*n+15*n+4;
            3*(6*n*n+5*n+1)+1;
        }
        assert 2*x*x + x + 1 == 3*(6*n*n+5*n+1)+1;
        assert !div3(3*(6*n*n+5*n+1)+1);
    }
    else { // x%3 == 2
        var n:= (x-2)/3;
        assert x==3*n+2;

        calc {
            2*x*x + x + 1;
            2*(3*n+2)*(3*n+2) + (3*n+2) + 1;
            18*n*n + 27*n + 11;
            3* (6*n*n+ 9*n + 3)+2;
        }
        assert 2*x*x + x + 1 == 3*(6*n*n+ 9*n + 3)+2;
        assert !div3( 3*(6*n*n+ 9*n + 3)+2);
    }
}



lemma Odd_Sum_Lemma (a:nat,b:nat)
requires a == b+1
ensures !div2(a+b) //(a+b)%2 == 1
{
// PRUEBA DIRECTA 
    assert (a+b)%2 == (b+1+b)%2 == 1;
// PRUEBA POR CONTRAPOSICION
    if (div2(a+b)){
        assert a != b+1;
    }
// PRUEBA POR CONTRADICCION
    if (div2(a+b)){
        assert div2(2*b+1);
        assert false;
    }
}

function exp (x:int,e:nat):int
{
if e == 0 then 1 else x * exp(x,e-1)    
}


// INDUCCION Y CONTRADICCION JUNTAS
lemma indContr_Lemma (n:nat)
requires n >= 3
ensures exp(n+1,n) < exp(n,n+1)
{
    if(n==3){
        assert exp(3+1,3) < exp(3,3+1);
    }
    else{
        indContr_Lemma(n-1);
        assert exp((n-1)+1,(n-1)) < exp((n-1),(n-1)+1);
        assert exp(n, n-1) < exp(n-1, n);

        calc {
            exp(n,n+1);
            n*exp(n,n);
            n*n*exp(n,n-1); <
            {
                indContr_Lemma(n-1);
                assert exp((n-1)+1,(n-1)) < exp((n-1),(n-1)+1);
                assert exp(n, n-1) < exp(n-1, n);
            }
            n*n*exp(n-1, n); <
            {
                // TODO: Es el problema de exponentes con bases distintas
                assume n*n*exp(n-1, n) < exp(n,n+1);
            }
            exp(n,n+1);
        }
    }
}

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

lemma expGET1_Lemma(x:int,e:nat)
requires  x >= 1 
ensures exp(x,e) >= 1


lemma expGET1_Forall_Lemma()
ensures forall x:int, e:nat :: x >= 1 ==> exp(x,e) >= 1;


lemma prod_Lemma (a:int, b:int, c:int, d:int)
requires a >= b >= 1 && c > d >= 1
ensures a * c > b * d
// PRUEBA CONTRPOSITIVA
{
    if a*c <= b*d {
        // Para que se cumpla la condicion tiene que ocurrir una de estas cosas
        assert a <= b || c <= d;
        // Esto ultimo resulta en la precondicion negada
        assert !(a >= b >= 1 && c > d >= 1);
    }
}

// IMPORTANTE LEMA QUE DEMUESTRA LA MULTIPLICACION DE BASES CON EXPONENTES IGUALES 
lemma EqualExp_Lemma (b1:int,b2:int,e:nat)
ensures exp(b1,e)*exp(b2,e) == exp(b1*b2,e)
{
    if e==0 {}
    else{
        EqualExp_Lemma (b1, b2, e-1);
        assert exp(b1,e-1)*exp(b2,e-1) == exp(b1*b2,e-1);

        calc{
            exp(b1,e)*exp(b2,e);
            b1*b2*exp(b1, e-1)*exp(b2, e-1);
            {
                EqualExp_Lemma (b1, b2, e-1);
                assert exp(b1,e-1)*exp(b2,e-1) == exp(b1*b2,e-1);
            }
            b1*b2*exp(b1*b2,e-1);
            exp(b1*b2, e);
        }
        assert exp(b1,e)*exp(b2,e) == exp(b1*b2,e);
    }
}

lemma EqualBase_Lemma(b:int, e1:nat, e2:nat)
ensures exp(b, e1)*exp(b, e2)== exp(b, e1+e2)
{
    if e1==0{}
    else {
        EqualBase_Lemma(b, e1-1, e2);
        assert exp(b, e1-1)*exp(b, e2)== exp(b, e1-1+e2);

        calc{
            exp(b, e1)*exp(b, e2);
            b*exp(b, e1-1)*exp(b, e2);
            {
                EqualBase_Lemma(b, e1-1, e2);
                assert exp(b, e1-1)*exp(b, e2)== exp(b, e1-1+e2);
            }
            b*exp(b, e1-1+e2);
            exp(b, e1+e2);
        }
        assert exp(b, e1)*exp(b, e2)== exp(b, e1+e2);
    }
}
lemma nodiv3_Lemma (x:nat)
requires !div3(x)
ensures exists k:int :: x*x == 3*k+1
{// INDUCCION POR CASOSs
    if (x%3==1){
        var n:= (x-1)/3;
        assert x== 3*n+1;

        calc {
            x*x;
            (3*n+1)*(3*n+1);
            9*n*n+6*n+1;
            3*(3*n*n+2*n)+1;
        //  3     k      +1
        }
    }
    else{ // x%3==2
        var n:= (x-2)/3;
        assert x== 3*n+2;

        calc {
            x*x;
            (3*n+2)*(3*n+2);
            9*n*n+12*n+4;
            3*(3*n*n+4*n+1)+1; 
        //  3     k      +1
        }
    }
}

function s (n:nat):int
requires n >= 1
{
    if n == 1 then 5 
    else if n == 2 then 13 
    else 5 *s(n-1) - 6*s(n-2)
}

lemma serie_Lemma (n:nat)
requires n >= 1
ensures s(n) == exp(2,n) + exp(3,n)
// PRUEBA POR DOBLE INDUCCION
{
    if n==1 || n==2 {}
    else{
        serie_Lemma(n-1);
        assert s(n-1) == exp(2,n-1) + exp(3,n-1); // HI 1

        serie_Lemma(n-2);
        assert s(n-2) == exp(2,n-2) + exp(3,n-2); // HI 2

        calc{
            s(n);
            5*s(n-1) - 6*s(n-2);
            {
                serie_Lemma(n-1);
                assert s(n-1) == exp(2,n-1) + exp(3,n-1); // HI 1

                serie_Lemma(n-2);
                assert s(n-2) == exp(2,n-2) + exp(3,n-2); // HI 2
            }
            5*(exp(2,n-1) + exp(3,n-1)) - 6*(exp(2,n-2) + exp(3,n-2));
            5*exp(2,n-1) + 5*exp(3,n-1) - 6*exp(2,n-2) - 6*exp(3,n-2);
            5*exp(2,n-1) + 5*exp(3,n-1) - 3*2*exp(2,n-2) - 3*2*exp(3,n-2);
            5*exp(2,n-1) + 5*exp(3,n-1) - 3*exp(2,n-1) - 2*exp(3,n-1);
            2*exp(2,n-1) + 3*exp(3, n-1);
            exp(2,n) + exp(3, n);
        }
        assert s(n) == exp(2,n) + exp(3,n);
    }
}

lemma IFF_Lemma (n:int)
ensures (n*n)%2 == 0 <==> n%2 == 0
{
    if (n*n)%2==0 {
        Cuadr1_Lemma(n);
    }
    if n%2 == 0{
        Cuadr2_Lemma(n);
    }
    
}

lemma Cuadr1_Lemma(n:int)
requires (n*n)%2 == 0 
ensures n%2 == 0       
// PRUEBA CONTRAPOSITIVA
{
    if n%2!=0{
        var k:= (n-1)/2;
        assert n== 2*k+1;

        calc == {
            (n*n);
            (2*k+1)*(2*k+1);
            4*k*k+4*k+1;
            4*(k*k+k)+1;
        }
        assert (4*(k*k+k)+1)%2 !=0;
        assert (n*n)%2 !=0;
    }
}


//Prueba directa
lemma Cuadr2_Lemma(n:int)
requires n%2 == 0
ensures (n*n)%2 == 0
{
    var k:= n/2;
    assert n== 2*k;
    
    calc{
        n*n;
        2*k*2*k;
        4*k*k;
        2*(2*k*k);
    }
    assert (2*(2*k*k))%2==0;
}

lemma noExists_Lemma (x:int)
ensures !exists k:int :: 4*k + 3 == x*x
//ensures forall k:int :: 4*k + 3 != x*x
// PRUEBA POR CONTRADICCION CON REDUCCION AL ABSURDO
{
if exists k:int :: 4*k + 3 == x*x{
    var j :| 4*j + 3 == x*x;
    assert x*x == 2*(2*j+1) + 1;
    IFF_Lemma(x);
    //assert (x*x)%2 == 0 <==> x%2 == 0;
    assert x%2 != 0; //x%2 == 1
    var a := (x-1)/2; // x == 2*a + 1;
    assert  4*j + 3 == (2*a + 1)*(2*a + 1) 
                    == 4*a*a + 4*a + 1;
    assert 2 //== 3 - 1 
                == 4*a*a + 4*a - 4*j;
    assert 1 == 2*a*a + 2*a - 2*j == 2*(a*a + a -j);
    assert false;
    }
}

lemma RA_Lemma (n:nat)
requires (1+exp(-1,n))/2 != 0
ensures n%2 == 0
// PRUEBA CONTRAPOSITIVA
{
    if n%2 != 0 {
        var k := (n-1)/2;
        // Utilizo este lemma para demostrar que -1 multiplicado por si mismo un numero impar de veces es -1
        expodd_Lemma (k);
        assert (1+exp(-1,n)) ==  (1+exp(-1,2*k + 1)) == 1 + (-1) == 0;
        assert (1+exp(-1,n))/2 == 0;
}  
}

lemma expodd_Lemma (k:nat)
ensures exp(-1,2*k+1) == -1
// PRUEBA POR INDUCCION
{
    if (k==0){}
    else {
        expodd_Lemma (k-1);
        assert exp(-1,2*(k-1)+1) == -1;
        assert exp(-1,2*k-2+1) == -1;
        assert exp(-1,2*k-1) == -1;

        calc {
            exp(-1,2*k+1);
            -1*exp(-1,2*k);
            -1*-1*exp(-1,2*k-1);
            {
                expodd_Lemma (k-1);
                assert exp(-1,2*(k-1)+1) == -1;
                assert exp(-1,2*k-2+1) == -1;
                assert exp(-1,2*k-1) == -1;
            }
            -1*-1*-1;
            -1;
        }
        assert exp(-1,2*k+1) == -1;
    }
}


function abs(x:real):real { if x >= 0.0 then x else -x }


// VALORES LIMITE
lemma cases_Lemma(x:real)
ensures -5.0 <= abs(x+2.0) - abs(x-3.0) <= 5.0
{
    // PRUEBA POR CASOS 
    if x <= -2.0 {
        assert abs(x+2.0) - abs(x-3.0) 
                == -(x+2.0) - (-(x-3.0))
                == -x - 2.0 + x - 3.0
                == -2.0-3.0 == -5.0;
    }
    else if x >= 3.0 {
        assert abs(x+2.0) - abs(x-3.0) ==
                x+2.0 - x + 3.0 ==
                5.0;
        assert -5.0 <= 5.0 <= 5.0;
    }
    else{
        assert abs(x+2.0) - abs(x-3.0)  
                == x+2.0 - (-(x-3.0))
                == 2.0*x-1.0;
        assert -5.0 <= 2.0*x-1.0 <= 5.0;
    }
}

// TODO: No se como seguir y los que tengo resueltos no me ayudan mucho
lemma EcCuadDiv2_Lemma (x:int)
requires x >= 1
ensures (x*x + x)%2 == 0
{
    if x==1{}
    else{
        EcCuadDiv2_Lemma(x-1);
        assert ((x-1)*(x-1) + (x-1))%2 == 0; // HI

        calc ==> {
            (x*x-2*x+1 + x-1)%2 == 0;
            (x*x-x)%2 == 0; 
        }

        // Como la HI simplificada cumple con la postcondicion queda demostrado el lemma
        assert (x*x-x)%2==0; //HI simplificada

    }
}

lemma EcCubicaDiv6_Lemma (x:int)
requires x >= 1
ensures (x*x*x + 3*x*x + 2*x)%6 == 0
{
    if x==1{}
    else{
        EcCubicaDiv6_Lemma(x-1);
        assert ((x-1)*(x-1)*(x-1) + 3*(x-1)*(x-1) + 2*(x-1))%6 == 0; // HI*/

        // Simplificico la HI
        calc{
            ( x*x*x - 3*x*x + 3*x-1) + 3*(x-1)*(x-1) + 2*(x-1);
            ( x*x*x - 3*x*x + 3*x-1) + 3*(x*x-2*x+1) + 2*(x-1);
            x*x*x - 3*x*x + 3*x-1 + 3*x*x-6*x+3 + 2*x-2;
            x*x*x-x;
        }
        assert (x*x*x-x)%6==0; // HI simplificada

        // Simplifico la poscondicion
        assert x*x*x + 3*x*x + 2*x == (x*x*x-x)+3*(x*x+x);

        // El primer sumando del termino de la derecha se demuestra que x*x+x es multiplo de 2 mediante el 
        // lema local EcCuadDiv2_Lemma. 
        EcCuadDiv2_Lemma(x);
        assert (x*x+x)%2==0;

        // Al estar multiplicado por 3 tambien es multiplo de 3. 
        assert (3*(x*x+x)%2)%3==0;

        // Por lo que al ser multiplo de 2 y 3 tambien lo es de 6.
        assert (3*(x*x+x))%6==0;

        // Mediante la hipotesis de induccion podemos afirmar que
        assert (x*x*x-x)%6==0 && (3*(x*x+x))%6==0;
        
        // Por lo que al sumarlos seguiran siendo un multiplo de 6.
        assert ((x*x*x-x)+(3*(x*x+x)))%6==0;

        // Quedando de esta manera la propiedad inductiva demostrada.

    }
}