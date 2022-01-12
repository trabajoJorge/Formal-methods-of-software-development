// APELLIDOS:
// NOMEBRE:
// ESPECIALIDAD:

// INDICACIONES GENERALES:
// 1.- Los lemmas que se pide probar pueden tener que utilizarse en otros ejercicios. Por tanto,
//     cada lema cuya prueba no hayas podido completar, debes dejar comentado todo el cuerpo del lemma
//     de modo que se pueda usar (en otros ejercicios), igual que un lema aún sin probar (equivale a un assume).
// 2.- Si en alguna expression la secuencia vacía [] te da problemas por la inferencia de tipos
//     puedes declarar 
//       var vac:seq<tipo-que interese> := []; 
//     y usar "vac", en lugar de [], en dichas expressiones. 

/////////////////////////////////////////////////////////////////////////////////////////////

// EJERCICIO 1: 
// Demostrar el lemma is_hill_Lemma (INDICACIÓN: probar por contradicción que se cumple down(s,|s|/2,|s|)),
// y después usarlo para demostrar el lemma is_hill_Lemma_Forall.

predicate palindromeBtw<T(==)> (s:seq<T>,i:int,j:int)
{
0 <= i <= j < |s| && forall k :: i <= k < j ==> s[k] == s[|s|-k-1]
}

predicate palindrome<T(==)> (s:seq<T>)
{
palindromeBtw(s,0,|s|/2)
}

predicate up (s:seq<int>,i:int,j:int)
{
0 <= i <=j < |s| && forall k :: i <= k < j ==> s[k] < s[k+1]
}

predicate down (s:seq<int>,i:int,j:int)
{
0 <= i <= j <= |s| && forall k :: i <= k < j-1 ==> s[k] > s[k+1]
}

predicate is_hill (s:seq<int>)
{
up(s,0,|s|/2)  && down(s,|s|/2,|s|)
}

lemma is_hill_Lemma(s:seq<int>)
requires |s| >= 1 &&  palindrome(s) && up(s,0,|s|/2)
ensures is_hill(s)
{
        if !(is_hill(s)){
                // Para no se hill tiene que estar desordenada la ultima parte de la secuencia
                assert !down(s,|s|/2,|s|);
                
                // Verifico que la que la 2ª parte esta ordenada
                assert exists k :: |s|/2 <= k < |s|-1 && s[k] <= s[k+1];
                // Asigno todos los valores posibles de k a la variable k
                var k :| |s|/2 <= k < |s|-1 && s[k] <= s[k+1];

                // Verifico que es palindromo
                assert s[k] == s[|s|-k-1];
                assert s[k+1] == s[|s|-(k+1)-1] == s[|s|-k-2];
                assert s[|s|-k-2] >= s[|s|-k-1]; //contradicción con up(s,0,|s|/2)
                assert false;
        }
}
// INDICACIÓN: probar por contradicción que se cumple down(s,|s|/2,|s|);


lemma is_hill_Lemma_Forall()
ensures forall s :: |s| >= 1 &&  palindrome(s) && up(s,0,|s|/2) ==> is_hill(s)
{
        forall s | |s| >= 1 &&  palindrome(s) && up(s,0,|s|/2)  {is_hill_Lemma(s);}
}
// EJERCICIO 2: 
// Poner los invariantes (usando los predicados de arriba) y 
// completar el method decideHill_VC con las condiciones de verificación que genera 
// la verificación del método decideHill
// INDICACIÓN: Para que una de las VC se verifique necesita una llamada a un lema del ejercicio 1.

method decideHill(s:seq<int>) returns (h:bool)
requires |s| >= 1
//ensures h <==> (is_hill(s) && palindrome(s)) //des-comentar una vez puestos los invariantes
{
        assert 0<= 0 <= |s|/2 && up(s, 0, 0) && palindromeBtw(s,0,0);
        var k := 0;
        assert 0<= k <= |s|/2 && up(s, 0, k) && palindromeBtw(s,0,k);
        while k < |s|/2 && s[k] == s[|s|-k-1] && s[k] < s[k+1]
                invariant 0<= k <= |s|/2
                invariant up(s, 0, k)
                invariant palindromeBtw(s,0,k)
                decreases |s|/2 - k
        {
                assert 0<= (k+1) <= |s|/2 && up(s, 0, (k+1)) && palindromeBtw(s,0,(k+1)); //1
                k := k + 1;
                assert 0<= k <= |s|/2 && up(s, 0, k) && palindromeBtw(s,0,k);
        }
        if k == |s|/2 { 
                is_hill_Lemma(s); 
        }
        h := (k == |s|/2); 
        assert 0<= k <= |s|/2 && up(s, 0, k) && palindromeBtw(s,0,k);
}

method decideHill_VC()
{
//is_hill_Lemma_Forall(); //des-comentar y poner delante de la VC que la necesita.
}

// EJERCICIO 3:
// Demostrar por inducción en s el lema multiplicity_Lemma.
// INDICACIÓN: Recuerda que puedes usar expresiones if-then-else como cualquier otra expresion.

function multiplicity<T(==)> (x:T,s:seq<T>):nat
decreases s
{
if s == [] then 0 
else if s[0] == x then 1 + multiplicity(x,s[1..])
else multiplicity(x,s[1..])
}

lemma multiplicity_Lemma<T(==)>(x:T,s:seq<T>)
ensures multiset(s)[x] == multiplicity(x,s)
decreases s
{
        if multiset(s)[x]==0 {}
        else{
                multiplicity_Lemma(x, s[1..]);
                assert multiset(s[1..])[x] == multiplicity(x,s[1..]);

                calc {
                        multiplicity(x,s);
                        if s[0] == x then 1 + multiplicity(x,s[1..]) else multiplicity(x,s[1..]);
                        (if s[0] == x then 1 else 0) + multiplicity(x,s[1..]);
                        {
                                multiplicity_Lemma(x, s[1..]);
                                assert multiset(s[1..])[x] == multiplicity(x,s[1..]); //HI
                        }
                        (if s[0] == x then 1 else 0) + multiset(s[1..])[x];
                        {
                                assert [s[0]] + s[1..] == s;
                                assert multiset{s[0]} + multiset(s[1..]) == multiset(s); 
                        }
                        multiset(s)[x];
                }
        }
}
// EJERCICIO 4: 
// Demostrar el lemma zipLength_Lemma por inducción en r y en s.
// Dafny lo prueba automáticamente, por eso tiene {:induction false}, no quitarlo
// y escribir detalladamente la HI y lo que se consigue a partir de la HI 
// INDICACIÓN: Si haces primero induccion en r, dentro del paso inductivo, debes hacer inducción en s

function min(a:int, b:int):int
{
if a <= b then a else b
}

function zip<T,S>(r:seq<T>, s:seq<S>): seq<(T,S)>
decreases r,s
{
if r == [] || s == []  then [] else [(r[0],s[0])] + zip(r[1..],s[1..])
}

lemma {:induction false} zipLength_Lemma<T,S>(r:seq<T>, s:seq<S>)
ensures |zip(r,s)| == min(|r|,|s|)
decreases r,s
{
        if |s| == 0  || |r|==0{}
        else {
                zipLength_Lemma(r[1..], s[1..]);
                assert |zip(r[1..],s[1..])| == min(|r[1..]|,|s[1..]|);

                calc == {
                        |zip(r,s)|;
                        {
                                assert zip(r,s) == [(r[0], s[0])] + zip(r[1..], s[1..]);
                        }
                        |[(r[0], s[0])] + zip(r[1..], s[1..])|;
                        1 + |zip(r[1..], s[1..])|; 
                        1 + min(|r[1..]|,|s[1..]|);
                        min(|r|,|s|);
                }
                assert |zip(r,s)| == min(|r|,|s|);
        }
}
//////////////// PARA REALIZAR EL RESTO DEL EXAMEN DEBES SABER QUE: 

// TIPOS POLOMÓRFICOS (T,S) Y seq<(T,S)> -- NOTACIÓN
// (T,S) es el tipo polimórfico de los pares (2-tuplas) 
// cuyo primer elemento es de tipo T 
// y su segundo elemento es de tipo S
// Si x:(T,S) entonces x.0 es el primer elemento del par y x.1 es el segundo.
// Por tanto, z:seq<(T,S)> es una secuencia de pares de elementos de tipo (T,S)
// para cualquier elemento z[i], z[i].0 es el primer elemento del par y z[i].1 es el segundo.
method ejemplos()
{
var p:(int,bool) := (25,true);
assert p.0 == 25 && p.1 == true;
var s:seq<(int,bool)> := [(25,true),(15,false),(1,true)];
assert s[0].0 == 25 && s[0].1 == true;
assert s[1].0 == 15 && s[1].1 == false;
assert s[2].0 == 1 && s[2].1 == true;
}

/////////////////////////////////////////////////////////////////////////////////////////////////

// EJERCICIO 5: 
// Prueba por contraposición el lemma unzip_Lemma.
// INDICACIÓN:  Puedes usar (SIN DEMOSTRAR) el siguiente lemma unzip_Distrib_Lemma.

function unzip<T,S> (z:seq<(T,S)>):(seq<T>,seq<S>)
decreases z
{
if z == []  then ([],[])
else ( [z[0].0] + unzip(z[1..]).0, [z[0].1] + unzip(z[1..]).1 )
}

lemma unzip_Distrib_np_Lemma<T,S>(r:seq<(T,S)>,s:seq<(T,S)>)
ensures unzip(r+s) == (unzip(r).0 + unzip(s).0, unzip(r).1 + unzip(s).1)
//NO DEMOSTRAR

lemma unzip_Lemma<T,S>(g:seq<(T,S)>,x:(T,S),z1:seq<T>,z2:seq<S>)
requires unzip(g) == (z1,z2)
ensures unzip(g + [x]) == (z1+[x.0], z2+[x.1])
// DEMOSTAR por contraposición
{
        if unzip(g + [x]) != (z1+[x.0], z2+[x.1]) {
                unzip_Distrib_np_Lemma(g,[x]);
                assert unzip(g) != (z1,z2) || unzip([x]) != ([x.0],[x.1]);
                
                var vac:seq<(T,S)> := [];  //Por la inferencia de tipos
                assert unzip(vac) == ([],[]);
                
                assert  [x.0] + [] == [x.0];
                assert  [x.1] + [] == [x.1];

                assert unzip([x]) == ([x.0],[x.1]);
                assert unzip(g) != (z1,z2);
        } 

}

// EJERCICIO 6: 
// Diseña un método compute_unzip iterativo que satisfaga la especificación:
// method compute_unzip<T,S>(z:seq<(T,S)>) returns (z1:seq<T>,z2:seq<S>)
// ensures unzip(z) == (z1,z2)
// a partir de los invariantes:
//      invariant z == g + r
//      invariant unzip(g) == (z1,z2)
// donde g es una variable ghost y "decreases r" prueba que la iteración termina.
// TENDRAS QUE ayudar con aserciones y llamando a unzip_Lemma, para que se verifique.

method compute_unzip<T,S>(z:seq<(T,S)>) returns (z1:seq<T>,z2:seq<S>)
ensures unzip(z) == (z1,z2)
// METODO UNZIP
{
        
        ghost var g:seq<(T,S)> := [];
        var r:= z;
        z1:= [];
        z2:= [];

        while r != [] 
                invariant z == g + r
                invariant unzip(g) == (z1,z2)
                decreases r
        {
                unzip_Lemma(g, (r[0].0, r[0].1), z1, z2);

                z1:= z1 + [r[0].0];
                z2:= z2 + [r[0].1];

                g:= g + [r[0]];
                r:=r[1..];
        }
        assert g == z;
}

//////////////////// EJERCICIOS EXTRA (HAZLOS SÓLO SI YA HAS HECHO TODOS LOS ANTERIORES)

// EJERCICIO 7: 
// Demostrar el lemma unzip_Distrib_Lemma por induccion en r.
// INDICACIÓN: En el caso inductivo, declarar al comienzo 
//             var <nombre-que-quieras> := r+s;
// y utilizar <nombre-que-quieras>, en lugar de r+s, para escribir los asserts y calculations.

lemma unzip_Distrib_Lemma<T,S>(r:seq<(T,S)>,s:seq<(T,S)>)
ensures unzip(r+s) == (unzip(r).0 + unzip(s).0, unzip(r).1 + unzip(s).1)
{
        if |r|==0 || |s|==0 {
                // TODO: Pero si una secuencia no tiene nada a parte de [] que puede ser??
                assume r==[] && s==[];
                assert unzip(r+s) == (unzip(r).0 + unzip(s).0, unzip(r).1 + unzip(s).1);
        }
        else {
                unzip_Distrib_Lemma(r[1..], s);
                assert unzip(r[1..]+s) == (unzip(r[1..]).0 + unzip(s).0, unzip(r[1..]).1 + unzip(s).1);
                assert unzip(r[1..]+s).0 == unzip(r[1..]).0 + unzip(s).0;
                assert unzip(r[1..]+s).1 == unzip(r[1..]).1 + unzip(s).1;
                var rs:= r+s;

                calc {
                        unzip(rs);
                        ( [rs[0].0] + unzip(rs[1..]).0, [rs[0].1] + unzip(rs[1..]).1 );
                        {
                                assert rs[1..]==r[1..]+s;
                        }
                        ( [rs[0].0] + unzip(r[1..]+s).0, [rs[0].1] + unzip(r[1..]+s).1 );
                        {
                                unzip_Distrib_Lemma(r[1..], s);
                                assert unzip(r[1..]+s) == (unzip(r[1..]).0 + unzip(s).0, unzip(r[1..]).1 + unzip(s).1);
                                assert unzip(r[1..]+s).0 == unzip(r[1..]).0 + unzip(s).0;
                                assert unzip(r[1..]+s).1 == unzip(r[1..]).1 + unzip(s).1;
                        }
                        ( [rs[0].0] + (unzip(r[1..]).0 + unzip(s).0), [rs[0].1] + (unzip(r[1..]).1 + unzip(s).1));
                        {
                                assert [rs[0].0] + (unzip(r[1..]).0 + unzip(s).0) ==  [rs[0].0] + unzip(r[1..]).0 + unzip(s).0;
                                assert [rs[0].1] + (unzip(r[1..]).1 + unzip(s).1) ==  [rs[0].1] + unzip(r[1..]).1 + unzip(s).1;
                        }
                        ( [rs[0].0] + unzip(r[1..]).0 + unzip(s).0 , [rs[0].1] + unzip(r[1..]).1 + unzip(s).1);
                        {
                                assert [rs[0].0] + unzip(r[1..]).0 == unzip(r).0;
                                assert [rs[0].1] + unzip(r[1..]).1 == unzip(r).1;
                        }
                        ( unzip(r).0 + unzip(s).0, unzip(r).1 + unzip(s).1);
                }
        }
}







