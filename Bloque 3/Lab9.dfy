method pruebas()
{
    var a: array<int>;

    a := new int[6](i => 0);
    assert a[3] == 0;
    assert forall k :: 0 <= k < 6 ==> a[k] == 0;

    a := new int[6](_ => 0);

    a := new int[6](i => i*2);
    assert a[3] == 6;
    assert forall k :: 0 <= k < 6 ==> a[k] == k*2;

    a := new int[6](i requires i>=0 =>  if i%2 == 0 then 5 else 7);

    a := new int[6](i requires i >=0 => f(i));
    assert a[2] == 1;
    assert a[3] == 1;
    assert a[1] == 0; 

    a := new int[6](g);
    assert a[2] == 2;
    assert a[3] == 2;
    assert a[1] == 1;
}

function method f(i:int):int
requires i >= 0
{
    if i%2 == 0 then i/2 else (i-1)/2
}

function method g(i:int):int
requires i >= 0
{
    if i%2 == 0 then (i/2)+1 else (i+1)/2
}

// Crear un array a partir de una secuencia
method arrayFromSeq<T>(s:seq<T>) returns (a:array<T>)
ensures a[..] == s
ensures fresh(a)
{
    a := new T[|s|](i requires 0 <= i < |s| => s[i]);
}


// Mínimo elemento de un array (Bucle e Invariantes)
method Min(a:array<int>) returns (m:int)
requires a.Length > 0
ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
ensures m in a[..] // a[..] == a[..a.Length] //a[..]:seq<int>
{
    var i:=0;
    m:= a[0];
    while i<a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> m <= a[j]
        invariant m in a[..]
        decreases a.Length - i
    {
        if (m>a[i]) {
            m:=a[i];
        }
        i:=i+1;
    }
}

//incrementar todos los elementos de un array

method add (v1:array<int>, c:int) returns (v2:array<int>)
ensures v2 == v1
ensures forall i :: 0 <= i < v1.Length ==> v1[i] == old(v1[i])+c
modifies v1
{
    var i:= 0;

    while i < v1.Length 
        invariant 0 <= i <= v1.Length
        invariant forall j :: i <= j < v1.Length ==> v1[j] == old(v1[j])
        invariant forall j :: 0 <= j < i ==> v1[j] == old(v1[j])+c
    {
        v1[i] := v1[i]+c;
        i:=i+1;
    }
    return v1;
}


//suma de componentes de un array
function sum (s:seq<int>):int
{
if s == [] then 0 else s[0] + sum(s[1..])
}

lemma sum_Lemma(s:seq<int>, i:nat)
requires 0 <= i < |s|
ensures sum(s[..i]) + s[i] == sum(s[..i+1])
{ 
    // FIJATE SIEMPRE EN QUE VARIABLE ES MAS FÁCIL HACER INDUCCION
    if i == 0 {}
    else {
        sum_Lemma(s, i-1);
        assert sum(s[..i-1]) + s[i-1] == sum(s[..i-1+1]);
        assert sum(s[..i-1]) + s[i-1] == sum(s[..i]);

        calc {
            sum(s[..i]) + s[i];
            {
                sum_Lemma(s, i-1);
                assert sum(s[..i-1]) + s[i-1] == sum(s[..i-1+1]);
                assert sum(s[..i-1]) + s[i-1] == sum(s[..i]);
            }
            sum(s[..i-1]) + s[i-1] + s[i];
            {
                assert sum(s[..i-1]) + s[i-1] == sum(s[..i]);
            }   
            sum(s[..i]) + s[i];
            {
                lemma_asociative_sum(s[..i], s[i]);
                assert sum(s[..i]) + s[i] == sum(s[..i] + [s[i]]);
            }
            sum(s[..i] + [s[i]]);
            {
                assert s[..i] + [s[i]] == s[..i+1];
            }
            sum(s[..i+1]);
        }
    }
}

// TODO: No me sale y por tanto no puedo demsotrar el de arriba
lemma lemma_asociative_sum(s:seq<int>, i:int)
ensures sum(s) + i == sum(s + [i])

method addInFirst(a:array<int>) 
modifies a
requires a.Length > 0
ensures a[0] == sum(old(a[..]))
ensures forall i :: 1 <= i < a.Length ==> a[i] == old(a[i])



// METODO DE LA BANDERA HOLANDESA
predicate perm<T>(s:seq<T>,r:seq<T>)
{
multiset(s) == multiset(r)
}

// The Dutch Flag Problem: A classification problem
datatype Color = Red | White | Blue // horizontal tricolour (red is up)

predicate bellow(c:Color, d:Color)
{
c == Red  || c == d || d == Blue
}
method DutchFlag(a:array<Color>) 
	modifies a
	ensures forall i, j :: 0 <= i < j < a.Length ==> bellow(a[i],a[j])
	ensures perm(a[..],old(a[..]))  
    {
        var l, m, h:= 0, 0, a.Length;
        while m<h 
            invariant 0 <= l <= m <= h <= a.Length
            invariant forall i :: 0 <= i < l ==> a[i] == Red
            invariant forall i :: l <= i < m ==> a[i] == White
            invariant forall i :: h <= i < a.Length ==> a[i] == Blue
            invariant perm(a[..],old(a[..]))
            decreases h-m
        {
            if a[m] == Red {
                a[l], a[m] := a[m], a[l];
                m:= m+1;
                l:=l+1;
            }
            else if a[m] == White {
                m:=m+1;
            }
            else { // a[m] == Blue
                a[m], a[h-1] := a[h-1], a[m];
                h:=h-1;
            }
        }
    }

// EJERCICIO PARA CASA: (Aplicación de la bandera holandesa) 
// Re-colocar (clasificar) los elementos de un array, poniendo los pares primero (a la izda)
// y los impares despues

predicate ord(x:nat,y:nat)
{
x%2==0 || (x%2==0 <==> y%2==0)|| y%2!=0
}

// TODO: Esto esta explicado como el culo
method partitionEvenOdd(a:array<nat>)
modifies a
ensures perm(a[..],old(a[..]))
ensures forall i,j :: 0 <= i < j < a.Length ==> ord(a[i],a[j])
{
    var f, l := 0, a.Length-1; //first untouched, last untouched

    if a.Length <= 1 {return;}
    //ya está sorteado, podemos suponer a.Length >= 2 para el resto.

    while f < l 
        decreases l - f;
        invariant 0 <= f <= l < a.Length
        invariant perm(a[..],old(a[..]))
        invariant forall i :: 0 <= i < f ==> a[i]%2 == 0
        invariant forall i :: l+1 <= i < a.Length ==> a[i]%2 == 1
    {
        if(a[f]%2 == 0){
            f := f + 1;
        } else {
            //assert a[f] %2 == 1;
            a[f], a[l] := a[l], a[f];
            l := l - 1;
        }
    }
}


/*
BUBBLE SORT 

First (i = 1)
( 5 1 4 2 3 ) ===> ( 1 5 4 2 3 ) Swap since 5 > 1.

Second (i = 2)
( 1 5 4 2 3 ) ===> ( 1 4 5 2 3 ) Swap since 5 > 4

Third (i = 3)
        j                j                j
( 1 4 5 2 3 ) ===> ( 1 4 2 5 3 ) ===> ( 1 2 4 5 3 ) 
                Swap since 5 > 2   Swap since 4 > 2

Fourth (i = 4)
( 1 2 4 5 3 ) ===> ( 1 2 4 3 5 ) ===> ( 1 2 3 4 5 )
                Swap since 5 > 3   Swap since 4 > 3

*/

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
//forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]  
}


method bubbleSort (a:array<int>)
requires a.Length > 0
ensures sortedArray(a)
ensures perm(a[..],old(a[..]))
modifies a
{
var i := 1;
while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sortedBetween(a,0,i)
    invariant perm(a[..],old(a[..]))
    decreases a.Length - i
    {
    pushLeft(a,i);
    //assert sortedBetween(a,0,i+1);
    i := i + 1; 
    //assert sortedBetween(a,0,i);
    }

}

method pushLeft (a:array<int>,index:nat)
requires 1 <= index < a.Length
requires sortedBetween(a,0,index)
ensures sortedBetween(a,0,index+1)
ensures perm(a[..],old(a[..]))
modifies a
{
var j := index;
while j > 0 && a[j-1] > a[j]
    invariant 0 <= j <= index
    invariant sortedBetween(a,0,j)
    invariant sortedBetween(a,j,index+1)
    //INV1 abajo: comentarlo para ver la necesidad en el assert del principio del while
    invariant 0 < j < index ==> a[j-1] <= a[j+1]
    //INV2 abajo: es más fuerte que INV1 pero también se satisface (usar INV1 o INV2, no los dos)
    //invariant forall k, k' :: 0 <= k <= j && j < k' <= index ==> a[k] <= a[k'];
    invariant perm(a[..],old(a[..]))
    decreases j
    {
    /*
    //primero se ve que el assert de abajo si se pone assume, va bien, pero al pasar a assert: 
    assert a[j] <= a[j-1]     //esto se cumple por la condicción del while
            && 
            (0 < j < index ==> a[j-1] <= a[j+1]) //assertion violation, no se puede probar porque
                                                    //lo que dice el invariante:
                                                    //sortedBetween(a,0,j) && sortedBetween(a,j,index+1)
                                                    //no relaciona a[j-1] con a[j+1] ==> poner INV1
                                                    //que en realidad la cumplen 
                                                    //los elementos a[..j] con a[j+1..index] 
                                                    // ==> opcionalmente se podría poner INV2
            &&
            forall i, k :: j < i < k < index + 1 ==> a[i] <= a[k]; 
            //este forall se cumple por sortedBetween(a,j,index+1) (en el invariante)
    */
    a[j-1],a[j] := a[j],a[j-1];

    //assert a[j-1] <= a[j] && (0 < j < index ==> a[j] <= a[j+1]) &&
    //       forall i, k :: j < i < k < index + 1 ==> a[i] <= a[k];  
    //assert forall i, k :: j-1 <= i < k < index+1 ==> a[i] <= a[k];
    //assert sortedBetween(a,j-1,index+1);
    j := j - 1;
    //assert sortedBetween(a,j,index+1);
    }
}

// METHOD MAIN PARA GENERAR UN EJECUTABLE
//crear un array a partir de una secuencia
method arrayFromSeq2<T>(s:seq<T>) returns (a:array<T>)
ensures a[..] == s
ensures fresh(a)
{
a := new T[|s|](i requires 0 <= i < |s| => s[i]);
}

method printArray<T> (a:array<T>)
{
var i := 0;
while i < a.Length {print a[i]; i := i+1;}   
}

method Main()   //Main con mayúscula
{
var s := [5,7,2,3,8,5,4,1,2,9,7,5,4,6,5,2,1,9,7,1,3,4,6,8,1,5,4,3,9,9,8,8,7];
var a := arrayFromSeq2(s);
printArray(a);
print "\n";
bubbleSort(a);
printArray(a);
print "\nfin";
}

/* Estos son los parámetros de mi PC de sobremesa con los que "Compile and Run" funciona perfectamente:
//verifyAllModules /compile:1 /spillTargetCode:3 /compileTarget:cs /out:bin\.....

Sospecho que ni mi portátil ni los PCs del Laboratorio 02 estaban bien configurados.

Entrad en 
Settings>Extensions>Dafny Extension Configuration>Dafny: Compiler Args>Edit in settings.json
y poned:
    "dafny.compilerArgs": [
        "/verifyAllModules",
        "/compile:1",
        "/spillTargetCode:3",
        "/compileTarget:cs"
    ],
    
Igual todo no es necesario, por ejemplo no usamos módulos, pero así os quedará configurado todo.
Esto es lo que me muestra a mi:
PS C:\Users\jiplucap\Desktop> & "C:\Program Files\dotnet\dotnet.EXE" 
"c:\Users\jiplucap\.vscode\extensions\correctnesslab.dafny-vscode-2.0.2\out\resources\dafny\Dafny.dll" 
"c:\Users\jiplucap\Desktop\BubbleSort.dfy" /verifyAllModules /spillTargetCode:3 /compile:3 /out:bin\BubbleSort

Dafny program verifier finished with 10 verified, 0 errors
Wrote textual form of target program to BubbleSort.cs
Running...

572385412975465219713468154399887
111122233344445555566777788889999
fin


