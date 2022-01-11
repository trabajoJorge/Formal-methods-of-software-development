<<<<<<< HEAD:Global/Apuntes/multisets.dfy

// Igual que los sets pero lo utilizamos para juntar secuencias y sets, transformandolos en una 
// estructura comun.
method test()
{
    assert (multiset{1,1,1} - multiset{1,1}) == multiset{1};
    assert(multiset{1,1} + multiset{1}) == multiset{1,1,1};

// Los multiset guardan el numero de apariciones de cada elemento
    var m:= multiset{2,2,1,2};
    assert m[2]==3;
    assert m[800]==0;

    // Dos multiset son iguales si tienen el mismo numero de veces los mismos numeros

    // !! → multiset disjuntos
    assert multiset([1,1]) == multiset{1,1};
    assert multiset({1,1}) == multiset{1};
    
=======

// Igual que los sets pero lo utilizamos para juntar secuencias y sets, transformandolos en una 
// estructura comun.
method test()
{
    assert (multiset{1,1,1} - multiset{1,1}) == multiset{1};
    assert(multiset{1,1} + multiset{1}) == multiset{1,1,1};

// Los multiset guardan el numero de apariciones de cada elemento
    var m:= multiset{2,2,1,2};
    assert m[2]==3;
    assert m[800]==0;

    // Dos multiset son iguales si tienen el mismo numero de veces los mismos numeros

    // !! → multiset disjuntos
    assert multiset([1,1]) == multiset{1,1};
    assert multiset({1,1}) == multiset{1};
    
>>>>>>> 4c5cf7c96f055678df6ce0d310ac420d7b8bd9e5:Parcial 2/Apuntes/multisets.dfy
}