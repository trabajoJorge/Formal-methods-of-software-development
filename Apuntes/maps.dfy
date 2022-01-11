<<<<<<< HEAD:Global/Apuntes/maps.dfy
 method test() {
    var m := map[4 := 5, 5 := 6];
    assert m[4] == 5;

    var m1 := map["A" := 5, "a":= 6];
    assert m1["A"] == 5;

    // Coge solo la key
    assert 4 in m;
    assert 6 !in m;

    // La igualdad solo compara la ultima key y su valor
    assert map[3 := 5, 3 := 4] == map[3 := 4];
    //assert map[3 := 5, 3 := 4] != map[3 := 5]; 
    
    //Map list comprehension
    var m2 := map i | 0 <= i < 10 :: 2*i;
    var m3 := map[3 := 5, 4 := 6, 1 := 4];
    var l := map i | i in m3 && i != 3 :: m3[i];
    assert l == map[4:= 6, 1 := 4];
=======
 method test() {
    var m := map[4 := 5, 5 := 6];
    assert m[4] == 5;

    var m1 := map["A" := 5, "a":= 6];
    assert m1["A"] == 5;

    // Coge solo la key
    assert 4 in m;
    assert 6 !in m;

    // La igualdad solo compara la ultima key y su valor
    assert map[3 := 5, 3 := 4] == map[3 := 4];
    //assert map[3 := 5, 3 := 4] != map[3 := 5]; 
    
    //Map list comprehension
    var m2 := map i | 0 <= i < 10 :: 2*i;
    var m3 := map[3 := 5, 4 := 6, 1 := 4];
    var l := map i | i in m3 && i != 3 :: m3[i];
    assert l == map[4:= 6, 1 := 4];
>>>>>>> 4c5cf7c96f055678df6ce0d310ac420d7b8bd9e5:Parcial 2/Apuntes/maps.dfy
}