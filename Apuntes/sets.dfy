<<<<<<< HEAD:Global/Apuntes/sets.dfy

method ej1()
{

// **** SETS ****
/*Sets of various types form one of the core tools of verification for Dafny. Sets 
represent an orderless collection of elements, without repetition. Like sequences, 
sets are immutable value types. This allows them to be used easily in annotations, 
without involving the heap, as a set cannot be modified once it has been created.*/
    //var s1 := {}; // the empty set
    var s2 := {3, 2, 1}; // set contains exactly 1, 2, and 3
    assert s2 == {1,1,2,3,3,3,3}; // same as before
    assert s2 == {3,1,2,3,3,3,3}; // same as before
    var s3, s4 := {1,2}, {1,4};

    assert s2 + s4 == {1,2,3,4}; // set union
    assert s2 * s3 == {1,2} && s2 * s4 == {1}; // set intersection
    assert s2 - s3 == {3}; // set difference

    assert {1} <= {1, 2} && {1, 2} <= {1, 2}; // subset
    assert {} < {1, 2} && !({1} < {1}); // strict, or proper, subset
    assert !({1, 2} <= {1, 4}) && ({1, 4} <= {1, 4}); // no relation
    assert {1, 2} == {1, 2} && {1, 3} != {1, 2}; // equality and non-equality

    assert 5 in {1,3,4,5};
    assert 1 in {1,3,4,5};
    assert 2 !in {1,3,4,5};
    assert forall x:nat :: x !in {};

    //TODO: No entiendo porque no funciona
    //assert (set x | x in {0,1,2} :: x * 1) == {0,1,2};  //sets using a set comprehension
=======

method ej1()
{

// **** SETS ****
/*Sets of various types form one of the core tools of verification for Dafny. Sets 
represent an orderless collection of elements, without repetition. Like sequences, 
sets are immutable value types. This allows them to be used easily in annotations, 
without involving the heap, as a set cannot be modified once it has been created.*/
    //var s1 := {}; // the empty set
    var s2 := {3, 2, 1}; // set contains exactly 1, 2, and 3
    assert s2 == {1,1,2,3,3,3,3}; // same as before
    assert s2 == {3,1,2,3,3,3,3}; // same as before
    var s3, s4 := {1,2}, {1,4};

    assert s2 + s4 == {1,2,3,4}; // set union
    assert s2 * s3 == {1,2} && s2 * s4 == {1}; // set intersection
    assert s2 - s3 == {3}; // set difference

    assert {1} <= {1, 2} && {1, 2} <= {1, 2}; // subset
    assert {} < {1, 2} && !({1} < {1}); // strict, or proper, subset
    assert !({1, 2} <= {1, 4}) && ({1, 4} <= {1, 4}); // no relation
    assert {1, 2} == {1, 2} && {1, 3} != {1, 2}; // equality and non-equality

    assert 5 in {1,3,4,5};
    assert 1 in {1,3,4,5};
    assert 2 !in {1,3,4,5};
    assert forall x:nat :: x !in {};

    //TODO: No entiendo porque no funciona
    //assert (set x | x in {0,1,2} :: x * 1) == {0,1,2};  //sets using a set comprehension
>>>>>>> 4c5cf7c96f055678df6ce0d310ac420d7b8bd9e5:Parcial 2/Apuntes/sets.dfy
}