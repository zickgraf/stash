LoadPackage( "GeneralizedMorphismsForCAP" );
LoadPackage( "ModulePresentationsForCAP" );

ZZ := HomalgRingOfIntegers();
ZZ_1 := FreeLeftPresentation( 1, ZZ );

M := HomalgMatrix( "[ 2 ]", 1, 1, ZZ );
times_2 := PresentationMorphism( ZZ_1, M, ZZ_1 );

M := HomalgMatrix( "[ 3 ]", 1, 1, ZZ );
times_3 := PresentationMorphism( ZZ_1, M, ZZ_1 );

M := HomalgMatrix( "[ 6 ]", 1, 1, ZZ );
times_6 := PresentationMorphism( ZZ_1, M, ZZ_1 );

M := HomalgMatrix( "[ 0 ]", 1, 1, ZZ );
times_0 := PresentationMorphism( ZZ_1, M, ZZ_1 );

times_2_gen := AsGeneralizedMorphismBySpan( times_2 );
times_3_gen := AsGeneralizedMorphismBySpan( times_3 );
times_6_gen := AsGeneralizedMorphismBySpan( times_6 );
times_0_gen := AsGeneralizedMorphismBySpan( times_0 );

lift1 := PreCompose( times_3_gen, PseudoInverse( times_2_gen ) );
lift2 := PreCompose( times_6_gen, PseudoInverse( times_2_gen ) );
lift3 := PreCompose( times_0_gen, PseudoInverse( times_0_gen ) );

HonestRepresentative( lift2 );
