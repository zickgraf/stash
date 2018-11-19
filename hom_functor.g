LoadPackage( "ModulePresentations" );
LoadPackage( "RingsForHomalg" );
LoadPackage( "ComplexesForCAP" );
LoadPackage( "StableCategoriesForCAP" );
Read("CategoryOfAdditiveFunctorsBetweenAbelianCategories.g");
Read("L_0.g");
Read("ProjectiveStabilizationOfFunctor.g");

R := HomalgFieldOfRationalsInSingular() * "x,y,z";;
cat := LeftPresentations( R );

R_1 := FreeLeftPresentation( 1, R );

m := HomalgMatrix( "[ x, y, z ]", 3, 1, R );
M := AsLeftPresentation( m );

n := HomalgMatrix( "[ x*y,y,z,y*x*z,x,-y,y*z,x ]", 4, 2, R );
N := AsLeftPresentation( n );

# The functor Hom( M, _ )
hom_functor := function( M )
    local Hom_M__;
    
    Hom_M__ := CapFunctor( "Hom(M,_)", cat, cat );
    
    AddObjectFunction( Hom_M__,
        function( N )
            return InternalHomOnObjects( M, N );
        end
    );
    
    AddMorphismFunction( Hom_M__,
        function( obj1, phi, obj2 )
            return InternalHomOnMorphisms( IdentityMorphism( M ), phi );
        end
    );
    
    return Hom_M__;
end;

test_function := function( phi )
  local B, C, u, A, F, pi, F__, coker;
    A := TensorUnit( CapCategory( phi ) );
    B := Source( phi );
    C := Range( phi );
    u := LeftUnitor( B );

    F := hom_functor( B );
    pi := AsCapNaturalTransformation( ProjectionOntoProjectiveStabilizationOfFunctor( F ) );
    F__ := Source( pi );
    coker := ApplyFunctor( F__, M );
    
    return IsZero( PreCompose( TensorProductToInternalHomAdjunctionMap( A, B, PreCompose( u, phi ) ), ApplyNaturalTransformation( pi, C ) ) );
end;

lp := LeftPresentations( R );

SetTestFunctionForStableCategories( lp, test_function );
stable_cat := StableCategory( lp );
Finalize( stable_cat );

Display( IsZero( AsStableMorphism( IdentityMorphism( FreeLeftPresentation( 1, R ) ) ) ) );
