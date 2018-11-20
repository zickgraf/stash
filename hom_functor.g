LoadPackage( "ModulePresentations" );
LoadPackage( "RingsForHomalg" );
LoadPackage( "ComplexesForCAP" );
LoadPackage( "StableCategoriesForCAP" );
LoadPackage( "AbEnrichedFunctors" );

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
            return HomomorphismStructureOnObjects( M, N );
        end
    );
    
    AddMorphismFunction( Hom_M__,
        function( obj1, phi, obj2 )
            return HomomorphismStructureOnMorphisms( IdentityMorphism( M ), phi );
        end
    );
    
    return Hom_M__;
end;


DeclareAttribute( "ZerothDerivedFunctor",
        IsObjectInAbEnrichedFunctors );
DeclareAttribute( "ZerothDerivedFunctorMorphism",
        IsObjectInAbEnrichedFunctors );
DeclareAttribute( "ProjectiveStabilization",
        IsObjectInAbEnrichedFunctors );
DeclareAttribute( "ProjectionOntoProjectiveStabilization",
        IsObjectInAbEnrichedFunctors );

##
InstallMethod( ZerothDerivedFunctor,
        "TODO",
        [ IsObjectInAbEnrichedFunctors ],
        
  function( F )
    local S, T, L_0_F;
    
    # TODO: check that ZerothDerivedFunctor exists
    
    S := SourceCapCategory( F );
    T := SourceCapCategory( F );
    
    L_0_F := CapFunctor( "L_0(F)", S, T );

    AddObjectFunction( L_0_F,
        function( X )
            local P;
            # TODO: stabil?
            P := ProjectiveResolution( X );
            return CokernelObject( MyApplyFunctor( F, P^(-1) ) );
    end );
    
    AddMorphismFunction( L_0_F,
        function( obj1, alpha, obj2 )
            local A, B, P, Q;
            # TODO: this is probably wrong
            # TODO: stabil?
            A := Source( alpha );
            B := Range( alpha );
            P := ProjectiveResolution( A );
            Q := ProjectiveResolution( B );
            return CokernelObjectFunctorialWithGivenCokernelObjects( obj1, MyApplyFunctor( F, P^(-1) ), MyApplyFunctor( F, alpha ), MyApplyFunctor( F, Q^(-1) ), obj2 );
    end );
    
    return AsObjectInAbEnrichedFunctors( L_0_F );
end );

##
InstallMethod( ZerothDerivedFunctorMorphism,
        "TODO",
        [ IsObjectInAbEnrichedFunctors ],
        
  function( F )
    local L_0_F, S, T, beta;

    # TODO: check that ZerothDerivedFunctor exists
    
    L_0_F := ZerothDerivedFunctor( F );
    
    S := SourceCapCategory( F );
    T := SourceCapCategory( F );
    
    beta := NaturalTransformation( L_0_F, F );
    AddNaturalTransformationFunction( beta, function( L_0_F_X, X, F_X )
        local P, alpha;
        
        # TODO: stable
        P := ProjectiveResolution( X );
        alpha := EpimorphismFromSomeProjectiveObject( X );
        
        # TODO: is this always true?
        Assert( 0, IsEqualForObjects( Source( alpha ), Range( P^(-1) ) ) );
        
        return CokernelColiftWithGivenCokernelObject( MyApplyFunctor( F, P^(-1) ), MyApplyFunctor( F, alpha ), L_0_F_X );
    end );

    return AsMorphismInAbEnrichedFunctors( beta );
end );

##
InstallMethod( ProjectiveStabilization,
        "TODO",
        [ IsObjectInAbEnrichedFunctors ],
        
  function( F )
    local beta;

    # TODO: check that ZerothDerivedFunctor exists
    
    beta := ZerothDerivedFunctorMorphism( F );
    return CokernelObject( beta );
end );

##
InstallMethod( ProjectionOntoProjectiveStabilization,
        "TODO",
        [ IsObjectInAbEnrichedFunctors ],
        
  function( F )
    local beta;

    # TODO: check that ZerothDerivedFunctor exists
    
    beta := ZerothDerivedFunctorMorphism( F );
    return CokernelProjection( beta );
end );

test_function := function( phi )
  local S, T, F, pi;
    S := Source( phi );
    T := Range( phi );

    F := hom_functor( S );
    pi := ProjectionOntoProjectiveStabilization( AsObjectInAbEnrichedFunctors( F ) );
    
    return IsZero( PreCompose( InterpretMorphismAsMorphismFromDinstinguishedObjectToHomomorphismStructure( phi ), MyApplyNaturalTransformation( pi, T ) ) );
end;

lp := LeftPresentations( R );

SetTestFunctionForStableCategories( lp, test_function );
stable_cat := StableCategory( lp );
Finalize( stable_cat );

Display( IsZero( AsStableMorphism( IdentityMorphism( FreeLeftPresentation( 1, R ) ) ) ) );
