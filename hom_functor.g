LoadPackage( "ModulePresentationsForCAP" );
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
    
    Hom_M__ := CapFunctor( "Hom(M,_)", CapCategory( M ), CapCategory( M ) );
    
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

test_function_via_hom_functor := function( phi )
  local S, T, F, pi;
    S := Source( phi );
    T := Range( phi );

    F := hom_functor( S );
    pi := ProjectionOntoProjectiveStabilization( AsObjectInAbEnrichedFunctors( F ) );
    
    return IsZero( PreCompose( InterpretMorphismAsMorphismFromDinstinguishedObjectToHomomorphismStructure( phi ), MyApplyNaturalTransformation( pi, T ) ) );
end;

test_function_via_lift := function( phi )
  local M, N, alpha, Q_0;
    
    M := Source( phi );
    N := Range( phi );
    
    alpha := EpimorphismFromSomeProjectiveObject( N );
    
    Q_0 := Source( alpha );
    
    return Lift( phi, alpha ) <> fail;
end;

lp := LeftPresentations( R );

SetTestFunctionForStableCategories( lp, test_function_via_lift );
stable_cat := StableCategory( lp );
Finalize( stable_cat );

Display( IsZero( AsStableMorphism( IdentityMorphism( N ) ) ) );
Display( IsZero( AsStableMorphism( IdentityMorphism( M ) ) ) );
Display( IsZero( AsStableMorphism( IdentityMorphism( R_1 ) ) ) );

LoadPackage("Modules");

input_stream := InputTextFile( "/dev/urandom" );
initial_seed := Sum( List( [ 1 .. 6 ], i -> ReadByte( input_stream ) * 256^( i - 1 ) ) );

fuzz := function()
  local ZZ, gens, i, j, k, l, M, N, matrices, random_matrix, phi, id;

    ZZ := HomalgRingOfIntegers();
    
    gens := [];
    
    # while IsEmpty( gens ) do
        i := Random( 1, 5 );
        j := Random( i, 10 );
        # k := Random( 0, 10 );
        # l := Random( 0, 10 );
        i := 1;
        j := i+5;
        # 
        M := HomalgMatrix( List( [ 1 .. i ], x -> List( [ 1 .. j ], j -> Random( -2^40, 2^40 ) ) ), i, j, ZZ );
        # 
        # N := RandomMatrix( k, l, ZZ );
        # 
        # gens := GetGenerators( Hom( LeftPresentation( M ), LeftPresentation( N ) ) );
        # matrices := List( gens, g -> MatrixOfMap( g ) );
        # 
        # random_matrix := Sum( matrices, m -> Random( 0, 10 ) * m );

    # od;

    # Display( "random matrix found" );
    Display( M );
    
    # phi := PresentationMorphism( AsLeftPresentation( M ), random_matrix, AsLeftPresentation( N ) );
    id := IdentityMorphism( AsLeftPresentation( M ) );
    
    # Display( "ensure well-definedness" );
    
    # Assert( 0, IsWellDefined( phi ) );

    Display( "ensure equality if test functions" );
    
    # Assert( 0, test_function_via_hom_functor( phi ) = test_function_via_lift( phi ) );
    # Assert( 0, test_function_via_hom_functor( id ) = test_function_via_lift( id ) );

    Display( test_function_via_lift( id ) );

    # Error("asd");
end;


seed := initial_seed;

while true do

	Display( seed );
	
	Reset( GlobalMersenneTwister, seed );

    fuzz();

	seed := Random( [ 0 .. 256^6 - 1 ] );
	
od;
