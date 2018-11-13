LoadPackage( "ModulePresentations" );
LoadPackage( "RingsForHomalg" );
LoadPackage( "ComplexesForCAP" );

R := HomalgFieldOfRationalsInSingular()*"x,y,z";;
cat := LeftPresentations( R );
chains := ChainComplexCategory( cat );

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

m := HomalgMatrix( "[ x, y, z ]", 3, 1, R );
M := AsLeftPresentation( m );

# n := HomalgMatrix( "[ [ w, t, 0, z ], [ x*y, w, s, s ] ]", 2, 4, R );
n := HomalgMatrix( "[ x*y,y,z,y*x*z,x,-y,y*z,x ]", 4, 2, R );

N := AsLeftPresentation( n );

P := ProjectiveResolution( N );

d_neg_1 := P^(-1);

Display( P );





L_0 := function( F )
    local S, T, L_0_F;
    
    S := AsCapCategory( Source( F ) );
    T := AsCapCategory( Range( F ) );
    
    L_0_F := CapFunctor( "L_0(F)", S, T );

    AddObjectFunction( L_0_F,
        function( X )
            local P;
            # TODO: stabil?
            P := ProjectiveResolution( X );
            return CokernelObject( ApplyFunctor( F, P^(-1) ) );
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
            return CokernelObjectFunctorialWithGivenCokernelObjects( obj1, ApplyFunctor( F, P^(-1) ), ApplyFunctor( F, alpha ), ApplyFunctor( F, Q^(-1) ), obj2 );
    end );
    
    return L_0_F;
end;


DeclareCategory( "IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories",
                 IsCapCategoryObject );
DeclareCategory( "IsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories",
                 IsCapCategoryMorphism );
DeclareAttribute( "AsCapFunctor",
        IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
DeclareAttribute( "AsCapNaturalTransformation",
        IsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
DeclareOperation( "AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories",
        [ IsCapCategory, IsCapCategory, IsCapFunctor ] );
DeclareOperation( "AsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories",
        [ IsCapCategory, IsCapCategory, IsCapNaturalTransformation ] );

# TODO cache
CategoryOfAdditiveFunctorsBetweenAbelianCategories := FunctionWithCache( function( C, D )
    local CategoryOfAdditiveFunctorsBetweenAbelianCategories;
    
    CategoryOfAdditiveFunctorsBetweenAbelianCategories := CreateCapCategory( Concatenation( "Category of additive functors between \"", Name( C ), "\" and \"", Name( D ), "\"" ) );
    
    SetIsAbelian( CategoryOfAdditiveFunctorsBetweenAbelianCategories, true );
    
    DisableAddForCategoricalOperations( CategoryOfAdditiveFunctorsBetweenAbelianCategories );
    
    AddObjectRepresentation( CategoryOfAdditiveFunctorsBetweenAbelianCategories, IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
    
    AddMorphismRepresentation( CategoryOfAdditiveFunctorsBetweenAbelianCategories, IsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
    
    ##
    AddCokernelObject( CategoryOfAdditiveFunctorsBetweenAbelianCategories,
      function ( beta )
        local F, G, cokernel_object;
        
        F := AsCapFunctor( Source( beta ) );
        G := AsCapFunctor( Range( beta ) );
        
        cokernel_object := CapFunctor( Concatenation( "A cokernel in the category ", Name( CategoryOfAdditiveFunctorsBetweenAbelianCategories ) ), Source( F ), Range( F ) );

        AddObjectFunction( cokernel_object,
            function( X )
                return CokernelObject( ApplyNaturalTransformation( beta, X ) );
        end );
        
        AddMorphismFunction( cokernel_object,
            function( obj1, alpha, obj2 )
                local A, B, P, Q;
                # TODO: this might be wrong
                # TODO: stabil?
                A := Source( alpha );
                B := Range( alpha );
                P := ProjectiveResolution( A );
                Q := ProjectiveResolution( B );
                return CokernelObjectFunctorialWithGivenCokernelObjects( obj1, ApplyNaturalTransformation( beta, obj1 ), ApplyFunctor( G, alpha ), ApplyNaturalTransformation( G, obj2 ), obj2 );
        end );
        
        return cokernel_object;
        
    end );

    Finalize( CategoryOfAdditiveFunctorsBetweenAbelianCategories );

    return CategoryOfAdditiveFunctorsBetweenAbelianCategories;
end );
    
InstallMethod( AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories,
        "TODO",
        [ IsCapCategory, IsCapCategory, IsCapFunctor ],
        
  function ( C, D, F )
    local object, cat;
    
    # TODO: test: F is a functor from C to D
    
    object := rec( );

    cat := CategoryOfAdditiveFunctorsBetweenAbelianCategories( C, D );
    
    ObjectifyObjectForCAPWithAttributes( object, cat,
            AsCapFunctor, F
    );
    
    return object;
    
end );

##
InstallMethod( AsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories,
        "TODO",
        [ IsCapCategory, IsCapCategory, IsCapNaturalTransformation ],
        
  function ( C, D, natural_transformation )
    local morphism, cat;

    # TODO: test: Source and Range of natural_transformation are functors from C to D
    
    morphism := rec( );

    cat := CategoryOfAdditiveFunctorsBetweenAbelianCategories( C, D );
    
    ObjectifyMorphismForCAPWithAttributes( morphism, cat,
        AsCapNaturalTransformation, natural_transformation,
        Source, AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories( C, D, Source( natural_transformation ) ),
        Range, AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories( C, D, Range( natural_transformation ) )
    );
    
    return morphism;
    
end );


L_0_morphism := function( F )
    local L_0_F, S, T, beta;
    L_0_F := L_0( F );
    
    S := AsCapCategory( Source( F ) );
    T := AsCapCategory( Range( F ) );
    
    beta := NaturalTransformation( L_0_F, F );
    AddNaturalTransformationFunction( beta, function( L_0_F_X, X, F_X )
        local P, alpha;
        
        # TODO: stable
        P := ProjectiveResolution( X );
        alpha := EpimorphismFromSomeProjectiveObject( X );
        
        # TODO: is this always true?
        Assert( 0, IsEqualForObjects( Source( alpha ), Range( P^(-1) ) ) );
        
        return CokernelColiftWithGivenCokernelObject( ApplyFunctor( F, P^(-1) ), ApplyFunctor( alpha ), L_0_F_X );
    end );

    return AsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories( S, T, beta );
end;



ProjectiveStabilizationOfFunctor := function( F )
    local beta;
    beta := L_0_morphism( F );
    return CokernelObject( beta );
end;





F := hom_functor( M );
F__ := ProjectiveStabilizationOfFunctor( F );
Display( ApplyFunctor( F__, N ) );







# Tensor_product_with_M_in_chains := ExtendFunctorToChainComplexCategoryFunctor( tensor_functor( M ) );
# hom_to_N := hom_functor( N );
# Hom_Obj_N_from_cochains_to_cochains := ExtendFunctorToCochainComplexCategoryFunctor( hom_to_N );
# Hom_Obj_N_from_chains_to_cochains := 
#     PreCompose( ChainCategoryToCochainCategoryOfOppositeCategory( cat ), Hom_Obj_N_from_cochains_to_cochains );

# quit;

# Very important
# CM := StalkChainComplex( M, 0 );
# P := ProjectiveResolution( CM );
# lambdas := List( [ 2 .. ActiveUpperBound( P ) ], i-> KernelEmbedding( P^(i-1) ) );
# kappas  := List( [ 2 .. ActiveUpperBound( P ) ], i-> KernelLift( P^(i-1), P^i ) );
# List( kappas, IsEpimorphism );
# hom_P := ApplyFunctor( Hom_Obj_N_from_chains_to_cochains, P );
# SetLowerBound( hom_P, -1 );
# SetUpperBound( hom_P, ActiveUpperBound( P ) );
# IsWellDefined( hom_P, -1, ActiveUpperBound( P ) );
# 
# hom_lambdas := List( lambdas, l -> ApplyFunctor( hom_to_N, Opposite( l ) ) );
# hom_kappas := List( kappas, k -> ApplyFunctor( hom_to_N, Opposite( k ) ) );
# # The following list should contain only true's
# List( hom_kappas, IsMonomorphism );
# # The following two lists are supposed to be equals
# List( hom_lambdas, IsEpimorphism );
# List( [ 2 .. ActiveUpperBound( P ) ], i-> IsExactInIndex( hom_P, i ) );
# pres := List( [ 2 .. ActiveUpperBound( P ) ], i-> PreCompose( hom_kappas[i-1], hom_P^(i) ) );
# # The output should be true
# ForAll( pres, IsZeroForMorphisms );
# l := List( [ 2 .. ActiveUpperBound( P ) ], i -> KernelLift( hom_P^(i), hom_kappas[ i-1 ] ) );
# # The list should contain only true's
# List( l, f-> IsIsomorphism( f ) );
