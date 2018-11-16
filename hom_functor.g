LoadPackage( "ModulePresentations" );
LoadPackage( "RingsForHomalg" );
LoadPackage( "ComplexesForCAP" );
LoadPackage( "FrobeniusCategoriesForCAP" );
LoadPackage( "StableCategoriesForCAP" );

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
        local F, G, beta_trafo, cokernel_object;
        
        F := AsCapFunctor( Source( beta ) );
        G := AsCapFunctor( Range( beta ) );

        beta_trafo := AsCapNaturalTransformation( beta );
        
        cokernel_object := CapFunctor( Concatenation( "A cokernel in the category ", Name( CategoryOfAdditiveFunctorsBetweenAbelianCategories ) ), Source( F ), Range( F ) );

        AddObjectFunction( cokernel_object,
            function( X )
                return CokernelObject( ApplyNaturalTransformation( beta_trafo, X ) );
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
                return CokernelObjectFunctorialWithGivenCokernelObjects( obj1, ApplyNaturalTransformation( beta_trafo, obj1 ), ApplyFunctor( G, alpha ), ApplyNaturalTransformation( beta_trafo, obj2 ), obj2 );
        end );
        
        return AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories( C, D, cokernel_object );
        
    end );

    ##
    AddCokernelProjectionWithGivenCokernelObject( CategoryOfAdditiveFunctorsBetweenAbelianCategories,
      function ( beta, cokernel_object )
        local F, G, beta_trafo, cokernel_projection;
        
        F := AsCapFunctor( Source( beta ) );
        G := AsCapFunctor( Range( beta ) );

        beta_trafo := AsCapNaturalTransformation( beta );
        
        cokernel_projection := NaturalTransformation( G, AsCapFunctor( cokernel_object ) );
        AddNaturalTransformationFunction( cokernel_projection,
            function( S, X, T )
                return CokernelProjection( ApplyNaturalTransformation( beta_trafo, X ) );
        end );
        
        return AsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories( C, D, cokernel_projection );
        
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
        
        return CokernelColiftWithGivenCokernelObject( ApplyFunctor( F, P^(-1) ), ApplyFunctor( F, alpha ), L_0_F_X );
    end );

    return AsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories( S, T, beta );
end;



ProjectiveStabilizationOfFunctor := function( F )
    local beta;
    beta := L_0_morphism( F );
    return CokernelObject( beta );
end;

ProjectionOntoProjectiveStabilizationOfFunctor := function( F )
    local beta;
    beta := L_0_morphism( F );
    return CokernelProjection( beta );
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
