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
