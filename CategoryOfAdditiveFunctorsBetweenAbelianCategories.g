DeclareCategory( "IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories",
                 IsCapCategoryObject );
DeclareCategory( "IsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories",
                 IsCapCategoryMorphism );

DeclareAttribute( "AsCapFunctor",
        IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
DeclareAttribute( "SourceCapCategory",
        IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
DeclareAttribute( "RangeCapCategory",
        IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
DeclareAttribute( "ZerothDerivedFunctor",
        IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
DeclareAttribute( "ZerothDerivedFunctorMorphism",
        IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
DeclareAttribute( "ProjectiveStabilization",
        IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
DeclareAttribute( "ProjectionOntoProjectiveStabilization",
        IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories );

DeclareAttribute( "AsCapNaturalTransformation",
        IsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories );

DeclareAttribute( "AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories",
        IsCapFunctor );
DeclareAttribute( "AsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories",
        IsCapNaturalTransformation );

BindGlobal( "MyApplyFunctor", function( F, A )
    if IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories( F ) then
        return ApplyFunctor( AsCapFunctor( F ), A );
    else
        return ApplyFunctor( F, A );
    fi;
end );

BindGlobal( "MyApplyNaturalTransformation", function( N, A )
    if IsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories( N ) then
        return ApplyNaturalTransformation( AsCapNaturalTransformation( N ), A );
    else
        return ApplyNaturalTransformation( N, A );
    fi;
end );

DeclareOperation( "NaturalTransformation",
        [ IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories, IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories ] );

##
InstallMethod( NaturalTransformation,
        "TODO",
        [ IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories, IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories ],
        
  function ( F, G )
    
    return NaturalTransformation( AsCapFunctor( F ), AsCapFunctor( G ) );
    
end );

##
# TODO cache
CategoryOfAdditiveFunctorsBetweenAbelianCategories := FunctionWithCache( function( C, D )
    local CategoryOfAdditiveFunctorsBetweenAbelianCategories;
    
    if not IsAbelianCategory( C ) or not IsAbelianCategory( D ) then
        Error( "cannot build CategoryOfAdditiveFunctorsBetweenAbelianCategories from non-abelian categories" );
    fi;
    
    CategoryOfAdditiveFunctorsBetweenAbelianCategories := CreateCapCategory( Concatenation( "Category of additive functors between \"", Name( C ), "\" and \"", Name( D ), "\"" ) );
    
    SetIsAbelian( CategoryOfAdditiveFunctorsBetweenAbelianCategories, true );
    
    DisableAddForCategoricalOperations( CategoryOfAdditiveFunctorsBetweenAbelianCategories );
    
    AddObjectRepresentation( CategoryOfAdditiveFunctorsBetweenAbelianCategories, IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
    
    AddMorphismRepresentation( CategoryOfAdditiveFunctorsBetweenAbelianCategories, IsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories );
    
    ##
    AddCokernelObject( CategoryOfAdditiveFunctorsBetweenAbelianCategories,
      function ( beta )
        local F, G, cokernel_object;
        
        F := Source( beta );
        G := Range( beta );

        cokernel_object := CapFunctor( Concatenation( "A cokernel in the category ", Name( CategoryOfAdditiveFunctorsBetweenAbelianCategories ) ), SourceCapCategory( F ), RangeCapCategory( F ) );

        AddObjectFunction( cokernel_object,
            function( X )
                return CokernelObject( MyApplyNaturalTransformation( beta, X ) );
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
                return CokernelObjectFunctorialWithGivenCokernelObjects( obj1, MyApplyNaturalTransformation( beta, obj1 ), MyApplyFunctor( G, alpha ), MyApplyNaturalTransformation( beta, obj2 ), obj2 );
        end );
        
        return AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories( cokernel_object );
        
    end );

    ##
    AddCokernelProjectionWithGivenCokernelObject( CategoryOfAdditiveFunctorsBetweenAbelianCategories,
      function ( beta, cokernel_object )
        local F, G, beta_trafo, cokernel_projection;
        
        F := Source( beta );
        G := Range( beta );

        cokernel_projection := NaturalTransformation( G, cokernel_object );
        AddNaturalTransformationFunction( cokernel_projection,
            function( S, X, T )
                return CokernelProjection( MyApplyNaturalTransformation( beta, X ) );
        end );
        
        return AsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories( cokernel_projection );
        
    end );

    Finalize( CategoryOfAdditiveFunctorsBetweenAbelianCategories );

    return CategoryOfAdditiveFunctorsBetweenAbelianCategories;
end );
    
InstallMethod( AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories,
        "TODO",
        [ IsCapFunctor ],
        
  function ( F )
    local source_category, range_category, cat, object;
    
    source_category := AsCapCategory( Source( F ) );
    range_category := AsCapCategory( Range( F ) );
    
    cat := CategoryOfAdditiveFunctorsBetweenAbelianCategories( source_category, range_category );
    
    object := rec( );
    ObjectifyObjectForCAPWithAttributes( object, cat,
            AsCapFunctor, F,
            SourceCapCategory, source_category,
            RangeCapCategory, range_category
    );
    
    return object;
    
end );

##
InstallMethod( AsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories,
        "TODO",
        [ IsCapNaturalTransformation ],
        
  function ( natural_transformation )
    local F, G, source_category, range_category, cat, morphism;

    F := Source( natural_transformation );
    G := Range( natural_transformation );

    if not IsIdenticalObj( Source( F ), Source( G ) ) or not IsIdenticalObj( Range( F ), Range( G ) ) then
        Error( "given functors are not parallel" );
    fi;
    
    source_category := AsCapCategory( Source( F ) );
    range_category := AsCapCategory( Range( F ) );

    cat := CategoryOfAdditiveFunctorsBetweenAbelianCategories( source_category, range_category );
    
    morphism := rec( );
    ObjectifyMorphismForCAPWithAttributes( morphism, cat,
        AsCapNaturalTransformation, natural_transformation,
        Source, AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories( F ),
        Range, AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories( G )
    );
    
    return morphism;
    
end );

##
InstallMethod( ZerothDerivedFunctor,
        "TODO",
        [ IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories ],
        
  function( F )
    local S, T, L_0_F;
    
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
    
    return AsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories( L_0_F );
end );

##
InstallMethod( ZerothDerivedFunctorMorphism,
        "TODO",
        [ IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories ],
        
  function( F )
    local L_0_F, S, T, beta;
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

    return AsMorphismInCategoryOfAdditiveFunctorsBetweenAbelianCategories( beta );
end );

##
InstallMethod( ProjectiveStabilization,
        "TODO",
        [ IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories ],
        
  function( F )
    local beta;
    beta := ZerothDerivedFunctorMorphism( F );
    return CokernelObject( beta );
end );

##
InstallMethod( ProjectionOntoProjectiveStabilization,
        "TODO",
        [ IsObjectInCategoryOfAdditiveFunctorsBetweenAbelianCategories ],
        
  function( F )
    local beta;
    beta := ZerothDerivedFunctorMorphism( F );
    return CokernelProjection( beta );
end );
