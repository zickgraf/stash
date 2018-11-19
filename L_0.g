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
