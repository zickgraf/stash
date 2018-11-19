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
