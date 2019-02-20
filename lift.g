ReadPackage( "StableCategoriesForCAP", "/examples/lp_over_exterior_algebra/lp_over_exterior_algebra.g" );

R := KoszulDualRing( HomalgFieldOfRationalsInSingular()*"x" );
Q := CoefficientsRing( R ); 
basis_indices := standard_list_of_basis_indices( R );

e0 := HomalgMatrix( "[[e0]]", 1, 1, R );
zero := HomalgZeroMatrix( 1, 1, R );
id := HomalgIdentityMatrix( 1, 1, R );

# solve
# id * x * id + id * y * e0 = id
# e0 * x * id +  0 * y *  0 =  0

bu_e0 := MyBlownUpMatrix( basis_indices, e0 );
bu_zero := MyBlownUpMatrix( basis_indices, zero );
bu_id := MyBlownUpMatrix( basis_indices, id );

pair_to_left := function( A, B )
    return KroneckerMat( Involution( B ), A );
end;

C_11 := pair_to_left( bu_id, bu_id );
C_12 := pair_to_left( bu_id, bu_e0 );
C_21 := pair_to_left( bu_e0, bu_id );
C_22 := pair_to_left( bu_zero, bu_zero );

rhs_1 := vec( bu_id );
rhs_2 := vec( bu_zero );

mat := UnionOfRows( UnionOfColumns( C_11, C_12 ), UnionOfColumns( C_21, C_22 ) );
rhs := UnionOfRows( rhs_1, rhs_2 );

Display( CertainColumns( mat, [ 1, 2, 5, 6 ] ) );
Display( mat );
Display( "*" );

sol := LeftDivide( CertainRows( CertainColumns( mat, [ 1, 2, 5, 6 ] ), [ 1, 2, 5, 6 ] ), CertainRows( rhs, [ 1, 2, 5, 6 ] ) );

if sol = fail then
    Display( "fail" );
else
    Display( sol );
    # Display( devec( CertainRows( sol, [ 1 .. 4 ] ), 2, 2 ) );
    # Display( devec( CertainRows( sol, [ 5 .. 8 ] ), 2, 2 ) );
fi;


Display( "=" );
Display( CertainRows( rhs, [ 1, 2, 5, 6 ] ) );




#R := KoszulDualRing( HomalgFieldOfRationalsInSingular()*"x,y" );
#Q := CoefficientsRing( R ); 
#basis_indices := standard_list_of_basis_indices( R );
#

n := 2;
m := 1;

L_id_s := UnionOfRows( List( basis_indices, u -> KroneckerMat( HomalgIdentityMatrix( n, Q ), Q*FLeft( u, HomalgIdentityMatrix( m, R ) ) ) ) );

Display( L_id_s );


u := basis_indices[4];
Display(Q*FLeft( u, HomalgIdentityMatrix( 3, R ) ));
