ReadPackage( "StableCategoriesForCAP", "/examples/lp_over_exterior_algebra/lp_over_exterior_algebra.g" );

Join := function( list, separator )
    local result;
    
    result := Flat( List( list, l -> Concatenation( l, separator ) ) );
    
    Remove( result, Length( result ) );
    
    return result;
end;


S := KoszulDualRing( HomalgFieldOfRationalsInSingular() * "x,y" );
Q := CoefficientsRing( S );
basis_indices := standard_list_of_basis_indices( S );
l := Length( basis_indices );

var_names := ["b", "c", "d", "e", "x", "y", "z", "w"];
var_names_with_indices := Join( List( var_names, var_name -> Join( List( [ 0 .. l-1 ], i -> Concatenation( var_name, "_", String( i ) ) ), "," ) ), "," );
var_names_with_indices := Concatenation( var_names_with_indices, ",o" );

Display( var_names_with_indices );

R := HomalgFieldOfRationalsInSingular() * var_names_with_indices;
AssignGeneratorVariables( R );


BlowUpVarWithIndices := function( var_name )
  local mat, r, cur_mat, i;
    
    if not var_name in var_names then
        Error( "var_name not in var_names" );
    fi;
    
    mat := HomalgZeroMatrix( l, l, R );
    for i in [ 1 .. l ] do
        r := ring_element( basis_indices[ i ], S );
        Error("asd");
        cur_mat := UnionOfRows( List( basis_indices, u -> Q*FLeft( u, HomalgMatrix( [ [ r ] ], 1, 1, S ) ) ) );
        mat := mat + ( Concatenation( var_name, "_", String( i - 1 ) ) / R ) * ( R * cur_mat );
    od;
    
    return mat;
end;

# A := HomalgMatrix( [[a_0,0,0,0],[a_1,a_0,0,0],[a_2,0,a_0,0],[a_3,]] );

# A := BlowUpVarWithIndices( "a" );
A := R * MyBlownUpMatrix( basis_indices, HomalgIdentityMatrix( 1, 1, S ) );
XX := BlowUpVarWithIndices( "x" );
Y := BlowUpVarWithIndices( "y" );
ZZ := BlowUpVarWithIndices( "z" );
W := BlowUpVarWithIndices( "w" );
B := BlowUpVarWithIndices( "b" );
C := BlowUpVarWithIndices( "c" );
D := BlowUpVarWithIndices( "d" );
EEE := BlowUpVarWithIndices( "e" );

##########################################
if false then

L := KroneckerMat( Involution( UnionOfRows( CertainColumns( B, [ 1 ] ), CertainColumns( C, [ 1 ] ) ) ), A );
V := vec( UnionOfColumns( XX, Y ) );

entries := EntriesOfHomalgMatrixAsListList( L );

new_L := HomalgZeroMatrix( NrRows( L ), 0, R );
new_V := HomalgZeroMatrix( 0, 1, R );

vars := EntriesOfHomalgMatrix( V );

for i in [ 1 .. Length( vars )] do
    var := vars[i];
    if var <> 0 then
        new_column := CertainColumns( L, [ i ] );
        for j in [ (i+1) .. Length( vars ) ] do
            if vars[j] <> 0 and vars[j]/var <> fail then
                new_column := new_column + vars[j]/var * CertainColumns( L, [ j ] );
                vars[j] := 0;
            fi;
        od;
        new_L := UnionOfColumns( new_L, new_column );
        new_V := UnionOfRows( new_V, HomalgMatrix( [[var]], 1, 1, R ) );
    fi;
od;

entries := EntriesOfHomalgMatrixAsListList( new_L );
Browse( entries );
Browse( EntriesOfHomalgMatrixAsListList( new_V ) );
fi;



###########################################
if false then

A := R * MyBlownUpMatrix( basis_indices, HomalgIdentityMatrix( 2, S ) );
L := KroneckerMat( Involution( CertainColumns( C, [ 1 ] ) ), A );
V := vec( UnionOfRows( XX, Y ) );

entries := EntriesOfHomalgMatrixAsListList( L );

new_L := HomalgZeroMatrix( NrRows( L ), 0, R );
new_V := HomalgZeroMatrix( 0, 1, R );

vars := EntriesOfHomalgMatrix( V );

for i in [ 1 .. Length( vars )] do
    var := vars[i];
    if var <> 0 then
        new_column := CertainColumns( L, [ i ] );
        for j in [ (i+1) .. Length( vars ) ] do
            if vars[j] <> 0 and vars[j]/var <> fail then
                new_column := new_column + vars[j]/var * CertainColumns( L, [ j ] );
                vars[j] := 0;
            fi;
        od;
        new_L := UnionOfColumns( new_L, new_column );
        new_V := UnionOfRows( new_V, HomalgMatrix( [[var]], 1, 1, R ) );
    fi;
od;

entries := EntriesOfHomalgMatrixAsListList( new_L );
Browse( entries );
Browse( EntriesOfHomalgMatrixAsListList( new_V ) );
fi;



###########################################
if false then

A := R * MyBlownUpMatrix( basis_indices, HomalgIdentityMatrix( 2, S ) );
L := KroneckerMat( Involution( UnionOfRows( CertainColumns( B, [ 1 ] ), CertainColumns( C, [ 1 ] ) ) ), A );
V := vec( UnionOfColumns( UnionOfRows( XX, Y ), UnionOfRows( ZZ, W ) ) );

entries := EntriesOfHomalgMatrixAsListList( L );

new_L := HomalgZeroMatrix( NrRows( L ), 0, R );
new_V := HomalgZeroMatrix( 0, 1, R );

vars := EntriesOfHomalgMatrix( V );

for i in [ 1 .. Length( vars )] do
    var := vars[i];
    if var <> 0 then
        new_column := CertainColumns( L, [ i ] );
        for j in [ (i+1) .. Length( vars ) ] do
            if vars[j] <> 0 and vars[j]/var <> fail then
                new_column := new_column + vars[j]/var * CertainColumns( L, [ j ] );
                vars[j] := 0;
            fi;
        od;
        new_L := UnionOfColumns( new_L, new_column );
        new_V := UnionOfRows( new_V, HomalgMatrix( [[var]], 1, 1, R ) );
    fi;
od;

entries := EntriesOfHomalgMatrixAsListList( new_L );
Browse( entries );
Browse( EntriesOfHomalgMatrixAsListList( new_V ) );
fi;



###########################################
if false then

A := R * MyBlownUpMatrix( basis_indices, HomalgIdentityMatrix( 2, S ) );
L := KroneckerMat( Involution( UnionOfColumns( UnionOfRows( CertainColumns( B, [ 1 ] ), CertainColumns( C, [ 1 ] ) ), UnionOfRows( CertainColumns( D, [ 1 ] ), CertainColumns( EEE, [ 1 ] ) ) ) ), A );
V := vec( UnionOfColumns( UnionOfRows( XX, Y ), UnionOfRows( ZZ, W ) ) );

entries := EntriesOfHomalgMatrixAsListList( L );

new_L := HomalgZeroMatrix( NrRows( L ), 0, R );
new_V := HomalgZeroMatrix( 0, 1, R );

vars := EntriesOfHomalgMatrix( V );

for i in [ 1 .. Length( vars )] do
    var := vars[i];
    if var <> 0 then
        new_column := CertainColumns( L, [ i ] );
        for j in [ (i+1) .. Length( vars ) ] do
            if vars[j] <> 0 and vars[j]/var <> fail then
                new_column := new_column + vars[j]/var * CertainColumns( L, [ j ] );
                vars[j] := 0;
            fi;
        od;
        new_L := UnionOfColumns( new_L, new_column );
        new_V := UnionOfRows( new_V, HomalgMatrix( [[var]], 1, 1, R ) );
    fi;
od;

entries := EntriesOfHomalgMatrixAsListList( new_L );
Browse( entries );
Browse( EntriesOfHomalgMatrixAsListList( new_V ) );
fi;



###########################################
A := R * MyBlownUpMatrix( basis_indices, HomalgIdentityMatrix( 2, S ) );
L := KroneckerMat( Involution( CertainColumns( A, [ 1, 5 ] ) ), UnionOfColumns( UnionOfRows( B, C ), UnionOfRows( D, EEE ) ) );
V := vec( UnionOfColumns( UnionOfRows( XX, Y ), UnionOfRows( ZZ, W ) ) );

entries := EntriesOfHomalgMatrixAsListList( L );

new_L := HomalgZeroMatrix( NrRows( L ), 0, R );
new_V := HomalgZeroMatrix( 0, 1, R );

vars := EntriesOfHomalgMatrix( V );

for i in [ 1 .. Length( vars )] do
    var := vars[i];
    if var <> 0 then
        new_column := CertainColumns( L, [ i ] );
        for j in [ (i+1) .. Length( vars ) ] do
            if vars[j] <> 0 and vars[j]/var <> fail then
                new_column := new_column + vars[j]/var * CertainColumns( L, [ j ] );
                vars[j] := 0;
            fi;
        od;
        new_L := UnionOfColumns( new_L, new_column );
        new_V := UnionOfRows( new_V, HomalgMatrix( [[var]], 1, 1, R ) );
    fi;
od;

entries := EntriesOfHomalgMatrixAsListList( new_L );
Browse( entries );
Browse( EntriesOfHomalgMatrixAsListList( new_V ) );



