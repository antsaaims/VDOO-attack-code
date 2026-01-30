
printf "*************************************************************** \n";
printf "***        Attacking Vdoo Signature Scheme                  *** \n";
printf "*** Using the combined Simple and Rectangular Minrank attack*** \n";
printf "***          Method: Kipnis and Shamir                      *** \n";
printf "*************************************************************** \n \n";


q:=4; // Field Size, replace this with yoru field size
vdooparameters := [3,4,2,2]; //Write your VDOO parameter here


m:= vdooparameters[2] + vdooparameters[3] +vdooparameters[4] ;
n:= vdooparameters[1] + m;
o2 :=vdooparameters[4];
K<w>:=GaloisField(q);


ksimple := n - m; // this is the number of variables
r := o2; //This is the target rank
s := r*(n-r);// This should not change.

vars := [ Sprintf("z%o", j) : j in [1..s] ] cat  [ Sprintf("a%o", i) : i in [1..ksimple] ] ;
//vars;

A:= PolynomialRing(K, #vars, "grevlex");

AssignNames(~A, vars);

P<[y]> := PolynomialRing(A,n);
Pol<[x]>:=PolynomialRing(P,n);

// Change this to your public key polynomial



Pk:=  [
w^2*x[1]^2 + w*x[1]*x[3] + x[1]*x[4] + x[1]*x[6] + w*x[1]*x[9] + w*x[1]*x[10] +
w*x[1]*x[11] + w*x[2]^2 + x[2]*x[3] + w*x[2]*x[5] + w*x[2]*x[6] + x[2]*x[7] +
w*x[2]*x[8] + w*x[2]*x[10] + w^2*x[3]^2 + w^2*x[3]*x[5] + w^2*x[3]*x[6] +
w*x[3]*x[7] + w*x[3]*x[8] + w*x[3]*x[10] + w*x[4]^2 + x[4]*x[5] + w^2*x[4]*x[7]
+ w*x[4]*x[8] + x[4]*x[9] + w*x[4]*x[10] + w*x[4]*x[11] + w^2*x[5]^2 +
w*x[5]*x[7] + x[5]*x[8] + w^2*x[5]*x[9] + x[5]*x[11] + x[6]*x[9] +
w^2*x[6]*x[10] + w^2*x[6]*x[11] + w^2*x[7]^2 + x[7]*x[8] + w*x[7]*x[9] +
w^2*x[7]*x[11] + x[8]^2 + x[8]*x[9] + x[8]*x[10] + w^2*x[8]*x[11] + w*x[9]*x[11]
+ w^2*x[10]^2 + w^2*x[10]*x[11] + x[11]^2,
x[1]^2 + w*x[1]*x[2] + w^2*x[1]*x[3] + x[1]*x[4] + w^2*x[1]*x[5] + w^2*x[1]*x[6]
+ w*x[1]*x[8] + w*x[1]*x[9] + w^2*x[1]*x[10] + w^2*x[2]*x[3] + x[2]*x[4] +
x[2]*x[6] + x[2]*x[7] + w^2*x[2]*x[9] + w^2*x[2]*x[10] + w^2*x[2]*x[11] +
w*x[3]^2 + w*x[3]*x[4] + x[3]*x[5] + x[3]*x[6] + w^2*x[3]*x[7] + w^2*x[3]*x[8] +
w^2*x[3]*x[9] + x[4]^2 + w*x[4]*x[5] + w^2*x[4]*x[6] + w*x[4]*x[7] + w*x[4]*x[8]
+ w*x[4]*x[9] + w^2*x[4]*x[10] + w*x[4]*x[11] + w^2*x[5]*x[7] + x[5]*x[8] +
w^2*x[5]*x[11] + w^2*x[6]^2 + x[6]*x[7] + w*x[6]*x[8] + x[6]*x[9] + x[6]*x[10] +
w^2*x[6]*x[11] + w^2*x[7]^2 + x[7]*x[8] + w^2*x[7]*x[11] + w^2*x[8]^2 +
x[8]*x[9] + w*x[8]*x[10] + w^2*x[8]*x[11] + w^2*x[9]*x[11] + w*x[10]^2 +
x[10]*x[11] + w*x[11]^2,
w*x[1]^2 + w*x[1]*x[4] + w*x[1]*x[5] + w*x[1]*x[6] + x[1]*x[7] + w^2*x[1]*x[9] +
x[1]*x[10] + x[1]*x[11] + w*x[2]*x[3] + w^2*x[2]*x[4] + w^2*x[2]*x[5] +
x[2]*x[6] + w*x[2]*x[7] + w*x[2]*x[8] + w^2*x[2]*x[9] + w*x[2]*x[10] +
w^2*x[2]*x[11] + w^2*x[3]*x[4] + w^2*x[3]*x[5] + x[3]*x[8] + w^2*x[3]*x[9] +
w^2*x[3]*x[10] + w^2*x[3]*x[11] + w*x[4]^2 + x[4]*x[5] + w^2*x[4]*x[6] +
w^2*x[4]*x[7] + w^2*x[4]*x[8] + x[4]*x[10] + w^2*x[4]*x[11] + w*x[5]^2 +
w*x[5]*x[6] + w*x[5]*x[7] + x[5]*x[9] + w*x[5]*x[10] + w*x[5]*x[11] + w^2*x[6]^2
+ w^2*x[6]*x[7] + w*x[6]*x[9] + w^2*x[6]*x[11] + w*x[7]^2 + w^2*x[7]*x[8] +
x[7]*x[10] + w*x[7]*x[11] + x[8]^2 + x[8]*x[11] + x[9]^2 + x[9]*x[10] +
w*x[9]*x[11] + x[10]^2 + w^2*x[11]^2,
w^2*x[1]^2 + w*x[1]*x[2] + w^2*x[1]*x[3] + w^2*x[1]*x[4] + w^2*x[1]*x[5] +
w^2*x[1]*x[6] + w*x[1]*x[9] + x[2]^2 + x[2]*x[3] + x[2]*x[4] + w*x[2]*x[5] +
w^2*x[2]*x[6] + w*x[2]*x[7] + w^2*x[2]*x[8] + w^2*x[2]*x[10] + x[2]*x[11] +
w*x[3]^2 + w^2*x[3]*x[6] + w^2*x[3]*x[7] + w^2*x[3]*x[8] + w^2*x[3]*x[9] +
w^2*x[3]*x[10] + w^2*x[3]*x[11] + x[4]^2 + w^2*x[4]*x[5] + w^2*x[4]*x[7] +
x[4]*x[8] + w*x[4]*x[11] + w^2*x[5]^2 + x[5]*x[6] + w*x[5]*x[7] + w*x[5]*x[10] +
w*x[5]*x[11] + w*x[6]^2 + x[6]*x[7] + w^2*x[6]*x[9] + w^2*x[6]*x[10] +
x[6]*x[11] + w*x[7]^2 + x[7]*x[9] + x[7]*x[10] + w^2*x[7]*x[11] + w*x[8]*x[9] +
w^2*x[8]*x[10] + w*x[8]*x[11] + w^2*x[9]^2 + x[10]^2 + w^2*x[10]*x[11],
x[1]*x[2] + w*x[1]*x[3] + w*x[1]*x[4] + x[1]*x[5] + x[1]*x[6] + w*x[1]*x[8] +
x[1]*x[9] + w^2*x[1]*x[11] + w^2*x[2]^2 + w*x[2]*x[3] + w*x[2]*x[4] + x[2]*x[7]
+ w*x[2]*x[8] + w^2*x[2]*x[9] + x[2]*x[10] + w*x[2]*x[11] + w*x[3]^2 +
w^2*x[3]*x[5] + w*x[3]*x[6] + w^2*x[3]*x[7] + w*x[3]*x[8] + x[3]*x[10] +
w^2*x[3]*x[11] + x[4]^2 + w*x[4]*x[5] + w^2*x[4]*x[6] + w*x[4]*x[7] +
w^2*x[4]*x[8] + w*x[4]*x[9] + w^2*x[4]*x[10] + w*x[4]*x[11] + x[5]^2 +
w*x[5]*x[6] + w*x[5]*x[8] + w*x[5]*x[9] + w^2*x[5]*x[10] + w^2*x[5]*x[11] +
w^2*x[6]^2 + w^2*x[6]*x[7] + w*x[6]*x[8] + w^2*x[6]*x[9] + x[6]*x[10] +
w*x[6]*x[11] + x[7]^2 + w^2*x[7]*x[9] + x[7]*x[11] + w^2*x[8]^2 + w^2*x[8]*x[9]
+ x[8]*x[10] + x[9]^2 + w^2*x[9]*x[10] + x[9]*x[11] + w*x[10]^2,
x[1]^2 + w*x[1]*x[2] + x[1]*x[3] + x[1]*x[4] + x[1]*x[5] + x[1]*x[7] +
w*x[1]*x[8] + w^2*x[1]*x[9] + w*x[1]*x[10] + w*x[1]*x[11] + w^2*x[2]^2 +
x[2]*x[3] + w*x[2]*x[4] + w*x[2]*x[6] + x[2]*x[7] + x[2]*x[8] + w^2*x[2]*x[10] +
x[2]*x[11] + x[3]^2 + x[3]*x[9] + w^2*x[4]^2 + w*x[4]*x[7] + w^2*x[4]*x[8] +
w^2*x[4]*x[9] + x[4]*x[10] + w^2*x[4]*x[11] + w*x[5]^2 + w*x[5]*x[6] +
w*x[5]*x[8] + w^2*x[5]*x[10] + x[5]*x[11] + x[6]*x[7] + w*x[6]*x[8] +
w^2*x[6]*x[9] + w*x[6]*x[10] + w^2*x[7]^2 + w*x[7]*x[8] + x[7]*x[10] +
x[7]*x[11] + w^2*x[8]*x[9] + w^2*x[8]*x[10] + w^2*x[9]^2 + w^2*x[9]*x[10] +
w*x[9]*x[11] + x[10]^2 + w*x[10]*x[11],
w*x[1]^2 + w^2*x[1]*x[2] + w*x[1]*x[4] + w^2*x[1]*x[6] + x[1]*x[7] +
w^2*x[1]*x[8] + x[1]*x[9] + w*x[1]*x[10] + x[1]*x[11] + w^2*x[2]*x[4] +
x[2]*x[6] + w*x[2]*x[9] + w^2*x[2]*x[10] + x[2]*x[11] + x[3]^2 + x[3]*x[5] +
w^2*x[3]*x[6] + w*x[3]*x[7] + w*x[3]*x[8] + w*x[3]*x[9] + x[3]*x[10] +
x[3]*x[11] + x[4]^2 + w^2*x[4]*x[5] + w^2*x[4]*x[6] + w^2*x[4]*x[7] + x[4]*x[8]
+ w^2*x[4]*x[10] + x[4]*x[11] + w^2*x[5]^2 + x[5]*x[7] + x[5]*x[9] + x[5]*x[10]
+ x[5]*x[11] + w^2*x[6]^2 + w^2*x[6]*x[7] + w^2*x[6]*x[8] + x[6]*x[9] +
x[6]*x[10] + x[6]*x[11] + x[7]^2 + x[7]*x[8] + x[7]*x[9] + w^2*x[7]*x[10] +
x[7]*x[11] + x[8]*x[9] + w^2*x[8]*x[10] + x[8]*x[11] + x[9]^2 + w*x[9]*x[10] +
x[9]*x[11] + w*x[10]^2 + x[10]*x[11] + w*x[11]^2,
w^2*x[1]*x[3] + w^2*x[1]*x[4] + x[1]*x[5] + w*x[1]*x[7] + x[1]*x[8] +
w*x[1]*x[10] + w*x[1]*x[11] + w*x[2]^2 + w*x[2]*x[3] + w^2*x[2]*x[5] +
w^2*x[2]*x[7] + w^2*x[2]*x[8] + w^2*x[2]*x[9] + w*x[2]*x[11] + x[3]^2 +
x[3]*x[4] + w*x[3]*x[5] + x[3]*x[6] + x[3]*x[7] + w*x[3]*x[8] + w^2*x[3]*x[10] +
x[3]*x[11] + x[4]^2 + w*x[4]*x[5] + w^2*x[4]*x[6] + x[4]*x[7] + x[4]*x[8] +
w^2*x[4]*x[10] + w*x[4]*x[11] + x[5]^2 + w^2*x[5]*x[6] + x[5]*x[7] + x[5]*x[8] +
w^2*x[5]*x[9] + w^2*x[5]*x[10] + x[5]*x[11] + w*x[6]^2 + w^2*x[6]*x[7] +
x[6]*x[8] + x[6]*x[9] + w*x[7]^2 + w^2*x[7]*x[8] + w^2*x[7]*x[9] + x[7]*x[10] +
x[8]^2 + w^2*x[8]*x[9] + x[8]*x[10] + x[8]*x[11] + x[9]^2 + w^2*x[9]*x[10] +
x[9]*x[11] + w^2*x[10]*x[11] + x[11]^2
] ;

// Public key ends here, don't touch anything below

Vm:=VectorSpace(K,m) ;
Vn:= VectorSpace(K,n) ;

// creating the basis vectors

basis_vectors := [ Vn!([ i eq j select 1 else 0 : j in [1..n] ]) 
    : i in [1..n]
];
//basis_vectors;

yvar :=   Vector(([P.i: i in [1..n]]));
Y := [A.i: i in [1..s]];


MatY := Matrix(r, n - r, Y);
I := IdentityMatrix(A, n - r);
MY := VerticalJoin( I , MatY);




SimpleRecMinAttackKS := function(Pk)
    printf "*************************************************************** \n";
    printf "***        Attacking Vdoo Signature Scheme                  *** \n";
    printf "*** Using the combined Simple and Rectangular Minrank attack*** \n";
    printf "***          Method: Kipnis and Shamir                      *** \n";
    printf "*************************************************************** \n \n";
    Pprimelist:= [Vector(Evaluate( Pk, Eltseq(yvar + basis_vectors [i] ))) 
                - Vector(Evaluate( Pk, Eltseq( basis_vectors [i] )))
                -Vector(Evaluate( Pk, Eltseq(yvar  ))): i in [1..n]]; 




    foundx := 0;


    for numiter in [1..50] do
    //printf "running iteration number %o \n", numiter;


    //Randomly generating x 

    random_x := [ Random(K) : i in [1..n] ];
    // Generate the Kernel Dx
    D_x := Matrix([Evaluate( Pprimelist[i], Eltseq(random_x)): i in [1..n]]);

    // Find the kernel, if it's 0 then break.
    KernelSpace := Kernel(D_x);
    BasisVectorsListX := Basis(KernelSpace);

    if #BasisVectorsListX ne (n-m) then
        //printf "The dimension of kernel space is not n-m \n";
        continue;
    end if;
    // Form the matrices


    Ltildematrices  := [Matrix(A,([ Eltseq(Evaluate( Pprimelist[i], Eltseq(BasisVectorsListX [j])) ): i in [1..n]])):j in [1..#BasisVectorsListX]];
        

    X := [A.i: i in [s+1..ksimple+s]];

    avec := [X[i]: i in [1..ksimple]] cat [0: i in [1..n-ksimple]];

    //MY;

    // Creating the polynomial ring
    //X;


    MX  := &+[ X[i] * Ltildematrices[i] : i in [1..ksimple]] ;
    //MX;
    KS := Transpose(MY)*MX;
    //KS;
    // PolyList  := Eltseq(KS); //Uncomment this and comment the next line if you don't wanna add the p(y)=0


    ao2 := &+ [X[i]*BasisVectorsListX[i]: i in [1..n-m]]; // this is the vector in O2 we are working on

    ao2list := [P!item: item in Eltseq(ao2)];

    Eval := Eltseq(Evaluate(Pk, ao2list));



    zerovec:= [A!0: i in [1..n]]; // Evaluate(Pk, ao2) is in P<y> and we want it to be in A so that we can take the ideal. 

    PolyList  := Eltseq(KS) cat [Evaluate(item,zerovec): item in Eval];


    // You need to do this manually to find a unique solution
    //constraints:= [Name(A,s+1), Name(A,s+1)+1];


    constraints:= [A.(s+1) - 1];//theoritically, this should work but I ran out of memory so I needed to keep adding constraints

    PolyList := PolyList cat constraints;

    // Create a new list where every polynomial is explicitly forced into ring A

    CoercedPolyList := [ A ! f : f in PolyList ];

    // Now, construct the ideal using the coerced list
    PolyList := PolyList cat constraints;
    CoercedPolyList := [ A ! f : f in PolyList ];
    I := ideal< A | CoercedPolyList >;
    Groebner(I);
    V := Variety(I: Al := "Wiedemann");  // list of solutions as tuples
    if #V ne 0 then     
        for v in V do
        //compute whether v is 0 or not.
        nz:=false;
        for xx in v do
            
                if xx ne K!0 then // one of the entries is not zero
                    nz := true;
                    break;
                end if;
            end for; 
            if nz eq true then
                sol := v;
                break;           
            end if;
        end for;

        if nz eq true then
            foundx := 1;
            printf "\nSolution found after %o iterations\n", numiter;
            print "A non-zero solution of the MinRank Problem is:\n";
            print sol;
            list_sol := [sol[i]: i in [1..s+ksimple]];//making sol as a list instead of tuple
            print "\nThis gives the following element o2 in O2:";
            foundvec :=&+ [list_sol[s+i]*BasisVectorsListX[i]: i in [1..n-m]];
            foundveclist := [P!item: item in Eltseq(foundvec)];
            print foundvec;
            return foundvec;
        end if;
    end if;

    if foundx eq 1 then
    break;
    end if;
    end for;

    return [K!0: i in [1..n]]; // return zero vector if no solution found
end function;
SimpleRecMinAttackKS(Pk);