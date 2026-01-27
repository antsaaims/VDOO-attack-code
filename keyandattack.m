/* ---------------------------------------------------------
Generation of a VDOO public key over K(q). 
Some of the code where adapted from
https://drive.google.com/file/d/1wb6LD9vi4M9C5Za1-P2fBFob0mE1-pgK/view, 
which was created by Ding et al.
------------------------------------------------------------*/

SetupAttackRings := function(q, v, d, o1, o2)
    "Defining Rings for VDOO Attack...";
    m := d + o1 + o2;
    n := v + m;
    K<w>:=GaloisField(q);
    
    Vm:=VectorSpace(K,m);
    Vn:= VectorSpace(K,n);
    // 1. Define the base Ring A (for the Groebner Basis)
    k := n - o2 + 1;
    r := o2;
    s := r * (n - r);
    vars_A := [ Sprintf("z%o", j) : j in [1..s] ] cat [ Sprintf("a%o", i) : i in [1..k] ];
    A := PolynomialRing(K, #vars_A, "lex");
    AssignNames(~A, vars_A);
    
    // 2. Define Ring P over A (for the Polar Form / y-variables)
    P<[y]> := PolynomialRing(A, n);
    
    // 3. Define Ring Pol over P (for the Public Key / x-variables)
    Pol<[x]> := PolynomialRing(P, n);
    // Return them as a list/tuple to be unpacked
    return <K,A, P, Pol,n, m, k, r, s,x,y,w,Vm,Vn>;
end function;



PubKey := function(q,v,d,o1,o2,K,A,P,Pol,n, m, k, r, s,x,y,w,Vm,Vn)
    diag := [1 : i in [1..d]];
    parameters := [v] cat diag cat [o1,o2];
    u:= #parameters -1;
    v:=[];
    o:=[];
    v[1]:=parameters[1];
    for i:=1 to u do
        o[i]:=parameters[i+1];
        v[i+1]:=v[i]+o[i];
    end for;

    // key generation
    // affine map T -----------------------------------------------------------------------------
    repeat
        MT:= Matrix(Pol,n,n, [ Random(K): i in [1..n*n]]);
    until IsInvertible(MT) eq true;
    cT:= Random(Vn);

    //T:=[P!0: i in [1..n] ];
    T := MT*Matrix(Pol, n,1,x);
    // central map Q ---------------------------------------------------------------------------
    Qc:=[]; 
    Q:=[];

    for greatloop:=1 to u do

        for loop:=v[greatloop]-v[1]+1 to v[greatloop+1]-v[1] do // greatloop-th Layer --------------------------------
            Q[loop]:=Pol!0;

            for i:=1 to v[greatloop] do
                for j:=1 to v[greatloop+1] do
                    Q[loop]:=Q[loop] + Random(K)*Pol.i*Pol.j;
                end for;
            end for;
        end for;
    end for; 
    // affine map S ---------------------------------------------------------------------------------------

    repeat
        MSF:=RandomMatrix(K,m,m);
    until IsInvertible(MSF) eq true;
    cS:=Matrix(Pol,m,1,ChangeUniverse(Eltseq(Random(Vm)),Pol));
    MS:=Matrix(Pol,m,m,ChangeUniverse(Eltseq(MSF),Pol));
    // public key Pk ----------------------------------------------------------------------------
    QT :=  Matrix(Pol, m,1, [Evaluate(Q[i],Eltseq(T)): i in [1..m]]); // F o T
    //Pk:=MS*QT+cS;  // VDOO only consider homogeneous polynomials, uncomment this for affine case
    //Pk:= Eltseq(MS*QT);
    Pk:= (MS*QT);
    return Pk;
end function;



"***************************************************";
"Attacking Vdoo Signature Scheme";
"Using Rectangular Minrank attack and P(y)=0";
"Method: Kipnis and Shamir";
"***************************************************";

RecMinAttackKS := function(q,v,d,o1,o2,Pk,K,A,P,Pol,n,m, k, r, s,x,y,w,Vm,Vn)
    //"Pk at this point";
    //Pk;
    yvec := Vector( [P.i: i in [1..n]] );


    // creating the basis vectors
    basis_vectors := [ Vn!([ i eq j select 1 else 0 : j in [1..n] ]) 
        : i in [1..n]
    ];

    yvar :=  Vector(([P.i: i in [1..n]]));
    zerovar :=  Vector(([P!0: i in [1..n]]));
    zerovec:= [K!0: i in [1..n]];// Evaluate(Pk, avec) is in P<y> and we want it to be in A so that we can take the ideal. 
    
    
    FlattenToA := function(poly)
        //Use this for constant polynomial only
        // 1. If it's in Pol, evaluate at x=0 to get into P
        if Parent(poly) eq Pol then
            poly := Evaluate(poly, [P!0 : i in [1..n]]);
        end if;
        
        // 2. If it's in P, evaluate at y=0 to get into A
        if Parent(poly) eq P then
            poly := Evaluate(poly, [A!0 : i in [1..n]]);
        end if;
        
        return A ! poly;
    end function;
   
    FlattenMatrix := function(M)
        rows := NumberOfRows(M);
        cols := NumberOfColumns(M);
        
        // Apply FlattenToA to every entry in a single flat list
        flat_entries := [ FlattenToA(M[i, j]) : j in [1..cols], i in [1..rows] ];
        
        // Reconstruct the matrix over Ring A
        return Matrix(A, rows, cols, flat_entries);
    end function;

    Pprimelist:= [];
    for i in [1..n] do
        eval1:= Vector( Evaluate( Pk, Eltseq(yvar + basis_vectors [i] )));
        eval2:= Vector( Evaluate( Pk, Eltseq(zerovar + basis_vectors [i] ))) ;
        eval3:=  Vector( Evaluate( Pk, Eltseq(yvar  )));
        Append(~Pprimelist, eval1 - eval2 - eval3);
    end for;

    Qdeformed := [Matrix(Pol,([ Eltseq(Evaluate( Pprimelist[i], Eltseq(basis_vectors [j])) ): i in [1..n]])): j in [1..n]];
    Qdeformed := [ FlattenMatrix(Qdeformed[i]) : i in [1..n]];
    Qdeformed;


    X := [A.i: i in [s+1..k+s]];
    Y := [A.i: i in [1..s]];
    avec := [X[i]: i in [1..n - o2+1]] cat [0: i in [1..o2-1]];
    MatY := Matrix(r, n - r, Y);
    I := IdentityMatrix(A, n - r);
    MY := VerticalJoin( I , MatY);
    MX  := &+[ X[i] * Qdeformed[i] : i in [1..k]] ;

    KS := Transpose(MY)*MX;

    Eval1 := Evaluate( Eltseq(Pk), Eltseq(yvec));
    Eval := Evaluate( Eltseq(Eval1), Eltseq(avec));

    PolyList  := Eltseq(KS) cat [Evaluate(item,zerovec): item in Eval];
    //PolyList  := Eltseq(KS) cat Eval;

    // You need to do this manually to find a unique solution
    constraints:= [Name(A,s+9), Name(A,s+10)+1];

    //constraints:= [];//theoritically, this should work but I ran out of memory so I needed to keep adding constraints
    PolyList := PolyList cat constraints;
    CoercedPolyList := [ A ! f : f in PolyList ];
    I := ideal< A | CoercedPolyList >;
    G := GroebnerBasis(I);
    V := Variety(I);   // list of solutions as tuples
    //print "Number of solutions:", #V;
    if #V eq 0 then
        print "No solutions.";
    else
        // pick first non-zero vector (if exists)       
        for v in V do
        //compute whether v is 0 or not.
        //v;
        nz:=false;
        for xx in v do
            
                if xx ne K!0 then
                    nz := true;
                    break;
                end if;
            end for; 
            if nz eq true then
                sol := v;
                break;           
            end if;
        end for;

        if nz then
            print "A non-zero solution of the MinRank Problem is:";
            print sol;
            list_sol := [sol[i]: i in [1..s+k]];//making sol as alits instead of tuple
            print "This gives the following element o2 in O2:";
            foundvec := list_sol[(s+1)..(s+k)] cat [0: i in [1..o2-1]];
            print foundvec;
        else
            print "All solutions returned are zero.";
        end if;
    end if;
    return foundvec;
end function;




// 1. Initialize once
print Date(); // Returns a string like "Tue Jan 27 2026"
print Time(); // Returns a string like "10:30:05"

q, v, d, o1, o2 := Explode([4, 3, 4, 2, 3]);
SetupAttackRings(q, v, d, o1, o2);

//K,A, P, Pol,n, m, k, r, s,x,y,w,Vm,Vn:= Explode(SetupAttackRings(q, v, d, o1, o2));

// 2. Generate Key
//Pk := PubKey(q,v,d,o1,o2,K,A,P,Pol,n, m, k, r, s,x,y,w,Vm,Vn);
//Pk;
// 3. Rectangular MinRank Attack Using Kipnis and Shamir
"Starting Attack...";
//foundvec := RecMinAttackKS(q,v,d,o1, o2, Pk,K,A,P,Pol,n, m, k, r, s,x,y,w,Vm,Vn);

//function newattack
//return the new attack

