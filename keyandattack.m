/* ---------------------------------------------------------
Generation of a VDOO public key over GF(q). 
Some of the code where adapted from
https://drive.google.com/file/d/1wb6LD9vi4M9C5Za1-P2fBFob0mE1-pgK/view, 
which was created by Ding et al.
------------------------------------------------------------*/

PubKey := function(q,v,d,o1,o2)
    diag := [1 : i in [1..d]];
    parameters := [q] cat diag cat [o1,o2];
    u:= #parameters -1;
    v:=[];
    o:=[];
    v[1]:=parameters[1];
    for i:=1 to u do
        o[i]:=parameters[i+1];
        v[i+1]:=v[i]+o[i];
    end for;

    n:=v[u+1];
    m:=n-v[1];
    GF<w>:=GaloisField(q);
    Vn:=VectorSpace(GF,n);
    Vm:=VectorSpace(GF,m);

    P<[x]>:=PolynomialRing(GF,n);
    Pol<[y]>:=PolynomialRing(P,n);


    // key generation
    // affine map T -----------------------------------------------------------------------------
    repeat
        MT:=RandomMatrix(GF,n,n);
    until IsInvertible(MT) eq true;
    cT:= Random(Vn);

    T:=[];
    for i:=1 to n do
        T[i]:=P!0;
        for j:=1 to n do
            T[i]:=T[i]+MT[i][j]*x[j];
        end for;
        //T[i]:=T[i]+cT[i]; // VDOO only consider homogeneous polynomials, uncomment this for affine case
    end for;

    // central map Q ---------------------------------------------------------------------------
    Qc:=[]; Q:=[];

    for greatloop:=1 to u do

        for loop:=v[greatloop]-v[1]+1 to v[greatloop+1]-v[1] do // greatloop-th Layer --------------------------------
            Q[loop]:=Pol!0;

            for i:=1 to v[greatloop] do
                for j:=1 to v[greatloop+1] do
                    Q[loop]:=Q[loop] + Random(GF)*Pol.i*Pol.j;
                end for;
            end for;
        end for;
    end for; 

    // affine map S ---------------------------------------------------------------------------------------

    repeat
        MSF:=RandomMatrix(GF,m,m);
    until IsInvertible(MSF) eq true;
    cS:=Matrix(Pol,m,1,ChangeUniverse(Eltseq(Random(Vm)),Pol));
    MS:=Matrix(Pol,m,m,ChangeUniverse(Eltseq(MSF),Pol));

    // public key Pk ----------------------------------------------------------------------------
    QT:=ZeroMatrix(Pol,m,1);
    for i:=1 to m do
        QT[i][1]:=Evaluate(Q[i],y[1], T[1]);
        for j:=2 to n do
            QT[i][1]:=Evaluate(QT[i][1],y[j], T[j]);
        end for;
    end for;

    //Pk:=MS*QT+cS;  // VDOO only consider homogeneous polynomials, uncomment this for affine case
    Pk:=MS*QT;

    D:=[];
    for i:=1 to m do
        D[i]:=MonomialCoefficient(Pk[i][1],1);
    end for;
    Pk := D;
    return Pk;
end function;





function attackrecmin
return the decrypted message

function newattack
return the new attack

