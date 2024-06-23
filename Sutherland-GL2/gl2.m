// Some handy utility functions

function strip(s)
    return Join(Split(Join(Split(s," "),""),"\n"),"");
end function;

function sprint(X)
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return strip(Sprintf("%o",X));
end function;

function stringlist(s)
    s := strip(s);
    assert s[1] eq "[" and s[#s] eq "]";
    s := s[2..#s-1];
    return Split(s,",");
end function;

function index(S,f:Project:=func<x|x>,Unique:=false)
    A := AssociativeArray();
    if Unique then
        for x in S do A[f(x)] := Project(x); end for;
    else
        for x in S do y := f(x); A[y] := IsDefined(A,y) select Append(A[y],Project(x)) else [Project(x)]; end for;
    end if;
    return A;
end function;

intrinsic TracesToLPolynomial (t::SeqEnum[RngIntElt], q::RngIntElt) -> RngUPolElt
{ Given a sequence of Frobenius traces of a genus g curve over Fq,Fq^2,...,Fq^g returns the corresponding L-polynomial. }
    require IsPrimePower(q): "q must be a prime power.";
    R<T> := PolynomialRing(Integers());
    if #t eq 0 then return R!1; end if;
    g := #t;
    // use Newton identities to compute compute elementary symmetric functions from power sums
    e := [t[1]];  for k:=2 to g do e[k] := ExactQuotient((-1)^(k-1)*t[k]+&+[(-1)^(i-1)*e[k-i]*t[i]:i in [1..k-1]],k); end for;
    return R!([1] cat [(-1)^i*e[i]:i in [1..g]] cat [(-1)^i*q^i*e[g-i]:i in [1..g-1]] cat [q^g]);
end intrinsic;

intrinsic PointCountsToLPolynomial (n::SeqEnum[RngIntElt], q::RngIntElt) -> RngUPolElt
{ Given a sequence of point counts of a genus g curve over Fq,Fq^2,...,Fq^g returns the corresponding L-polynomial. }
    return TracesToLPolynomial([q^i+1-n[i] : i in [1..#n]], q);
end intrinsic;

intrinsic LPolynomialToTraces (L::RngUPolElt:d:=0) -> SeqEnum[RngIntElt], RngIntElt
{ Returns the sequence of Frobenius traces for a genus g curve over Fq,Fq^2,...,Fq^g corresponding to the givien L-polynomial of degree 2g (or just over Fq,..Fq^d if d is specified). }
    require Degree(L) gt 0 and IsEven(Degree(L)): "Lpolynomial must have positive even degree 2g";
    g := ExactQuotient(Degree(L),2);
    b,p,e := IsPrimePower(Integers()!LeadingCoefficient(L));
    require b: "Not a valid L-polynomial, leading coefficient is not a prime power";
    require IsDivisibleBy(e,g): "Not a valid L-polynomial, leading coefficient is not a prime power with an integral gth root.";
    q := p^ExactQuotient(e,g);
    L := Reverse(L);
    if d eq 0 then d:=g; end if;
    e := [Integers()|(-1)^i*Coefficient(L,2*g-i):i in [1..d]];
    // use Newton identities to compute compute power sums from elementary symmetric functions;
    t := [e[1]]; for k:=2 to d do t[k] := (-1)^(k-1)*k*e[k] + &+[(-1)^(k-1+i)*e[k-i]*t[i] : i in [1..k-1]]; end for;
    return t, q;
end intrinsic;

intrinsic LPolynomialToPointCounts (L::RngUPolElt:d:=0) -> SeqEnum[RngIntElt], RngIntElt
{ Returns the sequence of point counrs of a genus g curve over Fq,Fq^2,...,Fq^g corresponding to the givien L-polynomial of degree 2g (or just over Fq,..Fq^d if d is specified). }
    t, q := LPolynomialToTraces(L:d:=d);
    if d eq 0 then d := #t; end if;
    return [q^i+1-t[i] : i in [1..d]];
end intrinsic;

intrinsic GL2PermutationCharacter(H::GrpMat) -> UserProgram
{ The permutation character given by the GL2-action on the right coset space [H\\GL2]. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return func<A|1>; end if;
    require IsFinite(R): "H must be defined over a finite ring";
    pi := CosetAction(GL(Degree(H),BaseRing(H)),H);
    return func<g|#Fix(pi(g))>;
end intrinsic;

intrinsic GL2Transpose(H::GrpMat) -> GrpMat
{ Given a subgroup H of GL(n,R) for some ring R returns the transposed subgroup. }
    return sub<GL(Degree(H),BaseRing(H))|[Transpose(g):g in Generators(H)]>;
end intrinsic;

intrinsic SL2Size(N::RngIntElt) -> RngIntElt    // This is much faster than #SL(2,Integers(N))
{ The cardinality of SL(2,Z/NZ). }
    if N eq 1 then return 1; end if;
    P := PrimeDivisors(N);
    return N*(N div &*P)^2*&*[p^2-1:p in P];
end intrinsic;

intrinsic GL2Size(N::RngIntElt) -> RngIntElt
{ The cardinality of GL(2,Z/NZ). }
    return EulerPhi(N)*SL2Size(N);
end intrinsic;

// Note that to deal with the fact that Magma won't let us define GL(2,Integers(1)),
// We represent this group as the trivial subgroup of GL(2,Z) and check for this in the functions below.

intrinsic SL2Index(H::GrpMat) -> RngIntElt
{ Index of H cap SL(2,Z/NZ) in SL(2,Z/NZ). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    SL2 := SL(2,R);
    if not H subset SL2 then H := H meet SL2; end if;
    return SL2Size(#R) div #H;
end intrinsic;

intrinsic GL2Index(H::GrpMat) -> RngIntElt
{ The index of H in GL(2,Z/NZ). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    return Index(GL(2,R),H);
end intrinsic;

intrinsic GL2DeterminantIndex(H::GrpMat) -> RngIntElt
{ The index of det(H) in GL1. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    M,pi := MultiplicativeGroup(R);
    return Index(M,sub<M|[Inverse(pi)(Determinant(h)):h in Generators(H)]>);
end intrinsic;

intrinsic GL2ScalarIndex(H::GrpMat) -> RngIntElt
{ The index of (H meet scalars) in H, where H is a subgroup of GL(2,R). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    require Degree(H) eq 2: "H must be a subgroup of GL(2,R) for some ring R.";
    M,pi := MultiplicativeGroup(R);
    return #M div #(H meet sub<GL(2,R)|[[pi(g),0,0,pi(g)]:g in Generators(M)]>);
end intrinsic;

// Given a subgroup H of GL(2,Z/nZ), returns true if H contains an element corresponding to complex conjugation
intrinsic GL2ContainsComplexConjugation(H::GrpMat) -> BoolElt
{ True if H contains an element corresponding to complex conjugation (any GL_2-conjugate of [1,0,0,-1] or [1,1,0,-1]). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    cc := [[1,0,0,-1],[-1,0,0,1],[1,-1,0,-1],[1,1,0,-1],[-1,0,1,1],[-1,1,0,1],[-1,0,-1,1],[1,0,1,-1],[-1,-1,0,1],[1,0,-1,-1],[0,-1,-1,0],[0,1,1,0]];
    GL2 := GL(2,R);
    if &or[GL2!c in H:c in cc] then return true; end if;
    if #R ne 2 and not IsEven(#MultiplicativeGroup(R) div GL2DeterminantIndex(H)) then return false; end if;
    Z := Conjugates(GL2,GL2![1,0,0,-1]);
    for z in Z do if z in H then return true; end if; end for;
    if IsOdd(#R) then return false; end if;
    Z := Conjugates(GL2,GL2![1,1,0,-1]);
    for z in Z do if z in H then return true; end if; end for;
    return false;
end intrinsic;

intrinsic GL2ContainsCC(H::GrpMat) -> BoolElt
{ True if H contains an element corresponding to complex conjugation (any GL_2-conjugate of [1,0,0,-1] or [1,1,0,-1]). }
    return GL2ContainsComplexConjugation(H);
end intrinsic;

intrinsic GL2ContainsNegativeOne(H::GrpMat) -> BoolElt
{ True if -I list in H. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return true; end if;
    return -Identity(H) in H;
end intrinsic;

intrinsic GL2ContainsNegId(H::GrpMat) -> BoolElt
{ True if -I list in H. }
    return GL2ContainsNegativeOne(H);
end intrinsic;

intrinsic GL2Level(H::GrpMat) -> RngIntElt
{ The least integer N such that H is the full inverse image of its reduction modulo N. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1,sub<GL(2,Integers())|>; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    N := #R;
    cH := #H; cGL2 := GL2Size(N);
    if cH eq cGL2 then return 1,sub<GL(2,Integers())|>; end if;
    if IsPrime(N) then return N,H; end if;
    for p in PrimeDivisors(N) do
        while N gt p and N mod p eq 0 and cGL2*#ChangeRing(H,Integers(N div p)) eq GL2Size(N div p)*cH do N div:= p; end while;
    end for;
    return N,ChangeRing(H,Integers(N));
end intrinsic;

intrinsic SL2Level(H::GrpMat) -> RngIntElt, GrpMat
{ The least integer N such that H cap SL2 is the full inverse image of its reduction modulo N, along with corresponding subgroup of SL2. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return 1,sub<SL(2,Integers())|>; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    N := #R;
    SL2 := SL(2,R);
    if not H subset SL2 then
        // Computing the intersection with SL2 is costly enough to make it worth checking the GL2Level first
        N := GL2Level(H);  if N eq 1 then return 1,sub<SL(2,Integers())|>; end if;
        if N ne #R then R:=Integers(N); SL2 := SL(2,R); H := ChangeRing(H,R); end if;
        H := SL2 meet H;
    end if;
    cH := #H; cSL2 := SL2Size(N);
    if cH eq cSL2 then return 1,_; end if;
    if IsPrime(N) then return N,H; end if;
    for p in PrimeDivisors(N) do
        while N gt p and N mod p eq 0 and cSL2*#ChangeRing(H,Integers(N div p)) eq SL2Size(N div p)*cH do N div:= p; end while;
    end for;
    return N,ChangeRing(H,Integers(N));
end intrinsic;

intrinsic GL2CuspCount(H::GrpMat) -> RngIntElt
{ The number of cusps of X_H over C. }
    N,H := SL2Level(H);
    if N eq 1 then return 1; end if;
    SL2 := SL(2,Integers(N));
    H := sub<SL2|H,[-1,0,0,-1]>;
    pi,G := CosetAction(SL2,H);
    T:=sub<SL2|[1,1,0,1]>;
    return #Orbits(pi(T));
end intrinsic;

intrinsic GL2RationalCuspCount(H::GrpMat) -> RngIntElt
{ The number of Q-rational cusps of X_H. }
    N,H := GL2Level(H);
    if N eq 1 then return 1; end if;
    GL2 := GL(2,Integers(N));
    pi,G := CosetAction(GL2,H);
    U := sub<GL2|[1,1,0,1],[-1,0,0,-1]>;
    M,piM := MultiplicativeGroup(BaseRing(H));
    B := sub<GL2|[[piM(g),0,0,1]:g in Generators(M)]>;
    return #{o:o in Orbits(pi(U))|o^pi(B) eq {o}};
end intrinsic;

intrinsic GL2RationalCuspCount(H::GrpMat, q::RngIntElt) -> RngIntElt
{ The number of Fq-rational cusps of the reduction of X_H to the finite field F_q (where q is coprime to the level of H). }
    N,H := GL2Level(H);
    if N eq 1 then return 1; end if;
    require GCD(q,N) eq 1: "q must be coprime to the level of H.";
    GL2 := GL(2,Integers(N));
    if not -Identity(H) in H then H := sub<GL2|H,[-1,0,0,-1]>; end if;
    pi := CosetAction(GL2,H);
    U := sub<GL2|[1,1,0,1]>;
    B := sub<GL2|[q,0,0,1]>;
    return #{o:o in Orbits(pi(U))|o^pi(B) eq {o}};
end intrinsic;

intrinsic GL2Genus(H::GrpMat) -> RngIntElt
{ The genus of the modular curve X_H for H in GL(2,Z/NZ). }
    N,H := SL2Level(H);
    if N le 5 then return 0; end if;
    SL2 := SL(2,Integers(N));
    if not -Identity(H) in H then H := sub<SL2|H,-Identity(H)>; end if;
    pi := CosetAction(SL2,H);
    n2 := #Fix(pi(SL2![0,1,-1,0]));
    n3 := #Fix(pi(SL2![0,1,-1,-1]));
    c := #Orbits(pi(sub<SL2|[1,1,0,1]>));
    return Integers()!(1 + Index(SL2,H)/12 - n2/4  - n3/3 - c/2);
end intrinsic;

intrinsic GL2Lift(H::GrpMat,M::RngIntElt) -> GrpMat
{ The full preimage in GL(n,Z/MZ) of H in GL(n,Z/NZ) for a multiple M of N. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return GL(Degree(H),Integers(M)); end if;
    require Type(R) eq RngIntRes: "H must be a sugroup of GL(n,Z/NZ) for some positive integer N.";
    N := #R;
    require IsDivisibleBy(M,N): "M must be divisible by N for H in GL(n,Z/NZ)";
    GL2:=GL(Degree(H),Integers(M));
    _,pi:=ChangeRing(GL2,R);
    return sub<GL2|Kernel(pi),Inverse(pi)(H)>;
end intrinsic;

intrinsic GL2Project(H::GrpMat,M::RngIntElt) -> GrpMat
{ The projection of the preimage of H in GL(2,Zhat) to GL(2,Z/MZ). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return GL(Degree(H),Integers(M)); end if;
    require Type(R) eq RngIntRes: "H must be a sugroup of GL(n,Z/NZ) for some positive integer N.";
    N := #R;
    if N eq M then return H; end if;
    if IsDivisibleBy(N,M) then return ChangeRing(H,Integers(M)); end if;
    return ChangeRing(GL2Lift(H,LCM(M,N)),Integers(M));
end intrinsic;

intrinsic GL2SplitCartan(R::Rng) -> GrpMat
{ The standard split Cartan subgroup of GL(2,R), equivalently, the subgroup of diagonal matrices in GL(2,R). }
    M,pi := MultiplicativeGroup(R);
    gens := [Integers()!pi(g):g in Generators(M)];
    return sub<GL(2,R) | [[g,0,0,1] : g in gens] cat [[1,0,0,g] : g in gens]>;
end intrinsic;

intrinsic GL2SplitCartan(N::RngIntElt) -> GrpMat
{ The standard split Cartan subgroup of GL(2,Z/NZ), equivalently, the subgroup of diagonal matrices in GL(2,Z/NZ). }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2SplitCartan(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

intrinsic GL2NormalizerSplitCartan(R::Rng) -> GrpMat
{ The normalizer of the standard split Cartan subgroup of GL(2,R). }
    return Normalizer(GL(2,R),GL2SplitCartan(R));
end intrinsic;

intrinsic GL2NormalizerSplitCartan(N::RngIntElt) -> GrpMat
{ The normalizer of the standard split Cartan subgroup of GL(2,Z/NZ). }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2NormalizerSplitCartan(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

// Non-split Cartan -- isomorphic to (OK/N*OK)* where OK is a quadratic order of discriminant prime to N with every p|N inert in OK
// See Baran https://core.ac.uk/download/pdf/82651427.pdf for details
// This implementation uses brute force subgroup enumeration, it will be very slow if N is large
intrinsic GL2NonsplitCartan(R::RngIntRes) -> GrpMat
{ A non-split Cartan subgroup of GL(2,Z/NZ) (isomorphic to OK/N*OK where OK is a quadratic order of discriminant prime to N with every p|N inert in OK). }
    N := #R;  P := PrimeDivisors(N);  M := (N div &*P)^2*&*[p^2-1:p in P];
    S := [H`subgroup : H in Subgroups(GL(2,R):IsAbelian:=true,OrderEqual:=M)];
    if M eq 1 then return S[1]; end if;    // this already handles prime powers and odd N up to 151
    // Construct a suitable Z/NZ algebra using a quadratic order R of discriminant prime to N in which ever p|N is inert
    D := -163;  while not &and[KroneckerSymbol(D,p) eq -1 : p in P] do N -:= 4; end while;
    OK := RingOfIntegers(QuadraticField(D));
    I := Invariants(UnitGroup(quo<OK|N*OK>));
    S := [H : H in S | Invariants(H) eq I];
    assert #S eq 1;
    return S[1];
end intrinsic;

intrinsic GL2NonsplitCartan(N::RngIntElt) -> GrpMat
{ A non-split Cartan subgroup of GL(2,Z/NZ) (isomorphic to OK/N*OK where OK is a quadratic order of discriminant prime to N with every p|N inert in OK). }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2NonsplitCartan(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

intrinsic GL2NormalizerNonsplitCartan(R::RngIntRes) -> GrpMat
{ The normalizer of a non-split Cartan subgroup of GL(2,Z/NZ). }
    return Normalizer(GL(2,R),GL2NonsplitCartan(R));
end intrinsic;

intrinsic GL2NormalizerNonsplitCartan(N::RngIntElt) -> GrpMat
{ The normalizer of a non-split Cartan subgroup of GL(2,Z/NZ). }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2NormalizerNonsplitCartan(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

// Borel group -- upper triangular matrices in GL(2,Z/nZ) -- E admits a rational n-isogeny if and only if \im\rho_{E,n} is conjugate to a subgroup of  the Borel
intrinsic GL2Borel(R::Rng) -> GrpMat
{ The standard Borel subgroup of GL(2,R), equivalently, the subgroup of upper triangular matrices in GL(2,R). }
    return sub<GL(2,R) | [1,1,0,1], GL2SplitCartan(R)>;
end intrinsic;

intrinsic GL2Borel(N::RngIntElt) -> GrpMat
{ The standard Borel subgroup of GL(2,Z/NZ), equivalently, the subgroup of upper triangular matrices in GL(2,Z/NZ). }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2Borel(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

intrinsic GL2Borel1(R::Rng) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,R) that a basis vector (under the left action of GL2 on column vectors), equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left. }
    M,pi:=MultiplicativeGroup(R);    
    return sub<GL(2,R) | [1,1,0,1], [[1,0,0,pi(g)] : g in Generators(M)]>;
end intrinsic;

intrinsic GL2Borel1(N::RngIntElt) -> GrpMat
{ The subgroup of the standard Borel subgroup of GL(2,Z/NZ) that a basis vector (under the left action of GL2 on column vectors), equivalently, the subgroup of upper triangular matrices in GL(2,R) with a 1 in the upper left. }
    require N gt 0: "N must be positive";
    return N gt 1 select GL2Borel1(Integers(N)) else sub<GL(2,Integers())|>;
end intrinsic;

intrinsic GL2ProjectiveImage(H::GrpMat) -> GrpPerm
{ The image of the subgroup H of GL(2,Z/NZ) in PGL(2,Z/NZ). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return SymmetricGroup(1); end if;
    require Type(R) eq RngIntRes: "H must be a sugroup of GL(n,Z/NZ) for some positive integer N.";
    _,pi:=quo<GL(2,R)|Center(GL(2,R))>;
    return pi(H);
end intrinsic;

// Given a subgroup G of GL(2,p^2) that is conjugate to a subgroup H of GL(2,p), returns such an H, using the algorithm in Glasby and Howlett (Writing representations over minimal fields, Comm. Alg. 25 (1997), 1703-1711).
function ConjugateToRationalSubgroup(G)
    local F,p,r,x,C,mu,R,v,X,A,H;
    F:=BaseRing(G);  assert IsFinite(F) and IsField(F);
    if Degree(F) eq 1 then return G; end if;
    assert Degree(F) eq 2;
    p:=Characteristic(F);
    MatFrob := func<A|Parent(A)![A[1][1]^p,A[1][2]^p,A[2][1]^p,A[2][2]^p]>;
    r := [];
    for g in Generators(G) do
        r:=Append(r,[g[1][1]-g[1][1]^p,-g[2][1]^p,g[1][2],0]);
        r:=Append(r,[-g[1][2]^p,g[1][1]-g[2][2]^p,0,g[1][2]]);
        r:=Append(r,[g[2][1],0,g[2][2]-g[1][1]^p,-g[2][1]^p]);
        r:=Append(r,[0,g[2][1],-g[1][2]^p,g[2][2]-g[2][2]^p]);
    end for;
    while true do
        x:=Random(NullspaceOfTranspose(Matrix(r)));
        C:=MatrixRing(F,2)![x[i]:i in [1..Degree(x)]];
        if IsInvertible(C) then C:=GL(2,F)!C; break; end if;
    end while;
    for g in Generators(G) do if C^-1*g*C ne MatFrob(g) then print C, g; assert false; end if; end for;
    mu := C*MatFrob(C);
    assert mu[1][1] eq mu[2][2] and mu[1][2] eq 0 and mu[2][1] eq 0;
    mu := GF(p)!mu[1][1];
    b,v:=NormEquation(F,mu);
    C:=GL(2,F)![1/v,0,0,1/v]*C;
    assert C*MatFrob(C) eq Identity(G);
    while true do
        X:=Random(MatrixRing(F,2));
        A:=X+C*MatFrob(X);
        if not IsInvertible(A) then continue; end if;
        A:=GL(2,F)!A;
        H:=Conjugate(G,A);
        for h in Generators(H) do assert MatFrob(h) eq h; end for;
        return sub<GL(2,p)|Generators(H)>;
    end while;
end function;

// Based on Thm 5.5 of Flannery-O'Brien (Linear groups of small degree over finite fields, Internat. J. Algebra Comput.  15 (2005), 467--502),
intrinsic GL2MaximalA4(p::RngIntElt) -> GrpMat[RngIntRes]
{ The largest subgroup of GL(2,Z/pZ) with projective image A4 (it will necessarily have determinant index 2). }
    require IsPrime(p) and p ge 5: "p must be a prime greater than 3.";
    F := p mod 4 eq 1 select GF(p) else GF(p^2);  G:=GL(2,F);
    w:=RootOfUnity(4,F); z:=F!PrimitiveRoot(p);
    H := ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[w,0,0,-w],[z,0,0,z]>);
    return ChangeRing(H,Integers(p));
end intrinsic;

// Based on Thm 5.8 of Flannery-O'Brien (Linear groups of small degree over finite fields, Internat. J. Algebra Comput.  15 (2005), 467--502),
intrinsic GL2MaximalS4(p::RngIntElt) -> GrpMat[RngIntRes]
{ The largest subgroup of GL(2,Z/pZ) with projective image S4 (it will necessarily have determinant index 2 for p=1,7 mod 8). }
    require IsPrime(p) and p ge 5: "p must be a prime greater than 3.";
    a := (p mod 8 in [1,7]) select 1 else 2;
    F:=GF(p^2);  G:=GL(2,F);
    w:=RootOfUnity(4,F);  c:=Sqrt(F!2); t:=G![(1+w)/c,0,0,(1-w)/c];  z:=F!PrimitiveRoot(p);
    if a eq 1 then
        H:=ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[(1+w)/c,0,0,(1-w)/c],[z,0,0,z]>);
    elif p mod 8 eq 1 then
        H:=ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[z*(1+w)/c,0,0,z*(1-w)/c],[z^2,0,0,z^2]>);
    else
        H:=ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[u*(1+w)/c,0,0,u*(1-w)/c],[z,0,0,z]>) where u:=Sqrt(z);
    end if;
    return ChangeRing(H,Integers(p));
end intrinsic;

// Based on Thm 5.11 of Flannery-O'Brien (Linear groups of small degree over finite fields, Internat. J. Algebra Comput.  15 (2005), 467--502),
intrinsic GL2MaximalA5(p::RngIntElt) -> GrpMat[RngIntRes]
{ For a prime p = +/-1 mod 5, the largest subgroup of GL(2,Z/pZ) with projective image A5 (it will necessarily have determinant index 2). }
    require IsPrime(p) and p mod 5 in [1,4]: "p must be a prime congruent to +/-1 mod 5.";
    F:=GF(p^2);  G:=GL(2,F);
    w:=RootOfUnity(4,F); b := Sqrt(F!5); z:=F!PrimitiveRoot(p);
    H := ConjugateToRationalSubgroup(sub<G|[(w-1)/2,(w-1)/2,(w+1)/2,-(w+1)/2],[w,0,0,-w],[w/2,(1-b)/4-w*(1+b)/4,(-1+b)/4-w*(1+b)/4,-w/2],[z,0,0,z]>);
    return ChangeRing(H,Integers(p));
end intrinsic;

intrinsic GL2MinimizeGenerators(G::Grp) -> Grp
{ Attempts to minimize the number of generators of a finite group by sampling random elements.  Result is not guaranteed to be optimal unless G is abelian (but it very likely will be optimal or very close to it, see https://doi.org/10.1016/S0021-8693(02)00528-8). }
    require IsFinite(G): "G must be a finite group";
    n := #G;
    if IsAbelian(G) then Gab,pi := AbelianGroup(G); B := AbelianBasis(Gab); return sub<G|[Inverse(pi)(b):b in B]>; end if;
    r := 2;
    while true do
        for i:=1 to 100 do H := sub<G|[Random(G):i in [1..r]]>; if #H eq n then return H; end if; end for;
        r +:= 1;
    end while;
end intrinsic;

intrinsic GL2Standardize(H::GrpMat) -> GrpMat
{ Given a subgroup of GL(2,Z/NZ) attempts to conjugate to a nice form (e.g. diagonal or upper triangular).  Ths can be very slow, use with caution. }
    require Degree(H) eq 2: "H should be a subgroup of GL(2,R) for some finite ring R.";
    function IsDiagonal(A) return A[1][2] eq 0 and A[2][1] eq 0; end function;
    function IsDiagonalOrAntiDiagonal(A) return (A[1][2] eq 0 and A[2][1] eq 0) or (A[1][1] eq 0 and A[2][2] eq 0); end function;
    function IsUpperTriangular(A) return A[2][1] eq 0; end function;
    function IsZDiagonal(A) return A[1][1] eq A[2][2]; end function;
    function IsZDiagonalorNZDiagonal(A) return A[1][1] eq A[2][2] or A[1][1] eq -A[2][2]; end function;
    C := [K:K in Conjugates(GL(2,BaseRing(H)),H)];
    for K in C do if &and[IsDiagonal(h):h in Generators(K)] then return K; end if; end for;
    for K in C do if &and[IsUpperTriangular(h):h in Generators(K)] then return K; end if; end for;
    for K in C do if &and[IsDiagonalOrAntiDiagonal(h):h in Generators(K)] then return K; end if; end for;
    for K in C do if &and[IsZDiagonal(h):h in Generators(K)] then return K; end if; end for;
    for K in C do if &and[IsZDiagonalorNZDiagonal(h):h in Generators(K)] then return K; end if; end for;
    return Sort(C,func<a,b|&+[#[c:c in Eltseq(g)|c eq 0]:g in Generators(b)] - &+[#[c:c in Eltseq(g)|c eq 0]:g in Generators(a)]>)[1];
end intrinsic;

// Magma wants matrices to act on row vectors from the right, so when computing orbits we transpose
// to remain consistent with our convention that matrices act on column vectors from the left.

intrinsic GL2OrbitSignature(H::GrpMat:N:=0) -> SeqEnum[SeqEnum[RngIntElt]]
{ The orbit signature of H (the ordered list of triples [e,s,m] where m is the number of left H-orbits of (Z/NZ)^2 of size s and exponent e). }
    if N eq 0 then N := GL2Level(H); end if;  if N eq 1 then return [[1,1,1]]; end if;
    H := GL2Transpose(ChangeRing(H,Integers(N)));
    D := Divisors(N);
    function ord(v) return Min([n:n in D|n*v eq 0*v]); end function;
    M := {*[ord(o[1]),#o]:o in Orbits(H)*};
    return Sort([r cat [Multiplicity(M,r)]:r in Set(M)]);
end intrinsic;

intrinsic GL2TorsionDegree (H::GrpMat:N:=0) -> RngIntElt
{ The minimal size of a left H-orbit of (Z/NZ)^2 of exponent N (for elliptic curves with mod-N image H this is the minimal degree extension over which they acquire a rational point of order N). }
    if N eq 0 then N := GL2Level(H); end if;  if N eq 1 then return 1; end if;
    O := GL2OrbitSignature(H:N:=N);  d := Min([r[2]:r in O|r[1] eq N]); return d;
end intrinsic;

intrinsic GL2IsogenySignature(H::GrpMat:N:=0) -> SeqEnum[SeqEnum[RngIntElt]]
{ The isogeny signature of the subgroup H of GL(2,Z/NZ) (the ordered list of triples [e,s,m] where m is the number of left H-orbits of cyclic submodules of (Z/NZ)^2 of size s and degree e). }
    if N eq 0 then N := GL2Level(H); end if;  if N eq 1 then return [[1,1,1]]; end if;
    H := GL2Transpose(ChangeRing(H,Integers(N)));
    S := {sub<RSpace(Integers(N),2)|[i,j]>:i in Divisors(N),j in [0..N-1]};
    X := {* [#v,#(v^H)] : v in S*};
    return Sort([r cat [ExactQuotient(Multiplicity(X,r),r[2])]: r in Set(X)]);
end intrinsic;

intrinsic GL2IsogenyDegree (H::GrpMat:N:=0) -> RngIntElt
{ The minimal size of a left H-orbit of a cyclic submodule of (Z/NZ)^2 of degree N (for elliptic curves with mod-N image H this is the minimal degree extension over which they acquire a rational cyclic isogeny of degree N). }
    if N eq 0 then N := GL2Level(H); end if;  if N eq 1 then return 1; end if;
    O := GL2IsogenySignature(H);  d := Min([r[2]:r in O|r[1] eq N]);  return d;
end intrinsic;

intrinsic GL2ClassSignature(H::GrpMat:N:=0) ->RngIntElt
{ The class signature of H (the ordered list of 5-tuples (o,d,t,s,m) where m is the number of conjugacy classes of elements of H of size s, order o, determinant d, trace t. }
    if N eq 0 then N := GL2Level(H); end if;  if N eq 1 then return []; end if;
    function csig(c) return [c[1],Integers()!Determinant(c[3]),Integers()!Trace(c[3]),c[2]]; end function;
    C := ConjugacyClasses(ChangeRing(H,Integers(N)));
    S := {* csig(c) : c in C *};
    return Sort([r cat [Multiplicity(S,r)]:r in S]);
end intrinsic;

intrinsic GL2Twists(H::GrpMat:IncludeSelf:=false) -> SeqEnum[GrpMat]
{ Given a subgroup H of GL(2,Z/NZ), returns the list of subgroups K of GL(2,Z/NZ) with the same determinant index and intersection with SL(2,Z/NZ), up to GL2-conjugacy (H is not included unless IncludeSelf is set to true). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return IncludeSelf select [H] else []; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    GL2:=GL(2,R); SL2:=SL(2,R);
    H1 := H meet SL2;  d := GL2DeterminantIndex(H);
    K := Normalizer(GL2,H1);
    Q,pi := quo<K|H1>; QH := pi(H);
    m := #UnitGroup(R) div d;
    S := [Inverse(pi)(K`subgroup) : K in Subgroups(Q:OrderEqual:=m,IsAbelian:=true) | IncludeSelf or not IsConjugate(Q,QH,K`subgroup)];
    return [K : K in S|GL2DeterminantIndex(K) eq d];
end intrinsic;

// Given a subgroup H of GL(2,Z/NZ) returns <H,-I> subset GL(2,ZNZ) followed by a list of non GL2-conjugate index 2 subgroups of <H,-I> that do not contain -I
// Quadratic twists all have the same level
intrinsic GL2QuadraticTwists(H::GrpMat:IncludeSelf:=false) -> SeqEnum[GrpMat]
{ Given a subgroup H of GL(2,Z/NZ), returns the list of subgroups K of GL(2,Z/NZ) for which <H,-I> = <K,-I> (H is not included unless IncludeSelf is set to true). }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return IncludeSelf select [H] else []; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    I := Identity(H);  nI := -I;
    if I eq nI then return [H]; end if;
    G := nI in H select H else sub<GL(2,R)|H,nI>;
    S := [K`subgroup:K in Subgroups(H:IndexEqual:=2)|not nI in K`subgroup];
    if G ne H and not IncludeSelf then S := [K:K in S| not IsConjugate(G,H,K)]; end if;
    if #S gt 1 then
        GL2 := GL(2,R); N := GL2Level(H);
        X := index(S,func<H|GL2OrbitSignature(H:N:=N)>);
        for k in Keys(X) do X[k] := [X[k][i]:i in [1..#X[k]]|&and[not IsConjugate(GL2,X[k][i],X[k][j]):j in [1..i-1]]]; end for;
        S := &cat[X[k]:k in Keys(X)];
    end if;
    S := ((IncludeSelf or G ne H) select [G] else []) cat S;
    return S;
end intrinsic;

intrinsic GL2GenericQuadraticTwist(H::GrpMat) -> GrpMat
{ Returns the group <H,-I>. }
    R := BaseRing(H);  if not IsFinite(R) and #H eq 1 then return H; end if;
    require Degree(H) eq 2 and Type(R) eq RngIntRes: "H must be a sugroup of GL(2,Z/NZ) for some positive integer N.";
    return sub<GL(2,BaseRing(H))|H,-Identity(H)>;
end intrinsic;

intrinsic GL2MinimalConjugate(H::GrpMat) -> GrpMat
{ The lexicographically minimal conjugate of H in GL(2,Z/NZ), where N is the level of H.  This is expensive to compute, use sparingly! }
    N := GL2Level(H);
    if N eq 1 then return sub<GL(2,Integers())|>; end if;
    R := Integers(N);
    H := ChangeRing(H,R);
    GL2 := GL(2,R);
    S := Conjugates(GL2,H);
    h := GL2![0,1,1,0];
    T := [H:H in S|h in H];
    if #T gt 0 then S := T; else h := GL2![0,1,1,1]; T := [H:H in S|h in H]; if #T gt 0 then S := T; end if; end if;
    if #S eq 1 then return Sort([Eltseq(h):h in S[1]]); end if;
    return Min([Sort([Eltseq(h):h in K]):K in S]);
end intrinsic;

// This section consists of point-counting helper functions which are not part of the external interface

// returns an array C such that C[q mod N] is the number of Fq-rational cusps on X_H for q coprime to the level N of H
function RationalCuspCounts(H);
    N := #BaseRing(H);
    GL2 := GL(2,Integers(N));
    if not -Identity(H) in H then H := sub<GL2|H,[-1,0,0,-1]>; end if;
    pi := CosetAction(GL2,H);
    U := sub<GL2|[1,1,0,1]>;
    C := [-1:q in [1..N]];
    for q in [1..N] do
        if C[q] lt 0 and GCD(q,N) eq 1 then
            H := sub<GL2|[q,0,0,1]>;
            S := [Integers()!h[1][1]:h in H];
            c := #{o:o in Orbits(pi(U))|o^pi(sub<GL2|[q,0,0,1]>) eq {o}};
            for h in H do if Order(h[1][1]) eq #H then C[Integers()!h[1][1]] := c; end if; end for;
        end if;
    end for;
    return C;
end function;

// Use Cornacchia's algorithm to solve x^2 + dy^2 = m for (x,y) with y != 0
function norm_equation(d,m)
    if not IsSquare(m) then return NormEquation(d,m); end if;
    t,r1 := IsSquare(Integers(m)!-d);
    if not t then return false,_,_; end if;
    r1 := Integers()!r1;
    if 2*r1 gt m then r1 := m-r1; end if;
    r0 := m;
    while r1^2 ge m do s := r0 mod r1; r0:= r1;  r1:= s; end while;
    t,s := IsSquare((m-r1^2) div d);
    if not t then return false,_,_; end if;
    assert s ne 0 and r1^2 + s^2*d eq m;
    return t,r1,s;
end function;

// returns a table whose (-D)th entry is h(-D), using cached data xgclassnumbers.dat if present (will create if not)
function ClassNumberTable(N)
    try
        fp := Open("xgclassnumbers.dat","r");
        htab := ReadObject(fp);
    catch e
        htab := [];
    end try;
    N := Abs(N);
    if #htab lt N then 
        htab := [d mod 4 in [0,3] select ClassNumber(-d) else 0 : d in [1..N]];
        fp := Open("xgclassnumbers.dat","w");
        WriteObject(fp,htab);
        delete fp;
    end if;
    fp := Open("xgclassnumbers.dat","r");
    htab := ReadObject(fp);
    return htab[1..N];    
end function;

function GetClassNumber(htab,D) return -D le #htab select htab[-D] else ClassNumber(D); end function;

// Apply Theorem 2.1 of Duke and Toth, given a,b,D satisfying that 4q=a^2-b^2D, where a is the trace of the Frobenius endomorphism pi,
// D is the discriminant of Z[pi], and b is the index of Z[pi] in End(E) unless Z[pi]=Z in which case D=1 and b=0
// returns a list of integers representing an element of GL_2(Z) with trace a and determinant q representing action of Frob (up to conj)
function FrobMat(a,b,D)
    //if q ne 0 then assert 4*q eq a^2-b^2*D; end if;
    return [(a+b*d) div 2, b, b*(D-d) div 4, (a-b*d) div 2] where d := D mod 2;
end function;
    
forward j1728FM;

// See Waterhouse Theorem 4.1 in http://www.numdam.org/article/ASENS_1969_4_2_4_521_0.pdf
// and Oort (p.37) in https://www.math.nyu.edu/~tschinke/books/finite-fields/final/05_oort.pdf
// for superinsingular j=0,1728
// The function j0FM and j1728FM below each return a list of pairs <A,w> where A ia Frobenius matrix and w is a rational weight
// The rational points in the fiber of X_H -> X(1) above j=0 can then be computed as the weighted sum of fixpoints of the A's
function j0FM(q)
    _,p,e:=IsPrimePower(q);
    if p eq 2 then return j1728FM(q); end if;
    if p mod 3 eq 2 then
        if e mod 2 eq 1 then
            return [<FrobMat(0,1,-4*q),1>];
        else
            a := 2*p^(e div 2); b:= 0;
        end if;
    elif p mod 3 eq 1 then
        _,a,b := norm_equation(3,4*q);
    else // p = 3
        if e mod 2 eq 1 then
            return [<FrobMat(0,2,-q),1/6>,<FrobMat(0,1,-4*q),1/2>,<FrobMat(3^((e+1) div 2),3^((e-1) div 2),-3),1/3>];
        else
            return [<FrobMat(0,1,-4*q),1/2>,<FrobMat(3^(e div 2),3^(e div 2),-3),1/3>,<FrobMat(2*3^(e div 2),0,1),1/6>];
        end if;
    end if;
    // note that if b=0 then D=-3 will be ignored
    return [<FrobMat(a,b,-3),1/3>,<FrobMat((a+3*b) div 2,(a-b) div 2,-3),1/3>,<FrobMat((a-3*b) div 2,(a+b) div 2,-3),1/3>];
end function;

function j0Points(N,f,q) GL2 := GL(2,Integers(N)); return Integers()! &+[f(GL2!A[1])*A[2]:A in j0FM(q)]; end function;

function j1728FM(q)
    _,p,e:=IsPrimePower(q);
    if p eq 3 then return j0FM(q); end if;
    if p mod 4 eq 3 then
        if e mod 2 eq 1 then
            return [<FrobMat(0,2*p^((e-1) div 2),-p),1/2>,<FrobMat(0,p^((e-1) div 2),-4*p),1/2>];
        else
            a := 2*p^(e div 2); b:=0;
        end if;
    elif p mod 4 eq 1 then
        _,a,b := norm_equation(4,4*q);
    else // p = 2
        // in the trace 0 cases we could pull 2^x into b but the matrices will be conjugate
        if e mod 2 eq 1 then
            return [<FrobMat(0,1,-4*q),1/2>,<FrobMat(2^((e+1) div 2),2^((e-1) div 2),-4),1/2>];
        else
            // the weight 2/3 comes from 4*1/6 for trace 1
            return [<FrobMat(0,1,-4*q),1/4>,<FrobMat(2^(e div 2),2^(e div 2),-3),2/3>,<FrobMat(2*2^(e div 2),0,1),1/12>];
        end if;
    end if;
    // note that if b=0 then D=-4 will be ignored
    return [<FrobMat(a,b,-4),1/2>,<FrobMat(2*b,a div 2,-4),1/2>];
end function;

function j1728Points(N,f,q) GL2 := GL(2,Integers(N)); return Integers()! &+[f(GL2!A[1])*A[2]:A in j1728FM(q)]; end function;

// Given level N, permutation character f table C indexed by conjugacy class, class map f, class number table htab for -D <= 4q, prime power q coprime to {N
// returns the number of non-cuspidal points on X_G(Fq) that coming from j!=0,1728
function jNormalPoints(N,f,htab,q)
    t,p,e := IsPrimePower(q); assert(t);
    GL2 := GL(2,Integers(N));
    assert GCD(q,N) eq 1;
    cnt := 0;
    // iterate over ordinary traces
    for a in [1..Floor(2*Sqrt(q))] do
        if a mod p eq 0 then continue; end if; // supersingular cases handled below
        D1 := a^2-4*q; // discriminant of Z[pi] for trace a
        D0 := FundamentalDiscriminant(D1);
        _,v:=IsSquare (D1 div D0); // now 4*q = a^2 - v^2*D0 with D0 fundamental
        for u in Divisors(v) do
            D := D0*u^2;
            if D ge -4 then continue; end if;   // ignore j=0,1728
            n := f(GL2!FrobMat(a,v div u,D));
            if n gt 0 then cnt +:= n * GetClassNumber(htab,D); end if;
        end for;
    end for;
    if p le 3 then return cnt; end if;
    // Now deal with trace 0 (e odd) and trace 2sqrt(q) (e even), excluding j=0,1728 which are handled separately
    s0 := p mod 3 eq 2 select 1 else 0; s1728 := p mod 4 eq 3 select 1 else 0;
    if e mod 2 eq 1 then
    // handle trace 0, which for j != 1728 occurs only when e is odd
    // See https://wwwproxy.iwr.uni-heidelberg.de/groups/arith-geom/centeleghe/up.pdf for why we divide by 2
    // we distinguish D=-p and D=-4p cases, and note that h(-4p)=3h(-p) for p=3 mod 8 while h(-4p)=h(-p) for p-7 mod 8
    // for p = 1 mod 4 we get h(-4p)/2
    // for p = 3 mod 8 we get h(-p)/2 + h(-4p)/2 = 2h(-p)
    // for p = 7 mod 8 we get h(-p)/2 + h(-4p)/2 = h(-p)
        if p mod 4 eq 3 then
            a:=0; D:=-p; b:=2*p^((e-1) div 2);
            n := f(GL2!FrobMat(a,b,D));
            cnt +:= n*((GetClassNumber(htab,D)-1) div 2);                                    // Don't include j=1728
        end if;
        a:=0; D:=-4*p; b:=p^((e-1) div 2);
        n := f(GL2!FrobMat(a,b,D));
        cnt +:= n * ((GetClassNumber(htab,D)-s0-s1728) div 2);         // Don't include j=0,1728
    else
        // handle trace 2*sqrt(q), which occurse only when e is even
        a:=2*p^(e div 2); D:=1; b:=0;
        n := f(GL2!FrobMat(a,b,D));
        // Schoof 1987 "Nonsingular plane cubics over finite fields" counts curves with trace 2sqrt(q)
        cnt +:= n * ( (p+6-4*KroneckerSymbol(-3,p)-3*KroneckerSymbol(-4,p)) div 12 - s0 - s1728 );
    end if;
    return cnt;
end function;

// htab:=ClassNumbers(4*p), f:=GL2PermutationCharacter(H cup -H), CC:=RationalCuspCounts(H)
function XHPoints(N,htab,f,C,q)
    assert GCD(q,N) eq 1;
    j := jNormalPoints(N,f,htab,q); j0 := j0Points(N,f,q); j1728 := GCD(q,6) eq 1 select j1728Points(N,f,q) else 0;
    return j+j0+j1728+C[q mod N];
end function;

intrinsic GL2PointCount(H::GrpMat,q::RngIntElt) -> RngIntElt
{ The number of Fq-rational points on X_H. }
    N,H := GL2Level(H);
    require IsPrimePower(q) and GCD(q,N) eq 1: "q must be a prime power that is coprime to the level of H";
    if N eq 1 then return q+1; end if;
    GL2 := GL(2,Integers(N));
    htab := q lt 2^13 select ClassNumberTable(4*q) else [];
    C := [0:i in [1..N]]; // only q mod N will be filled in
    C[q mod N] := GL2RationalCuspCount(H,q);
    f := GL2PermutationCharacter(sub<GL2|H,-Identity(GL2)>);
    return XHPoints(N,htab,f,C,q);
end intrinsic;

intrinsic GL2PointCounts(H::GrpMat,B::RngIntElt:B0:=1,PrimePowers:=false,Traces:=false) -> SeqEnum
{ The number of Fp-rational points on X_H for p not dividing N up to B (and p >= B0 if specified).  Set traces flag to get traces instead of point counts. Return value is an array with entries for each prime p <= B not dividing the level, where each entry is either an integer giving the point count (or trace) over Fp, or a list of integers giving point counts (or traces) over Fq for q=p,p^2,...<= B.}
    N,H := GL2Level(H);
    if N eq 1 then return [Traces select 0 else p+1:p in PrimesInInterval(B0,B)]; end if;
    GL2 := GL(2,Integers(N));
    htab := ClassNumberTable(4*B);
    C := RationalCuspCounts(H);
    f := GL2PermutationCharacter(sub<GL2|H,-Identity(GL2)>);
    badp := Set(PrimeDivisors(N));
    if Traces then
        if PrimePowers then
            return [[p^i+1-XHPoints(N,htab,f,C,p^i):i in [1..Floor(Log(p,B))]] : p in PrimesInInterval(B0,B) | not p in badp];
        else
            return [p+1-XHPoints(N,htab,f,C,p) : p in PrimesInInterval(B0,B) | not p in badp];
        end if;
    else
        if PrimePowers then
            return [[XHPoints(N,htab,f,C,p^i):i in [1..Floor(Log(p,B))]] : p in PrimesInInterval(B0,B) | not p in badp];
        else
            return [XHPoints(N,htab,f,C,p) : p in PrimesInInterval(B0,B) | not p in badp];
        end if;
    end if;
end intrinsic;

intrinsic GL2PointCounts(H::GrpMat,p::RngIntElt,r::RngIntElt:Traces:=false) -> SeqEnum[RngIntElt]
{ The number of Fq-rational points on X_H for q=p,p^2,...,p^r for a prime power p.  Set traces flag to get traces instead of point counts. }
    N,H := GL2Level(H);
    require IsPrimePower(p) and GCD(N,p) eq 1: "p must be prime that does not divide the level.";
    require r ge 1: "r must be a positive integer";
    if p^r ge 10^12 then printf "Warning counting points over Fq with q=%o^%o=%o is going to take a while...\n", p, r, p^r; end if;
    if N eq 1 then return [Traces select 0 else p^i+1 : i in [1..r]]; end if;
    GL2 := GL(2,Integers(N));
    htab := p lt 2^13 select ClassNumberTable(4*p) else [];
    C := RationalCuspCounts(H);
    f := GL2PermutationCharacter(sub<GL2|H,-Identity(GL2)>);
    if Traces then
        return [q+1-XHPoints(N,htab,f,C,q) where q:=p^i : i in [1..r]];
    else
        return [XHPoints(N,htab,f,C,p^i) : i in [1..r]];
    end if;
end intrinsic;

intrinsic GL2Traces(H::GrpMat,B::RngIntElt:B0:=1,PrimePowers:=false) -> SeqEnum[RngIntElt]
{ Frobenius traces of X_H at p not dividing N up to B (and p >= B0 if specified). }
    return GL2PointCounts(H,B:B0:=B0,PrimePowers:=PrimePowers,Traces:=true);
end intrinsic;

intrinsic GL2Traces(H::GrpMat,p::RngIntElt,r::RngIntElt) -> SeqEnum[RngIntElt]
{ The traces of Frobneius of X_H/Fq for q=p,p^2,...,p^r. }
    return GL2PointCounts(H,p,r:Traces:=true);
end intrinsic;

intrinsic GL2LPolynomial(H::GrpMat,q::RngIntElt) -> RngUPolElt
{ The L-polynomial of X_H/Fq for a prime power q coprime to the level of H. }
    g := GL2Genus(H);
    R<T>:=PolynomialRing(Integers());
    if g eq 0 then return R!1; end if;
    return PointCountsToLPolynomial(GL2PointCounts(H,q,g),q);
end intrinsic;

intrinsic GL2IsogenyClass(H::GrpMat) -> MonStgElt, RngIntElt
{ The Cremona label of the isogeny class of a genus 1 curve X_H, along with its rank.  Will fail if the level is out of range of the Cremona DB. }
    N,H := GL2Level(H);
    require N gt 1:  "H must be have genus 1.";
    require GL2DeterminantIndex(H) eq 1 and GL2Genus(H) eq 1: "H must have determinant index 1 and genus 1";

    P := PrimeDivisors(N);
    badi := {#PrimesUpTo(p):p in P};

    // Computes an integer M so that the conductor of any elliptic curve E/Q with good reduction outside P divides M.
    M := &*[p^2:p in P];
    if 2 in P then M *:= 2^6; end if;
    if 3 in P then M *:= 3^3; end if;

    D:=EllipticCurveDatabase();
    assert M lt LargestConductor(D);  // Ensures that J is isomorphic to a curve in the current database

    EE:= &cat[[EllipticCurve(D,N,i,1) : i in [1.. NumberOfIsogenyClasses(D,N)]] : N in Divisors(M)];   
    // The Jacobian of X_G is isogenous to precisely one of the curves in EE.

    function GoodTracesOfFrobenius(E,B) // Return traces up to B with traces at bad p set to p+2
        T := TracesOfFrobenius(E,B);
        return [T[i] : i in [1..#T] | not i in badi];
    end function;
  
    B := 20;  // this is already enough to distinguish all isogeny classes of prime power level <= 400000
    while #EE gt 1 do
        T := GL2Traces(H,B);
        EE:= [E: E in EE | GoodTracesOfFrobenius(E,B) eq T];
        B *:= 2;
   end while;
   assert #EE eq 1;

   // return the isogeny class label of our representative curve, along with its rank
   _,c:=Regexp("[0-9]+[a-z]+",CremonaReference(EE[1]));
   return c, Rank(EE[1]);
end intrinsic;

intrinsic GL2QAdmissible(H::GrpMat:RequireNegId:=false) -> BoolElt
{ True if the specified subgroup of GL2(Z/NZ) has determinant index one and contains an element corresponding to complex conjugation (these are preconditions to having Q-rational points). }
    if not IsFinite(BaseRing(H)) and #H eq 1 then return true; end if;
    return (not RequireNegId or -Identity(H) in H) and (GL2DeterminantIndex(H) eq 1) and GL2ContainsComplexConjugation(H);
end intrinsic;

intrinsic GL2QObstructions(H::GrpMat:B:=0) -> SeqEnum[RngIntElt]
{ List of good places p where X_H has no Qp-points (p=0 is used for the real place). }
    require GL2DeterminantIndex(H) eq 1: "H must have determinant index 1 (otherwise it is obstructed at infinitely many places).";
    N,H := GL2Level(H);
    if N eq 1 then return [Integers()|]; end if;
    if GL2RationalCuspCount(H) gt 0 then return [Integers()|]; end if;
    X := GL2ContainsComplexConjugation(H) select [Integers()|] else [Integers()|0];
    g := GL2Genus(H);  if g eq 0 then return X; end if;
    maxp := B gt 0 select B else 4*g^2;
    badp := Set(PrimeDivisors(N));
    P := [p:p in PrimesInInterval(1,maxp)| not p in badp];
    cnts := GL2PointCounts(H,maxp);
    return X cat [P[i] : i in [1..#P] | cnts[i] eq 0];
end intrinsic;

intrinsic GL2QInfinite(N::RngIntElt) -> SeqEnum[GrpMat]
{ List of subgroups of GL(2,Z/NZ) for which X_H(Q) is infinite (not all of which will have level N). }
    require N gt 0: "N must be a positive integer.";
    if N eq 1 then return [sub<GL(2,Integers())|>]; end if;
    Xkey := func<r|<r[1],r[2],r[3],r[4],r[5]>>;
    // Qinf will only be applied to Q-admissible subgroups, in which case g(H)=0 => X_H(Q) is infinite
    Qinf := func<genus,H|genus eq 0 or (genus eq 1 and rank gt 0 where _,rank:=GL2IsogenyClass(H))>;
    GL2:=GL(2,Integers(N));
    r := <1,1,0,[[1,1,1]],1,GL2>; S := [r];
    X := AssociativeArray(); X[Xkey(r)] := S;
    n := 1;
    while n le #S do
        L := [H`subgroup: H in MaximalSubgroups(S[n][6]) | GL2QAdmissible(H`subgroup:RequireNegId)];
        genus := [GL2Genus(H) : H in L];
        I := [i: i in [1..#L]|genus[i] le 1];
        L := [<level,GL2Index(L[i]),genus[i],GL2OrbitSignature(L[i]:N:=level),GL2ScalarIndex(L[i]),L[i]> where level:=GL2Level(L[i]):i in I];
        // Reduce to conjugacy class reps
        Z := index(L,Xkey);
        L := [];
        for k in Keys(Z) do
            if #Z[k] gt 1 then Z[k] := [Z[k][i]:i in [1..#Z[k]] | &and[not IsConjugate(GL2,Z[k][i][6],Z[k][j][6]):j in [1..i-1]]]; end if;
            L cat:= Z[k];
        end for;
        // Only keep groups we haven't already seen that have X_H(Q) infinite
        L := [r : r in L | (not IsDefined(X,k) or &and[not IsConjugate(GL2,r[6],s[6]):s in X[k]] where k:=Xkey(r)) and Qinf(r[3],r[6])];
        S := S cat L;
        for r in L do k:=Xkey(r); if IsDefined(X,k) then Append(~X[k],r); else X[k] := [r]; end if; end for;
        n +:= 1;
    end while;
    return &cat[&cat[[H : H in GL2QuadraticTwists(r[6]:IncludeSelf) | Qinf(r[3],r[6])] : r in X[k]]:k in Keys(X)];
end intrinsic;

intrinsic GL2ArithmeticallyMaximalBounds(p::RngIntElt) -> RngIntElt, RngIntElt
{ A pair of integers N(p), I(p) such tthat every Q-admissible arithmetically maximal subgroup of GL(2,Zp) has level at most N(p) and index at most I(p). }
    require IsPrime(p): "p must be prime";
    if p gt 13 then
        G:=GL(2,Integers(p));
        m := Max([#G div H`order : H in MaximalSubgroups(G) | GL2QAdmissible(H`subgroup)]);
        return p,m;
    end if;
    e :=  [5,3,2,1,1,1][#PrimesInInterval(1,p)]; // from SZ17, see Lemma 3.2
    S := GL2QInfinite(p^e);  GL2 := GL(2,Integers(p^(e+1)));
    m := Max([Max([0] cat [#GL2 div H`order : H in MaximalSubgroups(G) | GL2QAdmissible(H`subgroup)]) where G:=GL2Lift(H0,p^(e+1)):H0 in S]);
    return p^(e+1),m;
end intrinsic;

intrinsic GL2CompareLabels(a::MonStgElt,b::MonStgElt) -> RngIntElt
{ Lexicographically compares subgroup labels of the form N.i.g.n or N.i.g.d.n (N=level, i=index, g=genus, d=determinant index, n=ordinal) as lists of integers.  Returns -1,0,1. }
    if a eq b then return 0; end if; if a eq "?" then return 1; end if; if b eq "?" then return -1; end if;
    r := [StringToInteger(x):x in Split(a,".")]; s := [StringToInteger(x):x in Split(b,".")];
    require #r in {4,5} and #s in {4,5}: "Invalid subgroup label";
    if #r ne #s then if #r lt #s then r:=r[1..3] cat [1] cat r[4]; else s:=s[1..3] cat [1] cat s[4]; end if; end if;
    return r lt s select -1 else 1;
end intrinsic;

intrinsic GL2CompareLabelLists(a::SeqEnum[MonStgElt],b::SeqEnum[MonStgElt]) -> RngIntElt
{ Lexicographically compares two lists of subgroup labels. }
    if a eq b then return 0; end if;
    for i in [1..#a] do
        if i gt #b then return 1; end if;
        if a[i] ne b[i] then return GL2CompareLabels(a[i],b[i]); end if;
    end for;
    return #a lt #b select -1 else 0;
end intrinsic;

gl2node := recformat<
    label:MonStgElt,
    level:RngIntElt,
    index:RngIntElt,
    genus:RngIntElt,
    orbits:SeqEnum,
    zindex:RngIntElt,
    children:SeqEnum,
    parents:SeqEnum,
    subgroup:GrpMat>;

intrinsic GL2Lattice(N::RngIntElt, IndexLimit::RngIntElt : DeterminantIndex:=1, verbose:=false) -> Assoc
{ Lattice of subgroups of GL(2,Z/NZ) of index bounded by IndexLimit with deteerminant index 1 (or as specified).  Returns a list of records with attributes level, index, genus, orbits, zindex, children, parents, subgroup, where children and parents are indices into this list that identify maximal subgroups and minimal supergroups. }
    require N gt 0 and IndexLimit gt 0: "Level and index limit must be positive integers";
    require IsDivisibleBy(EulerPhi(N),DeterminantIndex): "DeeterminantIndex must divide the order of (Z/NZ)*";
    if N eq 1 then return [rec<gl2node|level:=1,index:=1,genus:=0,orbits:=[[1,1,1]],zindex:=1,childen:=[Integers()|],parents:=[Integers()|],subgroup:=sub<GL(2,Integers())|>>]; end if;
    if verbose then printf "Enumerating subgroups of GL(2,Z/%oZ) of index at most %o...", N, IndexLimit; s := Cputime(); end if;
    S := [H`subgroup: H in Subgroups(GL(2,Integers(N)):IndexLimit:=IndexLimit) | GL2DeterminantIndex(H`subgroup) eq DeterminantIndex];
    if verbose then
        printf "found %o subgroups of determinant index 1 in %.3os\n", #S, Cputime()-s;
        printf "Computing index, level, genus, orbit signature, scalar index for %o groups...", #S; s := Cputime();
    end if;
    T := [<level,GL2Index(H),GL2Genus(H),GL2OrbitSignature(H:N:=level),GL2ScalarIndex(H)> where level:=GL2Level(H) : H in S];
    if verbose then printf "%.3os\nComputing lattice edges for %o groups...", Cputime()-s, #T; s:=Cputime(); end if;
    X := index([1..#T],func<i|<T[i][1],T[i][2],T[i][4],T[i][5]>>);
    M := {};
    for i:= 1 to #T do
        if 2*T[i][2] gt IndexLimit then continue; end if;
        m := [H`subgroup:H in MaximalSubgroups(S[i]:IndexLimit:=IndexLimit div T[i][2])|GL2DeterminantIndex(H`subgroup) eq DeterminantIndex];
        for H in m do
            level := GL2Level(H);  K := ChangeRing(H,Integers(level));
            J := X[<level,GL2Index(K),GL2OrbitSignature(K:N:=level),GL2ScalarIndex(K)>]; j := 1;
            if #J gt 1 then
                GL2:=GL(2,Integers(level));
                while j lt #J do if IsConjugate(GL2,ChangeRing(S[J[j]],Integers(level)),K) then break; end if; j+:=1; end while;
            end if;
            Include(~M,<i,J[j]>);
        end for;
    end for;
    if verbose then printf "found %o edges in %.3os\n", #M, Cputime()-s; end if;
    Xsubs := index(M,func<r|r[1]>:Project:=func<r|r[2]>); subs := func<i|IsDefined(Xsubs,i) select Xsubs[i] else []>;
    Xsups := index(M,func<r|r[2]>:Project:=func<r|r[1]>); sups := func<i|IsDefined(Xsups,i) select Xsups[i] else []>;
    X := index([1..#T],func<i|<T[i][1],T[i][2],T[i][3]>>);
    L := ["" : i in [1..#T]];
    Lsups := [[] : i in [1..#T]];
    if verbose then printf "Labeling %o subgroups...", #S; s := Cputime(); end if;
    cmpkeys := function(a,b)
        n := GL2CompareLabelLists(a[1],b[1]); if n ne 0 then return n; end if;
        if a[2] lt b[2] then return -1; elif a[2] gt b[2] then return 1; end if;
        if a[3] lt b[3] then return -1; elif a[3] gt b[3] then return 1; end if;
        return 0;
    end function;
    format := DeterminantIndex eq 1 select "%o.%o.%o.%o" else "%o.%o.%o." cat sprint(DeterminantIndex) cat ".%o";
    for k in Sort([k:k in Keys(X)]) do
        // all parents of nodes in X[k] correespond to smaller keys and have already been labeled
        for i in X[k] do Lsups[i] := Sort([L[j]:j in sups(i)],func<a,b|GL2CompareLabels(a,b)>); end for;
        n := 1;
        if #X[k] eq 1 then i:=X[k][1]; L[i] := Sprintf(format,k[1],k[2],k[3],n); continue; end if;
        Y := index(X[k],func<i|<Lsups[i],T[i][4],GL2ClassSignature(S[i]:N:=k[1])>>);
        Z := Sort([r:r in Keys(Y)],cmpkeys);
        for r in Z do
            if #Y[r] gt 1 then Y[r] := [a[2]:a in A] where A := Sort([<GL2MinimalConjugate(S[i]),i>:i in Y[r]]); end if;
            for i in Y[r] do L[i] := Sprintf(format,k[1],k[2],k[3],n); n +:= 1; end for;
        end for;
    end for;
    Lsubs := [Sort([L[j]:j in subs(i)],func<a,b|GL2CompareLabels(a,b)>): i in [1..#S]];
    if verbose then printf "%.3os\nMinimizing generators for %o groups...", Cputime()-s, #L; s:=Cputime(); end if;
    X := AssociativeArray();
    for i:=1 to #L do
        H := T[i][1] eq 1 select sub<GL(2,Integers())|> else GL2MinimizeGenerators(ChangeRing(S[i],Integers(T[i][1])));
        X[L[i]]:= rec<gl2node|label:=L[i],level:=T[i][1],index:=T[i][2],genus:=T[i][3],orbits:=T[i][4],zindex:=T[i][5],children:=Lsubs[i],parents:=Lsups[i],subgroup:=H>;
    end for;
    if verbose then printf "%.3os\n", Cputime()-s; end if;
    return X;
end intrinsic;

intrinsic GL2LookupLabel(X::Assoc, H::GrpMat : g:=-1, NotFound:="?") -> MonStgElt
{ The label of the specified subgroup of GL(2,Z/NZ) if it is present in the specified subgroup lattice (up to conjugacy). }
    N := GL2Level(H);
    if N eq 1 then return "1.1.0.1"; end if;
    i := GL2Index(H);  g := g lt 0 select GL2Genus(H) else g;  d := GL2DeterminantIndex(H);
    prefix := d eq 1 select Sprintf("%o.%o.%o",N,i,g) else Sprintf("%o.%o.%o.%o",N,i,g,d);
    if not IsDefined(X,prefix cat ".1") then return NotFound; end if;
    o := GL2OrbitSignature(H:N:=N); z := GL2ScalarIndex(H);
    G := GL(2,Integers(N)); H := ChangeRing(H,Integers(N));
    S := []; n:=1;
    while true do
        k := prefix cat Sprintf(".%o",n); if not IsDefined(X,k) then break; end if;
        if X[k]`orbits eq o and X[k]`zindex eq z then Append(~S,k); end if;
        n +:= 1;
    end while;
    assert #S ne 0; // we assume X is complete, so if H has level,index,genus matching any element of X it must be in X
    if #S eq 1 then return S[1]; end if;
    csig := GL2ClassSignature(H:N:=N);
    S:=[k:k in S|csig eq GL2ClassSignature(X[k]`subgroup)]; assert #S ne 0;
    if #S eq 1 then return S[1]; end if;
    for k in S do if IsConjugate(G,H,X[k]`subgroup) then return k; end if; end for;
    assert false;
end intrinsic;

intrinsic GL2QInfinite(X::Assoc) -> SeqEnum[MonStgElt]
{ Sorted list of labels in the specified subgroup lattice for which X_H(Q) is infinite. }
    posrank := func<r|"rank" in Names(r) select r`rank gt 0 else (rank gt 0 where _,rank:=GL2IsogenyClass(r`subgroup))>;
    S := Sort([k : k in Keys(X) | X[k]`genus le 1 and GL2QAdmissible(X[k]`subgroup) and (X[k]`genus eq 0 or posrank(X[k]))],func<a,b|GL2CompareLabels(a,b)>);
    return S;
end intrinsic;

intrinsic GL2ArithmeticallyMaximal(X) -> SeqEnum[MonStgElt]
{ Sorted list of labels of arithmetically maximal subgroups in the specified subgroup lattice (these are Q-admissible groups with finitely many Q-points whose parents all have infinitely many Q-points). }
    Q := Set(GL2QInfinite(X));
    S := Sort([k:k in Keys(X)|not k in Q and Set(X[k]`parents) subset Q and GL2QAdmissible(X[k]`subgroup)],func<a,b|GL2CompareLabels(a,b)>);
    return S;
end intrinsic;
