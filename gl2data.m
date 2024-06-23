/*
    This file implements the following functions:

        GL2Data(p) -- computes p-power level subgroup data that includes all arithmetically maximal subgroups
        GL2Load(filename) -- loads subgroup data created by GL2Data, returning an associative array X indexed by label

    Subgroups of GL_2(Zhat) with determinant index 1 are identified by labels of the form N.i.g.n,
    where N is the level, i is the index, g is the genus, and n is a (deterministic) tie-breaker.
    These labels are computed by GL2Data.  See gl2rec for details on the data computed for each subgroup.

    The total time to compute GL2Data(p) for p in 3,5,7,11,...,37 is arouond an hour.
    GL2Data(2) takes aroound 6 hours, but only about 1 if you set Cheat:=true (this will make it use level=32, index=96 as bounds rather than level=64, index=192).

    This code relies on two external datafiles:

        cmfdata.txt -- newform data for prime power levels 2,..,37
        cpdata.txt -- Cummins-Pauli data for subgroups of SL(2,Z)
*/

Attach("gl2.m");

// this record format extends that of gl2node in gl2.m (names need to be compatible!)
gl2rec := recformat<
    label:MonStgElt,
    level:RngIntElt,
    index:RngIntElt,
    genus:RngIntElt,
    zindex:RngIntElt,
    subgroup:GrpMat,
    children:SeqEnum,
    parents:SeqEnum,
    reductions:SeqEnum,
    orbits:SeqEnum,
    iorbits:SeqEnum,
    qtwist:MonStgElt,
    obstructions:SeqEnum,
    cusps:RngIntElt,
    ratcusps:RngIntElt,
    iclass:MonStgElt,
    rank:RngIntElt,
    cplabel:MonStgElt,
    newforms:SeqEnum,
    dims:SeqEnum>;

function strip(s)
    return Join(Split(Join(Split(s," "),""),"\n"),"");
end function;

function sprint(X)
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return strip(Sprintf("%o",X));
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

function GL2RecToString(r)
    return Join([r`label,sprint(r`level),sprint(r`index),sprint(r`genus),sprint(r`zindex),sprint([Eltseq(g):g in Generators(r`subgroup)]),
                 sprint(r`children),sprint(r`parents),sprint(r`reductions),sprint(r`orbits),sprint(r`iorbits),r`qtwist,sprint(r`obstructions),
                 sprint(r`cusps),sprint(r`ratcusps),r`iclass,sprint(r`rank),r`cplabel,sprint(r`newforms),sprint(r`dims)],":");
end function;

function atoi(s) return StringToInteger(s); end function;

function GL2RecFromString(s)
    function labels(s) return Split(s[2..#s-1],","); end function;
    s := Split(s,":");
    N := atoi(s[2]); H := N eq 1 select sub<GL(2,Integers())|> else sub<GL(2,Integers(N))|eval(s[6])>;
    return rec<gl2rec|label:=s[1],level:=N,index:=atoi(s[3]),genus:=atoi(s[4]),zindex:=atoi(s[5]),subgroup:=H,children:=labels(s[7]),parents:=labels(s[8]),
                      reductions:=labels(s[9]),orbits:=eval(s[10]),iorbits:=eval(s[11]),qtwist:=s[12],obstructions:=eval(s[13]),cusps:=atoi(s[14]),ratcusps:=atoi(s[15]),
                      iclass:=s[16],rank:=atoi(s[17]),cplabel:=s[18],newforms:=labels(s[19]),dims:=eval(s[20])>;
end function;

// file format is lavel:index:genus:CPlabel:generators
function SL2LoadCPData(filename,p)
    cprecs := [Split(r,":"):r in Split(Read(filename))];
    cprecs := [r:r in cprecs|N ne 1 and IsPrimePower(N) and IsDivisibleBy(N,p) where N:=StringToInteger(r[1])];
    return [<atoi(r[1]),atoi(r[2]),atoi(r[3]),r[4],sub<GL(2,Integers(atoi(r[1])))|eval(r[5])>>:r in cprecs];
end function;

cmfrec := recformat<
    label:MonStgElt,
    level:RngIntElt,
    cond:RngIntElt,
    dim:RngIntElt,
    rank:RngIntElt,
    hash:FldFinElt,
    traces:SeqEnum>;

function CMFLabelCompare(s,t)
    a := Split(s,".");  b := Split(t,".");
    if a[1] ne b[1] then return StringToInteger(a[1]) - StringToInteger(b[1]); end if;
    if a[2] ne b[2] then return StringToInteger(a[2]) - StringToInteger(b[2]); end if;
    if a[3] ne b[3] then return a[3] lt b[3] select -1 else 1; end if;
    if a[4] ne b[4] then return  a[4] lt b[4] select -1 else 1; end if;
    return 0;
end function;

// expected file format is label:level:cond:dim:rank:hash:traces
function CMFLoad(filename,p)
    S := [Split(s,":"): s in Split(Read(filename))];
    S := [r:r in S|PrimeDivisors(atoi(r[2])) eq [p]];
    S := [rec<cmfrec|label:=s[1],level:=atoi(s[2]),cond:=atoi(s[3]),dim:=atoi(s[4]),rank:=atoi(s[5]),hash:=GF(2^61-1)!atoi(s[6]),traces:=eval(s[7])>: s in S];
    X := AssociativeArray();
    for r in S do X[r`label] := r; end for;
    return X;
end function;

function GL2NewformDecomposition(X,H:g:=-1)
    N,H := GL2Level(H);
    if g eq -1 then g := GL2Genus(H); end if;
    if g eq 0 then return [], [], -1; end if;
    Z := [r:r in X|r`dim le g and r`level le N^2 and r`cond le N];
    badp := Set(PrimeDivisors(N)); badi := {#PrimesUpTo(p):p in badp};
    maxi := Ceiling(2*#Z+10);  B0:=1;
    t := [g];
    while true do
        maxp := NthPrime(maxi);
        t cat:= GL2Traces(H,maxp:B0:=B0);  B0:=maxp+1;
        b := Vector(t);
        A := Matrix([[r`dim] cat [r`traces[i]:i in [1..maxi]|not i in badi]:r in Z]);
        try x,K := Solution(A,b); catch e; return [],[], -1; end try;
        // printf "Using %o columns\n", Degree(b);
        if Dimension(K) eq 0 then
            forms := Sort([s:s in {* Z[i]`label^^x[i]:i in [1..Degree(x)] *}], CMFLabelCompare);
            dims := [X[f]`dim:f in forms];
            assert &+dims eq g;
            rank := &+[X[f]`rank:f in forms];
            return forms, dims, rank;
        end if;
        maxi := Ceiling(1.5*maxi);
    end while;
end function;

// Output file format is label:gens:children:parents:orbits:iorbits:ccsig:sl2twists:qtwists:obstructions:cusps:ratcusps:iclass:rank:cplabel:forms:dims
// Currently we only fill in iclass:forms:dims:rank for genus 1
function GL2Data(p:cmfdatafile:="cmfdata.txt",cpdatafile:="cpdata.txt",outfile:="",Cheat:=false)
    assert IsPrime(p);
    try cpdata := SL2LoadCPData(cpdatafile,p); catch e; cpdata:=[]; printf "Unable to find/read file '%o', CP labels won't be set (use cpdatafile to specify an alternate location)\n", cpdatafile; end try;
    try cmfdata := CMFLoad(cmfdatafile,p); catch e; cmfdata:=[]; printf "Unable to find/read file '%o', newform decompositions will not be computed (use cmfdatafile to specify an alternate location)\n", cmfdatafile; end try;
    t := Cputime(); s:=t;
    if Cheat and p eq 2 then
        maxN := 32;  maxI := 96;
        printf "Cheating by using previously computed arithmetically maximal level bound %o and index bound %o\n", maxN, maxI;
    elif Cheat and p eq 3 then
        maxN := 27;  maxI := 729;
        printf "Cheating by using previously computed arithmetically maximal level bound %o and index bound %o\n", maxN, maxI;
    else
        if Cheat then print "Not cheating (there is no real advantage to doing so)."; end if;
        maxN,maxI := GL2ArithmeticallyMaximalBounds(p);
        printf "Computed arithmetically maximal level bound %o and index bound %o in %.3os\n", maxN, maxI, Cputime()-s; s:=Cputime();
    end if;
    X := GL2Lattice(maxN,maxI:verbose);
    L := Sort([k:k in Keys(X)],func<a,b|GL2CompareLabels(a,b)>);
    T := [X[k]:k in L];
    printf "Computed subgroup lattice and labels for %o groups in %.3os\n", #L, Cputime()-s; s:=Cputime();
    reductions := [[GL2LookupLabel(X,ChangeRing(T[i]`subgroup,Integers(T[i]`level div p^e))) :e in [1..Valuation(T[i]`level,p)-1]]:i in [1..#T]];
    printf "Computed reduction labels for %o groups in %.3os\n", #T, Cputime()-s; s:=Cputime();
    for i:=1 to #T do if T[i]`level gt 1 then T[i]`subgroup := GL2Standardize(T[i]`subgroup); end if; end for;
    printf "Standardized generators for %o groups in %.3os\n", #T, Cputime()-s; s:=Cputime();
    Z := index([1..#L],func<i|<T[i]`level,T[i]`index,T[i]`genus,T[i]`orbits,T[i]`zindex>>);
    qtwists := [GL2LookupLabel(X,GL2GenericQuadraticTwist(T[i]`subgroup):g:=T[i]`genus) : i in [1..#T]];
    printf "Labeled %o generic quadratic twists in %.3os\n", #T, Cputime()-s; s:=Cputime();
    cplabels := ["?":i in [1..#T]];
    if #cpdata gt 0 then
        Z := index(cpdata,func<r|<r[1],r[2],r[3],GL2OrbitSignature(r[5])>>);
        function cplabel(H,genus)
            N := SL2Level(H);  if N eq 1 then return "1A0"; end if;
            H := ChangeRing(H meet SL(2,BaseRing(H)),Integers(N));
            k := <N,SL2Index(H),genus,GL2OrbitSignature(H)>;
            if not IsDefined(Z,k) then return "?"; end if;
            I := Z[k]; if #I eq 1 then return I[1][4]; end if;
            SL2 := SL(2,Integers(N)); I := [r:r in I|IsConjugate(SL2,r[5],H)];
            return #I eq 0 select "?" else I[1][4];
        end function;
        cplabels := [cplabel(T[i]`subgroup,T[i]`genus):i in [1..#T]];
        printf "Computed %o cplabels in %.3os\n", #[s:s in cplabels|s ne "?"], Cputime()-s; s:=Cputime();
    end if;
    cusps := [0:i in [1..#T]];
    for i in [1..#T] do cusps[i] := GL2CuspCount(T[i]`subgroup); end for;
    printf "Counted cusps in %.3os\n", Cputime()-s; s:=Cputime();
    ratcusps := [0:i in [1..#T]];
    for i in [1..#T] do ratcusps[i] := GL2RationalCuspCount(T[i]`subgroup); end for;
    printf "Counted rational cusps in %.3os\n", Cputime()-s; s:=Cputime();
    obs := [[]:i in [1..#T]];
    for i in [1..#T] do if ratcusps[i] eq 0 then obs[i] := GL2QObstructions(T[i]`subgroup:B:=100); end if; end for;
    printf "Identified local obstructions in %.3os\n", Cputime()-s; s:=Cputime(); 
    iclasses := ["?":i in [1..#T]];  ranks := [-1:i in [1..#T]]; n:=0;
    for i in [1..#T] do if T[i]`genus eq 1 then e,r := GL2IsogenyClass(T[i]`subgroup); iclasses[i]:= e; ranks[i]:=r; n+:=1; end if; end for;
    printf "Computed isogeny class and rank of %o genus 1 subgroups in %.3os\n", n, Cputime()-s; s:=Cputime();
    iorbits := [[]:i in [1..#T]];
    for i in [1..#T] do iorbits[i] := GL2IsogenySignature(T[i]`subgroup); end for;
    printf "Computed isogeny orbits in %.3os\n", Cputime()-s; s:=Cputime();
    newforms := [[]:i in [1..#T]]; dims := [[]:i in [1..#T]];
    if #cmfdata gt 0 then
        for i in [1..#T] do
            if T[i]`genus gt 0 then
                f, d, r := GL2NewformDecomposition(cmfdata,T[i]`subgroup:g:=T[i]`genus);
                newforms[i] := f; dims[i] := d; ranks[i] := r;
                if #newforms eq 0 then printf "Missing newforms in decomposition of J_H for %o\n", L[i]; end if;
            end if;
        end for;
        printf "Computed newform decompositions in %.3os\n", Cputime()-s; s:=Cputime();
    end if;
    recs := Sort([rec<gl2rec|label:=L[i],level:=T[i]`level,index:=T[i]`index,genus:=T[i]`genus,zindex:=T[i]`zindex,subgroup:=T[i]`subgroup,
                             children:=T[i]`children,parents:=T[i]`parents,reductions:=reductions[i],orbits:=T[i]`orbits,iorbits:=iorbits[i],qtwist:=qtwists[i],obstructions:=obs[i],
                             cusps:=cusps[i],ratcusps:=ratcusps[i],iclass:=iclasses[i],rank:=ranks[i],cplabel:=cplabels[i],newforms:=newforms[i],dims:=dims[i]>:i in [1..#T]],
                 func<a,b|GL2CompareLabels(a`label,b`label)>);
    if #outfile gt 0 then
        fp := Open(outfile, "w");
        for r in recs do Puts(fp,GL2RecToString(r)); end for;
        Flush(fp);
        printf "Output written to %o\n", outfile;
    end if;
    printf "Total time: %os\n", Cputime()-t;
    return index(recs,func<r|r`label>:Unique);
end function;

function GL2Load(filename)
    return index([GL2RecFromString(s):s in Split(Read(filename))],func<r|r`label>:Unique);
end function;

function texcplabel(s)
    if #s eq 0 then return "none"; end if;
    i := [i:i in [1..#s]|s[i] ge "A" and s[i] le "Z"][1];
    l := s[1..i-1]; a := s[i];  g:=s[i+1..#s];
    return Sprintf("\\href{https://mathstats.uncg.edu/sites/pauli/congruence/csg%oM.html#level%o}{%o%o\\textsuperscript{%o}}", g,l,l,a,g);
end function;

function texdim(d,n)
    return n gt 1 select Sprintf("%o^{%o}",d,n) else Sprintf("%o",d);
end function;

function texmflabel(s,n)
    t := "\\mflabel{" cat s cat "}";
    if n gt 1 then t cat:= Sprintf("\\textsuperscript{%o}",n); end if;
    return t;
end function;

function texmflabels(newforms)
    cnts := [1:f in newforms];
    for i:=2 to #cnts do if newforms[i] eq newforms[i-1] then cnts[i] +:= cnts[i-1]; cnts[i-1] := 0; end if; end for;
    return Join([texmflabel(newforms[i],cnts[i]):i in [1..#newforms] | cnts[i] gt 0], ", ");
end function;

procedure textable(X)
    S := GL2ArithmeticallyMaximal(X);
    top := "\\begin{table}\n\\begin{center}\\small\n\\begin{tabular}{lllrrrrl}\nlabel & generators & CP & \\hspace{-12pt}$\\#X_H^\\infty(\\Qbar)$ & \\hspace{-4pt}$\\#X_H^\\infty(\\Q)$ & $r$ & $g$ & dimensions\\\\\\toprule";
    bottom := "\\end{tabular}\n\\end{center}\n\\end{table}";
    if #S ge 22 then print top; end if;
    for i:=1 to #S do
        r := X[S[i]];
        s := Sprintf("\\texttt{%o}",r`label);
        s cat:= " & $" cat Join([Sprintf("\\smallmat{%o}{%o}{%o}{%o}",g[1][1],g[1][2],g[2][1],g[2][2]):g in Generators(r`subgroup)],", ") cat "$";
        s cat:= " & " cat texcplabel(r`cplabel);
        s cat:= Sprintf(" & %o & %o", r`cusps, r`ratcusps);
        s cat:= Sprintf(" & %o & %o", r`rank, r`genus);
        M := Multiset(r`dims);  D := Sort([d:d in Set(r`dims)]);
        s cat:= " & $" cat Join([texdim(d,Multiplicity(M,d)):d in D], ", ") cat "$";
        s cat:= "\\\\[0.5pt]\n& \\multicolumn{7}{l}{\\parbox[l]{13.0cm}{\\raggedright";
        s cat:= texmflabels(r`newforms);
        s cat:= "}}\\\\[-1pt]";
        if i lt #S then s cat:= "\\hline\\noalign{\\vskip 2pt}"; end if;
        print s;        
        if i mod 22 eq 0 then print bottom; print top; end if;
    end for;
    if #S ge 22 then print bottom; end if;
end procedure;

procedure texobstable(dir,P)
    X := AssociativeArray();
    for p in P do X[p] := GL2Load(Sprintf("%o/gl2_%oadic.txt",dir,p)); end for;
    for p in P do
        for k in GL2ArithmeticallyMaximal(X[p]) do
            if #X[p][k]`obstructions gt 0 then
                s := Sprintf("\\texttt{%o}",k);
                s cat:= Sprintf(" & $%o^%o$",p,Round(Log(p,X[p][k]`level)));
                s cat:= " & $\\langle" cat Join([Sprintf("\\smallmat{%o}{%o}{%o}{%o}",g[1][1],g[1][2],g[2][1],g[2][2]):g in Generators(X[p][k]`subgroup)],", ") cat "\\rangle$";
                s cat:= " & $" cat Join([IntegerToString(q):q in X[p][k]`obstructions],",") cat "$";
                s cat:= Sprintf(" & %o", X[p][k]`genus);
                s cat:= Sprintf(" & %o\\\\", X[p][k]`rank);
                print s;
            end if;
        end for;
    end for;
end procedure;
