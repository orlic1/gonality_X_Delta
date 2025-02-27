# The Sage and Magma codes from the article "Tetragonal Intermediate Modular Curves" by P. Orlić.

## Contents

- XH_models folder contains canonical models of curves $X_\Delta(N)$. These models are then used in other Magma codes.

- Sage_canonical_models.txt contains a sample Sage code that produces a canonical model of the curve $X_{\{\pm1,\pm12\}}(29)$. We can use it in the same way for any other curve $X_\Delta(N)$ that has a canonical model composed of quadrics (that is, not subhyperelliptic nor trigonal).

The code requires MD Sage to be installed previously. The output file contains the model of the curve as well as the code for Magma to import that model. 

### Example
We compute a canonical model of a curve $X_{\{\pm1,\pm12\}}(29)$.
```sage
from mdsage import *
G=GammaH(29,[12,-1])
quadratic_forms = vanishing_quadratic_forms(G)
R=quadratic_forms[0].parent()
n=R.ngens()

variables=",".join(f"x{i}" for i in range(n))

magma_file=f"""P<{variables}>:=ProjectiveSpace(Rationals(),{n-1}); equations:={quadratic_forms};"""

with open("XH_29-12.m", "w") as file: file.write(magma_file)
```
We now load this model into Magma as follows:
```magma
load "XH_29-12.m";
C:= Curve(P,equations);
```

- Betti_numbers.txt contains codes that disprove the existence of a degree $4$ morphism to $\mathbb{P}^1$ by computing $\beta_{2,2}$.

### Example
For a curve $X_{\{\pm1,\pm12\}}(29)$ we compute $\beta_{2,2}=0$, implying that this curve is not tetragonal. 
```magma
load "XH_29-12.m";
C:= Curve(P,equations);
A:=QuotientModule(DefiningIdeal(X));
BettiTable(A);
BettiNumber(A,2,4);  // Returns 0. Notice that the indexations of Betti numbers are different. This is more thoroughly explained in the paper.
```

- Genus5GonalMap.txt constructs degree $4$ rational maps to $\mathbb{P}^1$ from curves $X_{\Delta}(N)$ of genus $5$ using the Magma function Genus5GonalMap().

### Example
We explicitly find a degree $4$ rational map from $X_0^{\{\pm1,\pm11\}}(30)$ to $\mathbb{P}^1$. 
```magma
load "XH_30-11.m";
C:= Curve(P,equations);
assert Genus(C) eq 5;
Genus5GonalMap(C); // Returns a map from $C$ to $\mathbb{P}^1$. It is easy to visually check that it is defined over $\Q$.
```

- QuadPts.txt is an auxiliary file that was used to search for quadratic points via intersections with hyperplanes. These quadratic points were then used in codes in the folder Riemann-Roch_search to find degree $4$ rational functions.

The main function there is SearchPts(X,bd) which searches for quadratic points on $X$ via intersections with hyperplanes $a_0x_0+a_1x_1+a_2x_2=0$, where $|a_i|\leq bd$. Note that this function can have a long running time, but the output of points is continuous (the points can and will repeat).

### Example
```magma
load "XH_29-12.m";
C:= Curve(P,equations);
SearchPts(C,20);
```

- Riemann-Roch_search folder contains codes that find rational functions of degree $4$. Each file is a code for one curve.

- Fp_gonality folder contains codes that give lower bounds on $\mathbb{Q}$-gonality by bounding the $\mathbb{F}_p$-gonality. We prove that all $\mathbb{F}_p$-rational divisors $D\geq0$ of degree $d$ have Riemann-Roch dimension $1$.

- Sutherland-GL2 folder also gives bounds on the $\mathbb F_p$ -gonality by counting the number of $\mathbb{F}_{p^2}$ points and concluding it is too large (greater than $d(p^2+1)$). The code works with groups $\Gamma\leq \textup{GL}_2(\mathbb{Z}/N\mathbb{Z})$ instead of $\Delta\leq(\mathbb{Z}/N\mathbb{Z})^\times$. More details are in the paper.

### Example
We prove that the curve $(N,\Delta)=(71,\left<-1,5\right>)$ has $\mathbb{Q}$-gonality at least $6$.
```magma
load "gl2data.m";
G:=sub<GL(2,Integers(71))|[ [1,0,0,-1], [1,0,0,7], [-1,0,0,1], [5,0,0,1], [1,1,0,1] ]>;
GL2PointCount(G,25);
```
The output is $182>5(5^2+1)$ which proves our claim.

## Imported files

The files gl2.m, gl2.sig, and gl2data.m from the folder Sutherland-GL2 were retrieved from the repository https://github.com/AndrewVSutherland/ell-adic-galois-images by Jeremy Rouse, Andrew V. Sutherland, and David Zureick-Brown.
