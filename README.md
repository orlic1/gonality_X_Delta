The Sage and Magma codes from the article "Tetragonal Intermediate Modular Curves" by P. Orlić.

Sage_canonical_models.txt contains a sample Sage code that produces a canonical model of the curve $X_{\{\pm1,\pm12\}}(29)$. We can use it in the same way for any other curve $X_\Delta(N)$. The code requires MD Sage to be installed previously. The output file contains the model of the curve as well as the code for Magma to import that model. The canonical models of the curves are stored in the folder XH_models. These models are then used in other Magma codes.

Fp-gonality folder contains Magma codes that give lower bound on the $\mathbb{Q}$-gonality by computing the $\mathbb{F}p$-gonality. not-tetragonal.txt contains the code for Proposition 3.6 and not-pentagonal.txt contains the code for Proposition 3.7. Other files in this folder are the codes for Proposition 3.8. Each file is a code for one curve $X_\Delta(N)$.

The files gl2.m, gl2.sig, and gl2data.m from the folder Sutherland-GL2 were retrieved from the repository https://github.com/AndrewVSutherland/ell-adic-galois-images by Jeremy Rouse, Andrew V. Sutherland, and David Zureick-Brown. They were used in the file Fp2_point_count.txt to solve Proposition 3.5.

Riemann-Roch_search folder contains codes that find rational functions in Proposition 3.14. Each file is a code for one curve.

QuadPts.txt is an auxiliary file that was used to search for quadratic points via intersections with hyperplanes. These quadratic points were then used in codes in the folder Riemann-Roch_search to find rational functions.

Betti_numbers.txt contains codes for Proposition 3.25. We prove that there is no degree $4$ function by computing that $\beta_{2,2}=0$.
