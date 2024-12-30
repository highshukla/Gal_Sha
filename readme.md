This repo has following files:
- curves_K11.m
- curves_K31.m
- check_vis.m
- check_Lval_K11.m
- helper_funcs.m
- compute_Selmer_11.m

The files above have the following descriptions:

- curves_K11.m: curve data on LMFDB that acquire 11-torsion of Sha over the degree 5
                field K that is the degree 5 subfield of 11th cyclotomic field.

- curves_K31.m: curve data on LMFDB that acquire 11-torsion of Sha over the degree 5
                field K that is the degree 5 subfield of 31th cyclotomic field.

- check_vis.m:  this file checks the claims in Section 2.2 in the manuscript 

- check_Lval_K11.m: this file checks that the 11-part of the factorization of the
                    special L-value ideal varies as conjectured in Conjecture 1.3 
                    in the manuscript w.r.t the Galois action on Sha[11] of the 
                    curves in the file curves_K11.m

- helper_funcs.m: this files contains helper functions for all the files in this repo.
                  The descriptions of these functions are given in the file above 
                  each function.

- compute_Selmer_11.m: this file contains the main function to compute the Sel_11(E/K)
                       and compute action of Galois on Sel_11(E/K) and output the 
                       polynomials h_theta. 

