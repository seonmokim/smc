(1) Files like 6_5_1 are convex bodies expressed in linear integer theory, which is extracted from literature [1].

(2) Files like 6_5_1 are converted into yices' bitvector format whose keywords are different from SMT-LIB. The result file is with suffix .ys, e.g., 6_5_1 => 6_5_1.ys.
 
(3) Bitblaster a .ys file to a DIMACS .cnf file, using the following command
yices  --logic=QF_BV  6_5_1.ys
And, the CNF file is named 6_5_1.ys.cnf, as a command "(export-to-dimacs "6_5_1.ys.cnf" ) " is embedded in 6_5_1.ys.

(4) Estimate the number of models by running:
approxmc 6_5_1.ys.cnf


You may verify the correctness of these translations by examing a small size problem 5_10_1, whose exact volume is 4162.

Note:
.cnf files are for the model counter ApproxMC2 [2].

.smt2 files are for the model counter SMTApproxMC [3].

References:
[1] Zhou, M.; He, F.; Song, X.; He, S.; Chen, G; Gu, M. Estimating the Volume of Solution Space for Satisfiability Modulo Linear Real Arithmetic. Theor. Comput. Syst. 2015, 56, 347-371.
[2] Chakraborty, S., Meel, K.S. and Vardi, M.Y. Algorithmic improvements in approximate counting for probabilistic inference: from linear to logarithmic SAT calls. IJCAI, 2016, pp. 3569-3576.
[3] Chakraborty, S.; Meel, K.S.; Mistry, R.; Vardi, M.Y. Approximate Probabilistic Inference via Word-Level Counting. AAAI, 2016, pp. 3218-3224.
