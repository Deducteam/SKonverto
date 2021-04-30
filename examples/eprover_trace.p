# Initializing proof state
# Scanning for AC axioms
#
#cnf(i_0_1, plain, (p(X1,s(f(X1))))).
#
#cnf(i_0_3, plain, (p(X1,X3)|~p(X2,X3)|~p(X1,X2))).
#
#cnf(i_0_7, plain, (p(X1,X2)|~p(s(f(X1)),X2))).
#
#cnf(i_0_4, negated_conjecture, (~p(a,s(s(X1))))).
#
#cnf(i_0_2, plain, (p(s(X1),s(X2))|~p(X1,X2))).
#
#cnf(i_0_14, plain, (p(X1,s(X2))|~p(f(X1),X2))).
#
#cnf(i_0_8, plain, (p(X1,s(f(X2)))|~p(X1,X2))).
#
#cnf(i_0_11, negated_conjecture, (~p(X2,s(s(X1)))|~p(a,X2))).
#
#cnf(i_0_9, plain, (p(X1,s(f(s(f(X1))))))).
#
#cnf(i_0_15, plain, (p(X1,s(s(f(f(X1))))))).

# Proof found!
# SZS status Theorem
# SZS output start CNFRefutation
fof(ax_tran, axiom, ![X1, X2, X3]:(p(X1,X2)=>(p(X2,X3)=>p(X1,X3))), file('examples/problem.p', ax_tran)).
fof(ax_step, axiom, ![X1]:p(X1,s(f(X1))), file('examples/problem.p', ax_step)).
fof(ax_congr, axiom, ![X1, X2]:(p(X1,X2)=>p(s(X1),s(X2))), file('examples/problem.p', ax_congr)).
fof(goal, conjecture, ?[X4]:p(a,s(s(X4))), file('examples/problem.p', goal)).
fof(c_0_4, plain, ![X8, X9, X10]:(~p(X8,X9)|(~p(X9,X10)|p(X8,X10))), inference(shift_quantors,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[ax_tran])])])])).
fof(c_0_5, plain, ![X5]:p(X5,s(f(X5))), inference(variable_rename,[status(thm)],[ax_step])).
cnf(c_0_6, plain, (p(X1,X3)|~p(X1,X2)|~p(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
cnf(c_0_7, plain, (p(X1,s(f(X1)))), inference(split_conjunct,[status(thm)],[c_0_5])).
fof(c_0_8, plain, ![X6, X7]:(~p(X6,X7)|p(s(X6),s(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[ax_congr])])).
fof(c_0_9, negated_conjecture, ~(?[X4]:p(a,s(s(X4)))), inference(assume_negation,[status(cth)],[goal])).
cnf(c_0_10, plain, (p(X1,X2)|~p(s(f(X1)),X2)), inference(pm,[status(thm)],[c_0_6, c_0_7])).
cnf(c_0_11, plain, (p(s(X1),s(X2))|~p(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
fof(c_0_12, negated_conjecture, ![X11]:~p(a,s(s(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])).
cnf(c_0_13, plain, (p(X1,s(X2))|~p(f(X1),X2)), inference(pm,[status(thm)],[c_0_10, c_0_11])).
cnf(c_0_14, negated_conjecture, (~p(a,s(s(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
cnf(c_0_15, plain, (p(X1,s(s(f(f(X1)))))), inference(pm,[status(thm)],[c_0_13, c_0_7])).
cnf(c_0_16, negated_conjecture, ($false), inference(pm,[status(thm)],[c_0_14, c_0_15]), ['proof']).
# SZS output end CNFRefutation
# Proof object total steps             : 17
# Proof object clause steps            : 8
# Proof object formula steps           : 9
# Proof object conjectures             : 5
# Proof object clause conjectures      : 2
# Proof object formula conjectures     : 3
# Proof object initial clauses used    : 4
# Proof object initial formulas used   : 4
# Proof object generating inferences   : 4
# Proof object simplifying inferences  : 0
# Training examples: 0 positive, 0 negative
# Parsed axioms                        : 4
# Removed by relevancy pruning/SinE    : 0
# Initial clauses                      : 4
# Removed in clause preprocessing      : 0
# Initial clauses in saturation        : 4
# Processed clauses                    : 10
# ...of these trivial                  : 0
# ...subsumed                          : 0
# ...remaining for further processing  : 10
# Other redundant clauses eliminated   : 0
# Clauses deleted for lack of memory   : 0
# Backward-subsumed                    : 0
# Backward-rewritten                   : 0
# Generated clauses                    : 29
# ...of the previous two non-trivial   : 23
# Contextual simplify-reflections      : 0
# Paramodulations                      : 29
# Factorizations                       : 0
# Equation resolutions                 : 0
# Propositional unsat checks           : 0
#    Propositional check models        : 0
#    Propositional check unsatisfiable : 0
#    Propositional clauses             : 0
#    Propositional clauses after purity: 0
#    Propositional unsat core size     : 0
# Current number of processed clauses  : 10
#    Positive orientable unit clauses  : 3
#    Positive unorientable unit clauses: 0
#    Negative unit clauses             : 1
#    Non-unit-clauses                  : 6
# Current number of unprocessed clauses: 17
# ...number of literals in the above   : 44
# Current number of archived formulas  : 0
# Current number of archived clauses   : 0
# Clause-clause subsumption calls (NU) : 3
# Rec. Clause-clause subsumption calls : 3
# Non-unit clause-clause subsumptions  : 0
# Unit Clause-clause subsumption calls : 0
# Rewrite failures with RHS unbound    : 0
# BW rewrite match attempts            : 4
# BW rewrite match successes           : 0
# Condensation attempts                : 0
# Condensation successes               : 0
# Termbank termtop insertions          : 473
