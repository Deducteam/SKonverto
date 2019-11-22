# Initializing proof state
# Scanning for AC axioms
#
#cnf(i_0_2, negated_conjecture, (p(esk1_1(X1)))).
#
#cnf(i_0_1, negated_conjecture, (~p(X1))).

# Proof found!
# SZS status Theorem
# SZS output start CNFRefutation
fof(tauto, conjecture, ![X1]:(?[X2]:p(X1)=>p(X2)), file('examples/tauto.p', tauto)).
fof(c_0_1, negated_conjecture, ~(![X1]:(?[X2]:p(X1)=>p(X2))), inference(assume_negation,[status(cth)],[tauto])).
fof(c_0_2, negated_conjecture, (p(esk1_1(X2))&~p(X2)), inference(skolemize,[status(esa)],[inference(shift_quantors,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_1])])])])])).
cnf(c_0_3, negated_conjecture, (p(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_2])).
cnf(c_0_4, negated_conjecture, (~p(X1)), inference(split_conjunct,[status(thm)],[c_0_2])).
cnf(c_0_5, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_3, c_0_4]), ['proof']).
# SZS output end CNFRefutation
# Proof object total steps             : 6
# Proof object clause steps            : 3
# Proof object formula steps           : 3
# Proof object conjectures             : 6
# Proof object clause conjectures      : 3
# Proof object formula conjectures     : 3
# Proof object initial clauses used    : 2
# Proof object initial formulas used   : 1
# Proof object generating inferences   : 0
# Proof object simplifying inferences  : 1
# Training examples: 0 positive, 0 negative
# Parsed axioms                        : 1
# Removed by relevancy pruning/SinE    : 0
# Initial clauses                      : 2
# Removed in clause preprocessing      : 0
# Initial clauses in saturation        : 2
# Processed clauses                    : 2
# ...of these trivial                  : 0
# ...subsumed                          : 0
# ...remaining for further processing  : 2
# Other redundant clauses eliminated   : 0
# Clauses deleted for lack of memory   : 0
# Backward-subsumed                    : 0
# Backward-rewritten                   : 0
# Generated clauses                    : 1
# ...of the previous two non-trivial   : 0
# Contextual simplify-reflections      : 0
# Paramodulations                      : 0
# Factorizations                       : 0
# Equation resolutions                 : 0
# Propositional unsat checks           : 0
#    Propositional check models        : 0
#    Propositional check unsatisfiable : 0
#    Propositional clauses             : 0
#    Propositional clauses after purity: 0
#    Propositional unsat core size     : 0
# Current number of processed clauses  : 1
#    Positive orientable unit clauses  : 0
#    Positive unorientable unit clauses: 0
#    Negative unit clauses             : 1
#    Non-unit-clauses                  : 0
# Current number of unprocessed clauses: 0
# ...number of literals in the above   : 0
# Current number of archived formulas  : 0
# Current number of archived clauses   : 1
# Clause-clause subsumption calls (NU) : 0
# Rec. Clause-clause subsumption calls : 0
# Non-unit clause-clause subsumptions  : 0
# Unit Clause-clause subsumption calls : 0
# Rewrite failures with RHS unbound    : 0
# BW rewrite match attempts            : 0
# BW rewrite match successes           : 0
# Condensation attempts                : 0
# Condensation successes               : 0
# Termbank termtop insertions          : 75