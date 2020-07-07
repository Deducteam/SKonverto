fof(ax_step, axiom, (![X]: (p(X, s(f(X)))))).
fof(ax_congr, axiom, (![X, Y] : (p(X, Y) => p(s(X), s(Y))))).
fof(ax_tran, axiom, (![X,Y, Z]: ( p(X, Y) => (p(Y, Z) => p(X, Z))))).
fof(goal, conjecture, (?[H]: (p(a, s(s(H)))))).
