nqueens(N, Queens) :-
  length(Queens, N),
  Queens ins 1 .. N,
  all_different(Queens),
  diagonal(Queens, 1, Diagonal),
  all_different(Diagonal),
  antidiagonal(Queens, 1, Antidiagonal),
  all_different(Antidiagonal),
  labeling([ff], Queens).

diagonal([], _, []).

diagonal([H | T], I, [X | U]) :-
  X #= H - I,
  J is I + 1,
  diagonal(T, J, U).

antidiagonal([], _, []).

antidiagonal([H | T], I, [X | U]) :-
  X #= H + I,
  J is I + 1,
  antidiagonal(T, J, U).
