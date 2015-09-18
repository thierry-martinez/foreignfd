:- use_module(foreignfd).
:- use_module(library(plunit)).

:- begin_tests(foreignfd).

%test(debug) :-
%  foreignfd:debug.

test('equal, not equal') :-
  [X, Y] ins 0 .. 1,
  X #\= Y,
  X #= 0,
  \+ (Y #= 0).

test(unify, [true(integer(X))]) :-
  X in 0 .. 1,
  X #< 1.

test(indomain, [true(L == [0, 1, 2])]) :-
  X in 0 .. 2,
  findall(X, indomain(X), L).

test(all_different, [true(Y == 1)]) :-
  [X, Y] ins 0 .. 2,
  X #= 0,
  all_different([X, Y, 2]).

test(fd_dom, [true(Dom == 2 \/ 4 .. 5)]) :-
  X in 0 .. 2 \/ 4 .. 6,
  X in 2 .. 5,
  fd_dom(X, Dom).

test(fd_inf, [true(Min == 2)]) :-
  X in 0 .. 2 \/ 4 .. 6,
  X in 2 .. 5,
  fd_inf(X, Min).

test(fd_sup, [true(Max == 5)]) :-
  X in 0 .. 2 \/ 4 .. 6,
  X in 2 .. 5,
  fd_sup(X, Max).

test(fd_size, [true(Size == 3)]) :-
  X in 0 .. 2 \/ 4 .. 6,
  X in 2 .. 5,
  fd_size(X, Size).

test(or, [true(X == 2)]) :-
  X in 0 .. 2,
  X #= 0 #\/ X #= 2,
  X #\= 0.

test(pow, [true(X == 2)]) :-
  X in 0 .. 2,
  X ^ 2 #= 4.

test(div, [true(X == 2)]) :-
  X in 0 .. 2,
  Y in 6 .. 7,
  Y // 3 #= X.

test(min, [true(X == 2)]) :-
  X in 0 .. 2,
  Y in 6 .. 7,
  Z in 2 .. 4,
  X #= min(Y, Z).

test(labeling_min, [true(X == 1)]) :-
  X in 0 .. 2,
  once(labeling([min(abs(X - 1))], [X])).

test(sum, [true((X == 3, Y == 2))]) :-
  X in 0 .. 3,
  Y in 0 .. 2,
  sum([X, Y], #=, 5).

test(nqueens) :-
  [examples/nqueens],
  once(nqueens(10, _)).

:- end_tests(foreignfd).