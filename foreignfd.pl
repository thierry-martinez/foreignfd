:- module(
  foreignfd,
  [
    op(450, xfx, (..)),
    op(700, xfx, in),
    op(700, xfx, ins),
    op(700, xfx, (#=)),
    op(700, xfx, (#\=)),
    op(700, xfx, (#<)),
    op(700, xfx, (#=<)),
    op(700, xfx, (#>)),
    op(700, xfx, (#>=)),
    op(710, fx, (#\)),
    op(720, yfx, (#/\)),
    op(730, yfx, (#\)),
    op(740, yfx, (#\/)),
    op(750, yfx, (#==>)),
    op(750, yfx, (#<==)),
    op(760, yfx, (#<==>)),
    solver/1,
    (in)/2,
    (ins)/2,
    (#=)/2,
    (#\=)/2,
    (#<)/2,
    (#=<)/2,
    (#>)/2,
    (#>=)/2,
    (#\)/1,
    (#/\)/2,
    (#\/)/2,
    (#\)/2,
    (#==>)/2,
    (#<==)/2,
    (#<==>)/2,
    all_different/1,
    all_different/2,
    all_distinct/1,
    sum/3,
    scalar_product/4,
    indomain/1,
    label/1,
    labeling/2,
    fd_var/1,
    fd_inf/2,
    fd_sup/2,
    fd_size/2,
    fd_dom/2
  ]
).


/** <module> clpfd-like interface for external solvers.
*/

:- use_module(library(error)).

%% solver(?Solver)
%
%  Initializes the solver.  The only available solver is JaCoP and Solver will
%  be unified with the atom _jacop_.

solver(jacop) :-
  solver(path(java), ['foreignfd.Jacop']).

%% ?Var in +Domain
%
%  Var is an element of Domain. Domain is one of:
%
%         * Integer
%           Singleton set consisting only of _Integer_.
%         * Lower..Upper
%           All integers _I_ such that _Lower_ =< _I_ =< _Upper_.
%         * Domain1 \/ Domain2
%           The union of Domain1 and Domain2.

X in Domain :-
  singleton(Domain, V),
  !,
  X = V.

X in Domain :-
  get_attr(X, foreignfd, XId),
  !,
  check_domain(Domain),
  set_level,
  emit('<Constraint><Or>'),
  emit_domain_constraint(XId, Domain),
  emit('</Or></Constraint>\n'),
  check_consistency.

X in Domain :-
  var(X),
  !,
  check_domain(Domain),
  int_var(X, _, Domain).

X in _ :-
  type_error(variable, X).

check_domain(I) :-
  integer(I),
  !.

check_domain(I .. J) :-
  integer(I),
  integer(J),
  !.

check_domain(A \/ B) :-
  !,
  check_domain(A),
  check_domain(B).

check_domain(D) :-
  type_error(domain, D).

%% +Vars ins +Domain
%
%  The variables in the list Vars are elements of Domain.

[] ins _ :-
  !.

[H | T] ins Domain :-
  !,
  H in Domain,
  T ins Domain.

L ins _ :-
  type_error(list, L).

%% ?X #= ?Y
%
% X equals Y.

A #= B :-
  rel(A, B, '=', A = B).

%% ?X #\= ?Y
%
% X is not equal to Y.

A #\= B :-
  rel(A, B, '!=', A \= B).

%% ?X #< ?Y
%
% X is stricly less than Y.

A #< B :-
  rel(A, B, '&lt;', A < B).

%% ?X #=< ?Y
%
% X is less than or equal to Y.

A #=< B :-
  rel(A, B, '&lt;=', A =< B).

%% ?X #> ?Y
%
% X is stricly greater than Y.

A #> B :-
  rel(A, B, '>', A > B).

%% ?X #>= ?Y
%
% X is greater than or equal to Y.

A #>= B :-
  rel(A, B, '>=', A >= B).

%% #\ ?C
%
% The reifiable constraint D does _not_ hold.

#\ C :-
  reified_constraint(#\ C).

%% ?C #/\ ?D
%
% The two reifiable constraints C and D hold (and).

A #/\ B :-
  reified_constraint(A #/\ B).

%% ?C #\/ ?D
%
% At least one of the two reifiable constraints C and D holds (or).

A #\/ B :-
  reified_constraint(A #\/ B).

%% ?C #\ ?D
%
% Exactly one of the two reifiable constraints C and D holds (xor).

A #\ B :-
  reified_constraint(A #\ B).

%% ?C #==> ?D
%
% The reifiable constraint C implies the reifiable constraint D.

A #==> B :-
  reified_constraint(A #==> B).

%% ?C #<== ?D
%
% The reifiable constraint D implies the reifiable constraint C.

A #<== B :-
  reified_constraint(A #<== B).

%% ?C #<==> ?D
%
% The reifiable constraints C and D are equivalent.

A #<==> B :-
  reified_constraint(A #<==> B).

%% fd_var(+Var)
%
%  True iff Var is a finite-domain variable.

fd_var(X) :-
  get_attr(X, foreignfd, _).

%% fd_dom(+Var, -Dom)
%
%  Dom is the current domain (see in/2) of Var.

fd_dom(X, Dom) :-
  get_attr(X, foreignfd, XId),
  emit('<GetDomain X="~a"/>\n', [XId]),
  require_solver(_In, Out, _Err, _Pid),
  read(Out, Dom).

%% fd_inf(+Var, -Inf)
%
%  Inf is the infimum of the current domain of Var.

fd_inf(X, Inf) :-
  fd_dom(X, Dom),
  dom_inf(Dom, Inf).

%% fd_sup(+Var, -Sup)
%
%  Sup is the supremum of the current domain of Var.

fd_sup(X, Sup) :-
  fd_dom(X, Dom),
  dom_sup(Dom, Sup).

%% fd_size(+Var, -Size)
%
%  Determine the size of a variable's domain.

fd_size(X, Size) :-
  fd_dom(X, Dom),
  dom_size(Dom, Size).

%% indomain(?Var)
%
% Bind Var to all feasible values of its domain on backtracking.
% Equivalent to label([Var]).

indomain(Var) :-
  label([Var]).

%% label(+Vars)
%
% Equivalent to labeling([], Vars).

label(Vars) :-
  labeling([], Vars).

:- use_module(library(sort)).

%% labeling(+Options, +Vars)
%
% Assign a value to each variable in Vars.  Possible values are enumerable by
% backtracking.
%
% Options should be a list specifying:
% - at most one variable selection strategy among:
%
%   * leftmost
%   Label the variables in the order they occur in Vars. This is the
%   default.
%
%   * ff
%   _|First fail|_. Label the leftmost variable with smallest domain next,
%   in order to detect infeasibility early. This is often a good
%   strategy.
%
%   * ffc
%   Of the variables with smallest domains, the leftmost one
%   participating in most constraints is labeled next.
%
%   * min
%   Label the leftmost variable whose lower bound is the lowest next.
%
%   * max
%   Label the leftmost variable whose upper bound is the highest next.
%
% - at most one value selection strategy among:
%
%   * up
%   Try the elements of the chosen variable's domain in ascending order.
%   This is the default.
%
%   * down
%   Try the domain elements in descending order.
%
%   * middle
%   Try the domain elements starting by the middle values and going
%   outwards.
%
% - at most one branching strategy among
%
%   * step
%   * enum
%   For each variable X, a choice is made between X = V and X #\= V,
%   where V is determined by the value ordering options. This is the
%   default.
%
%   * bisect
%   For each variable X, a choice is made between X #=< M and X #> M,
%   where M is the midpoint of the domain of X.
%
% - the order of solutions can be influenced with:
%
%   * min(Expr)
%   * max(Expr)
%
% This generates solutions in ascending/descending order with respect
% to the evaluation of the arithmetic expression Expr. Labeling Vars
% must make Expr ground. If several such options are specified, they
% are interpreted from left to right.

labeling(Options, Vars) :-
  labeling_options(Options, VarSel, ValSel, Branching, Ordering),
  varsel(VarSel),
  valsel(ValSel),
  branching(Branching),
  !,
  (
    Ordering = []
  ->
    labeling(Vars, VarSel, ValSel, Branching)
  ;
    findall(Vars, labeling(Vars, VarSel, ValSel, Branching), Solutions),
    b_setval(foreign_vars, Vars),
    b_setval(foreign_ordering, Ordering),
    predsort(order, Solutions, SortedSolutions),
    b_setval(foreign_vars, 0),
    b_setval(foreign_ordering, 0),
    member(Vars, SortedSolutions)
  ).

%% sum(+Vars, +Rel, ?Expr)
%
% The sum of elements of the list Vars is in relation Rel to Expr.
% Rel is one of #=, #\=, #<, #>, #=< or #>=.

sum(Vars, Rel, Expr) :-
  length(Vars, N),
  length(Consts, N),
  list_ones(Consts),
  scalar_product(Consts, Vars, Rel, Expr).

%% scalar_product(+Cs, +Vs, +Rel, ?Expr)
%
% Cs is a list of integers, Vs is a list of variables and integers.
% True if the scalar product of Cs and Vs is in relation Rel to Expr,
% where Rel is #=, #\=, #<, #>, #=< or #>=.

scalar_product(Consts, Vars, Rel, Expr) :-
  scalar_product_expr(Consts, Vars, Product),
  G =.. [Rel, Product, Expr],
  G.

%% all_different(+Vars)
%
% Vars are pairwise distinct. Equivalent to all_different(Vars, bc).

all_different(Vars) :-
  all_different(Vars, bc).

%% all_different(+Vars, +Consistency)
%
% Vars are pairwise distinct.  Consistency is one of the following atom:
% * pairwise
%   Equivalent to the conjunction of constraints X #\= Y for every pair
%   {X, Y} in Vars.
%
% * bc
%   Ensures bound-consistency.
%
% * gac
%   Ensures global-arc-consistency.

all_different(Vars, Consistency) :-
  expr_id(Vars, VarsId),
  (
    Consistency = pairwise
  ->
    all_different_pairwise(VarsId)
  ;
    constraint(all_different(VarsId, Consistency))
  ).

all_different_pairwise([]).

all_different_pairwise([H | T]) :-
  different_list(T, H),
  all_different_pairwise(T).

different_list([], _).

different_list([YId | T], XId) :-
  constraint(linear(XId * 1 + YId * -1, '!=', 0)),
  different_list(T, XId).

%% all_distinct(+Vars)
%
% Vars are pairwise distinct. Equivalent to all_different(Vars, gac).

all_distinct(Vars) :-
  all_different(Vars, gac).

:- dynamic(current_solver/4).

require_solver(In, Out, Err, Pid) :-
  current_solver(In, Out, Err, Pid),
  !.

require_solver(_In, _Out, _Err, _Pid) :-
  solver(_).

:- use_module(library(process)).

solver(Exe, _Args) :-
  current_solver(_, _, _, _),
  permission_error(
      'run a solver while another one is already running.', 'solver', Exe).

solver(Exe, Args) :-
  process_create(
    Exe,
    Args,
    [
      stdin(pipe(In)),
      stdout(pipe(Out)),
%      stderr(pipe(Err)),
      process(Pid)
    ]
  ),
  asserta(current_solver(In, Out, _Err, Pid)),
  b_setval(foreign_assoc, []),
  b_setval(foreign_last_choice_point, 0),
  b_setval(foreign_current_level_b, 0),
  nb_setval(foreign_current_level_nb, 0).

:- dynamic(variable_counter/1).

variable_counter(0).

fresh_variable_id(Id) :-
  retract(variable_counter(Counter)),
  Next is Counter + 1,
  asserta(variable_counter(Next)),
  format(atom(Id), 'x~d', [Counter]).

:- use_module(library(assoc)).

assoc(AssocAVL) :-
  b_getval(foreign_assoc, Assoc),
  (
    Assoc = []
  ->
    empty_assoc(AssocAVL)
  ;
    AssocAVL = Assoc
  ).

fresh_variable(X, Id) :-
  fresh_variable_id(Id),
  put_attr(X, foreignfd, Id),
  assoc(Assoc),
  put_assoc(Id, Assoc, X, NewAssoc),
  b_setval(foreign_assoc, NewAssoc).

emit(Atom) :-
  emit('~a', [Atom]).

:- dynamic(debugging/0).

debug :-
  (
    debugging
  ->
    true
  ;
    asserta(debugging)
  ).

nodebug :-
  retractall(debugging).

emit(Format, Args) :-
  require_solver(In, _Out, _Err, _Pid),
  (
    debugging
  ->
    format(Format, Args),
    flush
  ;
    true
  ),
  format(In, Format, Args),
  flush_output(In).

int_var(X, XId, Domain) :-
  set_level,
  fresh_variable(X, XId),
  emit('<IntVar name="~a">', [XId]),
  emit_domain(Domain),
  emit('</IntVar>\n').

constant(C, XId) :-
  int_var(_, XId, C .. C).

dom_inf(I, I) :-
  integer(I),
  !.

dom_inf(I .. _, I).

dom_inf(A \/ _, Inf) :-
  dom_inf(A, Inf).

dom_sup(I, I) :-
  integer(I),
  !.

dom_sup(_ .. J, J).

dom_sup(_ \/ B, Inf) :-
  dom_sup(B, Inf).

dom_size(I, 1) :-
  integer(I),
  !.

dom_size(I .. J, Size) :-
  Size is J - I + 1.

dom_size(A \/ B, Size) :-
  dom_size(A, SizeA),
  dom_size(B, SizeB),
  Size is SizeA + SizeB.

singleton(A .. B, V) :-
  integer(A),
  integer(B),
  !,
  A = B,
  V = A.

singleton(A \/ B, V) :-
  singleton(A, V),
  singleton(B, V).

emit_domain(A) :-
  integer(A),
  !,
  emit('<Interval min="~d" max="~d"/>', [A, A]).

emit_domain(A .. B) :-
  integer(A),
  integer(B),
  !,
  emit('<Interval min="~d" max="~d"/>', [A, B]).

emit_domain(A \/ B) :-
  emit_domain(A),
  emit_domain(B).

emit_domain_constraint(XId, A) :-
  integer(A),
  !,
  emit('<And>'),
  emit(
    '<Linear rel="=" constant="~d"><Var X="~a" weight="1"/></Linear>',
    [A, XId]
  ),
  emit('</And>').

emit_domain_constraint(XId, A .. B) :-
  integer(A),
  integer(B),
  !,
  emit('<And>'),
  emit(
    '<Linear rel=">=" constant="~d"><Var X="~a" weight="1"/></Linear>',
    [A, XId]
  ),
  emit(
    '<Linear rel="&lt;=" constant="~d"><Var X="~a" weight="1"/></Linear>',
    [B, XId]
  ),
  emit('</And>').

emit_domain_constraint(XId, A \/ B) :-
  emit_domain_constraint(XId, A),
  emit_domain_constraint(XId, B).

auto_int_var(X, Id) :-
  set_level,
  fresh_variable(X, Id),
  emit('<AutoIntVar name="~a"/>\n', [Id]).

eval(X, X) :-
  integer(X),
  !.

eval(X, XId * 1 + 0) :-
  get_attr(X, foreignfd, XId),
  !.

eval(X, XId * 1 + 0) :-
  var(X),
  !,
  auto_int_var(X, XId).

eval(?(X), XId * 1 + 0) :-
  !,
  (
    get_attr(X, foreignfd, XId)
  ->
    true
  ;
    var(X)
  ->
    auto_int_var(X, XId)
  ).

eval(- E, X) :-
  !,
  eval(E, Y),
  linear_mul(Y, -1, X).

eval(A + B, X) :-
  !,
  eval(A, VA),
  eval(B, VB),
  linear_add(VA, VB, X).

eval(A - B, X) :-
  !,
  eval(A, VA),
  eval(B, VB),
  linear_mul(VB, -1, VBopp),
  linear_add(VA, VBopp, X).

eval(A * B, X) :-
  !,
  eval(A, VA),
  eval(B, VB),
  (
    integer(VA),
    integer(VB)
  ->
    X is VA * VB
  ;
    integer(VA)
  ->
    linear_mul(VB, VA, X)
  ;
    integer(VB)
  ->
    linear_mul(VA, VB, X)
  ;
    linear_var(VA, AId),
    linear_var(VB, BId),
    auto_int_var(_, XId),
    constraint('XmulYeqZ'(AId, BId, XId)),
    X = XId * 1 + 0
  ).

eval(A mod B, X) :-
  !,
  eval(A, VA),
  eval(B, VB),
  (
    integer(VA),
    integer(VB)
  ->
    X is VA mod VB
  ;
    integer(VA)
  ->
    linear_mul(VB, VA, X)
  ;
    integer(VB)
  ->
    linear_mul(VA, VB, X)
  ;
    linear_var(VA, AId),
    linear_var(VB, BId),
    auto_int_var(_, XId),
    constraint('XmodYeqZ'(AId, BId, XId)),
    X = XId * 1 + 0
  ).

eval(A rem B, X) :-
  !,
  eval(A mod B, X).

eval(A // B, X) :-
  !,
  eval(A, VA),
  eval(B, VB),
  (
    integer(VA),
    integer(VB)
  ->
    X is VA // VB
  ;
    integer(VA)
  ->
    linear_var(VB, BId),
    auto_int_var(_, XId),
    constraint('XmulYeqC'(BId, XId, VA)),
    X = XId * 1 + 0
  ;
    integer(VB)
  ->
    linear_var(VA, AId),
    auto_int_var(_, XId),
    constraint(linear(XId * VB + AId * -1, '=', 0)),
    X = XId * 1 + 0
  ;
    linear_var(VA, AId),
    linear_var(VB, BId),
    auto_int_var(_, XId),
    constraint('XmulYeqZ'(BId, XId, AId)),
    X = XId * 1 + 0
  ).

eval(A / B, X) :-
  !,
  eval(A // B, X).

eval(abs(A), X) :-
  !,
  eval(A, VA),
  (
    integer(VA)
  ->
    X is abs(VA)
  ;
    linear_var(VA, AId),
    auto_int_var(_, XId),
    constraint('AbsXeqZ'(AId, XId)),
    X = XId * 1 + 0
  ).

eval(A ^ B, X) :-
  !,
  (
    integer(B),
    B >= 1
  ->
    true
  ;
    domain_error('non-negative constant power', B)
  ),
  make_power_product(B, A, P),
  eval(P, X).

eval(min(A, B), X) :-
  !,
  eval(A, VA),
  eval(B, VB),
  (
    integer(VA),
    integer(VB)
  ->
    X is min(VA, VB)
  ;
    linear_var(VA, AId),
    linear_var(VB, BId),
    auto_int_var(_, XId),
    constraint('min'([AId, BId], XId)),
    X = XId * 1 + 0
  ).

eval(max(A, B), X) :-
  !,
  eval(A, VA),
  eval(B, VB),
  (
    integer(VA),
    integer(VB)
  ->
    X is max(VA, VB)
  ;
    linear_var(VA, AId),
    linear_var(VB, BId),
    auto_int_var(_, XId),
    constraint('max'([AId, BId], XId)),
    X = XId * 1 + 0
  ).

eval(E, _) :-
  type_error('arithmetic expression', E).

make_power_product(0, _, 1) :-
  !.

make_power_product(1, A, A) :-
  !.

make_power_product(N, A, A * P) :-
  !,
  M is N - 1,
  make_power_product(M, A, P).

linear_var(I, I) :-
  integer(I),
  !.

linear_var(XId * 1 + 0, XId) :-
  !.

linear_var(A + I, XId) :-
  auto_int_var(_X, XId),
  Iopp is -I,
  constraint(linear(XId * -1 + A, '=', Iopp)).

linear_add(I, J, K) :-
  integer(I),
  integer(J),
  !,
  K is I + J.

linear_add(A + I, J, A + K) :-
  integer(J),
  !,
  K is I + J.

linear_add(I, A + J, A + K) :-
  integer(I),
  !,
  K is I + J.

linear_add(A + I, B + J, A + B + K) :-
  K is I + J.

linear_mul(_, 0, 0) :-
  !.

linear_mul(V, C, M) :-
  linear_mul_aux(V, C, M).

linear_mul_aux(I, C, M) :-
  integer(I),
  !,
  M is I * C.

linear_mul_aux(A + B, C, M + N) :-
  linear_mul_aux(A, C, M),
  linear_mul_aux(B, C, N).

linear_mul_aux(X * K, C, X * L) :-
  L is K * C.

rel(A, B, LinOp, IntOp) :-
  eval(A, VA),
  eval(B, VB),
  (
    integer(VA),
    integer(VB)
  ->
    IntOp
  ;
    linear_mul(VB, -1, VBopp),
    linear_add(VA, VBopp, S + K),
    Kopp is -K,
    constraint(linear(S, LinOp, Kopp))
  ).

list_ones([]).

list_ones([1 | T]) :-
  list_ones(T).

scalar_product_expr([], [], 0).

scalar_product_expr([C | T], [X | U], C * X + V) :-
  scalar_product_expr(T, U, V).

reify(A #= B, Cr) :-
  reify_rel(A, B, '=', A = B, Cr).

reify(#\ C, Cr) :-
  reify(C, Cr0),
  reify_not(Cr0, Cr).

reify(C #\/ D, Cor) :-
  reify(C, Cr),
  reify(D, Dr),
  reify_or(Cr, Dr, Cor).

reify(C #/\ D, Cand) :-
  reify(C, Cr),
  reify(D, Dr),
  reify_and(Cr, Dr, Cand).

reify(C #\ D, Cxor) :-
  reify(C, Cr),
  reify(D, Dr),
  reify_xor(Cr, Dr, Cxor).

reify(C #==> D, Cimply) :-
  reify(C, Cr),
  reify(D, Dr),
  reify_imply(Cr, Dr, Cimply).

reify(C #==> D, Cimply) :-
  reify(C, Cr),
  reify(D, Dr),
  reify_imply(Dr, Cr, Cimply).

reify(C #<==> D, Cequiv) :-
  reify(C, Cr),
  reify(D, Dr),
  reify_equiv(Cr, Dr, Cequiv).

reify_not(0, 1) :-
  !.
reify_not(1, 0) :-
  !.
reify_not(Cr, #\ Cr).

reify_or(0, B, B) :-
  !.
reify_or(1, _, 1) :-
  !.
reify_or(A, 0, A) :-
  !.
reify_or(_, 1, 1) :-
  !.
reify_or(A, B, A #\/ B).

reify_and(0, _, 0) :-
  !.
reify_and(1, B, B) :-
  !.
reify_and(_, 0, 0) :-
  !.
reify_and(_, 1, 1) :-
  !.
reify_and(A, B, A #/\ B).

reify_imply(A, B, C) :-
  reify_not(A, Aopp),
  reify_or(Aopp, B, C).

reify_xor(0, B, B) :-
  !.
reify_xor(A, 0, A) :-
  !.
reify_xor(1, 1, 0) :-
  !.

reify_equiv(A, B, C) :-
  reify_xor(A, B, Copp),
  reify_not(Copp, C).

reify_rel(A, B, LinOp, IntOp, Cr) :-
  eval(A, VA),
  eval(B, VB),
  (
    integer(VA),
    integer(VB)
  ->
    (
      IntOp
    ->
      Cr = 1
    ;
      Cr = 0
    )
  ;
    linear_mul(VB, -1, VBopp),
    linear_add(VA, VBopp, S + K),
    Kopp is -K,
    Cr = linear(S, LinOp, Kopp)
  ).

reified_constraint(C) :-
  reify(C, Cr),
  constraint(Cr).

emit_constraint(#\ Sub) :-
  emit('<Not>'),
  emit_constraint(Sub),
  emit('</Not>').

emit_constraint(#\ Sub) :-
  emit('<Not>'),
  emit_constraint(Sub),
  emit('</Not>').

emit_constraint(A #\/ B) :-
  emit('<Or>'),
  emit_constraint(A),
  emit_constraint(B),
  emit('</Or>').

emit_constraint(A #/\ B) :-
  emit('<And>'),
  emit_constraint(A),
  emit_constraint(B),
  emit('</And>').

emit_constraint(A #\ B) :-
  emit('<Xor>'),
  emit_constraint(A),
  emit_constraint(B),
  emit('</Xor>').

emit_constraint(linear(WeightedSum, Rel, C)) :-
  emit('<Linear rel="~a" constant="~d">', [Rel, C]),
  emit_sum(WeightedSum),
  emit('</Linear>').

emit_constraint('XmulYeqZ'(X, Y, Z)) :-
  emit('<XmulYeqZ X="~a" Y="~a" Z="~a"/>', [X, Y, Z]).

emit_constraint('XmulYeqC'(X, Y, C)) :-
  emit('<XmulYeqC X="~a" Y="~a" C="~d"/>', [X, Y, C]).

emit_constraint('XmodYeqZ'(X, Y, Z)) :-
  emit('<XmodYeqZ X="~a" Y="~a" Z="~a"/>', [X, Y, Z]).

emit_constraint('AbsXeqY'(X, Y)) :-
  emit('<AbsXeqZ X="~a" Y="~a"/>', [X, Y]).

emit_constraint('all_different'(Vars, Consistency)) :-
  emit('<AllDifferent consistency="~a">', [Consistency]),
  emit_vars(Vars),
  emit('</AllDifferent>').

emit_constraint(min(Vars, X)) :-
  emit('<Min X="~a">', [X]),
  emit_vars(Vars),
  emit('</Min>').

emit_constraint(max(Vars, X)) :-
  emit('<Max X="~a">', [X]),
  emit_vars(Vars),
  emit('</Max>').

vars_id([], []) :-
  !.

vars_id([I | T], [I | U]) :-
  integer(I),
  !,
  vars_id(T, U).

vars_id([H | T], [HId | U]) :-
  get_attr(H, foreignfd, HId),
  !,
  vars_id(T, U).

vars_id([H | _T], _) :-
  type_error('finite-domain variable expected', H).

vars_id(L, _) :-
  type_error('list of finite-domain variables expected', L).

expr_id([], []) :-
  !.

expr_id([I | T], [I | U]) :-
  integer(I),
  !,
  expr_id(T, U).

expr_id([H | T], [HId | U]) :-
  get_attr(H, foreignfd, HId),
  !,
  expr_id(T, U).

expr_id([H | T], [HId | U]) :-
  !,
  X #= H,
  get_attr(X, foreignfd, HId),
  expr_id(T, U).

expr_id(L, _) :-
  type_error('list of finite-domain arithmetic expressions expected', L).

order(Delta, E1, E2) :-
  b_getval(foreign_vars, Vars),
  b_getval(foreign_ordering, Ordering),
  order(Ordering, Vars, E1, E2, Delta).

order([], _Vars, _E1, _E2, '=').

order([min(E) | Tail], Vars, E1, E2, Delta) :-
  order_eval(E, Vars, E1, V1),
  order_eval(E, Vars, E2, V2),
  compare(Delta0, V1, V2),
  (
    Delta0 = '='
  ->
    order(Tail, Vars, E1, E2, Delta)
  ;
    Delta = Delta0
  ).

order([max(E) | Tail], Vars, E1, E2, Delta) :-
  order_eval(E, Vars, E1, V1),
  order_eval(E, Vars, E2, V2),
  compare(Delta0, V2, V1),
  (
    Delta0 = '='
  ->
    order(Tail, Vars, E1, E2, Delta)
  ;
    Delta = Delta0
  ).

order_eval(E, Vars, Values, V) :-
  \+ \+ (
    Vars = Values,
    I is E,
    nb_setval(order_value, I)
  ),
  nb_getval(order_value, V),
  nb_setval(order_value, 0).

labeling(Vars, VarSel, ValSel, Branching) :-
  vars_id(Vars, VarsId),
  set_level,
  emit(
    '<Labeling varSel="~a" valSel="~a" branching="~a">',
    [VarSel, ValSel, Branching]
  ),
  emit_vars(VarsId),
  emit('</Labeling>\n'),
  nb_getval(foreign_current_level_nb, CurrentLevelNb),
  repeat,
  nb_setval(foreign_current_level_nb, CurrentLevelNb),
  b_setval(foreign_current_level_b, CurrentLevelNb),
  (
    (
      check_consistency
    ->
      true
    ;
      !,
      fail
    )
  ;
    backtrack,
    emit('<Next/>\n'),
    fail
  ).

emit_vars([]).

emit_vars([H | T]) :-
  integer(H),
  !,
  emit('<Constant C="~d"/>', [H]),
  emit_vars(T).

emit_vars([Id | T]) :-
  emit('<Var X="~a"/>', [Id]),
  emit_vars(T).

labeling_options([], _VarSel, _ValSel, _Branching, []) :-
  !.

labeling_options([H | T], VarSel, ValSel, Branching, Ordering) :-
  varsel(H),
  !,
  VarSel = H,
  labeling_options(T, VarSel, ValSel, Branching, Ordering).

labeling_options([H | T], VarSel, ValSel, Branching, Ordering) :-
  valsel(H),
  !,
  ValSel = H,
  labeling_options(T, VarSel, ValSel, Branching, Ordering).

labeling_options([H | T], VarSel, ValSel, Branching, Ordering) :-
  branching(H),
  !,
  Branching = H,
  labeling_options(T, VarSel, ValSel, Branching, Ordering).

labeling_options([H | T], VarSel, ValSel, Branching, Ordering) :-
  ordering(H),
  !,
  Ordering = [H | Tail],
  labeling_options(T, VarSel, ValSel, Branching, Tail).

labeling_options([H | _T], _VarSel, _ValSel, _Branching, _Ordering) :-
  type_error('labeling option', H).

labeling_options(L, _VarSel, _ValSel, _Branching, _Ordering) :-
  type_error('list of labeling options', L).

varsel(leftmost).

varsel(ff).

varsel(ffc).

varsel(min).

varsel(max).

valsel(up).

valsel(middle).

valsel(down).

branching(step).

branching(enum).

branching(bisect).

ordering(min(_)).

ordering(max(_)).

attr_unify_hook(XId, Y) :-
  (
    get_attr(Y, foreignfd, YId)
  ->
    constraint(linear(XId * 1 + YId * -1, '=', 0))
  ;
    integer(Y)
  ->
    constraint(linear(XId * 1, '=', Y))
  ).

attribute_goals(X) -->
  {
    fd_dom(X, Dom)
  },
  [X in Dom].

constraint(0) :-
  !,
  fail.

constraint(1) :-
  !.

constraint(C) :-
  set_level,
  emit('<Constraint>'),
  emit_constraint(C),
  emit('</Constraint>\n'),
  check_consistency.

emit_sum(X * W) :-
  emit('<Var X="~a" weight="~d"/>', [X, W]).

emit_sum(A + B) :-
  emit_sum(A),
  emit_sum(B).

constraint(Format, Args) :-
  set_level,
  emit(Format, Args),
  check_consistency.

:- use_module(library(readutil)).

check_consistency :-
  require_solver(_In, Out, _Err, _Pid),
  consistency_loop(Out).

consistency_loop(Out) :-
  read(Out, S),
  (
    S = consistent
  ->
    true
  ;
    S = equal(Id, V)
  ->
    assoc(Assoc),
    get_assoc(Id, Assoc, X),
    del_attr(X, foreignfd),
    X = V,
    consistency_loop(Out)
  ).

set_level :-
  backtrack,
  try.

backtrack :-
  require_solver(_In, _Out, _Err, _Pid),
  b_getval_default(foreign_current_level_b, CurrentLevelB, 0),
  nb_getval(foreign_current_level_nb, CurrentLevelNb),
  LevelSucc is CurrentLevelB + 1,
  \+ (
    between(LevelSucc, CurrentLevelNb, _),
    \+ (
      emit('<Backtrack/>\n')
    )
  ).

try :-
  b_getval_default(foreign_current_level_b, CurrentLevelB, 0),
  LevelSucc is CurrentLevelB + 1,
  (
    prolog_current_choice(CurrentChoicePoint)
  ->
    true
  ;
    CurrentChoicePoint = 0
  ),
  b_getval_default(foreign_last_choice_point, LastChoicePoint, 0),
  (
    CurrentChoicePoint > LastChoicePoint
  ->
    emit('<Try/>\n'),
    b_setval(foreign_last_choice_point, CurrentChoicePoint),
    b_setval(foreign_current_level_b, LevelSucc),
    nb_setval(foreign_current_level_nb, LevelSucc)
  ;
    nb_setval(foreign_current_level_nb, CurrentLevelB)
  ).

b_getval_default(Var, Value, Default) :-
  b_getval(Var, Value0),
  (
    Value0 = []
  ->
    Value = Default
  ;
    Value = Value0
  ).
