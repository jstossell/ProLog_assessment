/*
1.YES.
2.YES.
3.YES.
4.NO.
5.YES.
6.YES.
7.YES.
8.NO.
9.NO.
10.YES.
*/

:-op(140, fy, neg).
:-op(160, xfy, [and, or, imp, revimp, equiv, notequiv, uparrow, downarrow,
notimp , notrevimp]).

/* member(Item, List) :- Item occurs in List.
*/

member(X, [X | _]).
member(X, [_ | Tail]) :- member(X, Tail).

/*  remove (Item, List, Newlist) :-
      Newlist is the result of removing all occurrences of
      Item from List.
*/

remove(_, [ ], [ ]).
  remove(X, [X | Tail], Newtail):-
  remove(X, Tail, Newtail).

remove(X, [Head | Tail], [Head | Newtail]):-
    remove(X, Tail, Newtail).

/* conjunctive (X) :- X is an alpha formula.
*/

conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).
conjunctive(_ equiv _).
conjunctive(neg(_ notequiv _)).
conjunctive(neg(_ equiv _)).
conjunctive(_ notequiv _).

/* disjunctive (X) :- X is a beta formula.
*/

disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).


/*  unary(X) :- X is a double negation,
      or a negated constant.
*/

unary(neg neg _).
unary(neg true).
unary(neg false).

/*  components (X, Y, Z) Y and Z are the components
      of the formula X, as defined in the alpha and
      beta table.
*/

components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y).
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).
components(X equiv Y, neg X or Y, X or neg Y).
components(neg(X equiv Y), neg X or neg Y, X or Y).
components(X notequiv Y, neg X or neg Y, X or Y).
components(neg(X notequiv Y), neg X or Y, X or neg Y).

/*  component(X, Y) Y is the component of the
      unary formula X.
*/

component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/*  singlestep(Old, New) :- New is the result of applying
      a single step of the expansion process to Old, which
      is a generalized Conjunction of generalized
      disjunctions.
*/

singlestep([Disjunction | Rest], New) :-
  member(Formula, Disjunction),
  unary(Formula),
  component(Formula, Newformula),
  remove(Formula, Disjunction, Temporary),
  Newdisjunction = [Newformula | Temporary],
  New = [Newdisjunction | Rest].

singlestep([Disjunction | Rest], New) :-
  member(Beta, Disjunction),
  disjunctive(Beta) ,
  components(Beta, Betaone, Betatwo),
  remove(Beta, Disjunction, Temporary),
  Newdis = [Betaone, Betatwo | Temporary],
  New = [Newdis | Rest].

singlestep([Disjunction | Rest], New) :-
 member(Alpha, Disjunction),
 conjunctive(Alpha),
 components(Alpha, Alphaone, Alphatwo),
 remove(Alpha, Disjunction, Temporary),
 Newdisone = [Alphaone | Temporary],
 Newdistwo = [Alphatwo | Temporary],
 New = [Newdisone, Newdistwo | Rest].

singlestep([Disjunction|Rest], [Disjunction|Newrest]):-
  singlestep(Rest, Newrest).

/* expand(Old, New) :- New is the result of applying
    singlestep as many times as possible, starting
    with Old.
*/

expand(Con, Newcon) :-
  singlestep(Con, Temp),
  expand(Temp, Newcon).

expand(Con, Con).

/* clauseform(X, Y) :- Y is the clause form of X.
*/

clauseform(X, Y) :- expand([[X]], Y).

/*tautologiesremover(X,Y) :- The CNF Y is X with the
    tautologies removed.
*/

tautologiesremover([],[]).
tautologiesremover([Disjunction | Rest], New) :-
  member(true, Disjunction),
  tautologiesremover(Rest, New).

tautologiesremover([Disjunction | Rest], New) :-
  member(Formula, Disjunction),
  member(neg Formula, Disjunction),
  tautologiesremover(Rest, New).

tautologiesremover([Disjunction | Rest], [Disjunction |New]):-
  tautologiesremover(Rest,New).

/* duplicateremover(Old,New):- Removes duplicate
    atoms within the disjunctions.
*/

duplicateremover([Disjunction | Rest], [NewDis | New]) :-
  sort(Disjunction, NewDis),
  duplicateremover(Rest, New).

  duplicateremover([],[]).

/* duplicateclause(Old,New):- Removes duplicate
    clauses from the CNF.
*/

duplicateclause(Old,New) :-
  sort(Old,New).

/*   not_member(Item, List) :-
         Item does not occur in List.
*/

not_member(_, [ ]).
not_member(Item, [Head | Tail]) :-
   	Item \== Head,
    not_member(Item, Tail).

/* resolutionstep(Old, New) :- New is the result of applying
    a resolution step of the expansion process to Old.
*/

resolutionstep(Disjunction, Newdisjunction) :-
  member(Disjunctionone, Disjunction),
  member(Formula, Disjunctionone),
  member(Disjunctiontwo, Disjunction),
  member(neg Formula, Disjunctiontwo),
  remove(neg Formula, Disjunctiontwo, Disjunctiontwoa),
  remove(Formula, Disjunctionone, Disjunctiononea),
  append(Disjunctiononea, Disjunctiontwoa, New),
  sort(New, Newdis),
  Newdisjunction = [Newdis | Disjunction],
  not_member(Newdis, Disjunction).

/* resolution(Old, New) :- New is the result of applying
    resolutionstep as many times as possible, starting
    with Old.
*/

resolution(Res, Newres) :-
  resolutionstep(Res, Temp),
  resolution(Temp , Newres).

resolution(Res, Res).

/*  if_then_else(P, Q, R) :-
     either P and Q, or not P and R.
*/

if_then_else(P, Q, _) :- P, !, Q.
if_then_else(_, _, R) :- R.

/* test(X) :- Create a complete Resolution expansion
      for neg X, and see if it is closed.
*/

test(X):-
expand([[neg (X)]], Temp),
  duplicateremover(Temp, Medtemp),
  duplicateclause(Medtemp, MedMedtemp),
  tautologiesremover(MedMedtemp, Y),
resolution(Y,Z),
 if_then_else(member([], Z), yes, no).
      yes :- write('YES'), nl.
      no :- write('NO'), nl.
