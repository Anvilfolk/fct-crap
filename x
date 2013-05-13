a.
b.

c :- fail.

p(1, 4).
p(r(1), 3).

d(X, Y) :- not(p(X, Y)).

bachelor(P) :- male(P), not(married(P)). 

male(henry). 
male(tom). 

married(tom).

list([1,2,3,4]).
rem(2).
rem(3).

remList([], []).
remList([X|T1], [X|T2]) :- remList(T1, T2), \+ rem(X).
remList([X|T1], T2) :- remList(T1, T2), rem(X).
