/* 
   Aug 08, 2012
   Veronica Dahl and J.Emilio Miralles
   Grammar Sanctioning program

   Version 1.15
     -code cleanups
     -no longer count unsats
   Version 1.14
     -all grammar properties are now constraints of the form g(Prop).
     -init_grammar procedure now initializes all the g/1 constraints.
     -these constraints are removed as soon as they are found to be unsatisfied by a sentence.
     -counting no longer makes sense, as a second instance will never occur.
   Version 1.13
     -automate adding of unsat_c counters
     -add all possible properties
   Version 1.12
     -change ambiguous cat/3 symbol to word/3
     -keep unsat list after readout.
   Version 1.11
     -remove unused finished/0 and exclusion/4 constraints
   Version 1.1
     -added readout of sentence number and recommended grammar changes.
   Version 1
     -takes a list of sentences in the form of a Prolog predicate 
      "string([[list],[of,sentences]])."
     -checks for the violation of property grammar rules for 
      obligatority(n), exclusion(adj,sup), requirement(n,det),unicity(det),
      constituency(det),constituency(con),constituency(ver),
      constituency(adj),constituency(sa),constituency(n),constituency(sup), 
      precedence(det,n), precedence(det,adj),precedence(adj,n).
     -creates a list of unsatisfied properties in 
      unsat([prop1, prop2, ...]) chr constraint.
     -counts each instance of the unsatisfied property in 
      unsat_c([prop, count]) chr constraint.

*/

:- compile('chrg').		

:- chrg_symbols word/3, g/1, falsify/1, wait/1, remove_falsify/1, iCat/3.

:- chr_constraint checkExistentialConstraints/0, unsat/1, tpl/1, parseOrder/1,
   failed/1, revert/0, revertFrom/1, revertTo/1, evil/1, relaxable/1, grow/0.


% LEXICON: word(Category,Traits,Word) 

  [le] ::> word(det,[sing,masc],le).
  [les] ::> word(det,[plur,masc],le).
  [un] ::> word(det,[sing,masc],un).
  [une] ::> word(det,[sing,fem],un).
  [tres] ::> word(adv,[sing,masc],tres).
  
  %nouns
  [livre] ::> word(n,[sing,masc],livre).
  [livres] ::> word(n,[plur,masc],livre).

  [pomme] ::> word(n,[sing,fem],pomme).

  %adjectives
  [jaune] ::> word(adj,[sing,masc],jaune).
  [bleu] ::> word(adj,[sing,masc],bleu).

  %conjunction
  [et] ::> word(con,[na,na], et).

  %aux verb
  [a] ::> word(v,[sing, na], a).
  [mange] ::> word(v,[sing, na], mange).

  %proper name
  [amelie] ::> word(pn,[sing, feme], amelie).
  [jean] ::> word(pn,[sing, masc], jean).


% CREATE INSTANTIATED CATEGORIES FROM WORDS

word(Comp, Attr, Word) <:> Tree =.. [Comp,Word] | iCat(Comp, Attr, Tree).

% SAMPLE PARSES/TESTS
  
  string([
         [amelie],
	 [le, livre, bleu],
	 [le, bleu, jaune],
	 [le, livres, tres, bleu],
         [le, plus, mauvais, livre],
	 [le,livre,jaune, et, bleu]]).

% falsify LISTS
% falsifys simply adds more unsatisfied constraints to the list.

    %First check if property is already in the list, if so signal remove falsify without adding to list.
    % remove the falsify marker
    %if it was not in the list, add to list
  falsify(N0, N1, Prop), unsat(List) ==> member(g(N0, N1, Prop), List) | remove_falsify(N0, N1, Prop).
  falsify(N0, N1, Prop), remove_falsify(N0, N1, Prop) <=> true.
  falsify(N0, N1, Prop), unsat(List) <=> unsat([g(N0, N1, Prop) | List]). 

 % RUN SINGLE EXAMPLE

doParse(S) :- unsat([]), evil([]), init_grammar, parse(S), grow, % chunker_phase,init_check, constraint_phase,
                                                 checkExistentialConstraints.

% GRAMMAR
%
%
% INIT GRAMMAR

init_grammar :- tpl(constituency(sentence, [np, vp])),
                tpl(constituency(np, [n, pn, det, adj])),
                tpl(constituency(vp, [v, np])),
                tpl(obligatority(sentence,vp)),
                tpl(obligatority(sentence,np)),
                tpl(obligatority(vp,v)),
                tpl(precedence(sentence,np,vb)),
                tpl(precedence(np,det,n)),
                tpl(precedence(vp,v,np)),
                tpl(requirement(np, n, det)),
                tpl(requirement(sentence, np, vp)),
                tpl(unicity(sentence,vp)),
                tpl(unicity(sentence,np)),
                tpl(unicity(vp,v)),
                tpl(unicity(vp,np)),
                tpl(unicity(np,det)), % extras for tests
                tpl(exclusion(np, pn, det)),
                tpl(dependence(np, det, n)),
                relaxable([unicity(vp,np),precedence(np,det,n)]),
                %relaxable([]),
                parseOrder([np,vp,sentence]).

% CATEGORIES, KERNELS, ETC

category(sentence).
category(np).
category(vp).

head(n, np).
head(pn, np).
head(v, vp).
head(vp, sentence).

% TREE RULES
%
% Given two tree-like structures and the to-expand category, create a new tree.

buildTree(Cat,C1,C2,T) :- %nl, write('*****<':Cat:'*****'),nl,write(C1), nl, write(C2), nl,
                          C1 = iCat(_, _, Cat,  _, T1),
                          C2 = iCat(_, _, Comp, _, _), !,
                          Cat \= Comp, T1=..[Cat|L1],
                          append(L1,[C2],L), T=..[Cat|L].

buildTree(Cat,C1,C2,T) :- %nl, write('*****':Cat:'>*****'),nl,write(C1), nl, write(C2), nl,
                          C1 = iCat(_, _, Comp, _, _),
                          C2 = iCat(_, _, Cat , _, T2),
                          Cat \= Comp, T2=..[Cat|L2],
                          append([C1],L2,L), T=..[Cat|L].

% GRAMMAR RULES
%
%
% CHECK EXISTENTIAL CONSTRAINTS
%
% Some constraints require the existence of certain categories. These can only be
% definitely verified at the end, once the categories have been filled. After parsing,
% checkExistentialConstraints is put into the bag and all the existential properties
% desired, which are marked using wait(Prop), are checked.
% The constraint_phase indicator is also removed to make output prettier :)
  !{checkExistentialConstraints}, wait(Prop) <:> falsify(Prop).
  checkExistentialConstraints <=> true.

% PRECEDENCE (universal property)
% prec(C,C1,C2) - any C1 within C must precede any C2 within that same C.
 
% Precedence is falsified whenever two categories C2, C1 are found in that order within the bounds of C.	
  iCat(C2,Attr2,Tree2):(N1,N2), ... ,         % Found C2
  iCat(C1,Attr1,Tree1):(N3,N4),               % Then a C1 sometime later
  {iCat(N5,N6,Cat,_,Tree)},                   % And there's a Cat
  {tpl(precedence(Cat,C1,C2))}                % In Cats, C1's must come C2's
  ::> N5 =< N1, N4 =< N6, Tree=..[Cat|T],     % C1 and C2 within Cat
      member(iCat(N1,N2,C2,Attr2,Tree2), T),  % Both are direct descendents of Cat
      member(iCat(N3,N4,C1,Attr1,Tree1), T)
  | falsify(precedence(Cat,C1,C2)):(N1,N4),   % Precedence falsified!
    {failed(g(N1,N4,precedence(Cat,C1,C2)))}. % Failure of tentative category

  
% UNICITY (universal property)
% unicity(Cat,C) - only one C is allowed in a Cat

% Unicity fails whenever you can find two distinct Cs within the bounds of Cat.
  iCat(C,Attr1,Tree1):(N1,N2), ... ,        % Found C
  iCat(C,Attr2,Tree2):(N3,N4),              % Then another C sometime later
  {iCat(N5,N6,Cat,_,Tree)},                 % And there's a Cat
  {tpl(unicity(Cat,C))}                     % Unicity
  ::> N5 =< N1, N4 =< N6, Tree=..[Cat|T],   % C's within Cat
      member(iCat(N1,N2,C,Attr1,Tree1), T), % Both are direct descendents of Cat
      member(iCat(N3,N4,C,Attr2,Tree2), T)
  | falsify(unicity(Cat,C)):(N1,N4),        % Unicity falsified!
    {failed(g(N1, N4, unicity(Cat,C)))}.    % Failure of tentative category
  
% EXCLUSION (universal property)
% exclusion(Cat,C1,C2) - C1 and C2 must not both occur in a Cat

% If we can find both a C1 and C2 (in either ordering) within a Cat, exclusion fails
  %iCat(C1,_,_):(N1,_), ... , iCat(C2,_,_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Found C1, C2 and C
  iCat(C1,Attr1,Tree1):(N1,N2), ... ,          % Found C1
  iCat(C2,Attr2,Tree2):(N3,N4),                % Then a C2 sometime later
  {iCat(N5,N6,Cat,_,Tree)},                    % And there's a Cat
  {tpl(exclusion(Cat,C1,C2))}                  % Exclusion
  ::> N5 =< N1, N4 =< N6, Tree=..[Cat|T],      % C1 and C2 within Cat
      member(iCat(N1,N2,C1,Attr1,Tree1), T),   % Both are direct descendents of Cat
      member(iCat(N3,N4,C2,Attr2,Tree2), T)
  | falsify(exclusion(Cat,C1,C2)):(N1,N4),     % Exclusion falsified!
    {failed(g(N1, N4, exclusion(Cat,C1,C2)))}. % Failure of tentative category
  
  iCat(C1,Attr1,Tree1):(N1,N2), ... ,        % Symmetry, C2 and C1
  iCat(C2,Attr2,Tree2):(N3,N4),
  {iCat(N5,N6,C,_,Tree)},
  {tpl(exclusion(C,C1,C2))}
  ::> N5 =< N1, N4 =< N6, Tree=..[C|T],
      member(iCat(N1,N2,C1,Attr1,Tree1), T),
      member(iCat(N3,N4,C2,Attr2,Tree2), T)
  | falsify(exclusion(C,C2,C1)):(N1,N4),
    {failed(g(N1, N4, exclusion(C,C2,C1)))}.

% DEPENDENCE (universal property)
% dependence(Cat,C1,C2) - the traits of C1 determine the traits of C2 inside a C

% If we can find C1 and C2 (in either ordering) whose two attributes are different, dependence fails
  iCat(C1,Attr1,Tree1):(N1,N2), ... ,           % Found C1
  iCat(C2,Attr2,Tree2):(N3,N4),                 % Then a C2 sometime later
  {iCat(N5,N6,Cat,_,Tree)},                     % And there's a Cat
  {tpl(dependence(Cat,C1,C2))}                  % Dependence & constraint phase
  ::> Attr1 \= Attr2,                           % Attributes differ
      N5 =< N1, N4 =< N6, Tree=..[Cat|T],       % C1 and C2 within Cat
      member(iCat(N1,N2,C1,Attr1,Tree1), T),    % Both are direct descendents of Cat
      member(iCat(N3,N4,C2,Attr2,Tree2), T)
  | falsify(dependence(Cat,C1,C2)):(N5,N6),     % Dependence falsified!
    {failed(g(N5, N6, dependence(Cat,C1,C2)))}. % Failure of tentative category

  iCat(C1,Attr1,Tree1):(N1,N2), ... ,           % Symmetric
  iCat(C2,Attr2,Tree2):(N3,N4),
  {iCat(N5,N6,Cat,_,Tree)},
  {tpl(dependence(Cat,C1,C2))}
  ::> Attr1 \= Attr2,
      N5 =< N1, N4 =< N6, Tree=..[Cat|T],
      member(iCat(N1,N2,C1,Attr1,Tree1), T),
      member(iCat(N3,N4,C2,Attr2,Tree2), T)
  | falsify(dependence(Cat,C2,C1)):(N5,N6),
    {failed(g(N5, N6, dependence(Cat,C2,C1)))}.





% IF THINGS FAILED, REVERT!

% If a non-relaxable property failed, it's time to revert. If all properties are relaxable, revert won't fire!
failed(g(_, _, Prop)), relaxable(R) ==> not(member(Prop, R)) | revert.
revert, revert <=> revert. % Only one revert.

% Since we are reverting, remove all unsatisfied properties until no more failed(P) apply.
revert \ unsat(L), failed(P) <=> delete(L, P, L2), write('FAILED ':P:(L2):(L)), nl | unsat(L2).

% Revert - remove the revertFrom/To predicates, the From, and add the To. Also add the failed predicate to the evil list!
evil(E), revert, 
revertFrom(iCat(N1,N2,Cat1, Attr1, Tree1)),
revertTo(iCat(N3,N4,Cat2, Attr2, Tree2)),
iCat(N1,N2,Cat1, Attr1, Tree1)
<=> %write('AAAAAAAAAAAAAAAAAAAAAAAAAAAA') |
  iCat(N3,N4,Cat2, Attr2, Tree2), evil([iCat(N1,N2,Cat1, Attr1, Tree1)|E]).


% In case there was no revert, simply remove the revertFroms, and the failed (which were relaxed for sure).
%revertFrom(F), revertTo(T) <=> nl, write('++++++++'), nl, write(F), nl, write(T), nl, write('--------'), nl | true.
revertFrom(_), revertTo(_) <=> true.
failed(_) <=> true.

% EXPANDING CATEGORIES - WITH CONSTRAINTS

   !iCat(Comp, Attr1, Tree1):(N1,N2), iCat(Cat, Attr2, Tree2):(N2,N3), % Comp next to Cat, subcategories stay, to-expand category disappears
   !{tpl(constituency(Cat, L))},!{evil(EL)},         % L is the set of constituents of Cat
   !{parseOrder([Cat|_])}
  <:> not(member(iCat(N1,N3,Cat, Attr2, Tree), EL)), % A constituent that is not a super-horrible thing.
      member(Comp, L),                               % Comp is a basic word constituent of Cat
      buildTree(Cat, iCat(N1,N2,Comp, Attr1, Tree1),
                     iCat(N2,N3,Cat , Attr2, Tree2),
                     Tree)                           % Build the tree for the expanded Cat
  | iCat(Cat, Attr2, Tree):(N1,N3),                  % Create expanded Cat, replacing the smaller, previous one
    {revertFrom(iCat(N1,N3,Cat, Attr2, Tree))},
    {revertTo(iCat(N2,N3,Cat, Attr2, Tree2))}.

   iCat(Cat, Attr1, Tree1):(N1,N2), !iCat(Comp, Attr2, Tree2):(N2,N3), % Symmetric rule
   !{tpl(constituency(Cat, L))}, !{evil(EL)},
   !{parseOrder([Cat|_])}
  <:> not(member(iCat(N1,N3,Cat, Attr1, Tree), EL)),
      member(Comp, L),
      buildTree(Cat, iCat(N1,N2,Cat , Attr1, Tree1),
                     iCat(N2,N3,Comp, Attr2, Tree2), Tree)
  | iCat(Cat, Attr1, Tree):(N1,N3),
    {revertFrom(iCat(N1,N3,Cat, Attr1, Tree))},
    {revertTo(iCat(N1,N2,Cat, Attr1, Tree1))}.



% OBLIGATORITY (existential property)
% obligatority(Cat, C) - all categories of type Cat must have a C included.

% For any category, if there is an obligatority template, then we must wait for it to be satisfied.
% It is satisfied whenever we can find the desired category within the boundaries of the root category.
  iCat(Cat, _, _),                 % Found Cat
  {tpl(obligatority(Cat, C))}      % Cat should have C & constraint phase
  ::> wait(obligatority(Cat, C)).  % then wait for C...
  
  
  !{iCat(N1, N2, C,_,_)},          % Found C!
  wait(obligatority(_,C)):(N3, N4) % We needed C within some bounds
  <:> N3 =< N1, N2 =< N4           % C is within those bounds
  | true.                          % Obligatority satisfied!

% REQUIREMENT (existential property)
% requirement(C,C1,C2) - if there is a C1 in C, then there must also be a C2
 
% If one can find a category of type C1 within a category of type C, then one must wait for a
% category of type C2 within the boundaries of C. Satisfaction is the same as above.

  iCat(C1,_,_):(N1, N2), {iCat(N3,N4,Cat,_,_)}, % C1, C
  {tpl(requirement(Cat,C1,C2))}                 % Constraints & constraint phase
  ::> N3 =< N1, N2 =< N4                        % C1 within C2
  | wait(requirement(Cat,C1,C2)):(N3, N4).      % then wait...
  
  !{iCat(N1, N2, C2,_,_)},                      % Found C2!
  wait(requirement(_,_,C2)):(N3, N4)            % There was a requirement for C2
  <:> N3 =< N1, N2 =< N4                        % C2 within C
  | true.                                       % Requirement satisfied!



% KERNELS ARE CATEGORIES AT THE CATEGORY LEVEL
iCat(Comp,Attr,Tree):(N1,N2), {parseOrder([Cat|_])} ::> head(Comp, Cat), NewTree=..[Cat,iCat(N1,N2,Comp,Attr,Tree)] | iCat(Cat, Attr, NewTree).

grow \ parseOrder([_|L]) <=> parseOrder(L).

end_of_CHRG_source.

% TODO LIST
% set of unsatisfied things so they don't get repeated
% Reverting based on failure
% Growing only once existentials are done?
% Remove restrictions where you can find constituency, e.g. VP constituency within Sentence for NP
% order in which things expand!!!
% doParse([jean,mange, une, pomme]).