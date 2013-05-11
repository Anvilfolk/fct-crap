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

%%%% CHANGES: g, update, wait, remove_update moved from constraints to symbols
%%%%          added template predicate tpl for generic constraints, not instantiated with intervals


:- chrg_symbols word/3, g/1, update/1, wait/1, remove_update/1, iCat/3, ambiguity/0.

:- chr_constraint clean/0, checkExistentialConstraints/0, unsat/1, expansion_phase/0, constraint_phase/0, tpl/1.

% LEXICON: word(Category,Traits,Word) 

  [le] ::> word(det,[sing,masc],le).
  [les] ::> word(det,[plur,masc],le).
  [tres] ::> word(adv,[sing,masc],tres).
  
  %nouns
  [livre] ::> word(n,[sing,masc],livre).
  [livres] ::> word(n,[plur,masc],livre).

  %adjectives
  [jaune] ::> word(adj,[sing,masc],jaune).
  [bleu] ::> word(adj,[sing,masc],bleu).

  %conjunction
  [et] ::> word(con,[na,na], et).

  %aux verb
  [a] ::> word(v,[sing, na], a).

  %proper name
  [amelie] ::> word(pn,[sing, feme], amelie).


% CREATE INSTANTIATED CATEGORIES FROM WORDS

word(Comp, Attr, Word) <:> iCat(Comp, Attr, Word).

% SAMPLE PARSES/TESTS
  
  string([
         [amelie],
	 [le, livre, bleu],
	 [le, bleu, jaune],
	 [le, livres, tres, bleu],
         [le, plus, mauvais, livre],
	 [le,livre,jaune, et, bleu]]).

% UPDATE LISTS
% Updates simply adds more unsatisfied constraints to the list.

    %First check if property is already in the list, if so signal remove update without adding to list.
    % remove the update marker
    %if it was not in the list, add to list
  update(N0, N1, Prop), unsat(List) ==> member(Prop, List) | remove_update(N0, N1, Prop).
  update(N0, N1, Prop), remove_update(N0, N1, Prop) <=> true.
  update(N0, N1, Prop), unsat(List) <=> unsat([g(N0, N1, Prop) | List]). 

 % RUN SINGLE EXAMPLE

doParse(S) :- unsat([]), init_grammar, expansion_phase, parse(S), checkExistentialConstraints.

% GRAMMAR
%
%
% INIT GRAMMAR
   init_grammar :- tpl(obligatority(np, n)), tpl(obligatority(np, det)),
		   tpl(constituency(np, det)), tpl(constituency(np, adj)), tpl(constituency(np, n)), tpl(constituency(np, adv)), tpl(constituency(np, pn)),
		   tpl(precedence(np, det,adj)), tpl(precedence(np, det,n)),
  		 tpl(precedence(np, adj,n)), tpl(precedence(np, sup,adj)), tpl(precedence(np, n,sup)), tpl(precedence(np, det,sup)),
		   tpl(unicity(np, det)),
		   tpl(requirement(np, n,det)),
		   tpl(dependence(np, det,n)),
		   tpl(dependence(np, n,adj)).


% CATEGORIES, KERNELS, ETC

category(np).
category(vp).
%category(adjp).

kernel(n, np).
kernel(v, vp).
%kernel(adj, adjp).

% TREE RULES
%
% Given two tree-like structures and the to-expand category, create a new tree.

buildTree(Cat,T1,T2,Tree):- T1=..[Cat|L], !, append(L,[T2],L1), Tree=..[Cat|L1].
buildTree(Cat,T1,T2,Tree):- T2=..[Cat|L], !, append([T1],L,L1), Tree=..[Cat|L1].
buildTree(Cat,T1,T2,Tree):- Tree=..[Cat,T1,T2].


% KERNELS ARE CATEGORIES
iCat(Comp,Attr,Tree) ::> kernel(Comp, Cat) | iCat(Cat,Attr,Tree).


% EXPANDING CATEGORIES

  !iCat(Comp,_,Tree1), iCat(Cat,Attr2,Tree2),         % Comp next to Cat, subcategories stay, to-expand category disappears
  !{tpl(constituency(Cat, Comp))}, !{expansion_phase} % Comp can be a constituent of Cat
  <:> buildTree(Cat, Tree1, Tree2, Tree)              % Build the tree for the expanded Cat
  | iCat(Cat, Attr2, Tree).                           % Create expanded Cat, replacing the smaller, previous one

  iCat(Cat,Attr1,Tree1), !iCat(Comp,_,Tree2),         % Symmetric rule
  !{tpl(constituency(Cat, Comp))}, !{expansion_phase}
  <:> buildTree(Cat, Tree1, Tree2, Tree)
  | iCat(Cat, Attr1, Tree).

% Same rules using <=> instead of <:>
%iCat(N1, N2, Comp,_,Tree1), tpl(constituency(Cat, Comp)), expansion_phase \ iCat(N2, N3, Cat, Attr2, Tree2) <=>
%   buildTree(Cat, Tree1, Tree2, Tree)
%   | iCat(N1, N3, Cat, Attr2, Tree).

%iCat(N2, N3, Comp,_,Tree2), tpl(constituency(Cat, Comp)), expansion_phase \ iCat(N1, N2, Cat, Attr1, Tree1) <=>
%   buildTree(Cat, Tree1, Tree2, Tree)
%   | iCat(N1, N3, Cat, Attr1, Tree).

% Once category expansion is done, i.e. no more of the above rules can be applied,
% change to the constraint phase where constraints can be checked.
expansion_phase <=> constraint_phase.

% Once we are in the constraint phase, check whether there is ambiguity.
% For this, we try to find two non-terminal categories that overlap.

iCat(N1, N2, _, _, _), iCat(N3, N4, _, _, _), constraint_phase ==> N1 < N3, N3 < N2, N2 < N4 | ambiguity(N3, N2).

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
  !{checkExistentialConstraints}, wait(Prop) <:> update(Prop).
  checkExistentialConstraints, constraint_phase <=> true.



% OBLIGATORITY (existential property)
% obligatority(Cat, C) - all categories of type Cat must have a C included.

% For any category, if there is an obligatority template, then we must wait for it to be satisfied.
% It is satisfied whenever we can find the desired category within the boundaries of the root category.
  iCat(Cat, _, _),                                % Found Cat
  {tpl(obligatority(Cat, C))}, {constraint_phase} % Cat should have C & constraint phase
  ::> wait(obligatority(Cat, C)).                 % then wait for C...
  
  
  !{iCat(N1, N2, C,_,_)},                               % Found C!
  wait(obligatority(_,_,C)):(N3, N4),{constraint_phase} % We needed C within some bounds
  <:> N3 =< N1, N2 =< N4                                % C is within those bounds
  | true.                                               % Obligatority satisfied!

% REQUIREMENT (existential property)
% requirement(C,C1,C2) - if there is a C1 in C, then there must also be a C2
 
% If one can find a category of type C1 within a category of type C, then one must wait for a
% category of type C2 within the boundaries of C. Satisfaction is the same as above.

  iCat(C1,_,_):(N1, N2), {iCat(N3,N4,Cat,_,_)},          % C1, C
  {tpl(requirement(Cat,C1,C2))}, {constraint_phase}      % Constraints & constraint phase
  ::> N3 =< N1, N2 =< N4                                 % C1 within C2
  | wait(requirement(Cat,C1,C2)):(N3, N4).               % then wait...
  
  !{iCat(N1, N2, C2,_,_)},                               % Found C2!
  wait(requirement(_,_,C2)):(N3, N4), {constraint_phase} % There was a requirement for C2
  <:> N3 =< N1, N2 =< N4                                 % C2 within C
  | true.                                                % Requirement satisfied!

%

% PRECEDENCE (universal property)
% prec(C,C1,C2) - any C1 within C must precede any C2 within that same C.
 
% Precedence is falsified whenever two categories C2, C1 are found in that order within the bounds of C.	
  iCat(Cat2,_,_):(N1,_), ... , iCat(Cat1,_,_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Found C2 and C1, in that order, and a C
  {tpl(precedence(Cat,Cat1,Cat2))}, {constraint_phase}                       % Precedence & constraint phase
  ::> N3 =< N1, N2 =< N4 |                                                   % C1 and C2 within C
  update(precedence(Cat,Cat1,Cat2)):(N1,N2).                                 % Precedence falsified!
  
% UNICITY (universal property)
% unicity(Cat,C) - only one C is allowed in a Cat

% Unicity fails whenever you can find two distinct Cs within the bounds of Cat.
  iCat(C,_,_):(N1,_), ... ,iCat(C,_,_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Found two C's and a Cat
  {tpl(unicity(Cat,C))}, {constraint_phase}                           % Unicity & constraint phase
  ::> N3 =< N1, N2 =< N4                                              % Both C's within Cat bounds
  | update(unicity(Cat,C)):(N1,N2).                                   % Unicity falsified!
  
% EXCLUSION (universal property)
% exclusion(Cat,C1,C2) - C1 and C2 must not both occur in a Cat

% If we can find both a C1 and C2 (in either ordering) within a Cat, exclusion fails
  iCat(C1,_,_):(N1,_), ... , iCat(C2,_,_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Found C1, C2 and C
  {tpl(exclusion(Cat,C1,C2))}, {constraint_phase}                        % Exclusion & constraint phase
  ::> N3 =< N1, N2 =< N4                                                 % C1 and C2 within C
  | update(exclusion(Cat,C1,C2)):(N1,N2).                                % Exclusion falsified!
  
  iCat(C1,_,_):(N1,_), ... , iCat(C2,_,_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Symmetric to the above
  {tpl(exclusion(Cat,C2,C1))}, {constraint_phase}
  ::> N3 =< N1, N2 =< N4
  | update(exclusion(Cat,C2,C1)):(N1,N2).

% DEPENDENCE (universal property)
% dependence(Cat,C1,C2) - the traits of C1 determine the traits of C2 inside a C

% If we can find C1 and C2 (in either ordering) whose two attributes are different, dependence fails
  iCat(C1,[_,T12],_):(N1,_), ..., iCat(C2,[_,T22],_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Found C1, C2 and C
  {tpl(dependence(Cat,C1,C2))}, {constraint_phase}                                  % Dependence & constraint phase
  ::> T12 \= T22, N3 =< N1, N2 =< N4                                                % The attributes differ, and C1 and C2 within C
  | update(dependence(Cat,C1,C2)):(N1,N2).                                          % Dependence falsified!

  iCat(C1,[T11,_],_):(N1,_), ..., iCat(C2,[T21,_],_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Symmetric wrt the other attributes
  {tpl(dependence(Cat,C1,C2))}, {constraint_phase}                                  % and wrt C1 and C2 ordering
  ::> T11 \= T21, N3 =< N1, N2 =< N4
  | update(dependence(Cat,C1,C2)):(N1,N2).
  
  iCat(C1,[T11,_],_):(N1,_), ..., iCat(C2,[T21,_],_):(_,N2), {iCat(N3,N4,Cat,_,_)},
  {tpl(dependence(Cat,C2,C1))}, {constraint_phase}
  ::> T11 \= T21, N3 =< N1, N2 =< N4
  | update(dependence(Cat,C2,C1)):(N1,N2).
  
  iCat(C1,[_,T12],_):(N1,_), ..., iCat(C2,[_,T22],_):(_,N2), {iCat(N3,N4,Cat,_,_)},
  {tpl(dependence(Cat,C2,C1))}, {constraint_phase}
  ::> T12 \= T22, N3 =< N1, N2 =< N4
  | update(dependence(Cat,C2,C1)):(N1,N2).

 end_of_CHRG_source.
