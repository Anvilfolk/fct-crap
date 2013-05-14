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

:- chrg_symbols word/3, g/1, falsify/1, wait/1, remove_falsify/1, iCat/3, ambiguity/0.

:- chr_constraint clean/0, checkExistentialConstraints/0, unsat/1, tentativeUnsat/1, failedCat/1,
   chunker_phase/0, init_check/0, constraint_phase/0, tpl/1, tentative/1, relaxable/1, tentativeRelaxed/1, relaxed/1.

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

word(Comp, Attr, Word) <:> Tree=..[Comp,Word] | iCat(Comp, Attr, Tree).

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
  falsify(N0, N1, Prop), unsat(List) ==> member(Prop, List) | remove_falsify(N0, N1, Prop).
  falsify(N0, N1, Prop), remove_falsify(N0, N1, Prop) <=> true.
  falsify(N0, N1, Prop), unsat(List) <=> unsat([g(N0, N1, Prop) | List]). 

 % RUN SINGLE EXAMPLE

%doParse(S) :- unsat([]), init_grammar, parse(S), chunker_phase,
%              init_check, constraint_phase, checkExistentialConstraints.

doParse(S) :- init_grammar, relaxed([]), failedCat([]), parse(S), chunker_phase,
              init_check, constraint_phase, checkExistentialConstraints.


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
                relaxable(requirement(np, n, det)).

% CATEGORIES, KERNELS, ETC

category(sentence).
category(np).
category(vp).

head(n, np).
head(pn, np).
head(v, vp).
head(vp, sentence).

% What trying out means

try(ICat) :- tentativeRelaxed([]), unsat([]), tentative(ICat).

% TREE RULES
%
% Given two tree-like structures and the to-expand category, create a new tree.

buildTree(Cat,T1,T2,Tree):- T1=..[Cat|L], !, append(L,[T2],L1), Tree=..[Cat|L1].%, write('s1'-Cat),nl.
buildTree(Cat,T1,T2,Tree):- T2=..[Cat|L], !, append([T1],L,L1), Tree=..[Cat|L1].%, write('s2'-Cat),nl.
buildTree(Cat,T1,T2,Tree):- Tree=..[Cat,T1,T2].%, write('s3'-Cat-Tree),nl.

% KERNELS ARE CATEGORIES AT THE LEAF LEVEL

iCat(Comp,Attr,Tree) ::> head(Comp, Cat), not(category(Comp)), CatTree=..[Cat,Tree] | iCat(Cat,Attr, CatTree).

% EXPANDING CATEGORIES - CHUNKER

  !iCat(Comp, _, Tree1), iCat(Cat, Attr2, Tree2), % Comp next to Cat, subcategories stay, to-expand category disappears
  !{tpl(constituency(Cat, L))}, !{chunker_phase}  % L is the set of constituents of Cat
  <:> member(Comp, L), not(category(Comp)),       % Comp is a basic word constituent of Cat
      buildTree(Cat, Tree1, Tree2, Tree)%,write('b1'-Cat-Tree),nl          % Build the tree for the expanded Cat
  | iCat(Cat, Attr2, Tree).                       % Create expanded Cat, replacing the smaller, previous one

  iCat(Cat, Attr1, Tree1), !iCat(Comp, _, Tree2), % Symmetric rule
  !{tpl(constituency(Cat, L))}, !{chunker_phase}
  <:> member(Comp, L), not(category(Comp)),
      buildTree(Cat, Tree1, Tree2, Tree)%, write('b2'-Cat-Tree),nl
  | iCat(Cat, Attr1, Tree).


% Once chunking is done, i.e. no more of the above rules can be applied,
% change to the constraint phase where constraints can be checked.

  init_check \ chunker_phase <=> true.

  init_check, iCat(N1, N2, Cat, Attr1, Tree1), failedCat(L)
  ==> category(Cat), not(member(iCat(N1, N2, Cat, Attr1, Tree1), L))
  | try(iCat(N1, N2, Cat, Attr1, Tree1)).
  
  init_check <=> true.

  constraint_phase \ init_check <=> true.

% Once we are in the constraint phase, check whether there is ambiguity.
% For this, we try to find two non-terminal categories that overlap.

iCat(N1, N2, _, _, _), iCat(N3, N4, _, _, _), init_check ==> N1 < N3, N3 < N2, N2 < N4 | ambiguity(N3, N2).

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
  checkExistentialConstraints, constraint_phase <=> true.



% OBLIGATORITY (existential property)
% obligatority(Cat, C) - all categories of type Cat must have a C included.

% For any category, if there is an obligatority template, then we must wait for it to be satisfied.
% It is satisfied whenever we can find the desired category within the boundaries of the root category.
  %iCat(Cat, _, _),                                % Found Cat
  %{tpl(obligatority(Cat, C))}, {constraint_phase} % Cat should have C & constraint phase
  %::> wait(obligatority(Cat, C)).                 % then wait for C...
  
  tentative(iCat(N1,N2,Cat, _, _)),                                % Found Cat
  tpl(obligatority(Cat, C)), constraint_phase % Cat should have C & constraint phase
  ==> wait(N1,N2,obligatority(Cat, C)).                 % then wait for C...
  
  
  !{iCat(N1, N2, C,_,_)},                               % Found C!
  wait(obligatority(_,C)):(N3, N4), !{constraint_phase} % We needed C within some bounds
  <:> N3 =< N1, N2 =< N4                                % C is within those bounds
  | true.                                               % Obligatority satisfied!

% REQUIREMENT (existential property)
% requirement(C,C1,C2) - if there is a C1 in C, then there must also be a C2
 
% If one can find a category of type C1 within a category of type C, then one must wait for a
% category of type C2 within the boundaries of C. Satisfaction is the same as above.

  %iCat(C1,_,_):(N1, N2), {iCat(N3,N4,Cat,_,_)},          % C1, C
  iCat(C1,_,_):(N1, N2), {tentative(iCat(N3,N4,Cat,_,_))},          % C1, C
  {tpl(requirement(Cat,C1,C2))}, {constraint_phase}      % Constraints & constraint phase
  ::> N3 =< N1, N2 =< N4                                 % C1 within C2
  | wait(requirement(Cat,C1,C2)):(N3, N4).               % then wait...
  
  !{iCat(N1, N2, C2,_,_)},                                % Found C2!
  wait(requirement(_,_,C2)):(N3, N4), !{constraint_phase} % There was a requirement for C2
  <:> N3 =< N1, N2 =< N4                                  % C2 within C
  | true.                                                 % Requirement satisfied!

% PRECEDENCE (universal property)
% prec(C,C1,C2) - any C1 within C must precede any C2 within that same C.
 
% Precedence is falsified whenever two categories C2, C1 are found in that order within the bounds of C.	
  %iCat(Cat2,_,_):(N1,_), ... , iCat(Cat1,_,_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Found C2 and C1, in that order, and a C
  iCat(Cat2,_,_):(N1,_), ... , iCat(Cat1,_,_):(_,N2), {tentative(iCat(N3,N4,Cat,_,_))}, % Found C2 and C1, in that order, and a C
  {tpl(precedence(Cat,Cat1,Cat2))}, {constraint_phase}                       % Precedence & constraint phase
  ::> N3 =< N1, N2 =< N4 |                                                   % C1 and C2 within C
  falsify(precedence(Cat,Cat1,Cat2)):(N1,N2).                                % Precedence falsified!
  
% UNICITY (universal property)
% unicity(Cat,C) - only one C is allowed in a Cat

% Unicity fails whenever you can find two distinct Cs within the bounds of Cat.
  %iCat(C,_,_):(N1,_), ... ,iCat(C,_,_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Found two C's and a Cat
  iCat(C,_,_):(N1,_), ... ,iCat(C,_,_):(_,N2), {tentative(iCat(N3,N4,Cat,_,_))}, % Found two C's and a Cat
  {tpl(unicity(Cat,C))}, {constraint_phase}                           % Unicity & constraint phase
  ::> N3 =< N1, N2 =< N4                                              % Both C's within Cat bounds
  | falsify(unicity(Cat,C)):(N1,N2).                                  % Unicity falsified!
  
% EXCLUSION (universal property)
% exclusion(Cat,C1,C2) - C1 and C2 must not both occur in a Cat

% If we can find both a C1 and C2 (in either ordering) within a Cat, exclusion fails
  %iCat(C1,_,_):(N1,_), ... , iCat(C2,_,_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Found C1, C2 and C
  iCat(C1,_,_):(N1,_), ... , iCat(C2,_,_):(_,N2), {tentative(iCat(N3,N4,Cat,_,_))}, % Found C1, C2 and C
  {tpl(exclusion(Cat,C1,C2))}, {constraint_phase}                        % Exclusion & constraint phase
  ::> N3 =< N1, N2 =< N4                                                 % C1 and C2 within C
  | falsify(exclusion(Cat,C1,C2)):(N1,N2).                               % Exclusion falsified!
  
  %iCat(C1,_,_):(N1,_), ... , iCat(C2,_,_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Symmetric to the above
  iCat(C1,_,_):(N1,_), ... , iCat(C2,_,_):(_,N2), {tentative(iCat(N3,N4,Cat,_,_))}, % Symmetric to the above
  {tpl(exclusion(Cat,C2,C1))}, {constraint_phase}
  ::> N3 =< N1, N2 =< N4
  | falsify(exclusion(Cat,C2,C1)):(N1,N2).

% DEPENDENCE (universal property)
% dependence(Cat,C1,C2) - the traits of C1 determine the traits of C2 inside a C

% If we can find C1 and C2 (in either ordering) whose two attributes are different, dependence fails
  %iCat(C1,[_,T12],_):(N1,_), ..., iCat(C2,[_,T22],_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Found C1, C2 and C
  iCat(C1,[_,T12],_):(N1,_), ..., iCat(C2,[_,T22],_):(_,N2), {tentative(iCat(N3,N4,Cat,_,_))}, % Found C1, C2 and C
  {tpl(dependence(Cat,C1,C2))}, {constraint_phase}                                  % Dependence & constraint phase
  ::> T12 \= T22, N3 =< N1, N2 =< N4                                                % The attributes differ, and C1 and C2 within C
  | falsify(dependence(Cat,C1,C2)):(N1,N2).                                         % Dependence falsified!

  %iCat(C1,[T11,_],_):(N1,_), ..., iCat(C2,[T21,_],_):(_,N2), {iCat(N3,N4,Cat,_,_)}, % Symmetric wrt the other attributes
  iCat(C1,[T11,_],_):(N1,_), ..., iCat(C2,[T21,_],_):(_,N2), {tentative(iCat(N3,N4,Cat,_,_))}, % Symmetric wrt the other attributes
  {tpl(dependence(Cat,C1,C2))}, {constraint_phase}                                  % and wrt C1 and C2 ordering
  ::> T11 \= T21, N3 =< N1, N2 =< N4
  | falsify(dependence(Cat,C1,C2)):(N1,N2).
  
  %iCat(C1,[T11,_],_):(N1,_), ..., iCat(C2,[T21,_],_):(_,N2), {iCat(N3,N4,Cat,_,_)},
  iCat(C1,[T11,_],_):(N1,_), ..., iCat(C2,[T21,_],_):(_,N2), {tentative(iCat(N3,N4,Cat,_,_))},
  {tpl(dependence(Cat,C2,C1))}, {constraint_phase}
  ::> T11 \= T21, N3 =< N1, N2 =< N4
  | falsify(dependence(Cat,C2,C1)):(N1,N2).
  
  %iCat(C1,[_,T12],_):(N1,_), ..., iCat(C2,[_,T22],_):(_,N2), {iCat(N3,N4,Cat,_,_)},
  iCat(C1,[_,T12],_):(N1,_), ..., iCat(C2,[_,T22],_):(_,N2), {tentative(iCat(N3,N4,Cat,_,_))},
  {tpl(dependence(Cat,C2,C1))}, {constraint_phase}
  ::> T12 \= T22, N3 =< N1, N2 =< N4
  | falsify(dependence(Cat,C2,C1)):(N1,N2).



% EXPANDING CATEGORIES - WITH CONSTRAINTS

  !iCat(Comp, _, Tree1), iCat(Cat, Attr2, Tree2), % Comp next to Cat, subcategories stay, to-expand category disappears
  !{tpl(constituency(Cat, L))}, !{chunker_phase}  % L is the set of constituents of Cat
  <:> member(Comp, L), category(Comp),       % Comp is a basic word constituent of Cat
      buildTree(Cat, Tree1, Tree2, Tree)%,write('b1'-Cat-Tree),nl          % Build the tree for the expanded Cat
  | iCat(Cat, Attr2, Tree).                       % Create expanded Cat, replacing the smaller, previous one

  iCat(Cat, Attr1, Tree1), !iCat(Comp, _, Tree2), % Symmetric rule
  !{tpl(constituency(Cat, L))}, !{chunker_phase}
  <:> member(Comp, L), category(Comp),
      buildTree(Cat, Tree1, Tree2, Tree)%, write('b2'-Cat-Tree),nl
  | iCat(Cat, Attr1, Tree).

% KERNELS ARE CATEGORIES AT THE CATEGORY LEVEL
  iCat(Comp,Attr,Tree), {chunker_phase}, {failedCat(L)}
  ::> head(Comp, Cat), category(Comp),
  CatTree=..[Cat,Tree], not(member(iCat(Comp,Attr,Tree), L))
  | iCat(Cat,Attr, CatTree).

% Tentative, relaxable constraint
  tentative(_), relaxable(R)
  \ tentativeUnsat([R|T]), tentativeRelaxed(RL)
  <=> tentativeUnsat(T), tentativeRelaxed([R|RL]).

  tentative(_) % not relaxable, hopefully
  \ tentativeUnsat([R|T]), unsat(UL)
  <=> tentativeUnsat(T), unsat([R|UL]).

% Failed, replace all the things with failed.
tentative(ICAT), failedCat(L), unsat([_|_]), tentativeRelaxed(_) <=> failedCat([ICAT|L]).
% Didn't fail
tentative(ICAT), unsat([]), tentativeRelaxed(L1), relaxed(L2) <=> append(L1, L2, L3) | ICAT, relaxed(L3).


end_of_CHRG_source.












