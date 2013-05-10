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

:- chrg_symbols word/3.

:- chr_constraint clean/0, check_waits/0, update/1, unsat/1, 
   wait/1, remove_update/1,oblig_check/0,g/1.

% LEXICON: word(Category,Traits,Word) 

  [le] ::> word(det,[sing,masc],le).
  [tres] ::> word(sup,[sing,masc],tres).
  
  %nouns
  [livre] ::> word(n,[sing,masc],livre).
  [livres] ::> word(n,[plur,masc],livre).

  %adjectives
  [jaune] ::> word(adj,[sing,masc],jaune).
  [bleu] ::> word(adj,[sing,masc],bleu).

  %conjunction
  [et] ::> word(con, [na,na], et).

  %aux verb
  [a] ::> word(ver, [sing, na], a).

  %proper name
  [amelie] ::> word(pn, [sing, feme], amelie).

% SAMPLE PARSES/TESTS
  
  string([
         [amelie],
	 [le, livre, bleu],
	 [le, bleu, jaune],
	 [le, livres, tres, bleu],
         [le, plus, mauvais, livre],
	 [le,livre,jaune, et, bleu]]).
  
% CLEANUP
    % when clean is triggered, remove all word(_,_,_), then replace clean 
    % with finished.
  word(_,_,_), {!clean} <:> true. 
  clean <=> true.

% UTILITIES
%
% RUN COMMANDS

    %First initializes the unsat([]) list and all the unsat_c counters for 
    %each property, then finds the list of strings
    %of the form "string([[a], [list,of], [strings]]).", and processes it.
  start :- unsat([]), init_grammar, string(X), process(X,0).

% BATCH processing
  process([],S_count) :- nl,write('There are '), write(S_count), write(' sentences.'),nl, nl,!.
  process([H|T],S_count) :- S_count_inc is S_count +1, oblig_check,
				parse(H), check_waits, clean, process(T, S_count_inc).

% UPDATE LISTS

    %First check if property is already in the list, if so signal remove update without adding to list.
    %remove the update marker and increment counter for that property
    %if it was not in the list, increment counter and add to list
  update(Prop), unsat(List) ==> member(Prop, List) | remove_update(Prop).
  update(Prop), remove_update(Prop) <=> true.
  update(Prop), unsat(List) <=> unsat([Prop | List]). 

% GRAMMAR
%
% INIT GRAMMAR
%
   init_grammar :- g(obligatority(n)),
		   g(constituency(det)), g(constituency(adj)), g(constituency(n)), g(constituency(sup)), g(constituency(pn)),
		   g(precedence(det,adj)), g(precedence(det,n)),
  		   g(precedence(adj,n)), g(precedence(sup,adj)), g(precedence(n,sup)), g(precedence(det,sup)),
		   g(unicity(det)),
		   g(requirement(n,det)),
		   g(dependence(det,n)),
		   g(dependence(n,adj)).
%GRAMMAR RULES
%
%
% CHECK WAITS

    %when check waits is called, remove wait marker for the unverified property, and signal adding to unsat list
  check_waits \ wait(Prop), g(Prop) <=> update(Prop).
  check_waits <=> true.

% CONSTITUENCY

    %no longer test for constituency, but get it from the representative lexicon
  
% OBLIGATORITY
  
  g(obligatority(C)), oblig_check ==> wait(obligatority(C)).
  oblig_check <=> true.

  {wait(obligatority(C))}, !word(C,_,_) <:> true.

% PRECEDENCE: prec(C1,C2)-- C1 must precede C2 inside a noun phrase
 	 
  !word(C2,_,_), ... , !word(C1,_,_), {g(precedence(C1,C2))} <:> {update(precedence(C1,C2))}.
 
% UNICITY one(C,SX)-- only one C is allowed in a phrase SX

  !word(C,_,_), ... ,!word(C,_,_), {g(unicity(C))} <:> {update(unicity(C))}.
  
% EXCLUSION: exclude(C1,C2,Ph)-- C1 and C2 must not both occur in a Ph

  !word(C1,_,_), ... , !word(C2,_,_), {g(exclusion(C1,C2))} <:> {update(exclusion(C1,C2))}.
  !word(C1,_,_), ... , !word(C2,_,_), {g(exclusion(C2,C1))} <:> {update(exclusion(C2,C1))}.

% REQUIREMENT: exige(C1,C2,Ph)-- if C1 is in Ph, C2 must be there too

  word(C1,_,_), {g(requirement(C1,C2))} ::> {wait(requirement(C1,C2))}.
  {wait(requirement(_,C2))}, !word(C2,_,_) <:> true.

% DEPENDENCE: dep(C1,C2,Ph) -- the traits of C1 determine the traits of C2 inside a Ph

  !word(C1,[_,T12],_), ..., !word(C2,[_,T22],_), {g(dependence(C1,C2))} <:> T12 \= T22 | {update(dependence(C1,C2))}.
  !word(C1,[T11,_],_), ..., !word(C2,[T21,_],_), {g(dependence(C1,C2))} <:> T11 \= T21 | {update(dependence(C1,C2))}.
  !word(C1,[T11,_],_), ..., !word(C2,[T21,_],_), {g(dependence(C2,C1))} <:> T11 \= T21 | {update(dependence(C2,C1))}.
  !word(C1,[_,T12],_), ..., !word(C2,[_,T22],_), {g(dependence(C2,C1))} <:> T12 \= T22 | {update(dependence(C2,C1))}.
 
 end_of_CHRG_source.
