%%% Rappresentazione delle formule
/* negazione: - F
   congiunzione: F & G
   disgiunzione: F v G
   implicazione: F => G
   doppia implicazione: F <=> G
   quantificazione universale: all(X,F)
   quantificazione esistenziale: some(X,F)
*/
%% Operatori: associativi a sinistra
:- op(800, yfx, &).
:- op(850, yfx, v).   
:- op(870, yfx, =>).  
:- op(880, yfx, <=>).  

/* http://www.swi-prolog.org/pldoc/man?section=opsummary
   l'operatore - e' predefinito,
   con priorita' 500 e associativita' fx
Attenzione: --p da` errore, -(-p) */

main :-
    open( './input.txt', read, Str ),
    read_file( Str, Lines ),
    close( Str ),
    write( Lines ), nl,
	%% test nnf
	nnf(-(p => q v r),X),
	write( X ), nl.

read_file( Stream,[] ) :-
    at_end_of_stream( Stream ).

read_file( Stream,[X|L] ) :-
    \+ at_end_of_stream( Stream ),
	read_line_to_codes( Stream, Codes ),
    atom_chars( X, Codes ),
    read_file( Stream, L ).

	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% forma normale negativa
nnf(A => B, F v G) :- !,
	nnf(-A,F), nnf(B,G).
nnf(-(A => B), F & G) :- !,
	nnf(A,F), nnf(-B,G).
nnf(A <=> B, F) :- !,
	nnf((A => B) & (B => A),F).
nnf(-(A <=> B), F) :- !,
	nnf(-((A => B) & (B => A)),F).
nnf(A v B, F v G) :- !,
	nnf(A,F), nnf(B,G).
nnf(-(A v B), F & G) :- !,
	nnf(-A,F), nnf(-B,G).
nnf(A & B, F & G) :- !,
	nnf(A,F), nnf(B,G).
nnf(-(A & B), F v G) :- !,
	nnf(-A,F), nnf(-B,G).
nnf(-(-A),F) :- !, nnf(A,F).
nnf(all(X,A),all(X,F)) :- !, nnf(A,F).
nnf(-(all(X,A)),some(X,F)) :- !, nnf(-A,F).
nnf(some(X,A),some(X,F)) :- !, nnf(A,F).
nnf(-(some(X,A)),all(X,F)) :- !, nnf(-A,F).
nnf(A,A).