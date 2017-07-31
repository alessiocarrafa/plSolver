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
	read_file_to_terms('./input.txt',L,[]),
	maplist(writeln, L),
	clause_form(F,all(x, all( y, p(x,y) => q(x) ) ) ),
	maplist(writeln, F) .
	
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

/*
?- nnf(-(p => q v r),X).
X = (p& (-q& -r))
*/

%%%%%%%%%%%%%%%%
%%% forma normale congiuntiva
cnf(A,F) :-
	nnf(A,NNFA),
	distrib(NNFA,F).

% applicazione delle leggi distributive
distrib(A & B,F & G) :-
	!, distrib(A,F), distrib(B,G).
distrib(A v B,F) :-
	distrib(A,A1 & A2), distrib(B,B1), !,
	distrib((A1 v B1) & (A2 v B1),F).
distrib(A v B,F) :-
	distrib(A,A1), distrib(B,B1 & B2), !,
	distrib((A1 v B1) & (A1 v B2),F).
distrib(A v B,F v G) :-
	!, distrib(A,F), distrib(B,G).
distrib(A,A).

/*
?- cnf(p & (q & r => t), X).
X = (p& (-q v -r v t)) 

?- cnf(-(p & (q & r => t)), X).
X = ((-p v q)& (-p v r)& (-p v -t))
*/

%%%%%%% forma normale prenessa

%%%%% step 0: ridenominazione delle variabili vincolate
%%% substep: sostituzione uniforme di X con Y
%% replace(+Term,-Newterm,+X,+Y) =
%% sostituendo X con Y in Term si ottiene Newterm
%% Term puo' anche essere una lista
replace(X,Y,X,Y) :- !.
replace(X,X,_,_) :- atom(X), !.
%% prima del caso generale, consideriamo le liste,
%% con un cut
%% La base replace([],[],_,_) non serve, [] e' un atom.
replace([First|Rest],[NewFirst|NewRest],X,Y) :-
	!, replace(First,NewFirst,X,Y),
	replace(Rest,NewRest,X,Y).
%% altrimenti la prossima clausola si applicherebbe anche
%% a liste, andando in loop.
replace(Term,Newterm,X,Y) :-
	Term =.. List,
	replace(List,Newlist,X,Y),
	Newterm =.. Newlist.
	
%% per generare nuovi simboli: gensym
%%% http://www.swi-prolog.org/pldoc/man?section=predsummary
%%% vedi sotto GENSYM

%%% ridenominiamo tutte le variabili vincolate
rename(all(X,A),all(Y,F)) :-
	!, gensym(X,Y),
	replace(A,F1,X,Y),
	rename(F1,F).
rename(some(X,A),some(Y,F)) :-
	!, gensym(X,Y),
	replace(A,F1,X,Y),
	rename(F1,F).
%% anche qui mettiamo prima il caso per le liste
% la base e' trattata dall'ultima clausola
rename([X|Rest],[NewX|NewRest]) :-
	!, rename(X,NewX),
	rename(Rest,NewRest).
%% poi il caso generale
rename(A,F) :-
	A =.. [Op|Args],
	member(Op,[-, &, v, =>, <=>]), !,
	rename(Args,NewArgs),
	F =.. [Op|NewArgs].
rename(A,A).


%%% Ridenominare, mettere in NNF
%%  e poi portare fuori i quantificatori
prenex(F,G) :-
	rename(F,F1),
	nnf(F1,F2),
	p_aux(F2,G).

% Il primo argomento di p_aux e' in NNF.
% Le regole per portare fuori i quantificatori dalla negazione
%    sono gia' gestite da nnf.
%% caso base: se A e' senza quantificatori, e' prenessa
p_aux(A,A) :- qfree(A).
% Regole per portare fuori dall'and
p_aux(A & B,all(X,H) ) :-
	% se A, in forma prenessa, e' un perogni:
	(p_aux(A,all(X,F)),
	 p_aux(B,G);
	% oppure lo e' B
	 p_aux(B,all(X,G)),
	 p_aux(A,F)), 
	p_aux(F & G,H).
p_aux(A & B,some(X,H) ) :-
	% se A, in forma prenessa, e' un esiste:
	(p_aux(A,some(X,F)),
	 p_aux(B,G);
	% oppure lo e' B
	 p_aux(B,some(X,G)),
	 p_aux(A,F)), 
	p_aux(F & G,H).
%% casi analoghi per l'or
p_aux(A v B,all(X,H) ) :-
	% se A, in forma prenessa, e' un perogni:
	(p_aux(A,all(X,F)),
	 p_aux(B,G);
	% oppure lo e' B
	 p_aux(B,all(X,G)),
	 p_aux(A,F)), 
	p_aux(F v G,H).
p_aux(A v B,some(X,H) ) :-
	% se A, in forma prenessa, e' un esiste:
	(p_aux(A,some(X,F)),
	 p_aux(B,G);
	% oppure lo e' B
	 p_aux(B,some(X,G)),
	 p_aux(A,F)), 
	p_aux(F v G,H).
p_aux(all(X,A),all(X,F)) :- !, p_aux(A,F).
p_aux(some(X,A),some(X,F)) :- !, p_aux(A,F).

% quantifier free
qfree([]):- !.
qfree([X|Rest]) :- !,
	qfree(X), qfree(Rest).
qfree(A) :-
	A =.. [Op|Args],
	not(member(Op,[all,some])),
	qfree(Args).

/* prenex(-(all(x,some(y,p(x,y))) v (all(x,p(x,c)) => some(y,q(y)))),F). */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% forma di skolem
skolem(A,F) :-
	prenex(A,P),
	skolemize(P,F,[]).
% il terzo argomento contiene le variabili universali incontrate
skolemize(all(X,A),F,Vars) :-
	!, skolemize(A,F,[X|Vars]).
skolemize(some(X,A),F,[]) :-
	!, gensym(c,Term),
	replace(A,F1,X,Term),
	skolemize(F1,F,[]).
skolemize(some(X,A),F,Vars) :-
	!, gensym(f,Fun),
	Term =.. [Fun|Vars],
	replace(A,F1,X,Term),
	skolemize(F1,F,Vars).
skolemize(A,A,_).

/*  skolem(all(x,p(x) => some(y,q(y) & r(x,y))),S). */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Forma a clausole
clause_form(F,Clauses) :-
	skolem(F,Skolem),
	cnf(Skolem,Cnf),
	split(Cnf,Clauses).
split(A & B,Clauses) :-
	!, split(A,C1), split(B,C2), append(C1,C2,Clauses).
split(A,[A]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%% GENSYM
%% come si potrebbe definire un gensym?

:- dynamic(counter/1).

counter(0).
gen(Root,Symbol) :-
	retract(counter(N)),
	N1 is N+1,
	asserta(counter(N1)),
	atomic_concat(Root,N1,Symbol).