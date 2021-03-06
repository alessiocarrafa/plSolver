%%% Rappresentazione delle formule
/* negazione: - F
   congiunzione: F & G
   disgiunzione: F v G
   implicazione: F => G
   doppia implicazione: F <=> G
   quantificazione universale: all(X,F) aka
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%% MAIN %%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main :-
	read_file_to_terms('./input.txt',L,[]),
	maplist(call, L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% forma normale negativa con writeln

nnf(A,B) :-
	cb_nnf(A,B),
	writeln(B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% CALLBACK forma normale negativa

cb_nnf(A => B, F v G) :- !,
	cb_nnf(-A,F), cb_nnf(B,G).
cb_nnf(-(A => B), F & G) :- !,
	cb_nnf(A,F), cb_nnf(-B,G).
cb_nnf(A <=> B, F) :- !,
	cb_nnf((A => B) & (B => A),F).
cb_nnf(-(A <=> B), F) :- !,
	cb_nnf(-((A => B) & (B => A)),F).
cb_nnf(A v B, F v G) :- !,
	cb_nnf(A,F), cb_nnf(B,G).
cb_nnf(-(A v B), F & G) :- !,
	cb_nnf(-A,F), cb_nnf(-B,G).
cb_nnf(A & B, F & G) :- !,
	cb_nnf(A,F), cb_nnf(B,G).
cb_nnf(-(A & B), F v G) :- !,
	cb_nnf(-A,F), cb_nnf(-B,G).
cb_nnf(-(-A),F) :- !, cb_nnf(A,F).
cb_nnf(all(X,A),all(X,F)) :- !, cb_nnf(A,F).
cb_nnf(-(all(X,A)),some(X,F)) :- !, cb_nnf(-A,F).
cb_nnf(some(X,A),some(X,F)) :- !, cb_nnf(A,F).
cb_nnf(-(some(X,A)),all(X,F)) :- !, cb_nnf(-A,F).
cb_nnf(A,A).

/*
?- cb_nnf(-(p => q v r),X).
X = (p& (-q& -r))
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% forma normale congiuntiva

cnf(A,B) :-
	cb_cnf(A,B),
	writeln(B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% CALLBACK forma normale congiuntiva

cb_cnf(A,F) :-
	cb_nnf(A,NNFA),
	cb_distrib(NNFA,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% applicazione delle leggi distributive

distrib(A,B) :-
	cb_distrib(A,B),
	writeln(B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% CALLBACK applicazione delle leggi distributive

cb_distrib(A & B,F & G) :-
	!, cb_distrib(A,F), cb_distrib(B,G).
cb_distrib(A v B,F) :-
	cb_distrib(A,A1 & A2), cb_distrib(B,B1), !,
	cb_distrib((A1 v B1) & (A2 v B1),F).
cb_distrib(A v B,F) :-
	cb_distrib(A,A1), cb_distrib(B,B1 & B2), !,
	cb_distrib((A1 v B1) & (A1 v B2),F).
cb_distrib(A v B,F v G) :-
	!, cb_distrib(A,F), cb_distrib(B,G).
cb_distrib(A,A).

/*
?- cb_cnf(p & (q & r => t), X).
X = (p& (-q v -r v t))

?- cb_cnf(-(p & (q & r => t)), X).
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

replace([First|[]],[NewFirst|[]],X,Y) :-
	!, replace(First,NewFirst,X,Y).

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
	write('%%%% calling rename with argument '), write( F ), writeln(' %%%%'),
	rename(F,F1),
	write('%%%% calling cb_nnf with argument '), write( F1 ), writeln(' %%%%'),
	cb_nnf(F1,F2),
	write('%%%% calling p_aux with argument '), write( F2 ), writeln(' %%%%'),
	p_aux(F2,G).

% Il primo argomento di p_aux e' in NNF.
% Le regole per portare fuori i quantificatori dalla negazione
%    sono gia' gestite da cb_nnf.
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% forma di skolem

skolem(A,B) :-
	cb_skolem(A,B),
	writeln(B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% CALLBACK forma di skolem

cb_skolem(A,F) :-
	write('%%%% calling prenex with argument '), write( A ), writeln(' %%%%'),
	prenex(A,P),
	write('%%%% calling skolemize with argument '), write( P ), write(' and '), write( F ), writeln(' %%%%'),
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

/*  cb_skolem(all(x,p(x) => some(y,q(y) & r(x,y))),S). */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Forma a clausole

clause_form(A,B) :-
	cb_clause_form(A,B),
	writeln(B).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% CALLBACK Forma a clausole

cb_clause_form(F,Clauses) :-
	cb_skolem(F,Skolem),
	cb_cnf(Skolem,Cnf),
	split(Cnf,Clauses).
split(A & B,Clauses) :-
	!, split(A,C1), split(B,C2), append(C1,C2,Clauses).
split(A,[A]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% GENSYM
%%% come si potrebbe definire un gensym?

:- dynamic(counter/1).

counter(0).
gen(Root,Symbol) :-
	retract(counter(N)),
	N1 is N+1,
	asserta(counter(N1)),
	atomic_concat(Root,N1,Symbol).

clausole_append( All, [_|[]], Dest ) :-
	append( [[All]], Dest ), ! .

clausole_append( _, Clausole, Dest ) :-
	append( [Clausole], Dest ), ! .

explode( [First|Rest], [B|Tail] ) :-
	explode( First, B ),
	explode( Rest, Tail ).

explode( A, B ) :-
	A =.. [_|Args],
	clausole_append( A, Args, B ) .