main :-
    open( './input.txt', read, Str ),
    read_file( Str, Lines ),
    close( Str ),
    write( Lines ), nl.

read_file( Stream,[] ) :-
    at_end_of_stream( Stream ).

read_file( Stream,[X|L] ) :-
    \+ at_end_of_stream( Stream ),
	read_line_to_codes( Stream, Codes ),
    atom_chars( X, Codes ),
    read_file( Stream, L ).