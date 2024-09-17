tiempo(presente).
tiempo(pasado).
tiempo(futuro).

persona(primera).
persona(segunda).
persona(tercera).

numero(singular).
numero(plural).


ser(presente,primera,singular,"am").
ser(presente,segunda,singular,"are").
ser(presente,tercera,singular,"is").
ser(presente,primera,plural,"are").
ser(presente,segunda,plural,"are").
ser(presente,tercera,plural,"are").

ser(pasado,primera,singular,"was").
ser(pasado,segunda,singular,"were").
ser(pasado,tercera,singular,"was").
ser(pasado,primera,plural,"were").
ser(pasado,segunda,plural,"were").
ser(pasado,tercera,plural,"were").

ser(futuro,primera,singular,"will be").
ser(futuro,segunda,singular,"will be").
ser(futuro,tercera,singular,"will be").
ser(futuro,primera,plural,"will be").
ser(futuro,segunda,plural,"will be").
ser(futuro,tercera,plural,"will be").

tener(presente,primera,singular,"have").
tener(presente,segunda,singular,"have").
tener(presente,tercera,singular,"has").
tener(presente,primera,plural,"have").
tener(presente,segunda,plural,"have").
tener(presente,tercera,plural,"have").

tener(pasado,primera,singular,"had").
tener(pasado,segunda,singular,"had").
tener(pasado,tercera,singular,"had").
tener(pasado,primera,plural,"had").
tener(pasado,segunda,plural,"had").
tener(pasado,tercera,plural,"had").

tener(futuro,primera,singular,"will have").
tener(futuro,segunda,singular,"will have").
tener(futuro,tercera,singular,"will have").
tener(futuro,primera,plural,"will have").
tener(futuro,segunda,plural,"will have").
tener(futuro,tercera,plural,"will have").

estudiar(presente, primera, singular, 'study').
estudiar(presente, segunda, singular, 'study').
estudiar(presente, tercera, singular, 'studies').
estudiar(presente, primera, plural, 'study').
estudiar(presente, segunda, plural, 'study').
estudiar(presente, tercera, plural, 'study').

estudiar(pasado, primera, singular, 'studied').
estudiar(pasado, segunda, singular, 'studied').
estudiar(pasado, tercera, singular, 'studied').
estudiar(pasado, primera, plural, 'studied').
estudiar(pasado, segunda, plural, 'studied').
estudiar(pasado, tercera, plural, 'studied').

estudiar(futuro, primera, singular, 'will study').
estudiar(futuro, segunda, singular, 'will study').
estudiar(futuro, tercera, singular, 'will study').
estudiar(futuro, primera, plural, 'will study').
estudiar(futuro, segunda, plural, 'will study').
estudiar(futuro, tercera, plural, 'will study').

jugar(presente, primera, singular, 'play').
jugar(presente, segunda, singular, 'play').
jugar(presente, tercera, singular, 'plays').
jugar(presente, primera, plural, 'play').
jugar(presente, segunda, plural, 'play').
jugar(presente, tercera, plural, 'play').

jugar(pasado, primera, singular, 'played').
jugar(pasado, segunda, singular, 'played').
jugar(pasado, tercera, singular, 'played').
jugar(pasado, primera, plural, 'played').
jugar(pasado, segunda, plural, 'played').
jugar(pasado, tercera, plural, 'played').

jugar(futuro, primera, singular, 'will play').
jugar(futuro, segunda, singular, 'will play').
jugar(futuro, tercera, singular, 'will play').
jugar(futuro, primera, plural, 'will play').
jugar(futuro, segunda, plural, 'will play').
jugar(futuro, tercera, plural, 'will play').

conjugar_verbo(Verbo,Tiempo,Persona,Numero,Conjugacion):-
    tiempo(Tiempo),
    persona(Persona),
    numero(Numero),
    (
    Verbo="to be" ->  
        ser(Tiempo,Persona,Numero,R),
        Conjugacion=R  
    ;
    Verbo="to study" ->
    	estudiar(Tiempo,Persona,Numero,R),
        Conjugacion=R
    ;   
    Verbo="to play" ->
    	jugar(Tiempo,Persona,Numero,R),
        Conjugacion=R
    ;   
    Verbo="to have" ->  
        tener(Tiempo,Persona,Numero,R),
        Conjugacion=R  
    ;
    Conjugacion=Verbo
    ).