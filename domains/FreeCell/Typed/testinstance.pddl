(define (problem freecell-2-1)
(:domain freecell)
(:objects
    DA
    D2
    D0
    CA
    C2
    C0
 - card
    N8
    N7
    N6
    N5
    N4
    N3
    N13
    N12
    N11
    N9
    N10
    N1
    N2
    N0
 - num
    D
    C
 - suit
)
(:init
    (VALUE C0 N0)
    (VALUE C2 N2)
    (VALUE CA N1)
    (VALUE D0 N0)
    (VALUE D2 N2)
    (VALUE DA N1)
    (SUCCESSOR N1 N0)
    (SUCCESSOR N10 N9)
    (SUCCESSOR N11 N10)
    (SUCCESSOR N12 N11)
    (SUCCESSOR N13 N12)
    (SUCCESSOR N2 N1)
    (SUCCESSOR N3 N2)
    (SUCCESSOR N4 N3)
    (SUCCESSOR N5 N4)
    (SUCCESSOR N6 N5)
    (SUCCESSOR N7 N6)
    (SUCCESSOR N8 N7)
    (SUCCESSOR N9 N8)
    (SUIT C0 C)
    (SUIT C2 C)
    (SUIT CA C)
    (SUIT D0 D)
    (SUIT D2 D)
    (SUIT DA D)
    (CANSTACK CA D2)
    (CANSTACK DA C2)
    (HOME C0)
    (HOME D0)
    (CELLSPACE N4)
    (COLSPACE N2)
    (ON C2 CA)
    (CLEAR C2)
    (CLEAR D2)
    (CLEAR DA)
    (BOTTOMCOL D2)
    (BOTTOMCOL DA)
    (BOTTOMCOL CA)
)
(:goal (and
    (HOME C2)
    (HOME D2)
)))
