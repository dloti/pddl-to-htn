(define (problem blocks-17-0)
(:domain blocks)
(:objects
    Q
    P
    O
    N
    M
    L
    K
    J
    I
    H
    G
    F
    E
    D
    C
    A
    B
 - block)
(:init
    (CLEAR Q)
    (CLEAR L)
    (CLEAR G)
    (CLEAR H)
    (CLEAR P)
    (ONTABLE M)
    (ONTABLE K)
    (ONTABLE O)
    (ONTABLE N)
    (ONTABLE P)
    (ON Q A)
    (ON A J)
    (ON J I)
    (ON I B)
    (ON B M)
    (ON L F)
    (ON F E)
    (ON E K)
    (ON G D)
    (ON D C)
    (ON C O)
    (ON H N)
    (HANDEMPTY)
)
(:goal (and
    (ON Q N)
    (ON N L)
    (ON L O)
    (ON O J)
    (ON J H)
    (ON H C)
    (ON C E)
    (ON E M)
    (ON M P)
    (ON P A)
    (ON A G)
    (ON G B)
    (ON B I)
    (ON I K)
    (ON K F)
    (ON F D)
)
)
)
