(define (problem BLOCKS-4-0)
(:domain BLOCKS)
(:objects B A C - block)
(:INIT  (CLEAR B) (CLEAR C) (ONTABLE A) (ON C A)
 (ONTABLE B) (HANDEMPTY))
(:goal (AND  (ON B C)  (ON A B) ))
)