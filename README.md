Das λ macht μ

Components
==========

    λ                   ≔ rule*
    rule                ≔ pattern* expression 
                          (λ arity)
	pattern             ≔ variable
	                    | constructor_pattern
	constructor_pattern ≔ Symbol pattern*
	                              (constructor arity) 
	expression          ≔ variable
	                    | call
	                    | constructor
	                    | integer
	call                ≔ expression expression*
	                      (function) (agruments)
	constructor         ≔ Symbol expression*
	                              (constructor arity)

Behavior
========

match(pattern, object, binding) ≔ { update binding | throw NoMatch }




Architecture
============

                API
                  |
    Interper------+---->Object-Model
                  |
    call          |     integer
    cond/case     |     constructor
                  |     λ

Some functions
==============

    nil    ≔ (nil)
    append ≔ λ x, y:
	         1. nil              , X ↦ X
			 2. (cons Head, Tail), X ↦ (cons Head, μ(append, Tail, X))



    a ≔ (cons 1, (cons 2, (cons 3, nil)))
    b ≔ (cons 4, (cons 5, (cons 6, nil)))
	
	μ(append, a, b)
	↳ μ(append, (cons 1, (cons 2, (cons 3, nil))), (cons 4, (cons 5, (cons 6, nil))))
	↳ (cons 1, μ(append, (cons 2, (cons 3, nil)), (cons 4, (cons 5, (cons 6, nil)))))
	↳ (cons 1, (cons 2, μ(append, (cons 3, nil), (cons 4, (cons 5, (cons 6, nil))))))
	↳ (cons 1, (cons 2, (cons 3, μ(append, nil, (cons 4, (cons 5, (cons 6, nil)))))))
	↳ (cons 1, (cons 2, (cons 3, (cons 4, (cons 5, (cons 6, nil))))))
	
Shapes
=====

Shapes tell about the shape of a constructor
	
	σ₁(◊)                          | 0. σ̭₂(◊,◊) ↻
	σ₂(◊,◊)                        | 1. σ₂(◊̭,◊) ↝ σ₂′(σ₁(◊),◊)
	σ₂ ⎡0, ◊ ↦ σ₂′(σ₁(◊),◊    )⎤   | 2. σ₂′(σ̭₁(◊),◊) ↻
	   ⎣1, ◊ ↦ σ₂″(◊    ,σ₁(◊))⎦   | 3. σ₂′(σ₁(◊),◊̭) ↝ σ₂′(σ₁(◊),◊)
	σ₂′[1, ◊ ↦ σ₂‴(σ₁(◊),σ₁(◊))]   | 4. σ₂‴(σ̭₁(◊),σ₁(◊)) ↻
	σ₂″[1, ◊ ↦         „       ]   | 5. σ₂‴(σ₁(◊),σ̭₁(◊)) ↻
	                                 ⇒  σ₂‴(σ₁(◊),σ₁(◊))
