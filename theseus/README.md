Parts of Theseus
================

<!-- Das λ macht μ -->

Components
----------

    expression          ≔ constuctor
                        | application
                        | lambda
                        | variable
                        | primitive
                        | primary

    constructor         ≔ Name ( expression* )
                        #      {arity}

    application         ≔ µ( expression expression* )
                        #    {function} {agruments}

    lambda              ≔ λ. rule+
    rule                ≔ pattern* ↦ expression
                        # {arity}

    pattern             ≔ variable
                        | primary
                        | constructor_pattern
    constructor_pattern ≔ Name ( pattern* )
                        #        {arity}

    variable            ≔ Name
    primitive           ≔ ⟪ Name ⟫
    primary             ≔ Integer
                        | “ String ”
                        | ‘ String ’


Behavior
------------

match(pattern, object, binding) ≔ { update binding | throw NoMatch }




Architecture
-----------------

                API
                  |
    Interper------+---->Object-Model
                  |
    call          |     integer
    cond/case     |     constructor
                  |     λ

Some functions
----------------------

    nil    ≔ nil()
    append ≔ λ.
             1. nil             , X ↦ X
             2. Cons(Head, Tail), X ↦ Cons(Head, μ(append, Tail, X))

    a ≔ Cons(1, Cons(2, Cons(3, nil)))
    b ≔ Cons(4, Cons(5, Cons(6, nil)))
    
    μ(append, a, b)
    ↳ μ(append, Cons(1, Cons(2, Cons(3, nil))), Cons(4, Cons(5, Cons(6, nil))))
    ↳ Cons(1, μ(append, Cons(2, Cons(3, nil)), Cons(4, Cons(5, Cons(6, nil)))))
    ↳ Cons(1, Cons(2, μ(append, Cons(3, nil), Cons(4, Cons(5, Cons(6, nil))))))
    ↳ Cons(1, Cons(2, Cons(3, μ(append, nil, Cons(4, Cons(5, Cons(6, nil)))))))
    ↳ Cons(1, Cons(2, Cons(3, Cons(4, Cons(5, Cons(6, nil))))))
    
Shapes
------

Shapes tell about the shape of a constructor
    
    σ₁(◊)                          | 0. σ̭₂(◊,◊) ↻
    σ₂(◊,◊)                        | 1. σ₂(◊̭,◊) ↝ σ₂′(σ₁(◊),◊)
    σ₂ ⎡0, ◊ ↦ σ₂′(σ₁(◊),◊    )⎤   | 2. σ₂′(σ̭₁(◊),◊) ↻
       ⎣1, ◊ ↦ σ₂″(◊    ,σ₁(◊))⎦   | 3. σ₂′(σ₁(◊),◊̭) ↝ σ₂′(σ₁(◊),◊)
    σ₂′[1, ◊ ↦ σ₂‴(σ₁(◊),σ₁(◊))]   | 4. σ₂‴(σ̭₁(◊),σ₁(◊)) ↻
    σ₂″[1, ◊ ↦         „       ]   | 5. σ₂‴(σ₁(◊),σ̭₁(◊)) ↻
                                     ⇒  σ₂‴(σ₁(◊),σ₁(◊))
