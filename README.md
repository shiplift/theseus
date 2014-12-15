A prototype for adaptive just-in-time data structure optimization.

Components
==========

    :::text
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
========

match(pattern, object, binding) ≔ { update binding | throw NoMatch }


Shapes
=====

Shapes tell about the shape of a constructor
    
    :::text
    σ₁(▼)                          | 0. σ̭₂(▼,▼) ↻
    σ₂(▼,▼)                        | 1. σ₂(◊̭,▼) ↝ σ₂′(σ₁(▼),▼)
    σ₂ ⎡0, ▼ ↦ σ₂′(σ₁(▼),▼    )⎤   | 2. σ₂′(σ̭₁(▼),▼) ↻
       ⎣1, ▼ ↦ σ₂″(▼    ,σ₁(▼))⎦   | 3. σ₂′(σ₁(▼),◊̭) ↝ σ₂′(σ₁(▼),▼)
    σ₂′[1, ▼ ↦ σ₂‴(σ₁(▼),σ₁(▼))]   | 4. σ₂‴(σ̭₁(▼),σ₁(▼)) ↻
    σ₂″[1, ▼ ↦         „       ]   | 5. σ₂‴(σ₁(▼),σ̭₁(▼)) ↻
                                     ⇒  σ₂‴(σ₁(▼),σ₁(▼))