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

match(pattern, object) ≔ No | name_binding




Architecture
============

                API
                  |
    Interper------+---->Object-Model
                  |
    call          |     integer
    cond/case     |     constructor
                  |     λ
