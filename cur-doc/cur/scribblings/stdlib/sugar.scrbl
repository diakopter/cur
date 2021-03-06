#lang scribble/manual

@(require
  "../defs.rkt"
  scribble/eval)

@(define curnel-eval (curnel-sandbox "(require cur/stdlib/nat cur/stdlib/bool cur/stdlib/sugar cur/stdlib/list)"))


@title{Sugar}
The @tech{curnel forms} are sort of terrible for actually writing code. Functions and applications are
limited to single artity. Functions type must be specified using the dependent @racket[forall], even
when the dependency is not used. Inductive elimination can only be done via the primitive eliminator
and not via pattern matching. However, with the full force of Racket's syntactic extension system, we
can define not only simply notation, but redefine what application means, or define a pattern matcher
that expands into the eliminator.

@defmodule[cur/stdlib/sugar]
This library defines various syntactic extensions making Cur easier to write than writing raw TT.

@defform*[((-> decl decl ... type)
           (→ decl decl ... type)
	   (forall decl decl ... type)
	   (∀ decl decl ... type)
	   (Π decl decl ... type)
	   (Pi decl decl ... type))
	  #:grammar
	  [(decl
	     type
	     (code:line (identifier : type)))]]{
A multi-artiy function type that supports dependent and non-dependent type declarations and automatic currying.
We provide lots of names for this form, because there are lots of synonyms in the literature.

@examples[#:eval curnel-eval
          (data And : (-> Type Type Type)
            (conj : (-> (A : Type) (B : Type) A B ((And A) B))))
          ((((conj Bool) Bool) true) false)]

@examples[#:eval curnel-eval
          (data And : (forall Type Type Type)
            (conj : (forall (A : Type) (B : Type) A B (And A B))))
          ((((conj Bool) Bool) true) false)]

}

@defform*[((lambda (a : t) ... body)
           (λ (a : t) ... body))]{
Defines a multi-arity procedure that supports automatic currying.

@examples[#:eval curnel-eval
          ((lambda (x : Bool) (lambda (y : Bool) y)) true)
          ((lambda (x : Bool) (y : Bool) y) true)
          ]
}

@defform[(#%app f a ...)]{
Defines multi-arity procedure application via automatic currying.

@examples[#:eval curnel-eval
          (data And : (-> Type Type Type)
	    (conj : (-> (A : Type) (B : Type) A B ((And A) B))))
          (conj Bool Bool true false)]
}

@defform[(: name type)]{
Declare that the @emph{function} which will be defined as @racket[name] has type @racket[type].
Must precede the definition of @racket[name].
@racket[type] must expand to a function type of the form @racket[(Π (x : t1) t2)]
When used, this form allows omitting the annotations on arguments in the definition @racket[name]
}

@defform*[((define name body)
           (define (name x ...) body)
	   (define (name (x : t) ...) body))]{
Like the @racket[define] provided by @racketmodname[cur], but supports
defining curried functions via @racket[lambda].
The second form, @racket[(define (name x ...) body)], can only be used when
a @racket[(: name type)] form appears earlier in the module.

@examples[#:eval curnel-eval
          (: id (forall (A : Type) (a : A) A))
	  (define (id A a) a)]
}

@defform*[((define-type name type)
           (define-type (name (a : t) ...) body))]{
Like @racket[define], but uses @racket[forall] instead of @racket[lambda].
}

@defform[(match e [maybe-in] [maybe-return] [pattern body] ...)
         #:grammar
         [(maybe-in
	    (code:line #:in type))
	  (maybe-return
	    (code:line #:return type))
	  (pattern
            constructor
            (code:line (constructor (x : t) ...)))]]{
A pattern-matcher-like syntax for inductive elimination.
Does not actually do pattern matching; instead, relies on the
constructors patterns being specified in the same order as when the
inductive type was defined.
Inside the @racket[body], @racket[recur] can be used to refer to the
inductive hypotheses for an inductive argument.
Generates a call to the inductive eliminator for @racket[e].
Currently does not work on inductive type-families as types indices
are not inferred.

If @racket[#:in] is not specified, attempts to infer the type of @racket[e].
If @racket[#:return] is not specified, attempts to infer the return type of the @racket[match].

@examples[#:eval curnel-eval
          (match z
            [z true]
            [(s (n : Nat))
             false])]

@examples[#:eval curnel-eval
          (match (s z)
	    #:in Nat
	    #:return Bool
            [z true]
            [(s (n : Nat))
	    (not (recur n))])]

@examples[#:eval curnel-eval
          ((match (nil Bool)
            [(nil (A : Type))
	     (lambda (n : Nat)
	       (none A))]
            [(cons (A : Type) (a : A) (rest : (List A)))
	     (lambda (n : Nat)
	       (match n
	         [z (some A a)]
		 [(s (n-1 : Nat))
		  ((recur rest) n-1)]))])
	   z)]

}

@defform[(recur id)]{
A form valid only in the body of a @racket[match] clause.
Generates a reference to the induction hypothesis for @racket[x]
inferred by a @racket[match] clause.
}

@defform[(let (clause ...) body)
         #:grammar
         [(clause
            (code:line (id expr))
            (code:line ((id : type) expr)))]]{
Evaluates the expressions @racket[expr] from each clause, left to right, and binds them to each
@racket[id]. If a @racket[type] is not given for the @racket[id], attempts to infer the type of the
corresponding @racket[expr], raising a syntax error if no type can be inferred.

@examples[#:eval curnel-eval
          (let ([x Type]
                [y (λ (x : (Type 1)) x)])
            (y x))
          (let ([x uninferrable-expr]
                [y (λ (x : (Type 1)) x)])
            (y x))]
}

@defform[(:: e type)]{
Check that expression @racket[e] has type @racket[type], causing a type-error if not, and producing
@racket[(void)] if so.

@examples[#:eval curnel-eval
          (:: z Nat)
          (:: true Nat)]
}

@defform[(run syn)]{
Like @racket[cur-normalize], but is a syntactic form to be used in surface syntax.
Allows a Cur term to be written by computing part of the term from
another Cur term.

@examples[#:eval curnel-eval
          (lambda (x : (run (if true Bool Nat))) x)]

}

@defform[(step syn)]{
Like @racket[run], but uses @racket[cur-step] to evaluate only one step and prints intermediate
results before returning the result of evaluation.

@examples[#:eval curnel-eval
          (step (plus z z))]

}

@defform[(step-n natural syn)]{
Like @racket[step], but expands to @racket[natural] calls to @racket[step].

@examples[#:eval curnel-eval
          (step-n 3 (plus z z))]

}

@defform[(query-type expr)]{
Print the type of @racket[expr], at compile-time. Similar to Coq's @racketfont{Check}.

@examples[#:eval curnel-eval
          (query-type Bool)]

}
