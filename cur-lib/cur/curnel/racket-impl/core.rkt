#lang racket/base

(require
 (for-syntax racket/base)
 racket/match)


;;; Syntax
(struct unv (level))

(struct app (rator rand))
(struct lam (name type body))
(struct pi (name type body))
(struct elim (type motive indices methods disc))

;;; Environments and declarations

; An env is an ordered map of variables and their type
; TODO: Should provide asym. constant type lookup, asym. constant setting, traversal in dependency order.
; TODO: Surely this is a well-known data structure.
(struct env (assq cache-dirty? type-cache))

; A decls is an ordered map of inductive types to their env of constructors
; TODO: Should provide asym. constant type lookup, asym. constant setting, traversal in dependency order.
(struct decls (assq cache-dirty? type-cache constr-cache constr-for-cache))

;; A term. syntax does not become a program until in context
(struct term (decls env syntax))

(define deconstruct-apply-ctxt
  (term-match/single tt-ctxtL [(in-hole Θ c) (list (term Θ) (term c))]))

(define destructable?
  (redex-match? tt-ctxtL (in-hole Θ c)))

(define ((constructor? Δ) c)
  (term (Δ-in-constructor-dom ,Δ ,c)))

(define-match-expander apply-ctxt
  (lambda (syn)
    (syntax-case syn ()
      [(_ Δ Θ c)
       #'(? destructable? (app deconstruct-apply-ctxt (list Θ (? (constructor? Δ) c))))])))

(define (cbv-eval Δ e)
  (let eval ([e e])
    (match e
      [`(elim ,D ,(app eval motive) ,(list (app eval is) ...) ,(list (app eval ms) ...) ,(app eval (apply-ctxt Δ Θ c)))
       (term-let ([e_mi (cdr (assq (term ,c) (map cons (term (Δ-ref-constructors ,Δ ,D)) (term ,ms))))]
                  [Θ_ih (term (Δ-inductive-elim ,Δ ,D (elim ,D ,motive ,is ,ms hole) ,Θ))]
                  [Θ_mi (term (in-hole Θ_ih ,Θ))])
                 (eval (term (in-hole Θ_mi e_mi))))]
      [`(,(app eval `(λ (,x : ,t) ,body)) ,(app eval v))
       (eval (term (substitute ,body ,x ,v)))]
      [`(,(app eval c) ,(app eval v))
       (term (,c ,v))]
      [`(Π (,x : ,(app eval t)) ,(app eval e))
       (term (Π (,x : ,t) ,e))]
      [`(λ (,x : ,t) ,(app eval e))
       (term (λ (,x : ,t) ,e))]
      [_ e])))
