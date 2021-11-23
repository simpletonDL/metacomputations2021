#lang racket

(provide findNameFcCompiled tmExampleCompiled)

(define findNameFcCompiled
'((read inp)
  (0 (st := (makeSt '(read name namelist valuelist) inp))
     (if (evalWithEnv st '(equal? name (car namelist))) 2 1))
  (1 (st := (changeSt st 'valuelist (evalWithEnv st '(cdr valuelist))))
     (st := (changeSt st 'namelist (evalWithEnv st '(cdr namelist))))
     (if (evalWithEnv st '(equal? name (car namelist))) 2 1))
  (2 (result := (evalWithEnv st '(car valuelist))) (return result)))
)

(define tmExampleCompiled
  '((read Right)
    (0 (Left := '())
       (if (equal? '0 (car Right)) 2 1))
    (1 (Left := (cons (car Right) Left))
       (Right := (cdr Right))
       (if (equal? '0 (car Right)) 2 1))
    (2 (Right := (cons '1 (cdr Right)))
       (return `(,Left unquote Right))))
)