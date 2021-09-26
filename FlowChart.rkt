#lang racket

(require test-engine/racket-tests)

; Debug config
(define PRINT_STATE 'PRINT_STATE)
(define PRINT_INST 'PRINT_INST)
(define PRINT_LBL 'PRINT_LBL)

(define DEBUG (list ;PRINT_INST
                    ;PRINT_LBL
                    ;PRINT_STATE
              ))

; Custom eval 
(define (evalWithEnv env code)
  (let [(ns (make-base-namespace))]
     (namespace-attach-module (current-namespace) 'racket/base ns)
     (map (lambda (p) (namespace-set-variable-value! (car p) (cdr p) #f ns)) env)
     (eval code ns)
  )
)

; Helper functions
(define (zip xs ys)
  (if (or (empty? xs) (empty? ys))
      empty
      (cons `(,(car xs) . ,(car ys)) (zip (cdr xs) (cdr ys)))
  )
)

(define (debugInclude mode)
  (member mode DEBUG)
)

; State
(define (makeSt head values)
  (match head
    [`(read . ,vars) (zip vars values)]
  )
)

(define (changeSt st var value)
    (if (assoc var st) (cons `(,var . ,value) (remove var st (lambda (x y) (equal? x (car y))))) (cons `(,var . ,value) st))
)

(define (printSt st)
  (for ([mp st])
    (println `(,(car mp) := ,(cdr mp)))
  )
)

; Interpreter

(define (intFc prog inp)
  (let* ([head (car prog)]
         [blocks (cdr prog)]
         [st (makeSt head inp)])
    (let ([result (intFcBlock (car blocks) blocks st)])
      result
    )
  )
)

(define (intFcBlock block blocks st)
  (if (debugInclude PRINT_LBL) (println `(Label: ,(car block))) '())
  (intFcInsts (cdr block) blocks st)
)

(define (intFcInsts insts blocks st)
  (match insts
    ['() (error "expected goto/return/if in the block")]
    [(cons inst insts)
      (if (debugInclude PRINT_INST) (println `(Eval inst: ,inst)) '())
      (match inst
        [`(,var := ,value)
          (let* ([newVal (evalWithEnv st value)]
                 [newSt (changeSt st var newVal)])
                 (if (debugInclude PRINT_STATE) (println `(State: ,newSt)) '())
                 (intFcInsts insts blocks newSt))
        ]
        [`(goto ,label) (intFcBlock (assoc label blocks) blocks st)]
        [`(if ,exp ,tr ,fs)
          (let ([lbl (if (evalWithEnv st exp) tr fs)])
            (intFcBlock (assoc lbl blocks) blocks st)
          )
        ]
        [`(return ,value) (evalWithEnv st value)]
        [else (println inst)]
      )
    ]
  )
)

; FlowChart example program

(define find_name
  '((read name namelist valuelist)
    (search (if (equal? name (car namelist)) found cont))
    (cont (valuelist := (cdr valuelist))
          (namelist := (cdr namelist))
          (goto search))
    (found (return (car valuelist)))
   )
)


; Turing machine interpreter
(define intTM
  '((read prog Right)
    (init (Left := '())
          (progTail := prog)
          (goto loopCond))
    (loopCond (if (equal? (length progTail) 0) exit loop))
    (loop (inst := (cdr (car progTail)))
          (instHead := (car inst))
          (progTail := (cdr progTail))
          (goto checkRight))
    (checkRight (if (equal? instHead 'right) moveRight checkLeft))
    (checkLeft (if (equal? instHead 'left) moveLeft checkGoto))
    (checkGoto (if (equal? instHead 'goto) jump checkWrite))
    (checkWrite (if (equal? instHead 'write) write checkIf))
    (checkIf (if (equal? instHead 'if) condJump exit))
    (moveRight (Left := (cons (car Right) Left))
               (Right := (cdr Right))
               (goto loopCond))
    (moveLeft (Right := (cons (car Left) Right))
              (Left := (cdr Left))
              (goto loopCond))
    (jump (nextLbl := (car (cdr inst)))
          (goto jumpTo_nextLbl))
    (write (value := (car (cdr inst)))
           (Right := (cons value (cdr Right)))
           (goto loopCond))
    (condJump (condValue := (car (cdr inst)))
              (nextLbl := (car (cdr (cdr (cdr inst)))))
              (if (equal? condValue (car Right)) jumpTo_nextLbl loopCond))
    (jumpTo_nextLbl (progTail := (member nextLbl prog (lambda (lbl inst) (equal? lbl (car inst)))))
                    (goto loopCond))
    (exit (return `(,Left . ,Right)))
   )
)

; Turing machine example program
(define tm-example '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))

; Testing
(check-expect (intFc find_name '(z (x y z) (1 2 3))) 3)
(check-expect (intFc intTM `(,tm-example (1 1 1 0 1 0))) '((1 1 1) 1 1 0))

