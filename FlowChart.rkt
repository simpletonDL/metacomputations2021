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
     (namespace-set-variable-value! 'evalWithEnv evalWithEnv #f ns)
     (namespace-set-variable-value! 'changeSt changeSt #f ns)
     (namespace-set-variable-value! 'reduceExpr reduceExpr #f ns)
     (namespace-set-variable-value! 'empty? empty? #f ns)
     (namespace-set-variable-value! 'static? static? #f ns)
     (namespace-set-variable-value! 'printSt printSt #f ns)
     (namespace-set-variable-value! 'modifyState modifyState #f ns)
     (namespace-set-variable-value! 'evalWithHashEnv evalWithHashEnv #f ns)
     (namespace-set-variable-value! 'reduceExprHash reduceExprHash #f ns)
     (eval code ns)
  )
)

(define (evalWithHashEnv env code)
  (let [(ns (make-base-namespace))]
     (namespace-attach-module (current-namespace) 'racket/base ns)
     (hash-for-each env (lambda (k v) (namespace-set-variable-value! k v #f ns)))

     (namespace-set-variable-value! 'evalWithHashEnv evalWithHashEnv #f ns)
     (namespace-set-variable-value! 'changeSt changeSt #f ns)
     (namespace-set-variable-value! 'reduceExpr reduceExpr #f ns)
     (namespace-set-variable-value! 'empty? empty? #f ns)
     (namespace-set-variable-value! 'static? static? #f ns)
     (namespace-set-variable-value! 'printSt printSt #f ns)
     (eval code ns)
  )
)

; Reduction
(define (reduceExpr expr vs)
  (if (isStatic expr vs) (quote (evalWithEnv vs expr))
  (match expr
  [(cons f exprs)
     (cons f (map (lambda (e) (reduceExpr e vs)) exprs))
  ]
  [else
     (let ([value (assoc expr vs)])
       (if value `',(cdr value) expr)
     )
  ]))
)

(define (isStatic expr vs)
  (match expr
  [`(quote ,xs) #t]
  [(cons f exprs)
     (all (map (lambda (e) (isStatic e vs)) exprs))
  ]
  [else (if (assoc expr vs) #t #f)]
  )
)

; Reduction with hash env
(define (reduceExprHash expr vs)
   (if (isStaticHash expr vs) `(quote ,(evalWithHashEnv vs expr))
  (match expr
  [(cons f exprs)
     (cons f (map (lambda (e) (reduceExprHash e vs)) exprs))
  ]
  [else
     (if (hash-has-key? vs expr) `',(hash-ref vs expr) expr)
  ]))
)

(define (isStaticHash expr vs)
  (match expr
  [`(quote ,xs) #t]
  [(cons f exprs)
     (all (map (lambda (e) (isStaticHash e vs)) exprs))
  ]
  [else (if (hash-has-key? vs expr) #t #f)]
  )
)

; end
(define (static? expr division)
  (match expr
  [`',const #t]
  [`(,func . ,exprs) (all (map (lambda (e) (static? e division)) exprs))
  ]
  [else
    (match expr
      [else
         (if (symbol? expr) (member expr division)
                            (or (boolean? expr) (string? expr) (number? expr)))
      ]
    )
  ])
)

; Helper functions
(define (zip xs ys)
  (if (or (empty? xs) (empty? ys))
      empty
      (cons `(,(car xs) . ,(car ys)) (zip (cdr xs) (cdr ys)))
  )
)

(define (all lst)
  (or (empty? lst)  
      (and (car lst)
           (all (cdr lst)))))

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
  (if (debugInclude PRINT_LBL) (println (car block)) '())
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
        [else
          (evalWithEnv st inst)
          (intFcInsts insts blocks st)
        ]
      )
    ]
  )
)

; Turing machine interpreter
(define intTM
  '((read progTM Right)
    (initTM (Left := '())
          (progTail := progTM)
          (goto loopCond))
    (loopCond (if (equal? (length progTail) 0) exitTM loop))
    (loop (inst := (cdr (car progTail)))
          (instHead := (car inst))
          (progTail := (cdr progTail))
          (goto checkRight))
    (checkRight (if (equal? instHead 'right) moveRight checkLeft))
    (checkLeft (if (equal? instHead 'left) moveLeft checkGoto))
    (checkGoto (if (equal? instHead 'goto) jump checkWrite))
    (checkWrite (if (equal? instHead 'write) write checkIf))
    (checkIf (if (equal? instHead 'if) condJump exitTM))
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
    (jumpTo_nextLbl (progTail := (member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst)))))
                    (goto loopCond))
    (exitTM (return `(,Left . ,Right)))
   )
)

(define tmDivision
  '(; Vars
      progTM progTail inst instHead nextLbl value condValue
   )
)

; Turing machine example program
(define tm-example '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))

; Testing
(check-expect (intFc find_name '(z (x y z) (1 2 3))) 3)
(check-expect (intFc intTM `(,tm-example (1 1 1 0 1 0))) '((1 1 1) 1 1 0))

; FlowChart example programs
(define find_name
  '((read name namelist valuelist)
    (search (if (equal? name (car namelist)) found cont))
    (cont (valuelist := (cdr valuelist))
          (namelist := (cdr namelist))
          (goto search))
    (found (return (car valuelist)))
   )
)

(define ex
  '((read x y)
    (step1
      (h := (+ x 2))
      (y := (+ h y))
      (return y))
   )
)

; Renaming
(define (renameInst inst labels)
  (match inst
    [`(goto ,label) `(goto ,(cdr (assoc label labels)))]
    [`(if ,exp ,tr ,fs)
     `(if ,exp ,(cdr (assoc tr labels)) ,(cdr (assoc fs labels)))
    ]
    [else inst]
  )
)

(define (renameInsts insts labels)
  (map (lambda (inst) (renameInst inst labels)) insts)
)

(define (renameHelper prog labels)
  (if (empty? prog)
      `(() . ,labels)
      (let* ([lbl (caar prog)]
             [insts (cdar prog)]
             [newLbl (assoc lbl labels)])
        (if newLbl
            (let* ([newLbl (cdr newLbl)]
                   [newBB (cons newLbl insts)]
                   [newProgAndLabels (renameHelper (cdr prog) labels)])
              `(,(cons newBB (car newProgAndLabels)) . ,(cdr newProgAndLabels))
            )
            (let* ([newLbl (length labels)]
                   [newLabels (cons `(,lbl . ,newLbl) labels)]
                   [newBB (cons newLbl insts)]
                   [newProgAndLabels (renameHelper (cdr prog) newLabels)])
              `(,(cons newBB (car newProgAndLabels)) . ,(cdr newProgAndLabels))
            )
        )
      )
  )
)

(define (renameProg prog)
  (let* ([newProgAndLabels (renameHelper prog '())]
         [newProg (car newProgAndLabels)]
         [labels (cdr newProgAndLabels)])
     (map (lambda (bb) (cons (car bb) (renameInsts (cdr bb) labels))) newProg)
  )
)

; Mix
; vs0:
;     progSp <- intTM
;     division <- ???

(define mixDivision
  '(trickLabels
    progSp
    division
    pp0
    curTrickLabels
    curLabel
    pp_static
    bb
    cmd
   
    exprIf
    true_pp
    false_pp
    
    varAssign
    expr
    next_pp)
)

(define mixDivision_2
  '(trickLabels_2
    progSp_2
    division_2
    pp0_2
    curTrickLabels_2
    curLabel_2
    pp_static_2
    bb_2
    cmd_2
   
    exprIf_2
    true_pp_2
    false_pp_2
    
    varAssign_2
    expr_2
    next_pp_2)
)

(define mix_2
  '((read progSp_2 division_2 vs0_2) ; progSp_2 -> intTM, division_2 -> tmDivision
    (init_2
       (progSp_2 := (cdr progSp_2)) ;s
       (trickLabels_2 := '(initTM jumpTo_nextLbl loopCond)); (map car progSp_2)) ;s
       (pp0_2 :=  (car (car progSp_2))) ;s
       (states_2 :=  (list (cons pp0_2 vs0_2))) ; dynamic
       (visited_2 := '()) ; dynamic
       (residual_2 := '()) ; dynamic
       (goto loop_2))
    (checkLoop_2
       (if (null? states_2) exit_2 loop_2)) ;d
    (loop_2
       (state_2 := (car states_2)) ; dynamic
       (states_2 := (cdr states_2)) ; dynamic
       (visited_2 := (cons state_2 visited_2)) ; dynamic

       (vs_2 := (cdr state_2)) ; dynamic
       (code_2 := (list state_2)) ; dynamic
       (goto the_trick_2))

    ; The Trick
    (the_trick_2
       (pp_2 := (car state_2)) ;d
       (curTrickLabels_2 := trickLabels_2) ;s
       (goto checkLoopTrick_2))
    (checkLoopTrick_2
       (if (empty? curTrickLabels_2) exit_2 loopTrick_2))
    (loopTrick_2
       (if (equal? pp_2 (car curTrickLabels_2)) assign_pp_static_2 nextLoopTrick_2)) ;d
    (nextLoopTrick_2
       (curTrickLabels_2 := (cdr curTrickLabels_2))
       (goto checkLoopTrick_2))
    (assign_pp_static_2
       (pp_static_2 := (car curTrickLabels_2)) ;s
       (goto make_bb_2))

    (make_bb_2
       (bb_2 := (cdr (assoc pp_static_2 progSp_2))) ;s
       (goto check_bb_2))
    (check_bb_2
       (if (null? bb_2) end_bb_2 process_bb_2)) ;s
    (end_bb_2
       (residual_2 := (append residual_2 (list code_2))) ;d
       (goto checkLoop_2))
    (process_bb_2
       (cmd_2 := (car bb_2)) ;s
       (bb_2 := (cdr bb_2)) ;s
       (goto checkIf_2))
    (checkIf_2
       (if (equal? (car cmd_2) 'if) makeIf_2 checkAssign_2)) ;s
    (checkAssign_2
       (if (equal? (cadr cmd_2) ':=) makeAssign_2 checkGoto_2)) ;s
    (checkGoto_2
       (if (equal? (car cmd_2) 'goto) makeGoto_2 checkReturn_2)) ;s
    (checkReturn_2
       (if (equal? (car cmd_2) 'return) makeReturn_2 makeOther_2)) ;s
    ; If processing
    (makeIf_2
       (if (static? (cadr cmd_2) division_2) makeIfStatic_2 makeIfDynamic_2)) ;s
    (makeIfStatic_2
       (if (evalWithEnv vs_2 (cadr cmd_2)) makeIfStaticTrue_2 makeIfStaticFalse_2)) ;d
    (makeIfStaticTrue_2
       (bb_2 := (cdr (assoc (caddr cmd_2) progSp_2))) ;s
       (goto check_bb_2))
    (makeIfStaticFalse_2
       (bb_2 := (cdr (assoc (cadddr cmd_2) progSp_2))) ;s
       (goto check_bb_2))
    (makeIfDynamic_2
       (true_state_2 := (cons (caddr cmd_2) vs_2)) ;d
       (false_state_2 := (cons (cadddr cmd_2) vs_2)) ;d
       (states_2 := (if (or (member true_state_2 visited_2) (member true_state_2 states_2)) states_2 (cons true_state_2 states_2))) ;d
       (states_2 := (if (or (member false_state_2 visited_2) (member false_state_2 states_2)) states_2 (cons false_state_2 states_2))) ;d
       (reducedExprIf_2 := (reduceExpr (cadr cmd_2) vs_2)) ;d
       (code_2 := (append code_2 (list (list 'if reducedExprIf_2 true_state_2 false_state_2)) )) ;d
       (goto check_bb_2))
    ; Assignment processing
    (makeAssign_2
       (if (member (car cmd_2) division_2) makeAssignStatic_2 makeAssignDynamic_2)) ;s
    (makeAssignStatic_2
       (valueAssignStatic_2 := (evalWithEnv vs_2 (caddr cmd_2))) ;d
       (vs_2 := (changeSt vs_2 (car cmd_2) valueAssignStatic_2)) ;d
       (goto check_bb_2))
    (makeAssignDynamic_2
       (reducedExprAss_2 := (reduceExpr (caddr cmd_2) vs_2)) ;d
       (cmdAssDynamic_2 := (list (car cmd_2) ':= reducedExprAss_2)) ;d
       (code_2 := (append code_2 (list cmdAssDynamic_2))) ;d
       (goto check_bb_2))
    ; Goto processing
    (makeGoto_2
       (bb_2 := (cdr (assoc (cadr cmd_2) progSp_2))) ;s
       (goto check_bb_2))
    ; Return processing
    (makeReturn_2
       (redExpr_2 := (reduceExpr (cadr cmd_2) vs_2)) ;d
       (code_2 := (append code_2 (list (list 'return redExpr_2)))) ;d
       (goto check_bb_2))
    (makeOther_2
       (reduceOtherCmd_2 := (reduceExpr cmd_2 vs_2)) ;d
       (code_2 := (append code_2 (list reduceOtherCmd_2))) ;d
       (goto check_bb_2))
    (exit_2 (return residual_2))
   )
)


; Basic mix
(define mix
  '((read progSp division vs0)
    (init
       (progSp := (cdr progSp))
       (trickLabels := (map car progSp))
       (pp0 :=  (car (car progSp)))
       (states :=  `((,pp0 . ,vs0)))
       (visited := '())
       (residual := '())
       (goto loop))
    (checkLoop
       (if (null? states) exit loop))
    (loop
       (println `(visited length: ,(length visited)))
       (state := (car states))

       (states := (cdr states))
       (visited := (cons state visited))

       (vs := (cdr state))
       (dbg := (if (hash-has-key? vs 'pp_static_2) (println (hash-ref vs 'pp_static_2)) (println "no pp_static")))

       (code := `(,state))
       (pp := (car state))
       (goto make_bb))

    (make_bb
       (bb := (cdr (assoc pp progSp)))
       (goto check_bb))
    (check_bb
       (if (null? bb) end_bb process_bb))
    (end_bb
       (residual := (append residual `(,code)))
       (goto checkLoop)
       )
    (process_bb
       (cmd := (car bb))
       (bb := (cdr bb))
       (goto checkIf))
    (checkIf
       (if (equal? (car cmd) 'if) makeIf checkAssign))
    (checkAssign
       (if (equal? (cadr cmd) ':=) makeAssign checkGoto))
    (checkGoto
       (if (equal? (car cmd) 'goto) makeGoto checkReturn))
    (checkReturn
       (if (equal? (car cmd) 'return) makeReturn makeOther))
    ; If processing
    (makeIf
       (exprIf := (cadr cmd))
       (true_pp := (caddr cmd))
       (false_pp := (cadddr cmd))
       (if (static? exprIf division) makeIfStatic makeIfDynamic))
    (makeIfStatic
       (valueIfStatic := (evalWithHashEnv vs exprIf))
       (if valueIfStatic makeIfStaticTrue makeIfStaticFalse))
    (makeIfStaticTrue
       (bb := (cdr (assoc true_pp progSp)))
       (goto check_bb))
    (makeIfStaticFalse
       (bb := (cdr (assoc false_pp progSp)))
       (goto check_bb))
    (makeIfDynamic
       (true_state := `(,true_pp . ,vs))
       (false_state := `(,false_pp . ,vs))
       (states := (if (or (member false_state visited) (member false_state states)) states (cons false_state states))) ;d
       (states := (if (or (member true_state visited) (member true_state states)) states (cons true_state states))) ;d
       (reducedExprIf := (reduceExprHash exprIf vs)) ; TODO reduce with hash env
       (code := (append code `((if ,reducedExprIf ,true_state ,false_state)))) ;d
       (goto check_bb))
    ; Assignment processing
    (makeAssign
       (varAssign := (car cmd)) ;s
       (expr := (caddr cmd)) ;s
       (if (member varAssign division) makeAssignStatic makeAssignDynamic)) ;s
    (makeAssignStatic
       ;(println `(staticAssign ,cmd))
       (valueAssignStatic := (evalWithHashEnv vs expr)) ;d
       (vs := (modifyState vs varAssign valueAssignStatic)) ;d
       (goto check_bb))
    (makeAssignDynamic
       ;(println `(dynamicAssign ,cmd))
       ;(println expr)

       (reducedExprAss := (reduceExprHash expr vs)) ;d TODO reduce with hash env
       (cmdAssDynamic := `(,varAssign := ,reducedExprAss)) ;d
       (code := (append code `(,cmdAssDynamic))) ;d
       (goto check_bb))
    ; Goto processing
    (makeGoto
       (next_pp := (cadr cmd)) ;s
       (bb := (cdr (assoc next_pp progSp))) ;s
       (goto check_bb))
    ; Return processing
    (makeReturn
       ; TODO: reduce expr
       (redExpr := (reduceExprHash (cadr cmd) vs)) ;d TODO reduce with hash env
       (code := (append code `((return ,redExpr)))) ;d
       (goto check_bb))
    (makeOther
       (reduceOtherCmd := (reduceExprHash cmd vs))  ; TODO reduce with hash env
       (code := (append code `(,reduceOtherCmd)))
       (goto check_bb))
    (exit (return residual))
   )
)

(define (makeCmp)
  (runMix mix_2 mixDivision_2 (modifyState (modifyState (makeEmptyState) 'progSp_2 intTM) 'division_2 tmDivision))
)

(define (runMix prog division vs)
  (renameProg (intFc mix `(,prog ,division ,vs)))
)

(define (runMix_2 prog division vs)
  (renameProg (intFc mix_2 `(,prog ,division ,vs)))
)

(define (compileTM prog)
  (runMix intTM tmDivision (modifyState (makeEmptyState) 'progTM prog))
)



(define (compileTM_2 prog)
  (runMix_2 intTM tmDivision `((progTM . ,prog))))

(define (runMixFindName vs0)
  (renameProg (intFc mix `(,find_name (valuelist (empty? valuelist)) ,vs0)))
)

; States
(define (makeEmptyState) (make-immutable-hash))
(define (modifyState st key value) (hash-set st key value))

(define (run)
  (renameProg (intFc compiler `( ((progTM . ,tm-example)) )
  ))
)

(define tm-example-compiled
 '((read Right)
   (0 (Left := '()) (if (equal? 0 (car Right)) 2 1))
   (1 (Left := (cons (car Right) Left)) (Right := (cdr Right)) (if (equal? 0 (car Right)) 2 1))
   (2 (Right := (cons 1 (cdr Right))) (return `(,Left unquote Right))))
)

(define compiler
'((read vs0_2)
  (0
   (states_2 := (list (cons 'initTM vs0_2)))
   (visited_2 := '())
   (residual_2 := '())
   (state_2 := (car states_2))
   (states_2 := (cdr states_2))
   (visited_2 := (cons state_2 visited_2))
   (vs_2 := (cdr state_2))
   (code_2 := (list state_2))
   (pp_2 := (car state_2))
   (if (equal? pp_2 'initTM) 1 86))
  (1
   (reducedExprAss_2 := (reduceExpr ''() vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (valueAssignStatic_2 := (evalWithEnv vs_2 'progTM))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (2 (redExpr_2 := (reduceExpr '`(,Left unquote Right) vs_2))
     (code_2 := (append code_2 (list (list 'return redExpr_2))))
     (residual_2 := (append residual_2 (list code_2)))
     (if (null? states_2) 3 4))
  (3 (return residual_2))
  (4 (state_2 := (car states_2)) (states_2 := (cdr states_2)) (visited_2 := (cons state_2 visited_2)) (vs_2 := (cdr state_2)) (code_2 := (list state_2)) (pp_2 := (car state_2)) (if (equal? pp_2 'initTM) 5 6))
  (5
   (reducedExprAss_2 := (reduceExpr ''() vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (valueAssignStatic_2 := (evalWithEnv vs_2 'progTM))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (6 (if (equal? pp_2 'jumpTo_nextLbl) 7 64))
  (7 (valueAssignStatic_2 := (evalWithEnv vs_2 '(member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst)))))) (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2)) (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (8 (redExpr_2 := (reduceExpr '`(,Left unquote Right) vs_2)) (code_2 := (append code_2 (list (list 'return redExpr_2)))) (residual_2 := (append residual_2 (list code_2))) (if (null? states_2) 9 10))
  (9 (return residual_2))
  (10 (state_2 := (car states_2)) (states_2 := (cdr states_2)) (visited_2 := (cons state_2 visited_2)) (vs_2 := (cdr state_2)) (code_2 := (list state_2)) (pp_2 := (car state_2)) (if (equal? pp_2 'initTM) 11 12))
  (11
   (reducedExprAss_2 := (reduceExpr ''() vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (valueAssignStatic_2 := (evalWithEnv vs_2 'progTM))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (12 (if (equal? pp_2 'jumpTo_nextLbl) 13 14))
  (13 (valueAssignStatic_2 := (evalWithEnv vs_2 '(member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst)))))) (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2)) (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (14 (if (equal? pp_2 'loopCond) 15 44))
  (15 (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (16 (redExpr_2 := (reduceExpr '`(,Left unquote Right) vs_2)) (code_2 := (append code_2 (list (list 'return redExpr_2)))) (residual_2 := (append residual_2 (list code_2))) (if (null? states_2) 17 18))
  (17 (return residual_2))
  (18 (state_2 := (car states_2)) (states_2 := (cdr states_2)) (visited_2 := (cons state_2 visited_2)) (vs_2 := (cdr state_2)) (code_2 := (list state_2)) (pp_2 := (car state_2)) (if (equal? pp_2 'initTM) 19 20))
  (19
   (reducedExprAss_2 := (reduceExpr ''() vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (valueAssignStatic_2 := (evalWithEnv vs_2 'progTM))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (20 (if (equal? pp_2 'jumpTo_nextLbl) 21 22))
  (21 (valueAssignStatic_2 := (evalWithEnv vs_2 '(member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst)))))) (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2)) (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (22 (if (equal? pp_2 'loopCond) 23 24))
  (23 (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (24 (return residual_2))
  (25
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(cdr (car progTail))))
   (vs_2 := (changeSt vs_2 'inst valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car inst)))
   (vs_2 := (changeSt vs_2 'instHead valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(cdr progTail)))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? instHead 'right)) 26 27))
  (26
   (reducedExprAss_2 := (reduceExpr '(cons (car Right) Left) vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (reducedExprAss_2 := (reduceExpr '(cdr Right) vs_2))
   (cmdAssDynamic_2 := (list 'Right ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (27 (if (evalWithEnv vs_2 '(equal? instHead 'left)) 28 29))
  (28
   (reducedExprAss_2 := (reduceExpr '(cons (car Left) Right) vs_2))
   (cmdAssDynamic_2 := (list 'Right ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (reducedExprAss_2 := (reduceExpr '(cdr Left) vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (29 (if (evalWithEnv vs_2 '(equal? instHead 'goto)) 30 31))
  (30
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr inst))))
   (vs_2 := (changeSt vs_2 'nextLbl valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst))))))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (31 (if (evalWithEnv vs_2 '(equal? instHead 'write)) 32 33))
  (32
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr inst))))
   (vs_2 := (changeSt vs_2 'value valueAssignStatic_2))
   (reducedExprAss_2 := (reduceExpr '(cons value (cdr Right)) vs_2))
   (cmdAssDynamic_2 := (list 'Right ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (33 (if (evalWithEnv vs_2 '(equal? instHead 'if)) 34 43))
  (34
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr inst))))
   (vs_2 := (changeSt vs_2 'condValue valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr (cdr (cdr inst))))))
   (vs_2 := (changeSt vs_2 'nextLbl valueAssignStatic_2))
   (true_state_2 := (cons 'jumpTo_nextLbl vs_2))
   (false_state_2 := (cons 'loopCond vs_2))
   (states_2 := (if (or (member true_state_2 visited_2) (member true_state_2 states_2)) states_2 (cons true_state_2 states_2)))
   (states_2 := (if (or (member false_state_2 visited_2) (member false_state_2 states_2)) states_2 (cons false_state_2 states_2)))
   (reducedExprIf_2 := (reduceExpr '(equal? condValue (car Right)) vs_2))
   (code_2 := (append code_2 (list (list 'if reducedExprIf_2 true_state_2 false_state_2))))
   (residual_2 := (append residual_2 (list code_2)))
   (if (null? states_2) 35 36))
  (35 (return residual_2))
  (36 (state_2 := (car states_2)) (states_2 := (cdr states_2)) (visited_2 := (cons state_2 visited_2)) (vs_2 := (cdr state_2)) (code_2 := (list state_2)) (pp_2 := (car state_2)) (if (equal? pp_2 'initTM) 37 38))
  (37
   (reducedExprAss_2 := (reduceExpr ''() vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (valueAssignStatic_2 := (evalWithEnv vs_2 'progTM))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (38 (if (equal? pp_2 'jumpTo_nextLbl) 39 40))
  (39 (valueAssignStatic_2 := (evalWithEnv vs_2 '(member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst)))))) (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2)) (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (40 (if (equal? pp_2 'loopCond) 41 42))
  (41 (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (42 (return residual_2))
  (43 (redExpr_2 := (reduceExpr '`(,Left unquote Right) vs_2)) (code_2 := (append code_2 (list (list 'return redExpr_2)))) (residual_2 := (append residual_2 (list code_2))) (if (null? states_2) 17 18))
  (44 (return residual_2))
  (45
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(cdr (car progTail))))
   (vs_2 := (changeSt vs_2 'inst valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car inst)))
   (vs_2 := (changeSt vs_2 'instHead valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(cdr progTail)))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? instHead 'right)) 46 47))
  (46
   (reducedExprAss_2 := (reduceExpr '(cons (car Right) Left) vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (reducedExprAss_2 := (reduceExpr '(cdr Right) vs_2))
   (cmdAssDynamic_2 := (list 'Right ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (47 (if (evalWithEnv vs_2 '(equal? instHead 'left)) 48 49))
  (48
   (reducedExprAss_2 := (reduceExpr '(cons (car Left) Right) vs_2))
   (cmdAssDynamic_2 := (list 'Right ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (reducedExprAss_2 := (reduceExpr '(cdr Left) vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (49 (if (evalWithEnv vs_2 '(equal? instHead 'goto)) 50 51))
  (50
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr inst))))
   (vs_2 := (changeSt vs_2 'nextLbl valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst))))))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (51 (if (evalWithEnv vs_2 '(equal? instHead 'write)) 52 53))
  (52
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr inst))))
   (vs_2 := (changeSt vs_2 'value valueAssignStatic_2))
   (reducedExprAss_2 := (reduceExpr '(cons value (cdr Right)) vs_2))
   (cmdAssDynamic_2 := (list 'Right ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (53 (if (evalWithEnv vs_2 '(equal? instHead 'if)) 54 63))
  (54
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr inst))))
   (vs_2 := (changeSt vs_2 'condValue valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr (cdr (cdr inst))))))
   (vs_2 := (changeSt vs_2 'nextLbl valueAssignStatic_2))
   (true_state_2 := (cons 'jumpTo_nextLbl vs_2))
   (false_state_2 := (cons 'loopCond vs_2))
   (states_2 := (if (or (member true_state_2 visited_2) (member true_state_2 states_2)) states_2 (cons true_state_2 states_2)))
   (states_2 := (if (or (member false_state_2 visited_2) (member false_state_2 states_2)) states_2 (cons false_state_2 states_2)))
   (reducedExprIf_2 := (reduceExpr '(equal? condValue (car Right)) vs_2))
   (code_2 := (append code_2 (list (list 'if reducedExprIf_2 true_state_2 false_state_2))))
   (residual_2 := (append residual_2 (list code_2)))
   (if (null? states_2) 55 56))
  (55 (return residual_2))
  (56 (state_2 := (car states_2)) (states_2 := (cdr states_2)) (visited_2 := (cons state_2 visited_2)) (vs_2 := (cdr state_2)) (code_2 := (list state_2)) (pp_2 := (car state_2)) (if (equal? pp_2 'initTM) 57 58))
  (57
   (reducedExprAss_2 := (reduceExpr ''() vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (valueAssignStatic_2 := (evalWithEnv vs_2 'progTM))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (58 (if (equal? pp_2 'jumpTo_nextLbl) 59 60))
  (59 (valueAssignStatic_2 := (evalWithEnv vs_2 '(member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst)))))) (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2)) (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (60 (if (equal? pp_2 'loopCond) 61 62))
  (61 (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (62 (return residual_2))
  (63 (redExpr_2 := (reduceExpr '`(,Left unquote Right) vs_2)) (code_2 := (append code_2 (list (list 'return redExpr_2)))) (residual_2 := (append residual_2 (list code_2))) (if (null? states_2) 9 10))
  (64 (if (equal? pp_2 'loopCond) 65 66))
  (65 (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (66 (return residual_2))
  (67
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(cdr (car progTail))))
   (vs_2 := (changeSt vs_2 'inst valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car inst)))
   (vs_2 := (changeSt vs_2 'instHead valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(cdr progTail)))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? instHead 'right)) 68 69))
  (68
   (reducedExprAss_2 := (reduceExpr '(cons (car Right) Left) vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (reducedExprAss_2 := (reduceExpr '(cdr Right) vs_2))
   (cmdAssDynamic_2 := (list 'Right ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (69 (if (evalWithEnv vs_2 '(equal? instHead 'left)) 70 71))
  (70
   (reducedExprAss_2 := (reduceExpr '(cons (car Left) Right) vs_2))
   (cmdAssDynamic_2 := (list 'Right ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (reducedExprAss_2 := (reduceExpr '(cdr Left) vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (71 (if (evalWithEnv vs_2 '(equal? instHead 'goto)) 72 73))
  (72
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr inst))))
   (vs_2 := (changeSt vs_2 'nextLbl valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst))))))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (73 (if (evalWithEnv vs_2 '(equal? instHead 'write)) 74 75))
  (74
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr inst))))
   (vs_2 := (changeSt vs_2 'value valueAssignStatic_2))
   (reducedExprAss_2 := (reduceExpr '(cons value (cdr Right)) vs_2))
   (cmdAssDynamic_2 := (list 'Right ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (75 (if (evalWithEnv vs_2 '(equal? instHead 'if)) 76 85))
  (76
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr inst))))
   (vs_2 := (changeSt vs_2 'condValue valueAssignStatic_2))
   (valueAssignStatic_2 := (evalWithEnv vs_2 '(car (cdr (cdr (cdr inst))))))
   (vs_2 := (changeSt vs_2 'nextLbl valueAssignStatic_2))
   (true_state_2 := (cons 'jumpTo_nextLbl vs_2))
   (false_state_2 := (cons 'loopCond vs_2))
   (states_2 := (if (or (member true_state_2 visited_2) (member true_state_2 states_2)) states_2 (cons true_state_2 states_2)))
   (states_2 := (if (or (member false_state_2 visited_2) (member false_state_2 states_2)) states_2 (cons false_state_2 states_2)))
   (reducedExprIf_2 := (reduceExpr '(equal? condValue (car Right)) vs_2))
   (code_2 := (append code_2 (list (list 'if reducedExprIf_2 true_state_2 false_state_2))))
   (residual_2 := (append residual_2 (list code_2)))
   (if (null? states_2) 77 78))
  (77 (return residual_2))
  (78 (state_2 := (car states_2)) (states_2 := (cdr states_2)) (visited_2 := (cons state_2 visited_2)) (vs_2 := (cdr state_2)) (code_2 := (list state_2)) (pp_2 := (car state_2)) (if (equal? pp_2 'initTM) 79 80))
  (79
   (reducedExprAss_2 := (reduceExpr ''() vs_2))
   (cmdAssDynamic_2 := (list 'Left ':= reducedExprAss_2))
   (code_2 := (append code_2 (list cmdAssDynamic_2)))
   (valueAssignStatic_2 := (evalWithEnv vs_2 'progTM))
   (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2))
   (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 2 67))
  (80 (if (equal? pp_2 'jumpTo_nextLbl) 81 82))
  (81 (valueAssignStatic_2 := (evalWithEnv vs_2 '(member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst)))))) (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2)) (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (82 (if (equal? pp_2 'loopCond) 83 84))
  (83 (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (84 (return residual_2))
  (85 (redExpr_2 := (reduceExpr '`(,Left unquote Right) vs_2)) (code_2 := (append code_2 (list (list 'return redExpr_2)))) (residual_2 := (append residual_2 (list code_2))) (if (null? states_2) 3 4))
  (86 (if (equal? pp_2 'jumpTo_nextLbl) 87 88))
  (87 (valueAssignStatic_2 := (evalWithEnv vs_2 '(member nextLbl progTM (lambda (lbl inst) (equal? lbl (car inst)))))) (vs_2 := (changeSt vs_2 'progTail valueAssignStatic_2)) (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 8 45))
  (88 (if (equal? pp_2 'loopCond) 89 90))
  (89 (if (evalWithEnv vs_2 '(equal? (length progTail) 0)) 16 25))
  (90 (return residual_2)))
)
