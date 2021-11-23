#lang racket

(require test-engine/racket-tests)
(require "generated.rkt")
(require "generatedPrograms.rkt")
(require "generatedCodeGen.rkt")

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
     (namespace-set-variable-value! 'makeHeader makeHeader #f ns)
     (namespace-set-variable-value! 'getTrickLabels getTrickLabels #f ns)
     (namespace-set-variable-value! 'makeSt makeSt #f ns)
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
     (namespace-set-variable-value! 'makeHeader makeHeader #f ns) getTrickLabels
     (namespace-set-variable-value! 'getTrickLabels getTrickLabels #f ns)
     (namespace-set-variable-value! 'makeSt makeSt #f ns)
     (eval code ns)
  )
)

; Reduction
(define (reduceExpr expr vs)
  (if (isStatic expr vs) `(quote ,(evalWithEnv vs expr))
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

; Static checker
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

(define (makeHeader args staticVars)
  (filter (lambda (arg) (not (member arg staticVars))) args)
)

(define (all lst)
  (or (empty? lst)  
      (and (car lst)
           (all (cdr lst)))))

(define (debugInclude mode)
  (member mode DEBUG)
)

(define (concat xs)
  (if (empty? xs) '() (append (car xs) (concat (cdr xs))))
)

(define (getDynamicLabelsOfInst inst div)
   (match inst
    [`(if ,exp ,tr ,fs) (if (static? exp div) '() (list tr fs))]
    [else '()]
   )
)

(define (getTrickLabels prog div)
  (cons (caadr prog) (concat (concat
      (map (lambda (bb) (map (lambda (inst) (getDynamicLabelsOfInst inst div)) (cdr bb))) (cdr prog))
  )))
)

; State list
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

; State hash
(define (makeEmptyState) (make-immutable-hash))

(define (modifyState st key value) (hash-set st key value))


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

; FC division
(define intFc_2_division
  '(progFC head blocks bb insts inst)
)

; FC interpreter
(define intFc_2
  '((read progFC inp) ; progFC = s
    (initFC
      (head := (car progFC))  ; s
      (st := (makeSt head inp))
      (blocks := (cdr progFC)) ; s
      (bb := (car blocks)) ; s
      (goto make_bb)
    )
    (make_bb
      (insts := (cdr bb)) ; s
      (goto check_insts)
    )
    (check_insts
      (if (empty? insts) error_expect_jump int_inst)
    )
    (int_inst
      (inst := (car insts)) ; s
      (insts := (cdr insts)) ; s
      (goto check_if)
    )
    (check_if
      (if (equal? (car inst) 'if) process_if check_assign)
    )
    (check_assign
      (if (equal? (cadr inst) ':=) process_assign check_goto)
    )
    (check_goto
      (if (equal? (car inst) 'goto) process_goto check_return)
    )
    (check_return
      (if (equal? (car inst) 'return) process_return error_expect_jump)
    )
    (process_if
      (if (evalWithEnv st (cadr inst)) process_if_true process_if_false)
    )
    (process_if_true
      (bb := (assoc (caddr inst) blocks)) ;s
      (goto make_bb)
    )
    (process_if_false
      (bb := (assoc (cadddr inst) blocks)) ;s
      (goto make_bb)
    )
    (process_assign
      (st := (changeSt st (car inst) (evalWithEnv st (caddr inst))))
      (goto check_insts)
    )
    (process_goto
      (bb := (assoc (cadr inst) blocks)) ;s
      (goto make_bb)
    )
    (process_return
      (result := (evalWithEnv st (cadr inst)) ) ;d
      (goto exit)
    )
    (error_expect_jump
      (println "Expected goto/if in the end of bb")
    )
    (exit
      (return result)
    )
    (debug
      (return 0))
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
  '(
      progTM progTail inst instHead nextLbl value condValue
   )
)

; Turing machine example program
(define tm-example '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))

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
  (let* ([newProgAndLabels (renameHelper (cdr prog) '())]
         [newProg (car newProgAndLabels)]
         [labels (cdr newProgAndLabels)])
     (cons (car prog) (map (lambda (bb) (cons (car bb) (renameInsts (cdr bb) labels))) newProg))
  )
)

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
       (trickLabels_2 := (getTrickLabels progSp_2 division_2))
       (println trickLabels_2)
       (residual_2 := (list (makeHeader (car progSp_2) division_2))) ; dynamic
       (progSp_2 := (cdr progSp_2))
       (pp0_2 :=  (car (car progSp_2))) ;s
       (states_2 :=  (list (cons pp0_2 vs0_2))) ; dynamic
       (visited_2 := '()) ; dynamic
       (goto loop_2))
    (checkLoop_2
       (if (null? states_2) exit_2 loop_2)) ;d
    (loop_2
       (println (list 'visited_2 'length: (length visited_2)))
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
       (if (empty? curTrickLabels_2) exit_2 loopTrick_2)) ;s
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
       (if (evalWithHashEnv vs_2 (cadr cmd_2)) makeIfStaticTrue_2 makeIfStaticFalse_2)) ;d
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
       (reducedExprIf_2 := (reduceExprHash (cadr cmd_2) vs_2)) ;d
       (code_2 := (append code_2 (list (list 'if reducedExprIf_2 true_state_2 false_state_2)) )) ;d
       (goto check_bb_2))
    ; Assignment processing
    (makeAssign_2
       (if (member (car cmd_2) division_2) makeAssignStatic_2 makeAssignDynamic_2)) ;s
    (makeAssignStatic_2
       (valueAssignStatic_2 := (evalWithHashEnv vs_2 (caddr cmd_2))) ;d
       (vs_2 := (modifyState vs_2 (car cmd_2) valueAssignStatic_2)) ;d 
       (goto check_bb_2))
    (makeAssignDynamic_2
       (reducedExprAss_2 := (reduceExprHash (caddr cmd_2) vs_2)) ;d
       (cmdAssDynamic_2 := (list (car cmd_2) ':= reducedExprAss_2)) ;d
       (code_2 := (append code_2 (list cmdAssDynamic_2))) ;d
       (goto check_bb_2))
    ; Goto processing
    (makeGoto_2
       (bb_2 := (cdr (assoc (cadr cmd_2) progSp_2))) ;s
       (goto check_bb_2))
    ; Return processing
    (makeReturn_2
       (redExpr_2 := (reduceExprHash (cadr cmd_2) vs_2)) ;d
       (code_2 := (append code_2 (list (list 'return redExpr_2)))) ;d
       (goto check_bb_2))
    (makeOther_2
       (reduceOtherCmd_2 := (reduceExprHash cmd_2 vs_2)) ;d
       (code_2 := (append code_2 (list reduceOtherCmd_2))) ;d
       (goto check_bb_2))
    (exit_2 (return residual_2))
   )
)

(define mixDivision_1
  '(progSp
    division
    pp0
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

; Basic mix
(define mix
  '((read progSp division vs0)
    (init
       (residual := (list (makeHeader (car progSp) division)))
       (progSp := (cdr progSp))
       (trickLabels := (map car progSp))
       (pp0 :=  (car (car progSp)))
       (states :=  `((,pp0 . ,vs0)))
       (visited := '())
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
       (reducedExprIf := (reduceExprHash exprIf vs)) ;
       (code := (append code `((if ,reducedExprIf ,true_state ,false_state)))) ;d
       (goto check_bb))
    ; Assignment processing
    (makeAssign
       (varAssign := (car cmd)) ;s
       (expr := (caddr cmd)) ;s
       (if (member varAssign division) makeAssignStatic makeAssignDynamic)) ;s
    (makeAssignStatic
       (valueAssignStatic := (evalWithHashEnv vs expr)) ;d
       (vs := (modifyState vs varAssign valueAssignStatic)) ;d
       (goto check_bb))
    (makeAssignDynamic
       (reducedExprAss := (reduceExprHash expr vs)) ;d
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
       (redExpr := (reduceExprHash (cadr cmd) vs)) ;d
       (code := (append code `((return ,redExpr)))) ;d
       (goto check_bb))
    (makeOther
       (reduceOtherCmd := (reduceExprHash cmd vs))  ;
       (code := (append code `(,reduceOtherCmd)))
       (goto check_bb))
    (exit (return residual))
   )
)

; Запуск mix
(define (runMix prog division vs)
  (renameProg (intFc mix `(,prog ,division ,vs)))
)

(define (runMix_2 prog division vs)
  (renameProg (intFc mix_2 `(,prog ,division ,vs)))
)

; Компиляция программы машины тьюринга
(define (compileTM prog)
  (runMix intTM tmDivision (modifyState (makeEmptyState) 'progTM prog))
)

(define (compileTM_2 prog)
  (runMix_2 intTM tmDivision (modifyState (makeEmptyState) 'progTM prog))
)

; Создание компилятора машины тьюринга
(define (makeTM_compiler_2)
  (runMix_2 mix_2 mixDivision_2 (modifyState (modifyState (makeEmptyState) 'progSp_2 intTM) 'division_2 tmDivision))
)

; Создание компилятора FlowChart
(define (makeFC_compiler)
  (runMix mix_2 mixDivision_2 (modifyState (modifyState (makeEmptyState) 'progSp_2 intFc_2) 'division_2 intFc_2_division))
)

; Создание кодгена
(define (makeCodeGen!)
  (runMix_2 mix_2 mixDivision_2 (modifyState (modifyState (makeEmptyState) 'progSp_2 mix_2) 'division_2 mixDivision_2))
)

; Компиляция программ через сгенеренные миксом компиляторы
(define (compileTmGen prog)
  (renameProg (intFc generatedTMCompiler (list (modifyState (makeEmptyState) 'progTM prog))
  ))
)

(define (compileFcGen prog)
  (renameProg (intFc generatedFCCompiler (list (modifyState (makeEmptyState) 'progFC prog))
  ))
)

; Генерация компилятора через codeGen
(define (makeCompiler interpreter division)
  (renameProg (intFc codeGen (list (modifyState (modifyState (makeEmptyState) 'progSp_2 interpreter) 'division_2 division))))
)

; Компиляция программ через сгенерированные кодгеном компиляторы
(define (compileTmGenByCodeGen prog)
  (renameProg (intFc codeGenTmCompiler (list (modifyState (makeEmptyState) 'progTM prog))
  ))
)

; Тесты
(check-expect (intFc find_name '(z (x y z) (1 2 3))) 3)
(check-expect (intFc intTM `(,tm-example (1 1 1 0 1 0))) '((1 1 1) 1 1 0))

(check-expect (intFc findNameFcCompiled '((z (x y z) (1 2 3)))) 3)
(check-expect (intFc tmExampleCompiled '((1 1 1 0 1 0 1))) '((1 1 1) 1 1 0 1))

(check-expect (equal? (compileTmGenByCodeGen tm-example) (compileTmGen tm-example)) #t)
