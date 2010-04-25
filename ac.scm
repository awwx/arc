; Arc Compiler.

(module ac mzscheme

(provide (all-defined))
(require "ar.scm")
(require (lib "pretty.ss"))

; compile an Arc expression into a Scheme expression,
; both represented as s-expressions.
; env is a list of lexically bound variables, which we
; need in order to decide whether set should create a global.

(define (ac s env)
  (cond ((string? s) (ac-string s env))
        ((literal? s) s)
        ((eqv? s 'nil) (list 'quote 'nil))
        ((ssyntax? s) (ac (expand-ssyntax s) env))
        ((symbol? s) (ac-var-ref s env))
        ((ssyntax? (xcar s)) (ac (cons (expand-ssyntax (car s)) (cdr s)) env))
        ((eq? (xcar s) 'quote) (list 'quote (ac-niltree (cadr s))))
        ((eq? (xcar s) 'quasiquote) (ac-qq (cadr s) env))
        ((eq? (xcar s) 'if) (ac-if (cdr s) env))
        ((eq? (xcar s) 'fn) (ac-fn (cadr s) (cddr s) env))
        ((eq? (xcar s) 'assign) (ac-set (cdr s) env))
        ; the next three clauses could be removed without changing semantics
        ; ... except that they work for macros (so prob should do this for
        ; every elt of s, not just the car)
        ((eq? (xcar (xcar s)) 'compose) (ac (decompose (cdar s) (cdr s)) env))
        ((eq? (xcar (xcar s)) 'complement) 
         (ac (list 'no (cons (cadar s) (cdr s))) env))
        ((eq? (xcar (xcar s)) 'andf) (ac-andf s env))
        ((pair? s) (ac-call (car s) (cdr s) env))
        (#t (err "Bad object in expression" s))))

(define atstrings #f)

(define (ac-string s env)
  (if atstrings
      (if (atpos s 0)
          (ac (cons 'string (map (lambda (x)
                                   (if (string? x)
                                       (unescape-ats x)
                                       x))
                                 (codestring s)))
              env)
          (unescape-ats s))
      (string-copy s)))          ; avoid immutable strings

(define (literal? x)
  (or (boolean? x)
      (char? x)
      (string? x)
      (number? x)
      (eq? x '())))

(define (ssyntax? x)
  (and (symbol? x)
       (not (or (eqv? x '+) (eqv? x '++) (eqv? x '_)))
       (let ((name (symbol->string x)))
         (has-ssyntax-char? name (- (string-length name) 1)))))

(define (has-ssyntax-char? string i)
  (and (>= i 0)
       (or (let ((c (string-ref string i)))
             (or (eqv? c #\:) (eqv? c #\~) 
                 (eqv? c #\&)
                 ;(eqv? c #\_) 
                 (eqv? c #\.)  (eqv? c #\!)))
           (has-ssyntax-char? string (- i 1)))))

(define (read-from-string str)
  (let ((port (open-input-string str)))
    (let ((val (read port)))
      (close-input-port port)
      val)))

; Though graphically the right choice, can't use _ for currying
; because then _!foo becomes a function.  Maybe use <>.  For now
; leave this off and see how often it would have been useful.

; Might want to make ~ have less precedence than &, because
; ~foo&bar prob should mean (andf (complement foo) bar), not 
; (complement (andf foo bar)).

(define (expand-ssyntax sym)
  ((cond ((or (insym? #\: sym) (insym? #\~ sym)) expand-compose)
         ((or (insym? #\. sym) (insym? #\! sym)) expand-sexpr)
         ((insym? #\& sym) expand-and)
     ;   ((insym? #\_ sym) expand-curry)
         (#t (error "Unknown ssyntax" sym)))
   sym))

(define (expand-compose sym)
  (let ((elts (map (lambda (tok)
                     (if (eqv? (car tok) #\~)
                         (if (null? (cdr tok))
                             'no
                             `(complement ,(chars->value (cdr tok))))
                         (chars->value tok)))
                   (tokens (lambda (c) (eqv? c #\:))
                           (symbol->chars sym) 
                           '() 
                           '() 
                           #f))))
    (if (null? (cdr elts))
        (car elts)
        (cons 'compose elts))))

(define (expand-and sym)
  (let ((elts (map chars->value
                   (tokens (lambda (c) (eqv? c #\&))
                           (symbol->chars sym)
                           '()
                           '()
                           #f))))
    (if (null? (cdr elts))
        (car elts)
        (cons 'andf elts))))

; How to include quoted arguments?  Can't treat all as quoted, because 
; never want to quote fn given as first.  Do we want to allow quote chars 
; within symbols?  Could be ugly.  

; If release, fix the fact that this simply uses v0... as vars.  Should
; make these vars gensyms.

(define (expand-curry sym)
  (let ((expr (exc (map (lambda (x) 
                          (if (pair? x) (chars->value x) x))
                        (tokens (lambda (c) (eqv? c #\_)) 
                                (symbol->chars sym) 
                                '() 
                                '() 
                                #t))
                    0)))
    (list 'fn 
          (keep (lambda (s) 
                  (and (symbol? s) 
                       (eqv? (string-ref (symbol->string s) 0) 
                             #\v)))
                expr)
          expr)))

(define (keep f xs)
  (cond ((null? xs) '())
        ((f (car xs)) (cons (car xs) (keep f (cdr xs))))
        (#t (keep f (cdr xs)))))

(define (exc elts n)
  (cond ((null? elts)
         '())
        ((eqv? (car elts) #\_)
         (cons (string->symbol (string-append "v" (number->string n)))
               (exc (cdr elts) (+ n 1))))
        (#t
         (cons (car elts) (exc (cdr elts) n)))))

(define (expand-sexpr sym)
  (build-sexpr (reverse (tokens (lambda (c) (or (eqv? c #\.) (eqv? c #\!)))
                                (symbol->chars sym)
                                '()
                                '()
                                #t))
               sym))

(define (build-sexpr toks orig)
  (cond ((null? toks)
         'get)
        ((null? (cdr toks))
         (chars->value (car toks)))
        (#t
         (list (build-sexpr (cddr toks) orig)
               (if (eqv? (cadr toks) #\!)
                   (list 'quote (chars->value (car toks)))
                   (if (or (eqv? (car toks) #\.) (eqv? (car toks) #\!))
                       (err "Bad ssyntax" orig)
                       (chars->value (car toks))))))))

(define (insym? char sym) (member char (symbol->chars sym)))

(define (symbol->chars x) (string->list (symbol->string x)))

(define (chars->value chars) (read-from-string (list->string chars)))

(define (tokens test source token acc keepsep?)
  (cond ((null? source)
         (reverse (if (pair? token) 
                      (cons (reverse token) acc)
                      acc)))
        ((test (car source))
         (tokens test
                 (cdr source)
                 '()
                 (let ((rec (if (null? token)
                            acc
                            (cons (reverse token) acc))))
                   (if keepsep?
                       (cons (car source) rec)
                       rec))
                 keepsep?))
        (#t
         (tokens test
                 (cdr source)
                 (cons (car source) token)
                 acc
                 keepsep?))))

(define (ac-var-ref s env)
  (if (lex? s env)
      s
      (ac-global-name s)))

; quasiquote

(define (ac-qq args env)
  (list 'quasiquote (ac-qq1 1 args env)))

; process the argument of a quasiquote. keep track of
; depth of nesting. handle unquote only at top level (level = 1).
; complete form, e.g. x or (fn x) or (unquote (fn x))

(define (ac-qq1 level x env)
  (cond ((= level 0)
         (ac x env))
        ((and (pair? x) (eqv? (car x) 'unquote))
         (list 'unquote (ac-qq1 (- level 1) (cadr x) env)))
        ((and (pair? x) (eqv? (car x) 'unquote-splicing) (= level 1))
         (list 'unquote-splicing
               (list 'ar-nil-terminate (ac-qq1 (- level 1) (cadr x) env))))
        ((and (pair? x) (eqv? (car x) 'quasiquote))
         (list 'quasiquote (ac-qq1 (+ level 1) (cadr x) env)))
        ((pair? x)
         (imap (lambda (x) (ac-qq1 level x env)) x))
        (#t x)))

; like map, but don't demand '()-terminated list

(define (imap f l)
  (cond ((pair? l)
         (cons (f (car l)) (imap f (cdr l))))
        ((null? l)
         '())
        (#t (f l))))

; (if) -> nil
; (if x) -> x
; (if t a ...) -> a
; (if nil a b) -> b
; (if nil a b c) -> (if b c)

(define (ac-if args env)
  (cond ((null? args) ''nil)
        ((null? (cdr args)) (ac (car args) env))
        (#t `(if (not (ar-false? ,(ac (car args) env)))
                 ,(ac (cadr args) env)
                 ,(ac-if (cddr args) env)))))

(define (ac-dbname! name env)
  (if (symbol? name)
      (cons (list name) env)
      env))

(define (ac-dbname env)
  (cond ((null? env) #f)
        ((pair? (car env)) (caar env))
        (#t (ac-dbname (cdr env)))))

; translate fn directly into a lambda if it has ordinary
; parameters, otherwise use a rest parameter and parse it.

(define (ac-fn args body env)
  (if (ac-complex-args? args)
      (ac-complex-fn args body env)
      (ac-nameit
       (ac-dbname env)
       `(lambda ,(let ((a (ac-denil args))) (if (eqv? a 'nil) '() a))
          ,@(ac-body* body (append (ac-arglist args) env))))))

; does an fn arg list use optional parameters or destructuring?
; a rest parameter is not complex

(define (ac-complex-args? args)
  (cond ((eqv? args '()) #f)
        ((symbol? args) #f)
        ((and (pair? args) (symbol? (car args)))
         (ac-complex-args? (cdr args)))
        (#t #t)))

; translate a fn with optional or destructuring args
; (fn (x (o y x) (o z 21) (x1 x2) . rest) ...)
; arguments in top-level list are mandatory (unless optional),
; but it's OK for parts of a list you're destructuring to
; be missing.

(define (ac-complex-fn args body env)
  (let* ((ra (ar-gensym))
         (z (ac-complex-args args env ra #t)))
    `(lambda ,ra
       (let* ,z
         ,@(ac-body* body (append (ac-complex-getargs z) env))))))

; returns a list of two-element lists, first is variable name,
; second is (compiled) expression. to be used in a let.
; caller should extract variables and add to env.
; ra is the rest argument to the fn.
; is-params indicates that args are function arguments
;   (not destructuring), so they must be passed or be optional.

(define (ac-complex-args args env ra is-params)
  (cond ((or (eqv? args '()) (eqv? args 'nil)) '())
        ((symbol? args) (list (list args ra)))
        ((pair? args)
         (let* ((x (if (and (pair? (car args)) (eqv? (caar args) 'o))
                       (ac-complex-opt (cadar args) 
                                       (if (pair? (cddar args))
                                           (caddar args) 
                                           'nil)
                                       env 
                                       ra)
                       (ac-complex-args
                        (car args)
                        env
                        (if is-params
                            `(car ,ra)
                            `(ar-xcar ,ra))
                        #f)))
                (xa (ac-complex-getargs x)))
           (append x (ac-complex-args (cdr args)
                                      (append xa env)
                                      `(ar-xcdr ,ra)
                                      is-params))))
        (#t (err "Can't understand fn arg list" args))))

; (car ra) is the argument
; so it's not present if ra is nil or '()

(define (ac-complex-opt var expr env ra)
  (list (list var `(if (pair? ,ra) (car ,ra) ,(ac expr env)))))

; extract list of variables from list of two-element lists.

(define (ac-complex-getargs a)
  (map (lambda (x) (car x)) a))

; (a b . c) -> (a b c)
; a -> (a)

(define (ac-arglist a)
  (cond ((null? a) '())
        ((symbol? a) (list a))
        ((symbol? (cdr a)) (list (car a) (cdr a)))
        (#t (cons (car a) (ac-arglist (cdr a))))))

(define (ac-body body env)
  (map (lambda (x) (ac x env)) body))

; like ac-body, but spits out a nil expression if empty

(define (ac-body* body env)
  (if (null? body)
      (list (list 'quote 'nil))
      (ac-body body env)))

; (set v1 expr1 v2 expr2 ...)

(define (ac-set x env)
  `(begin ,@(ac-setn x env)))

(define (ac-setn x env)
  (if (null? x)
      '()
      (cons (ac-set1 (ac-macex (car x)) (cadr x) env)
            (ac-setn (cddr x) env))))

; trick to tell Scheme the name of something, so Scheme
; debugging and profiling make more sense.

(define (ac-nameit name v)
  (if (symbol? name)
      (let ((n (string->symbol (string-append " " (symbol->string name)))))
        (list 'let `((,n ,v)) n))
      v))

; = replaced by set, which is only for vars
; = now defined in arc (is it?)
; name is to cause fns to have their arc names for debugging

(define (ac-set1 a b1 env)
  (if (symbol? a)
      (let ((b (ac b1 (ac-dbname! a env))))
        (list 'let `((zz ,b))
               (cond ((eqv? a 'nil) (err "Can't rebind nil"))
                     ((eqv? a 't) (err "Can't rebind t"))
                     ((lex? a env) `(set! ,a zz))
                     (#t `(namespace-set-variable-value! ',(ac-global-name a) 
                                                         zz)))
               'zz))
      (err "First arg to set must be a symbol" a)))

; given a list of Arc expressions, return a list of Scheme expressions.
; for compiling passed arguments.

(define (ac-args names exprs env)
  (if (null? exprs)
      '()
      (cons (ac (car exprs)
                (ac-dbname! (if (pair? names) (car names) #f) env))
            (ac-args (if (pair? names) (cdr names) '())
                     (cdr exprs)
                     env))))

; generate special fast code for ordinary two-operand
; calls to the following functions. this is to avoid
; calling e.g. ar-is with its &rest and apply.

(define ac-binaries
  '((is ar-is2)
    (< ar-<2)
    (> ar->2)
    (+ ar-+2)))

; (foo bar) where foo is a global variable bound to a procedure.

(define (ac-global-call fn args env)
  (cond ((and (assoc fn ac-binaries) (= (length args) 2))
         `(,(cadr (assoc fn ac-binaries)) ,@(ac-args '() args env)))
        (#t 
         `(,(ac-global-name fn) ,@(ac-args '() args env)))))
      
; compile a function call
; special cases for speed, to avoid compiled output like
;   (ar-apply _pr (list 1 2))
; which results in 1/2 the CPU time going to GC. Instead:
;   (ar-funcall2 _pr 1 2)
; and for (foo bar), if foo is a reference to a global variable,
;   and it's bound to a function, generate (foo bar) instead of
;   (ar-funcall1 foo bar)

(define direct-calls #f)

(define (ac-call fn args env)
  (let ((macfn (ac-macro? fn)))
    (cond (macfn
           (ac-mac-call macfn args env))
          ((and (pair? fn) (eqv? (car fn) 'fn))
           `(,(ac fn env) ,@(ac-args (cadr fn) args env)))
          ((and direct-calls (symbol? fn) (not (lex? fn env)) (bound? fn)
                (procedure? (namespace-variable-value (ac-global-name fn))))
           (ac-global-call fn args env))
          ((= (length args) 0)
           `(ar-funcall0 ,(ac fn env) ,@(map (lambda (x) (ac x env)) args)))
          ((= (length args) 1)
           `(ar-funcall1 ,(ac fn env) ,@(map (lambda (x) (ac x env)) args)))
          ((= (length args) 2)
           `(ar-funcall2 ,(ac fn env) ,@(map (lambda (x) (ac x env)) args)))
          ((= (length args) 3)
           `(ar-funcall3 ,(ac fn env) ,@(map (lambda (x) (ac x env)) args)))
          ((= (length args) 4)
           `(ar-funcall4 ,(ac fn env) ,@(map (lambda (x) (ac x env)) args)))
          (#t
           `(ar-apply ,(ac fn env)
                      (list ,@(map (lambda (x) (ac x env)) args)))))))

(define (ac-mac-call m args env)
  (let ((x1 (apply m (map ac-niltree args))))
    (let ((x2 (ac (ac-denil x1) env)))
      x2)))

; returns #f or the macro function

(define (ac-macro? fn)
  (if (symbol? fn)
      (let ((v (namespace-variable-value (ac-global-name fn) 
                                         #t 
                                         (lambda () #f))))
        (if (and v
                 (ar-tagged? v)
                 (eq? (ar-type v) 'mac))
            (ar-rep v)
            #f))
      #f))

; macroexpand the outer call of a form as much as possible

(define (ac-macex e . once)
  (if (pair? e)
      (let ((m (ac-macro? (car e))))
        (if m
            (let ((expansion (ac-denil (apply m (map ac-niltree (cdr e))))))
              (if (null? once) (ac-macex expansion) expansion))
            e))
      e))

; is v lexically bound?

(define (lex? v env)
  (memq v env))

(define (xcar x)
  (and (pair? x) (car x)))

; The next two are optimizations, except work for macros.

(define (decompose fns args)
  (cond ((null? fns) `((fn vals (car vals)) ,@args))
        ((null? (cdr fns)) (cons (car fns) args))
        (#t (list (car fns) (decompose (cdr fns) args)))))

(define (ac-andf s env)
  (ac (let ((gs (map (lambda (x) (ar-gensym)) (cdr s))))
               `((fn ,gs
                   (and ,@(map (lambda (f) `(,f ,@gs))
                               (cdar s))))
                 ,@(cdr s)))
      env))

; run-time primitive procedures

; TODO
(define explicit-flush #f)

; top level read-eval-print
; tle kept as a way to get a break loop when a scheme err

(define (arc-eval expr) 
  (eval (ac expr '())))

(define (tle)
  (display "Arc> ")
  (let ((expr (read)))
    (when (not (eqv? expr ':a))
      (write (arc-eval expr))
      (newline)
      (tle))))

(define last-condition* #f)

(define (tl)
  (display "Use (quit) to quit, (tl) to return here after an interrupt.\n")
  (tl2))

(define (tl2)
  (display "arc> ")
  (on-err (lambda (c) 
            (set! last-condition* c)
            (display "Error: ")
            (write (exn-message c))
            (newline)
            (tl2))
    (lambda ()
      (let ((expr (read)))
        (if (eqv? expr ':a)
            'done
            (let ((val (arc-eval expr)))
              (write (ac-denil val))
              (namespace-set-variable-value! '_that val)
              (namespace-set-variable-value! '_thatexpr expr)
              (newline)
              (tl2)))))))

(define (aload1 p)
  (let ((x (read p)))
    (if (eof-object? x)
        #t
        (begin
          (arc-eval x)
          (aload1 p)))))

(define (atests1 p)
  (let ((x (read p)))
    (if (eof-object? x)
        #t
        (begin
          (write x)
          (newline)
          (let ((v (arc-eval x)))
            (if (ar-false? v)
                (begin
                  (display "  FAILED")
                  (newline))))
          (atests1 p)))))

(define (aload filename)
  (call-with-input-file filename aload1))

(define (test filename)
  (call-with-input-file filename atests1))

(define (acompile1 ip op)
  (let ((x (read ip)))
    (if (eof-object? x)
        #t
        (let ((scm (ac x '())))
          (eval scm)
          (pretty-print scm op)
          (newline op)
          (newline op)
          (acompile1 ip op)))))

; compile xx.arc to xx.arc.scm
; useful to examine the Arc compiler output
(define (acompile inname)
  (let ((outname (string-append inname ".scm")))
    (if (file-exists? outname)
        (delete-file outname))
    (call-with-input-file inname
      (lambda (ip)
        (call-with-output-file outname 
          (lambda (op)
            (acompile1 ip op)))))))

(xdef macex (lambda (e) (ac-macex (ac-denil e))))

(xdef macex1 (lambda (e) (ac-macex (ac-denil e) 'once)))

(xdef eval (lambda (e)
              (eval (ac (ac-denil e) '()))))

(xdef ssyntax (lambda (x) (tnil (ssyntax? x))))

(xdef ssexpand (lambda (x)
                  (if (symbol? x) (expand-ssyntax x) x)))

(xdef declare (lambda (key val)
                (let ((flag (not (ar-false? val))))
                  (case key
                    ((atstrings)      (set! atstrings      flag))
                    ((direct-calls)   (set! direct-calls   flag))
                    ((explicit-flush) (set! explicit-flush flag)))
                  val)))

(define (codestring s)
  (let ((i (atpos s 0)))
    (if i
        (cons (substring s 0 i)
              (let* ((rest (substring s (+ i 1)))
                     (in (open-input-string rest))
                     (expr (read in))
                     (i2 (let-values (((x y z) (port-next-location in))) z)))
                (close-input-port in)
                (cons expr (codestring (substring rest (- i2 1))))))
        (list s))))

; First unescaped @ in s, if any.  Escape by doubling.

(define (atpos s i)
  (cond ((eqv? i (string-length s)) 
         #f)
        ((eqv? (string-ref s i) #\@)
         (if (and (< (+ i 1) (string-length s))
                  (not (eqv? (string-ref s (+ i 1)) #\@)))
             i
             (atpos s (+ i 2))))
        (#t                         
         (atpos s (+ i 1)))))

(define (unescape-ats s)
  (list->string (letrec ((unesc (lambda (cs)
                                  (cond 
                                    ((null? cs) 
                                     '())
                                    ((and (eqv? (car cs) #\@) 
                                          (not (null? (cdr cs)))
                                          (eqv? (cadr cs) #\@))
                                     (unesc (cdr cs)))
                                    (#t
                                     (cons (car cs) (unesc (cdr cs))))))))
                  (unesc (string->list s)))))
  
)

