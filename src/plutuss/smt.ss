;;; (plutuss smt) -- SMT-LIB target for the UPLC symbolic compiler.
;;;
;;; This module mirrors the current Moist.SMT.Basic surface and the fixed
;;; prelude in Moist.SMT.UPLC.  It intentionally stays small: expressions are
;;; just first-order SMT terms plus enough literal helpers to render Plutus
;;; constants into the shared Data/Val datatypes.
(library (plutuss smt)
  (export
   ;; SExpr constructors and combinators
   s-int s-bool s-str s-atom s-app s-tag
   sNot sAnd sOr sImplies sIte sEq sNe sAll sAny sOrs s-beq
   s-render
   ;; sorts
   ssort-render sanitize
   ;; universal Val builders / projectors / discriminators
   v-int v-as-int v-bool v-as-bool v-bs v-as-bs v-str v-as-str v-unit
   v-data v-as-data v-list v-as-list v-dlist v-as-dl v-pdlist v-as-dm
   v-arr v-as-arr v-pair v-fst v-snd v-paird v-fst-d v-snd-d
   v-constr v-ctag v-cargs v-g1 v-as-g1 v-g2 v-as-g2 v-ml v-as-ml
   v-is-con v-con-name v-sis-con
   ;; Plutus Data builders / projectors
   d-constr d-map d-list d-i d-b
   d-tag d-args d-entries d-elems d-ival d-bval
   ;; list datatypes
   vl-nil vl-cons vl-hd vl-tl vl-is-nil vl-of-list vl-sis-nil vl-shd vl-stl
   dl-nil dl-cons dl-hd dl-tl dl-is-nil dl-of-list dl-sis-nil dl-shd dl-stl
   dm-nil dm-cons dm-key dm-val dm-tl dm-is-nil dm-of-list
   ;; bytestrings and operators
   seq-empty seq-empty-sort seq-unit seq-len seq-nth seq-append seq-extract seq-of-bytes
   str-append
   op-add op-sub op-mul op-div op-mod op-lt op-le op-gt op-ge op-neg
   ;; prelude and scripts
   prelude datatype-preamble opaque-ufs ufdecl-render
   make-smt-script smt-script-consts smt-script-side smt-script-asserts
   smt-script->smtlib
   ;; z3 bridge
   z3-command run-z3 z3-check z3-model)
  (import (chezscheme) (plutuss base))

  ;;; ---- S-expression AST -------------------------------------------------
  (define (s-int n)         (vector 's-int n))
  (define (s-bool b)        (vector 's-bool b))
  (define (s-str s)         (vector 's-str s))
  (define (s-atom a)        (vector 's-atom a))
  (define (s-app head args) (vector 's-app head args))
  (define (s-tag e)         (vector-ref e 0))

  (define (s-true? e)  (and (eq? (vector-ref e 0) 's-bool) (vector-ref e 1)))
  (define (s-false? e) (and (eq? (vector-ref e 0) 's-bool) (not (vector-ref e 1))))

  (define (escape-quotes s)
    (let ((out (open-output-string)))
      (do ((i 0 (fx+ i 1))) ((fx>=? i (string-length s)) (get-output-string out))
        (let ((c (string-ref s i)))
          (when (char=? c #\") (write-char #\" out))
          (write-char c out)))))

  (define (s-emit e out)
    (match e
      ((s-int n)
       (if (< n 0)
           (begin (put-string out "(- ") (put-string out (number->string (- n))) (put-string out ")"))
           (put-string out (number->string n))))
      ((s-bool b) (put-string out (if b "true" "false")))
      ((s-str s) (write-char #\" out) (put-string out (escape-quotes s)) (write-char #\" out))
      ((s-atom a) (put-string out a))
      ((s-app f args)
       (if (null? args)
           (put-string out f)
           (begin
             (write-char #\( out)
             (put-string out f)
             (for-each (lambda (a) (write-char #\space out) (s-emit a out)) args)
             (write-char #\) out))))
      (else (error 's-render "bad sexpr" e))))

  (define (s-render e)
    (let ((out (open-output-string)))
      (s-emit e out)
      (get-output-string out)))

  (define (s-beq a b)
    (and (vector? a) (vector? b)
         (eq? (vector-ref a 0) (vector-ref b 0))
         (case (vector-ref a 0)
           ((s-int s-bool s-str s-atom) (equal? (vector-ref a 1) (vector-ref b 1)))
           ((s-app) (and (string=? (vector-ref a 1) (vector-ref b 1))
                         (s-beq-list (vector-ref a 2) (vector-ref b 2))))
           (else #f))))
  (define (s-beq-list as bs)
    (cond ((null? as) (null? bs))
          ((null? bs) #f)
          (else (and (s-beq (car as) (car bs)) (s-beq-list (cdr as) (cdr bs))))))

  ;; These follow Moist.SMT.Expr: only boolean negation folds literals.
  (define (sNot e)
    (cond ((s-true? e) (s-bool #f))
          ((s-false? e) (s-bool #t))
          (else (s-app "not" (list e)))))
  (define (sAnd a b)     (s-app "and" (list a b)))
  (define (sOr a b)      (s-app "or" (list a b)))
  (define (sImplies a b) (s-app "=>" (list a b)))
  (define (sIte c t e)   (s-app "ite" (list c t e)))
  (define (sEq a b)      (s-app "=" (list a b)))
  (define (sNe a b)      (sNot (sEq a b)))

  (define (sAll es)
    (cond ((null? es) (s-bool #t))
          ((null? (cdr es)) (car es))
          (else (fold-left sAnd (car es) (cdr es)))))
  (define (sAny es)
    (cond ((null? es) (s-bool #f))
          ((null? (cdr es)) (car es))
          (else (fold-left sOr (car es) (cdr es)))))
  (define sOrs sAny)

  ;;; ---- Sorts ------------------------------------------------------------
  (define (ssort-render s)
    (cond
     ((eq? s 'bool) "Bool")
     ((eq? s 'int) "Int")
     ((eq? s 'string) "String")
     ((or (eq? s 'bytes) (eq? s 'bytestring) (eq? s 'seqInt)) "Bytes")
     ((eq? s 'data) "Data")
     ((eq? s 'dataList) "DataList")
     ((or (eq? s 'dataPairList) (eq? s 'dataMap)) "DataPairList")
     ((eq? s 'val) "Val")
     ((eq? s 'valList) "ValList")
     ((eq? s 'g1) "G1")
     ((eq? s 'g2) "G2")
     ((or (eq? s 'ml) (eq? s 'mlResult)) "MlResult")
     ((string? s) s)
     (else (error 'ssort "bad sort" s))))

  (define (sanitize s)
    (let ((out (open-output-string)))
      (do ((i 0 (fx+ i 1))) ((fx>=? i (string-length s)))
        (let ((c (string-ref s i)))
          (write-char (if (or (char-alphabetic? c) (char-numeric? c)
                              (char=? c #\_) (char=? c #\-) (char=? c #\.)
                              (char=? c #\$))
                          c #\_)
                      out)))
      (let ((r (get-output-string out)))
        (if (fx=? (string-length r) 0) "x" r))))

  ;;; ---- Val / Data constructors -----------------------------------------
  (define (is-ctor ctor e) (s-app (string-append "(_ is " ctor ")") (list e)))

  (define (v-int e)     (s-app "VInt" (list e)))
  (define (v-as-int e)  (s-app "unVInt" (list e)))
  (define (v-bs e)      (s-app "VBytes" (list e)))
  (define (v-as-bs e)   (s-app "unVBytes" (list e)))
  (define (v-str e)     (s-app "VString" (list e)))
  (define (v-as-str e)  (s-app "unVString" (list e)))
  (define (v-bool e)    (s-app "VBool" (list e)))
  (define (v-as-bool e) (s-app "unVBool" (list e)))
  (define v-unit        (s-app "VUnit" '()))
  (define (v-list e)    (s-app "VList" (list e)))
  (define (v-as-list e) (s-app "unVList" (list e)))
  (define (v-dlist e)   (s-app "VDataList" (list e)))
  (define (v-as-dl e)   (s-app "unVDataList" (list e)))
  (define (v-pdlist e)  (s-app "VPairDataList" (list e)))
  (define (v-as-dm e)   (s-app "unVPairDataList" (list e)))
  (define (v-pair a b)  (s-app "VPair" (list a b)))
  (define (v-fst e)     (s-app "vfst" (list e)))
  (define (v-snd e)     (s-app "vsnd" (list e)))
  (define (v-paird a b) (s-app "VPairData" (list a b)))
  (define (v-fst-d e)   (s-app "pdfst" (list e)))
  (define (v-snd-d e)   (s-app "pdsnd" (list e)))
  (define (v-data e)    (s-app "VData" (list e)))
  (define (v-as-data e) (s-app "unVData" (list e)))
  (define (v-arr e)     (s-app "VArray" (list e)))
  (define (v-as-arr e)  (s-app "unVArray" (list e)))
  (define (v-g1 e)      (s-app "VG1" (list e)))
  (define (v-as-g1 e)   (s-app "unVG1" (list e)))
  (define (v-g2 e)      (s-app "VG2" (list e)))
  (define (v-as-g2 e)   (s-app "unVG2" (list e)))
  (define (v-ml e)      (s-app "VMlResult" (list e)))
  (define (v-as-ml e)   (s-app "unVMlResult" (list e)))
  (define (v-constr tag fields) (s-app "VConstr" (list tag fields)))
  (define (v-ctag e)    (s-app "vConstrTag" (list e)))
  (define (v-cargs e)   (s-app "vConstrFields" (list e)))
  (define (v-is-con con e) (is-ctor con e))

  (define unary-v-cons
    '("VInt" "VBytes" "VString" "VBool" "VList" "VDataList"
      "VPairDataList" "VData" "VArray" "VG1" "VG2" "VMlResult"))
  (define binary-v-cons '("VPair" "VPairData" "VConstr"))
  (define (v-con-name e)
    (case (vector-ref e 0)
      ((s-atom) (and (string=? (vector-ref e 1) "VUnit") "VUnit"))
      ((s-app)
       (let ((head (vector-ref e 1)) (n (length (vector-ref e 2))))
         (cond ((and (fx=? n 0) (string=? head "VUnit")) "VUnit")
               ((and (fx=? n 1) (member head unary-v-cons)) head)
               ((and (fx=? n 2) (member head binary-v-cons)) head)
               (else #f))))
      (else #f)))
  (define (v-sis-con con e)
    (let ((c (v-con-name e)))
      (if c (s-bool (string=? c con)) (v-is-con con e))))

  (define (d-constr tag args) (s-app "DConstr" (list tag args)))
  (define (d-map e)           (s-app "DMap" (list e)))
  (define (d-list e)          (s-app "DList" (list e)))
  (define (d-i e)             (s-app "DI" (list e)))
  (define (d-b e)             (s-app "DB" (list e)))
  (define (d-tag e)           (s-app "dataConstrTag" (list e)))
  (define (d-args e)          (s-app "dataConstrFields" (list e)))
  (define (d-entries e)       (s-app "dataMapEntries" (list e)))
  (define (d-elems e)         (s-app "dataListItems" (list e)))
  (define (d-ival e)          (s-app "dataInt" (list e)))
  (define (d-bval e)          (s-app "dataBytes" (list e)))

  (define vl-nil        (s-app "VNil" '()))
  (define (vl-cons h t) (s-app "VCons" (list h t)))
  (define (vl-hd e)     (s-app "vhead" (list e)))
  (define (vl-tl e)     (s-app "vtail" (list e)))
  (define (vl-is-nil e) (is-ctor "VNil" e))
  (define (vl-of-list xs) (if (null? xs) vl-nil (vl-cons (car xs) (vl-of-list (cdr xs)))))
  (define (vl-sis-nil e)
    (cond ((and (eq? (vector-ref e 0) 's-app) (string=? (vector-ref e 1) "VNil")
                (null? (vector-ref e 2))) (s-bool #t))
          ((and (eq? (vector-ref e 0) 's-app) (string=? (vector-ref e 1) "VCons")
                (fx=? (length (vector-ref e 2)) 2)) (s-bool #f))
          (else (vl-is-nil e))))
  (define (vl-shd e) (vl-hd e))
  (define (vl-stl e) (vl-tl e))

  (define dl-nil        (s-app "DNil" '()))
  (define (dl-cons h t) (s-app "DCons" (list h t)))
  (define (dl-hd e)     (s-app "dhead" (list e)))
  (define (dl-tl e)     (s-app "dtail" (list e)))
  (define (dl-is-nil e) (is-ctor "DNil" e))
  (define (dl-of-list xs) (if (null? xs) dl-nil (dl-cons (car xs) (dl-of-list (cdr xs)))))
  (define (dl-sis-nil e)
    (cond ((and (eq? (vector-ref e 0) 's-app) (string=? (vector-ref e 1) "DNil")
                (null? (vector-ref e 2))) (s-bool #t))
          ((and (eq? (vector-ref e 0) 's-app) (string=? (vector-ref e 1) "DCons")
                (fx=? (length (vector-ref e 2)) 2)) (s-bool #f))
          (else (dl-is-nil e))))
  (define (dl-shd e) (dl-hd e))
  (define (dl-stl e) (dl-tl e))

  (define dm-nil          (s-app "DPNil" '()))
  (define (dm-cons k v t) (s-app "DPCons" (list k v t)))
  (define (dm-key e)      (s-app "dpKey" (list e)))
  (define (dm-val e)      (s-app "dpValue" (list e)))
  (define (dm-tl e)       (s-app "dpTail" (list e)))
  (define (dm-is-nil e)   (is-ctor "DPNil" e))
  (define (dm-of-list ps)
    (if (null? ps) dm-nil (dm-cons (caar ps) (cdar ps) (dm-of-list (cdr ps)))))

  ;;; ---- Bytes and operators ---------------------------------------------
  (define (seq-empty-sort sort) (s-atom (string-append "(as seq.empty " sort ")")))
  (define seq-empty (seq-empty-sort "Bytes"))
  (define (seq-unit e)          (s-app "seq.unit" (list e)))
  (define (seq-len e)           (s-app "seq.len" (list e)))
  (define (seq-nth s i)         (s-app "seq.nth" (list s i)))
  (define (seq-append a b)      (s-app "seq.++" (list a b)))
  (define (seq-extract s off len) (s-app "seq.extract" (list s off len)))
  (define (seq-of-bytes bv)
    (let ((n (bytevector-length bv)))
      (let loop ((i 0) (acc seq-empty))
        (if (fx>=? i n)
            acc
            (loop (fx+ i 1)
                  (seq-append acc (seq-unit (s-int (bytevector-u8-ref bv i)))))))))
  (define (str-append a b) (s-app "str.++" (list a b)))

  (define (op-add a b) (s-app "+" (list a b)))
  (define (op-sub a b) (s-app "-" (list a b)))
  (define (op-mul a b) (s-app "*" (list a b)))
  (define (op-div a b) (s-app "div" (list a b)))
  (define (op-mod a b) (s-app "mod" (list a b)))
  (define (op-lt a b)  (s-app "<" (list a b)))
  (define (op-le a b)  (s-app "<=" (list a b)))
  (define (op-gt a b)  (s-app ">" (list a b)))
  (define (op-ge a b)  (s-app ">=" (list a b)))
  (define (op-neg a)   (s-app "-" (list a)))

  ;;; ---- Fixed prelude ----------------------------------------------------
  (define datatype-preamble
    (string-append
     "(define-sort Bytes () (Seq Int))\n"
     "(declare-sort G1 0)\n"
     "(declare-sort G2 0)\n"
     "(declare-sort MlResult 0)\n"
     "(declare-datatypes ((Data 0) (DataList 0) (DataPairList 0) (Val 0) (ValList 0))\n"
     "  (((DConstr (dataConstrTag Int) (dataConstrFields DataList))\n"
     "    (DMap (dataMapEntries DataPairList))\n"
     "    (DList (dataListItems DataList))\n"
     "    (DI (dataInt Int))\n"
     "    (DB (dataBytes Bytes)))\n"
     "   ((DNil) (DCons (dhead Data) (dtail DataList)))\n"
     "   ((DPNil) (DPCons (dpKey Data) (dpValue Data) (dpTail DataPairList)))\n"
     "   ((VInt (unVInt Int))\n"
     "    (VBytes (unVBytes Bytes))\n"
     "    (VString (unVString String))\n"
     "    (VBool (unVBool Bool))\n"
     "    (VUnit)\n"
     "    (VList (unVList ValList))\n"
     "    (VDataList (unVDataList DataList))\n"
     "    (VPairDataList (unVPairDataList DataPairList))\n"
     "    (VPair (vfst Val) (vsnd Val))\n"
     "    (VPairData (pdfst Data) (pdsnd Data))\n"
     "    (VData (unVData Data))\n"
     "    (VArray (unVArray ValList))\n"
     "    (VG1 (unVG1 G1))\n"
     "    (VG2 (unVG2 G2))\n"
     "    (VMlResult (unVMlResult MlResult))\n"
     "    (VConstr (vConstrTag Int) (vConstrFields ValList)))\n"
     "   ((VNil) (VCons (vhead Val) (vtail ValList)))))\n"
     "(define-fun same_sign ((a Int) (b Int)) Bool (= (>= a 0) (>= b 0)))\n"
     "(define-fun abs_int ((a Int)) Int (ite (< a 0) (- 0 a) a))\n"
     "(define-fun-rec bytes_valid_at ((bs Bytes) (i Int)) Bool (ite (>= i (seq.len bs)) true (and (>= (seq.nth bs i) 0) (<= (seq.nth bs i) 255) (bytes_valid_at bs (+ i 1)))))\n"
     "(define-fun bytes_valid ((bs Bytes)) Bool (bytes_valid_at bs 0))\n"
     "(define-funs-rec\n"
     "  ((data_valid ((d Data)) Bool)\n"
     "   (dlist_valid ((xs DataList)) Bool)\n"
     "   (dplist_valid ((xs DataPairList)) Bool)\n"
     "   (val_valid ((v Val)) Bool)\n"
     "   (vlist_valid ((xs ValList)) Bool)\n"
     "   (const_val_valid ((v Val)) Bool)\n"
     "   (const_vlist_valid ((xs ValList)) Bool))\n"
     "  ((or (and ((_ is DConstr) d) (dlist_valid (dataConstrFields d)))\n"
     "       (and ((_ is DMap) d) (dplist_valid (dataMapEntries d)))\n"
     "       (and ((_ is DList) d) (dlist_valid (dataListItems d)))\n"
     "       ((_ is DI) d)\n"
     "       (and ((_ is DB) d) (bytes_valid (dataBytes d))))\n"
     "   (or ((_ is DNil) xs) (and ((_ is DCons) xs) (data_valid (dhead xs)) (dlist_valid (dtail xs))))\n"
     "   (or ((_ is DPNil) xs) (and ((_ is DPCons) xs) (data_valid (dpKey xs)) (data_valid (dpValue xs)) (dplist_valid (dpTail xs))))\n"
     "   (or ((_ is VInt) v)\n"
     "       (and ((_ is VBytes) v) (bytes_valid (unVBytes v)))\n"
     "       ((_ is VString) v)\n"
     "       ((_ is VBool) v)\n"
     "       ((_ is VUnit) v)\n"
     "       (and ((_ is VList) v) (const_vlist_valid (unVList v)))\n"
     "       (and ((_ is VDataList) v) (dlist_valid (unVDataList v)))\n"
     "       (and ((_ is VPairDataList) v) (dplist_valid (unVPairDataList v)))\n"
     "       (and ((_ is VPair) v) (const_val_valid (vfst v)) (const_val_valid (vsnd v)))\n"
     "       (and ((_ is VPairData) v) (data_valid (pdfst v)) (data_valid (pdsnd v)))\n"
     "       (and ((_ is VData) v) (data_valid (unVData v)))\n"
     "       (and ((_ is VArray) v) (const_vlist_valid (unVArray v)))\n"
     "       ((_ is VG1) v)\n"
     "       ((_ is VG2) v)\n"
     "       ((_ is VMlResult) v)\n"
     "       (and ((_ is VConstr) v) (>= (vConstrTag v) 0) (vlist_valid (vConstrFields v))))\n"
     "   (or ((_ is VNil) xs) (and ((_ is VCons) xs) (val_valid (vhead xs)) (vlist_valid (vtail xs))))\n"
     "   (or ((_ is VInt) v)\n"
     "       (and ((_ is VBytes) v) (bytes_valid (unVBytes v)))\n"
     "       ((_ is VString) v)\n"
     "       ((_ is VBool) v)\n"
     "       ((_ is VUnit) v)\n"
     "       (and ((_ is VList) v) (const_vlist_valid (unVList v)))\n"
     "       (and ((_ is VDataList) v) (dlist_valid (unVDataList v)))\n"
     "       (and ((_ is VPairDataList) v) (dplist_valid (unVPairDataList v)))\n"
     "       (and ((_ is VPair) v) (const_val_valid (vfst v)) (const_val_valid (vsnd v)))\n"
     "       (and ((_ is VPairData) v) (data_valid (pdfst v)) (data_valid (pdsnd v)))\n"
     "       (and ((_ is VData) v) (data_valid (unVData v)))\n"
     "       (and ((_ is VArray) v) (const_vlist_valid (unVArray v)))\n"
     "       ((_ is VG1) v)\n"
     "       ((_ is VG2) v)\n"
     "       ((_ is VMlResult) v))\n"
     "   (or ((_ is VNil) xs) (and ((_ is VCons) xs) (const_val_valid (vhead xs)) (const_vlist_valid (vtail xs))))))\n"
     "(define-fun uplc_tdiv ((a Int) (b Int)) Int (ite (same_sign a b) (div (abs_int a) (abs_int b)) (- 0 (div (abs_int a) (abs_int b)))))\n"
     "(define-fun uplc_tmod ((a Int) (b Int)) Int (- a (* b (uplc_tdiv a b))))\n"
     "(define-fun uplc_div ((a Int) (b Int)) Int (let ((q (uplc_tdiv a b)) (r (uplc_tmod a b))) (ite (or (= r 0) (same_sign a b)) q (- q 1))))\n"
     "(define-fun uplc_mod ((a Int) (b Int)) Int (- a (* b (uplc_div a b))))\n"
     "(define-fun-rec bytes_lt_at ((a Bytes) (b Bytes) (i Int) (n Int)) Bool (ite (>= i n) (< (seq.len a) (seq.len b)) (ite (< (seq.nth a i) (seq.nth b i)) true (ite (> (seq.nth a i) (seq.nth b i)) false (bytes_lt_at a b (+ i 1) n)))))\n"
     "(define-fun bytes_lt ((a Bytes) (b Bytes)) Bool (bytes_lt_at a b 0 (ite (< (seq.len a) (seq.len b)) (seq.len a) (seq.len b))))\n"
     "(define-fun bytes_le ((a Bytes) (b Bytes)) Bool (or (= a b) (bytes_lt a b)))\n"
     "(define-fun-rec vlist_length ((xs ValList)) Int (ite ((_ is VNil) xs) 0 (+ 1 (vlist_length (vtail xs)))))\n"
     "(define-fun-rec dlist_length ((xs DataList)) Int (ite ((_ is DNil) xs) 0 (+ 1 (dlist_length (dtail xs)))))\n"
     "(define-fun-rec vlist_drop ((n Int) (xs ValList)) ValList (ite (or (<= n 0) ((_ is VNil) xs)) xs (vlist_drop (- n 1) (vtail xs))))\n"
     "(define-fun-rec dlist_drop ((n Int) (xs DataList)) DataList (ite (or (<= n 0) ((_ is DNil) xs)) xs (dlist_drop (- n 1) (dtail xs))))\n"
     "(define-fun-rec vlist_index ((n Int) (xs ValList)) Val (ite (<= n 0) (vhead xs) (vlist_index (- n 1) (vtail xs))))\n"))

  (define (make-uf name args ret) (vector name args ret))
  (define opaque-ufs
    (list
     (make-uf "valid_utf8" '(bytes) 'bool)
     (make-uf "uplc_decodeUtf8" '(bytes) 'string)
     (make-uf "uplc_encodeUtf8" '(string) 'bytes)
     (make-uf "uplc_serializeData" '(data) 'bytes)
     (make-uf "uplc_sha2_256" '(bytes) 'bytes)
     (make-uf "uplc_sha3_256" '(bytes) 'bytes)
     (make-uf "uplc_blake2b_256" '(bytes) 'bytes)
     (make-uf "uplc_keccak_256" '(bytes) 'bytes)
     (make-uf "uplc_blake2b_224" '(bytes) 'bytes)
     (make-uf "uplc_ripemd_160" '(bytes) 'bytes)
     (make-uf "uplc_verifyEd25519Signature" '(bytes bytes bytes) 'bool)
     (make-uf "uplc_verifyEcdsaSecp256k1Signature" '(bytes bytes bytes) 'bool)
     (make-uf "uplc_verifySchnorrSecp256k1Signature" '(bytes bytes bytes) 'bool)
     (make-uf "uplc_integerToByteString" '(bool int int) 'bytes)
     (make-uf "uplc_integerToByteString_defined" '(bool int int) 'bool)
     (make-uf "uplc_byteStringToInteger" '(bool bytes) 'int)
     (make-uf "uplc_andByteString" '(bool bytes bytes) 'bytes)
     (make-uf "uplc_orByteString" '(bool bytes bytes) 'bytes)
     (make-uf "uplc_xorByteString" '(bool bytes bytes) 'bytes)
     (make-uf "uplc_complementByteString" '(bytes) 'bytes)
     (make-uf "uplc_readBit" '(bytes int) 'bool)
     (make-uf "uplc_writeBits" '(bytes valList bool) 'bytes)
     (make-uf "uplc_writeBits_defined" '(bytes valList bool) 'bool)
     (make-uf "uplc_replicateByte" '(int int) 'bytes)
     (make-uf "uplc_shiftByteString" '(bytes int) 'bytes)
     (make-uf "uplc_rotateByteString" '(bytes int) 'bytes)
     (make-uf "uplc_countSetBits" '(bytes) 'int)
     (make-uf "uplc_findFirstSetBit" '(bytes) 'int)
     (make-uf "uplc_expModInteger" '(int int int) 'int)
     (make-uf "uplc_expModInteger_defined" '(int int int) 'bool)
     (make-uf "uplc_g1_add" '(g1 g1) 'g1)
     (make-uf "uplc_g1_neg" '(g1) 'g1)
     (make-uf "uplc_g1_scalarMul" '(int g1) 'g1)
     (make-uf "uplc_g1_equal" '(g1 g1) 'bool)
     (make-uf "uplc_g1_hashToGroup" '(bytes bytes) 'g1)
     (make-uf "uplc_g1_compress" '(g1) 'bytes)
     (make-uf "uplc_g1_uncompress" '(bytes) 'g1)
     (make-uf "uplc_g2_add" '(g2 g2) 'g2)
     (make-uf "uplc_g2_neg" '(g2) 'g2)
     (make-uf "uplc_g2_scalarMul" '(int g2) 'g2)
     (make-uf "uplc_g2_equal" '(g2 g2) 'bool)
     (make-uf "uplc_g2_hashToGroup" '(bytes bytes) 'g2)
     (make-uf "uplc_g2_compress" '(g2) 'bytes)
     (make-uf "uplc_g2_uncompress" '(bytes) 'g2)
     (make-uf "uplc_millerLoop" '(g1 g2) 'ml)
     (make-uf "uplc_mulMlResult" '(ml ml) 'ml)
     (make-uf "uplc_finalVerify" '(ml ml) 'bool)
     (make-uf "uplc_valueData" '(val) 'data)
     (make-uf "uplc_unValueData" '(data) 'val)
     (make-uf "uplc_insertCoin" '(bytes bytes int val) 'val)
     (make-uf "uplc_lookupCoin" '(bytes bytes val) 'int)
     (make-uf "uplc_scaleValue" '(int val) 'val)
     (make-uf "uplc_unionValue" '(val val) 'val)
     (make-uf "uplc_valueContains" '(val val) 'bool)
     (make-uf "uplc_g1_multiScalarMul" '(valList valList) 'g1)
     (make-uf "uplc_g2_multiScalarMul" '(valList valList) 'g2)))

  (define (string-join xs sep)
    (cond ((null? xs) "")
          (else (fold-left (lambda (acc s) (string-append acc sep s)) (car xs) (cdr xs)))))
  (define (ufdecl-render d)
    (string-append "(declare-fun " (vector-ref d 0) " ("
                   (string-join (map ssort-render (vector-ref d 1)) " ")
                   ") " (ssort-render (vector-ref d 2)) ")"))

  (define prelude
    (string-append datatype-preamble
                   (let loop ((us opaque-ufs) (acc ""))
                     (if (null? us) acc
                         (loop (cdr us)
                               (string-append acc (ufdecl-render (car us)) "\n"))))))

  ;;; ---- Script assembly --------------------------------------------------
  (define (make-smt-script consts side asserts) (vector consts side asserts))
  (define (smt-script-consts s)  (vector-ref s 0))
  (define (smt-script-side s)    (vector-ref s 1))
  (define (smt-script-asserts s) (vector-ref s 2))

  (define (assertion-expr a)
    (if (and (pair? a) (string? (car a))) (cdr a) a))

  (define (emit-assert out e)
    (put-string out "(assert ")
    (s-emit e out)
    (put-string out ")\n"))

  (define (smt-script->smtlib s)
    (let ((out (open-output-string)))
      (put-string out prelude)
      (for-each
       (lambda (c)
         (put-string out "(declare-const ")
         (put-string out (car c))
         (write-char #\space out)
         (put-string out (ssort-render (cdr c)))
         (put-string out ")\n"))
       (smt-script-consts s))
      (for-each (lambda (e) (emit-assert out e)) (smt-script-side s))
      (for-each (lambda (e) (emit-assert out (assertion-expr e))) (smt-script-asserts s))
      (put-string out "(check-sat)\n(get-model)\n")
      (get-output-string out)))

  ;;; ---- z3 bridge --------------------------------------------------------
  (define z3-command (make-parameter "z3 -smt2 -in"))

  (define (run-z3 script)
    (let-values (((stdin stdout stderr pid)
                  (open-process-ports (z3-command) 'block (native-transcoder))))
      (put-string stdin script)
      (close-port stdin)
      (let ((out (let loop ((acc '()))
                   (let ((l (get-line stdout)))
                     (if (eof-object? l)
                         (apply string-append (reverse acc))
                         (loop (cons (string-append l "\n") acc))))))
            (err (let loop ((acc '()))
                   (let ((l (get-line stderr)))
                     (if (eof-object? l)
                         (apply string-append (reverse acc))
                         (loop (cons (string-append l "\n") acc)))))))
        (close-port stdout)
        (close-port stderr)
        (when (and (fx=? (string-length out) 0) (fx>? (string-length err) 0))
          (eval-failure (string-append "z3 error: " err)))
        out)))

  (define (first-token s)
    (let ((n (string-length s)))
      (let skip ((i 0))
        (cond ((fx>=? i n) "")
              ((char-whitespace? (string-ref s i)) (skip (fx+ i 1)))
              (else (let loop ((j i))
                      (if (or (fx>=? j n) (char-whitespace? (string-ref s j)))
                          (substring s i j)
                          (loop (fx+ j 1)))))))))

  (define (z3-check script)
    (let ((tok (first-token (run-z3 script))))
      (cond ((string=? tok "unsat") 'unsat)
            ((string=? tok "sat") 'sat)
            (else 'unknown))))

  (define (z3-model script) (run-z3 script)))
