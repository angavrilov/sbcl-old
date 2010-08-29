;;;; SSE intrinsics support for x86-64

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!VM")

(defun ea-for-sse-stack (tn &optional (base rbp-tn))
  (make-ea :qword :base base
           :disp (- (* (+ (tn-offset tn)
                          2)
                       n-word-bytes))))

(defun float-sse-pack-tn-p (tn)
  (eq (sb!c::tn-primitive-type tn) (primitive-type-or-lose 'float-sse-pack)))
(defun double-sse-pack-tn-p (tn)
  (eq (sb!c::tn-primitive-type tn) (primitive-type-or-lose 'double-sse-pack)))
(defun int-sse-pack-tn-p (tn)
  (eq (sb!c::tn-primitive-type tn) (primitive-type-or-lose 'int-sse-pack)))

(define-move-fun (load-sse-pack-immediate 1) (vop x y)
  ((sse-pack-immediate) (sse-reg))
  (let ((x (register-inline-constant (tn-value x))))
    (cond ((float-sse-pack-tn-p y)
           (inst movaps y x))
          ((double-sse-pack-tn-p y)
           (inst movapd y x))
          (t
           (inst movdqa y x)))))

(define-move-fun (load-sse-pack 2) (vop x y)
  ((sse-stack) (sse-reg))
  (cond ((float-sse-pack-tn-p y)
         (inst movups y (ea-for-sse-stack x)))
        ((double-sse-pack-tn-p y)
         (inst movupd y (ea-for-sse-stack x)))
        (t
         (inst movdqu y (ea-for-sse-stack x)))))

(define-move-fun (store-sse-pack 2) (vop x y)
  ((sse-reg) (sse-stack))
  (cond ((float-sse-pack-tn-p x)
         (inst movups (ea-for-sse-stack y) x))
        ((double-sse-pack-tn-p x)
         (inst movupd (ea-for-sse-stack y) x))
        (t
         (inst movdqu (ea-for-sse-stack y) x))))

(define-vop (sse-pack-move)
  (:args (x :scs (sse-reg)
            :target y
            :load-if (not (location= x y))))
  (:results (y :scs (sse-reg)
               :load-if (not (location= x y))))
  (:note "SSE move")
  (:generator 0
     (move y x)))
(define-move-vop sse-pack-move :move (sse-reg) (sse-reg))

(define-vop (move-from-sse)
  (:args (value :scs (sse-reg)))
  (:results (result :scs (descriptor-reg)))
  (:node-var node)
  (:note "SSE to pointer coercion")
  (:generator 13
     (with-fixed-allocation (result
                             sse-pack-widetag
                             sse-pack-size
                             node)
       (let ((ta (make-ea-for-object-slot
                  result sse-pack-type-code-slot other-pointer-lowtag))
             (ea (make-ea-for-object-slot
                  result sse-pack-lo-value-slot other-pointer-lowtag)))
         (cond ((float-sse-pack-tn-p value)
                (inst mov ta 1)
                (inst movaps ea value))
               ((double-sse-pack-tn-p value)
                (inst mov ta 2)
                (inst movapd ea value))
               (t
                (inst mov ta 0)
                (inst movdqa ea value)))))))
(define-move-vop move-from-sse :move
  (sse-reg) (descriptor-reg))

(define-vop (move-to-sse)
  (:args (value :scs (descriptor-reg)))
  (:results (result :scs (sse-reg)))
  (:note "pointer to SSE coercion")
  (:generator 2
    (let ((ea (make-ea-for-object-slot
               value sse-pack-lo-value-slot other-pointer-lowtag)))
      (cond ((float-sse-pack-tn-p result)
             (inst movaps result ea))
            ((double-sse-pack-tn-p result)
             (inst movapd result ea))
            (t
             (inst movdqa result ea))))))
(define-move-vop move-to-sse :move (descriptor-reg) (sse-reg))

(define-vop (move-sse-arg)
  (:args (x :scs (sse-reg) :target y)
         (fp :scs (any-reg)
             :load-if (not (sc-is y sse-reg))))
  (:results (y))
  (:note "SSE argument move")
  (:generator 4
     (sc-case y
       (sse-reg
        (unless (location= x y)
          (cond ((float-sse-pack-tn-p y)
                 (inst movaps y x))
                ((double-sse-pack-tn-p y)
                 (inst movapd y x))
                (t
                 (inst movdqa y x)))))
       (sse-stack
        (cond ((float-sse-pack-tn-p x)
               (inst movups (ea-for-sse-stack y fp) x))
              ((double-sse-pack-tn-p x)
               (inst movupd (ea-for-sse-stack y fp) x))
              (t
               (inst movdqu (ea-for-sse-stack y fp) x)))))))
(define-move-vop move-sse-arg :move-arg
  (sse-reg descriptor-reg) (sse-reg))

(define-move-vop move-arg :move-arg (sse-reg) (descriptor-reg))


(define-vop (%sse-pack-low)
  (:translate %sse-pack-low)
  (:args (x :scs (sse-reg)))
  (:arg-types sse-pack)
  (:results (dst :scs (unsigned-reg)))
  (:result-types unsigned-num)
  (:policy :fast-safe)
  (:generator 3
    (inst movd dst x)))

(defun %sse-pack-low (x)
  (declare (type sse-pack x))
  (%sse-pack-low x))

(define-vop (%sse-pack-high)
  (:translate %sse-pack-high)
  (:args (x :scs (sse-reg)))
  (:arg-types sse-pack)
  (:temporary (:sc sse-reg) tmp)
  (:results (dst :scs (unsigned-reg)))
  (:result-types unsigned-num)
  (:policy :fast-safe)
  (:generator 3
    (inst movdqa tmp x)
    (inst psrldq tmp 8)
    (inst movd dst tmp)))

(defun %sse-pack-high (x)
  (declare (type sse-pack x))
  (%sse-pack-high x))

(define-vop (%sse-pack-type-code)
  (:translate %sse-pack-type-code)
  (:policy :fast-safe)
  (:args (value :scs (descriptor-reg)))
  (:arg-types sse-pack)
  (:results (result :scs (unsigned-reg)))
  (:result-types unsigned-num)
  (:generator 2
    (let ((ea (make-ea-for-object-slot
               value sse-pack-type-code-slot other-pointer-lowtag)))
      (inst mov result ea))))

(defun %sse-pack-type-code (x)
  (declare (type sse-pack x))
  (truly-the (mod 3) (%sse-pack-type-code x)))

(define-vop (%make-sse-pack)
  (:translate %make-sse-pack)
  (:policy :fast-safe)
  (:args (tc :scs (unsigned-reg))
         (lo :scs (unsigned-reg))
         (hi :scs (unsigned-reg)))
  (:arg-types unsigned-num unsigned-num unsigned-num)
  (:results (result :scs (descriptor-reg) :from :load))
  (:result-types sse-pack)
  (:node-var node)
  (:generator 13
    (with-fixed-allocation (result
                            sse-pack-widetag
                            sse-pack-size
                            node)
       (let ((ta (make-ea-for-object-slot
                  result sse-pack-type-code-slot other-pointer-lowtag))
             (la (make-ea-for-object-slot
                  result sse-pack-lo-value-slot other-pointer-lowtag))
             (ha (make-ea-for-object-slot
                  result sse-pack-hi-value-slot other-pointer-lowtag)))
         (inst mov ta tc)
         (inst mov la lo)
         (inst mov ha hi)))))

(defun %make-sse-pack (tc low high)
  (declare (type (unsigned-byte 64) low high)
           (type (integer 0 2) tc))
  (%make-sse-pack tc low high))

(define-vop (%sse-pack-float-item)
  (:args (x :scs (sse-reg)))
  (:arg-types sse-pack)
  (:info index)
  (:results (dst :scs (single-reg)))
  (:result-types single-float)
  (:temporary (:sc sse-reg) tmp)
  (:policy :fast-safe)
  (:generator 3
    (inst movdqa tmp x)
    (inst psrldq tmp (* 4 index))
    (inst xorps dst dst)
    (inst movss dst tmp)))

#-sb-xc-host
(defun %sse-pack-floats (pack)
  (declare (type sse-pack pack))
  (values (%primitive %sse-pack-float-item pack 0)
          (%primitive %sse-pack-float-item pack 1)
          (%primitive %sse-pack-float-item pack 2)
          (%primitive %sse-pack-float-item pack 3)))

(define-vop (%sse-pack-double-item)
  (:args (x :scs (sse-reg)))
  (:info index)
  (:arg-types sse-pack)
  (:results (dst :scs (double-reg)))
  (:result-types double-float)
  (:temporary (:sc sse-reg) tmp)
  (:policy :fast-safe)
  (:generator 3
    (inst movdqa tmp x)
    (inst psrldq tmp (* 8 index))
    (inst xorpd dst dst)
    (inst movsd dst tmp)))

#-sb-xc-host
(defun %sse-pack-doubles (pack)
  (declare (type sse-pack pack))
  (values (%primitive %sse-pack-double-item pack 0)
          (%primitive %sse-pack-double-item pack 1)))


(macrolet ((frob (fname atype aregtype rtype move &rest epilog)
             `(progn
                (defknown ,fname (,atype) ,rtype (foldable flushable))
                (define-vop (,fname)
                  (:translate ,fname)
                  (:args (arg :scs (,aregtype) :target dst))
                  (:arg-types ,atype)
                  (:results (dst :scs (sse-reg)))
                  (:result-types ,rtype)
                  (:policy :fast-safe)
                  (:generator 1
                    (unless (location= dst arg)
                      (inst ,move dst arg))
                    ,@epilog))
                (defun ,fname (arg)
                  (declare (type ,atype arg))
                  (,fname arg)))))
  (frob %set-ss single-float single-reg float-sse-pack movaps)
  (frob %set-sd double-float double-reg double-sse-pack movapd))

(declaim (ftype (function (real) float-sse-pack) set-ss)
         (inline set-ss)
         (ftype (function (real) double-sse-pack) set-sd)
         (inline set-sd))

(defun set-ss (arg) (%set-ss (coerce arg 'single-float)))
(defun set-sd (arg) (%set-sd (coerce arg 'double-float)))

(defknown xor-ps (sse-pack sse-pack) (sse-pack single-float))

(define-vop (xor-ps)
  (:policy :fast-safe)
  (:translate xor-ps)
  (:args (x :scs (sse-reg) :target r)
         (y :scs (sse-reg)))
  (:arg-types sse-pack sse-pack)
  (:results (r :scs (sse-reg)))
  (:result-types float-sse-pack)
  (:generator 1
     (cond ((location= x r)
            (inst xorps r y))
           ((location= y r)
            (inst xorps r x))
           (t
            (inst movaps r x)
            (inst xorps r y)))))

(defun xor-ps (a b)
  (declare (type sse-pack a b))
  (xor-ps a b))

(defknown xor-pd (sse-pack sse-pack) (sse-pack double-float))

(define-vop (xor-pd)
  (:policy :fast-safe)
  (:translate xor-pd)
  (:args (x :scs (sse-reg) :target r)
         (y :scs (sse-reg)))
  (:arg-types double-sse-pack double-sse-pack)
  (:results (r :scs (sse-reg)))
  (:result-types double-sse-pack)
  (:generator 1
     (cond ((location= x r)
            (inst xorpd r y))
           ((location= y r)
            (inst xorpd r x))
           (t
            (inst movaps r x)
            (inst xorpd r y)))))

(defun xor-pd (a b)
  (declare (type double-sse-pack a b))
  (xor-pd a b))

#|

Compiles to a bad load:

(defun foo (x) (declare (type double-float x)) (sb-vm::xor-ps (sb-vm::set-ss x) (sb-vm::set-ss 234.5)))
(defun foo (x) (declare (type double-float x)) (sb-vm::xor-ps (sb-vm::set-ss x) (the sb-kernel:float-sse-pack (sb-vm::set-ss 234.5))))
(defun foo (x) (declare (type double-float x)) (sb-vm::xor-ps (sb-vm::set-ss x) (the sb-kernel:float-sse-pack #.(sb-vm::set-ss 234.5))))
(defun foo (x) (declare (type double-float x)) (sb-vm::xor-ps (sb-vm::set-ss x) (truly-the sb-kernel:float-sse-pack #.(sb-vm::set-ss 234.5))))

; disassembly for FOO
; 02D349C9:       0F57C9           XORPS XMM1, XMM1           ; no-arg-parsing entry point
;      9CC:       F20F5AC8         CVTSD2SS XMM1, XMM0
;      9D0:       660F6F1578000000 MOVDQA XMM2, [RIP+120]
;      9D8:       0F57CA           XORPS XMM1, XMM2

|#

#|


                (deftransform ,fname ((obj) ((constant-arg real)))
                  (,fname (sb!c::lvar-value obj)))
                (deftransform ,fname ((obj) ((or ,@(remove atype '(integer single-float double-float)))))
`(,',fname (coerce obj ',',atype)))


(defknown widen-sse-type (sse-pack) sse-pack)
(define-vop (widen-sse-type)
  (:policy :fast-safe)
  (:translate widen-sse-type)
  (:args (x :scs (sse-reg) :target r))
  (:arg-types sse-pack)
  (:results (r :scs (sse-reg)))
  (:result-types sse-pack)
  (:generator 0
     (move r x)))

(defknown pxor (sse-pack sse-pack) (sse-pack integer))

(define-vop (pxor)
  (:policy :fast-safe)
  (:translate pxor)
  (:args (x :scs (sse-reg) :target r)
         (y :scs (sse-reg)))
  (:arg-types sse-pack sse-pack)
  (:results (r :scs (sse-reg)))
  (:result-types int-sse-pack)
  (:generator 1
     (cond ((location= x r)
            (inst pxor r y))
           ((location= y r)
            (inst pxor r x))
           (t
            (inst movaps r x)
            (inst pxor r y)))))
|#
