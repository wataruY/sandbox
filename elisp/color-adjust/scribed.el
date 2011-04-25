(require 'el-expectations)

(setq exec-path (delete-dups (append (split-string (getenv "PATH") ":" t) exec-path)))

(mapcar 'color-values (defined-colors))
(frame-parameter nil 'background-color)

(defun wataru:color-luminously-contrast-ratio (c1 c2)
  "calculate Luminourly Contrast Ratio from two COLORs C1 and C2. For each elements of COLOR (x), x in [0, #xff]."
  (assert (every (apply-partially 'every
			   (lambda (x) (and (<= 0 x) (<= x #xff))))
		 (list c1 c2))
	  nil
	  "out of range [0, #xff] : c1 = %s, c2 = %s" c1 c2)
  (flet ((calc (c) "Luma(Y') defined in Rec. 709"
	       (destructuring-bind (r g b) (mapcar 'wataru:color-rgb-to-linear c)
		 (+ (* r .2126) (* g .7152) (* b .0722)))))
    (destructuring-bind (l1 l2)
	(sort (mapcar 'calc (list c1 c2)) '>)
      (/ (+ l1 .05)
	 (+ l2 .05)))))

'(
  (FG -> BG -> OK + {fg | level3 fg})
  (\ fg bg -> isLevel3 fg)
  )

(expectations
  (desc "white:black = 21.0")
  (expect 21.0 (wataru:color-luminously-contrast-ratio (color-values "black") '(#xff #xff #xff)))
  (desc "x not in [0,#xff] is error")
  (expect (error) (wataru:color-luminously-contrast-ratio '(0 0 0) (#xfff #xfff #xfff))))

(defun wataru:color-color-values (x &optional frame)
  (mapcar (lambda (x) (lsh x -8)) (color-values x frame)))

(defun* wataru:color-rgb-to-linear (x &optional (maximum #xff))
  "map monitor RGB color element to linear RGB color element"
  (let ((sX (/ (* 1.0 x) maximum)))
    (if (<= sX 0.03928)
	(/ sX 12.92)
      (expt (/ (+ sX .055) 1.055) 2.4))))

(defun wataru:color-lcr-level3-p (fg bg)
  (< 10.0 (wataru:color-luminously-contrast-ratio fg bg)))

;;; find level3 colors 
(remove-if-not (lambda (x) (wataru:color-lcr-level3-p (wataru:color-color-values x) (wataru:color-color-values "#001100")))
	       (defined-colors))

(wataru:color-luminously-contrast-ratio (wataru:color-color-values "orchid") (wataru:color-color-values "#001100"))



(insert (pp (remove-if (lambda (x) (>= (plist-get x :level) 2))
		       (mapcar (lambda (x)
				 (plist-put x
					    :lcr (wataru:color-luminously-contrast-ratio (wataru:color-color-values (plist-get x :foreground))
											 (wataru:color-color-values (plist-get x :background))))
				 (plist-put x
					    :level (let ((lcr (plist-get x :lcr)))
						     (cond ((< lcr 4.5) 0)
							   ((< lcr 10) 2)
							   ((<= 10 lcr) 3)))))
			       (delete nil
				       (mapcar (lambda (face) (let ((fg (face-foreground face)))
								(if fg
								    (list :face face
									  :foreground fg
									  :background (or (face-background face)
											  (face-background 'default)) ))))
					       (face-list)))))))















