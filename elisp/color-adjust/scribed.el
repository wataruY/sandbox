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
  (flet ((calc (c) (destructuring-bind (r g b) (mapcar 'wataru:color-rgb-to-linear c)
		     (+ (* r .2126) (* g .7152) (* b .0722)))))
    (destructuring-bind (l1 l2)
	(sort (mapcar 'calc (list c1 c2)) '>)
      (/ (+ l1 .05)
	 (+ l2 .05)))))

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
(wataru:)
((:face org-hide :foreground "black" :background "#001100" :lcr 1.0801795217925958 :level 0)
 (:face which-func :foreground "Blue1" :background "#001100" :lcr 2.2625868669904947 :level 0)
 (:face custom-invalid :foreground "yellow1" :background "red1" :lcr 3.7235338918507237 :level 0)
 (:face magit-log-head-label-patches :foreground "IndianRed4" :background "IndianRed1" :lcr 2.721210589780212 :level 0)
 (:face magit-log-head-label-bisect-bad :foreground "IndianRed4" :background "IndianRed1" :lcr 2.721210589780212 :level 0)
 (:face magit-log-head-label-bisect-good :foreground "dark olive green" :background "light green" :lcr 4.1973890796378335 :level 0)
 (:face agda2-highlight-record-face :foreground "medium blue" :background "#001100" :lcr 1.741891571064085 :level 0)
 (:face agda2-highlight-primitive-face :foreground "medium blue" :background "#001100" :lcr 1.741891571064085 :level 0)
 (:face agda2-highlight-postulate-face :foreground "medium blue" :background "#001100" :lcr 1.741891571064085 :level 0)
 (:face agda2-highlight-module-face :foreground "purple" :background "#001100" :lcr 3.6656642642385826 :level 0)
 (:face agda2-highlight-function-face :foreground "medium blue" :background "#001100" :lcr 1.741891571064085 :level 0)
 (:face agda2-highlight-datatype-face :foreground "medium blue" :background "#001100" :lcr 1.741891571064085 :level 0)
 (:face agda2-highlight-coinductive-constructor-face :foreground "gold4" :background "#001100" :lcr 4.29772023926947 :level 0)
 (:face agda2-highlight-inductive-constructor-face :foreground "green4" :background "#001100" :lcr 4.3446921863527175 :level 0)
 (:face agda2-highlight-primitive-type-face :foreground "medium blue" :background "#001100" :lcr 1.741891571064085 :level 0)
 (:face agda2-highlight-number-face :foreground "purple" :background "#001100" :lcr 3.6656642642385826 :level 0)
 (:face agda2-highlight-string-face :foreground "firebrick" :background "#001100" :lcr 2.911465218100012 :level 0)
 (:face anything-emms-playlist :foreground "Springgreen4" :background "#001100" :lcr 4.424247691871591 :level 0)
 (:face anything-bmkext-man :foreground "Orange4" :background "#001100" :lcr 3.2959884619979203 :level 0)
 (:face anything-grep-file :foreground "BlueViolet" :background "#001100" :lcr 3.2627936313218933 :level 0)
 (:face anything-file-name :foreground "Blue" :background "#001100" :lcr 2.2625868669904947 :level 0)
 (:face navi2ch-article-message-separator-face :foreground "firebrick" :background "#001100" :lcr 2.911465218100012 :level 0)
 (:face navi2ch-article-auto-decode-face :foreground "gray10" :background "#001100" :lcr 1.1170332673870262 :level 0)
 (:face ac-yasnippet-selection-face :foreground "white" :background "coral3" :lcr 4.055466747380766 :level 0)
 (:face ac-selection-face :foreground "white" :background "steelblue" :lcr 4.107556611212924 :level 0)
 (:face popup-menu-selection-face :foreground "white" :background "steelblue" :lcr 4.107556611212924 :level 0)
 (:face isearch :foreground "brown4" :background "palevioletred2" :lcr 3.3316816553991817 :level 0))















