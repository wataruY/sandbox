
(setq exec-path (delete-dups (append (split-string (getenv "PATH") ":" t) exec-path)))

(mapcar 'color-values (defined-colors))
(frame-parameter nil 'background-color)

(defun wataru:color-luminously-contrast-ratio (c1 c2)
  (flet ((calc (c) (destructuring-bind (r g b) c
		     (+ (* r .2126)
			(* g .7152)
			(* b .0722)))))
    (destructuring-bind (l1 l2)
	(sort (mapcar 'calc (list c1 c2)) '>)
      (/ (+ l1 .05)
	 (+ l2 .05)))))



(wataru:color-luminously-contrast-ratio (color-values "#001100") (color-values "white"))

(insert (pp (remove-if (lambda (x) (>= (plist-get x :level) 2))
		       (mapcar (lambda (x)
				 (plist-put x
					    :lcr (wataru:color-luminously-contrast-ratio (color-values (plist-get x :foreground))
											 (color-values (plist-get x :background))))
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

((:face which-func :foreground "Blue1" :background "#001100" :lcr 1.520168473922962 :level 0)
 (:face coq-solve-tactics-face :foreground "red" :background "#001100" :lcr 4.476254324197864 :level 0)
 (:face custom-invalid :foreground "yellow1" :background "red1" :lcr 4.364051897426726 :level 0)
 (:face magit-log-head-label-patches :foreground "IndianRed4" :background "IndianRed1" :lcr 1.830312952309808 :level 0)
 (:face magit-log-head-label-tags :foreground "goldenrod4" :background "LemonChiffon1" :lcr 2.3358513518224937 :level 0)
 (:face magit-log-head-label-bisect-bad :foreground "IndianRed4" :background "IndianRed1" :lcr 1.830312952309808 :level 0)
 (:face magit-log-head-label-bisect-good :foreground "dark olive green" :background "light green" :lcr 2.1555959863158396 :level 0)
 (:face agda2-highlight-error-face :foreground "red" :background "#001100" :lcr 4.476254324197864 :level 0)
 (:face agda2-highlight-record-face :foreground "medium blue" :background "#001100" :lcr 1.2220993738868633 :level 0)
 (:face agda2-highlight-primitive-face :foreground "medium blue" :background "#001100" :lcr 1.2220993738868633 :level 0)
 (:face agda2-highlight-postulate-face :foreground "medium blue" :background "#001100" :lcr 1.2220993738868633 :level 0)
 (:face agda2-highlight-function-face :foreground "medium blue" :background "#001100" :lcr 1.2220993738868633 :level 0)
 (:face agda2-highlight-datatype-face :foreground "medium blue" :background "#001100" :lcr 1.2220993738868633 :level 0)
 (:face agda2-highlight-primitive-type-face :foreground "medium blue" :background "#001100" :lcr 1.2220993738868633 :level 0)
 (:face anything-gentoo-match-face :foreground "red" :background "#001100" :lcr 4.476254324197864 :level 0)
 (:face anything-bookmarks-su-face :foreground "red" :background "#001100" :lcr 4.476254324197864 :level 0)
 (:face anything-file-name :foreground "Blue" :background "#001100" :lcr 1.520168473922962 :level 0)
 (:face navi2ch-article-auto-decode-face :foreground "gray10" :background "#001100" :lcr 2.1467741249406767 :level 0)
 (:face info-menu-star :foreground "red1" :background "#001100" :lcr 4.476254324197864 :level 0)
 (:face ac-yasnippet-selection-face :foreground "white" :background "coral3" :lcr 2.24376810873723 :level 0)
 (:face ac-selection-face :foreground "white" :background "steelblue" :lcr 2.109982160707658 :level 0)
 (:face popup-menu-selection-face :foreground "white" :background "steelblue" :lcr 2.109982160707658 :level 0)
 (:face widget-button-pressed :foreground "red1" :background "#001100" :lcr 4.476254324197864 :level 0)
 (:face isearch :foreground "brown4" :background "palevioletred2" :lcr 2.602284142145173 :level 0)
 (:face header-line :foreground "grey90" :background "grey20" :lcr 4.490182764237567 :level 0)
 (:face mode-line-inactive :foreground "grey80" :background "grey30" :lcr 2.6493464820190966 :level 0))









