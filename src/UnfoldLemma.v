Notation unfold_lemma e :=
  (eq_refl : (ltac:(let t := eval red in e
                      in exact (e = t))))
    (only parsing).
