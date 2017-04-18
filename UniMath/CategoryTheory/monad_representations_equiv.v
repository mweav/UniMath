(** **********************************************************

 Matthew Weaver, 2017

 ************************************************************)


(** **********************************************************

 Contents : Equivalence of the traditional defintion of monads
            to those given in Kleisli form

 ************************************************************)

Require Import UniMath.MoreFoundations.Tactics
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.CategoryTheory.Monads.

Local Open Scope cat.

(** * Definition of a Kleisli Monad *)
Section kleisli_monad_def.

  Definition kleisli_data (C : precategory) : UU :=
    ∑ F : C → C, (∏ x, x --> F x) × (∏ x y, (x --> F y) → (F x --> F y)).

  Definition ob_function_from_kleisli_data (C : precategory) (F : kleisli_data C)
    : C → C := pr1 F.
  Coercion ob_function_from_kleisli_data : kleisli_data >-> Funclass.

  Definition kleisli_unit {C : precategory} (F : kleisli_data C) := (pr1 (pr2 F)).
  Local Definition η {C : precategory} := @kleisli_unit C.

  Definition kleisli_bind {C : precategory} {F : kleisli_data C} {x y : C} := (pr2 (pr2 F)) x y.
  Local Definition bind {C : precategory} {F : kleisli_data C} {x y : C} := @kleisli_bind C F x y.

  Definition kleisli_laws {C : precategory} (F : kleisli_data C) : UU :=
    (
      (∏ x, bind (η F x) = identity (F x))
        ×
      (∏ x y (f : x --> F y), (η F x) · (bind f) = f)
        ×
      (∏ x y z (f : x --> F y) (g : y --> F z), (bind f) · (bind g) = bind (f · (bind g)))
    ).

  Lemma isaprop_kleisli_laws {C : precategory} (hsC : has_homsets C) (F : kleisli_data C)
    : isaprop (kleisli_laws F).
  Proof.
    repeat apply isapropdirprod;
      repeat (apply impred; intro);
      now apply hsC.
  Qed.

  Definition kleisli_monad (C : precategory) : UU := ∑ F : kleisli_data C , kleisli_laws F.

  Coercion kleisli_data_from_kleisli_monad (C : precategory) (T : kleisli_monad C) : kleisli_data C := pr1 T.

  Definition kleisli_law1 {C : precategory} (T : kleisli_monad C) := pr1 (pr2 T).
  Definition kleisli_law2 {C : precategory} (T : kleisli_monad C) := pr1 (pr2 (pr2 T)).
  Definition kleisli_law3 {C : precategory} (T : kleisli_monad C) := pr2 (pr2 (pr2 T)).

End kleisli_monad_def.

(** * Equivalence of the types of Kelisli monads and traditional monads *)
Section monad_representations_equiv.

  Context {C : precategory}.

  Definition monad_to_kleisli : Monad C → kleisli_monad C :=
    fun T => (functor_on_objects T ,, (pr1 (@Monads.η C T) ,, @Monads.bind C T))
               ,, @Monad_law2 C T ,, @η_bind C T ,, @bind_bind C T.

  Definition kleisli_to_functor : kleisli_monad C → functor C C.
  Proof.
    intros T.
    use mk_functor.
    + exists T.
      intros x y f.
      exact (bind (f · (η T y))).
    + split.
      ++ abstract (intro x;
                   refine (_ @ kleisli_law1 T x);
                   exact (maponpaths bind (id_left _))).
      ++ abstract (intros x y z f g;
                   refine (_ @ !(kleisli_law3 T _ _ _ _ _));
                   refine (maponpaths bind (!(assoc _ _ _) @ maponpaths (compose f) _ @ assoc _ _ _));
                   exact (!(kleisli_law2 T y z _))).
  Defined.

  Definition kleisli_to_μ (T : kleisli_monad C) : (kleisli_to_functor T) □ (kleisli_to_functor T) ⟹ (kleisli_to_functor T).
  Proof.
    mkpair.
    + intro x.
      exact (bind (identity (T x))).
    + abstract (intros x y f;
                refine (kleisli_law3 T _ _ _ _ _ @ maponpaths bind _ @ !(kleisli_law3 T _ _ _ _ _));
                refine (!(assoc _ _ _) @ _ @ !(id_left _));
                refine (remove_id_right _ _ _ _ _ _ _ (idpath _));
                now apply kleisli_law2).
  Defined.

  Definition kleisli_to_η  (T : kleisli_monad C) : nat_trans (functor_identity C) (kleisli_to_functor T).
  Proof.
    use mk_nat_trans.
    + exact (η T).
    + abstract (intros x y f;
                exact (!(kleisli_law2 T _ _ _))).
  Defined.

  Definition kleisli_to_monad : kleisli_monad C → Monad C.
  Proof.
    intro T.
    refine (((kleisli_to_functor T,, kleisli_to_μ T) ,, kleisli_to_η T) ,, _).
    repeat split; intros; simpl.
    + abstract (now apply kleisli_law2).
    + abstract (refine (kleisli_law3 T _ _ _ _ _ @ _);
                rewrite <- assoc;
                refine (maponpaths (fun x => bind (η T c · x)) (kleisli_law2 T _ _ _) @ _);
                rewrite id_right;
                now apply kleisli_law1).
    + abstract (refine (kleisli_law3 T _ _ _ _ _ @ maponpaths bind _ @ !(kleisli_law3 T _ _ _ _ _));
                rewrite <- assoc , (kleisli_law2 T);
                refine (_ @ maponpaths (fun x => x · bind (identity (T c))) (kleisli_law1 T (T c)));
                refine (_ @ !(kleisli_law3 T _ _ _ _ _));
                rewrite (kleisli_law2 T);
                now apply id_right).
  Defined.

  Lemma kleisli_to_monad_inv (hsC : has_homsets C) (T : kleisli_monad C) :
    monad_to_kleisli (kleisli_to_monad T) = T.
  Proof.
    apply (invmaponpathsincl pr1).
      { apply isinclpr1.
        intros ?.
        now apply (isaprop_kleisli_laws hsC).
      }
      repeat (use total2_paths_f;
               try reflexivity;
               try rewrite idpath_transportf).
      simpl; unfold Monads.bind; simpl.
      apply funextsec; intro a.
      apply funextsec; intro b.
      apply funextsec; intro f.
      rewrite (kleisli_law3 T).
      apply (maponpaths bind).
      rewrite <- assoc , (kleisli_law2 T).
      now apply id_right.
  Qed.

  Lemma monad_to_kleisli_inv (hsC : has_homsets C) (T : Monad C) :
    kleisli_to_monad (monad_to_kleisli T) = T.
  Proof.
  Admitted.

  Lemma isweq_monad_to_kleisli (hsC : has_homsets C) : isweq monad_to_kleisli.
  Proof.
    intros T.
    refine ((kleisli_to_monad T ,, kleisli_to_monad_inv hsC T),, _).
    intros [T' Teq].
    apply (invmaponpathsincl pr1).
    { apply isinclpr1.
      intros ?.
      admit.
    }
    simpl. rewrite <- Teq.
    exact (!(monad_to_kleisli_inv hsC T')).
  Admitted.

  Definition weq_kleisli_monad : weq (Monad C) (kleisli_monad C) :=
    monad_to_kleisli ,, isweq_monad_to_kleisli.

End monad_representations_equiv.