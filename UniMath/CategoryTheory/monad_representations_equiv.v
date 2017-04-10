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

  Definition monad_to_kleisli {C : precategory} : Monad C → kleisli_monad C :=
    fun T => (functor_on_objects T ,, (pr1 (@Monads.η C T) ,, @Monads.bind C T))
               ,, @Monad_law2 C T ,, @η_bind C T ,, @bind_bind C T.

  Lemma isweq_monad_to_kleisli (C : precategory) : isweq (@monad_to_kleisli C).
  Proof.
  Admitted.

  Definition weq_kleisli_monad (C : precategory) : weq (Monad C) (kleisli_monad C) :=
    @monad_to_kleisli C ,, isweq_monad_to_kleisli C.

End monad_representations_equiv.