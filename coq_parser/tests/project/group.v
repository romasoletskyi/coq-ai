Require Import Ensembles.

Arguments In {U}.
Notation "x ∈ s" := (In s x) (at level 75).

Section Groups.
    Variable U : Type.

    Record Group : Type := makeGroup {
        G : Ensemble U;

        op : U -> U -> U;
        inv : U -> U;
        e : U;

        endo_op : forall x y, x ∈ G -> y ∈ G -> (op x y) ∈ G;
        endo_inv : forall x, x ∈ G -> (inv x) ∈ G;

        op_assoc : forall x y z, op x (op y z) = op (op x y) z;
        op_e_left : forall x, op e x = x;
        op_e_right : forall x, op x e = x;
        op_inv_left : forall x, op (inv x) x = e;
        op_inv_right : forall x, op x (inv x) = e;
    }.

    Variable g : Group.
    Notation "x * y" := (op g x y).
    Notation "x ⁻¹" := (inv g x) (at level 30).

    Lemma left_cancel : forall x y z, x * y = x * z -> y = z.
    Proof.
        intros x y z H. 
        assert (F : x ⁻¹ * x * y = x ⁻¹ * x * z).
        { rewrite <- op_assoc. rewrite <- op_assoc. rewrite H.
          reflexivity. }
        rewrite op_inv_left in F. rewrite op_e_left in F.
        rewrite op_e_left in F. apply F.
    Qed.

    Inductive subgroup (g1 g2 : Group) : Prop := subgroup_def : 
        Included U (G g1) (G g2) -> op g1 = op g2 -> subgroup g1 g2.

    Inductive normal (g1 g2 : Group) : Prop := normal_def :
        subgroup g1 g2 -> forall h g, h ∈ (G g1) -> g ∈ (G g2) ->
        g * h * g ⁻¹ ∈ (G g1) -> normal g1 g2.
    
    Variable h : Group.
    Hypothesis norm : normal h g.

    Inductive left_coset (z : {x: U | x ∈ (G g)}) : Ensemble U := left_coset_def :
        forall (y : {x: U | x ∈ (G h)}), (proj1_sig z) * (proj1_sig y) ∈ left_coset z.  

End Groups. 
