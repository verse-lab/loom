import Loom.MonadAlgebras.NonDetT.Extract

abbrev VelvetM α := NonDetT DivM α

set_option quotPrecheck false in
notation "[totl|" t "]" => open TotalCorrectness TotalCorrectness.DemonicChoice in t
set_option quotPrecheck false in
notation "[part|" t "]" => open PartialCorrectness PartialCorrectness.DemonicChoice in t

@[local simp]
lemma DivM.total_decompose (α : Type) (x : DivM α) (post₁ post₂ : α -> Prop) :
  ([totl| wp x post₁] ∧ [part| wp x post₂]) = [totl| wp x (post₁ ⊓ post₂)] := by
    simp [[totl| DivM.wp_eq], [part| DivM.wp_eq]]
    split <;> simp

@[local simp]
lemma wp_mono_part (x : NonDetT DivM α) (post₁ post₂ : α -> Prop) :
  (post₁ ≤ post₂) → ([totl|wp x post₁]) ≤ ([part| wp x post₂]) := by
    intro le
    simp [loomLogicSimp]
    simp [loomLogicSimp] at le
    unhygienic induction x <;> try simp [loomLogicSimp]
    { exact le ret }
    { simp [[totl| DivM.wp_eq], [part| DivM.wp_eq]]
      intro wp1
      match x_1 with
      | .div => trivial
      | .res a => simp; simp at wp1; exact f_ih a post₁ post₂ le wp1 }
    { intro wp1 i hi
      exact f_ih i post₁ post₂ le (wp1 i hi) }
    intro x x_1 h1 sp1
    exists x
    constructor
    { intro b xb
      have hbx := h1 b xb
      simp [←[totl| NonDetT.wp_eq_wp]] at hbx
      simp [←[part| NonDetT.wp_eq_wp]]
      exact f_ih b (fun x_2 ↦
        match x_2 with
        | ForInStep.yield b' => x (ForInStep.yield b') ∧ x_1 b' < x_1 b
        | ForInStep.done b' => x (ForInStep.done b'))
        x
        (by
          intro x2 hx2
          match x2 with
          | .yield b' => simp at hx2; simp [hx2]
          | .done b' => simp at hx2; simp [hx2] )
        hbx }
    simp [spec, LE.pure] at sp1
    simp [spec, LE.pure, sp1]
    exact le_trans sp1.right (by
      simp [loomLogicSimp, ←[totl| NonDetT.wp_eq_wp], ←[part| NonDetT.wp_eq_wp]]
      intro x1; exact cont_ih x1 post₁ post₂ le )

lemma VelvetM.total_decompose {α : Type} (x : VelvetM α) (post₁ post₂ : α -> Prop):
  [totl| wp x post₁] ⊓ [part| wp x post₂] = [totl| wp x (post₁ ⊓ post₂)] := by
    unhygienic induction x <;> try simp [loomLogicSimp]
    { simp [DivM.total_decompose]
      simp [[totl| DivM.wp_eq], [part| DivM.wp_eq]]
      split
      { simp }
      rename_i arg
      have ind := f_ih arg post₁ post₂
      simp at ind
      rw [ind]
      trivial }
    { constructor <;> intro hyp
      { intro i hi
        have hl := hyp.left i hi
        have hr := hyp.right i hi
        have ind := f_ih i post₁ post₂
        simp [hl, hr] at ind
        exact ind }
      constructor <;>
      { intro i hi
        have conj := hyp i hi
        have ind := f_ih i post₁ post₂
        simp [loomLogicSimp] at ind
        rw [←ind] at conj
        simp [conj] } }
    constructor
    { intro conj
      rcases conj with ⟨h, inv_spec, hspec⟩
      rcases h with ⟨inv, x1, hinv⟩
      rcases x1 with ⟨x, hx⟩
      exists inv ⊓ inv_spec
      constructor
      { exists x
        intro b hb
        simp [←[totl| NonDetT.wp_eq_wp]]
        simp [loomLogicSimp] at hb
        have hxb := hx b hb.left
        simp [←[totl| NonDetT.wp_eq_wp]] at hxb
        simp [spec, LE.pure, loomLogicSimp, ←[part| NonDetT.wp_eq_wp]] at hspec
        have hspecb := hspec.left b hb.right
        have ind := f_ih b
          (fun x_1 ↦
          match x_1 with
          | ForInStep.yield b' => inv (ForInStep.yield b') ∧ x b' < x b
          | ForInStep.done b' => inv (ForInStep.done b'))
          inv_spec
        simp [loomLogicSimp] at ind
        have indr := ind.mp (And.intro hxb hspecb)
        have v1 := [totl| NonDetT.wp_mono
          (f b)
          (fun x_1 ↦
            (match x_1 with
              | ForInStep.yield b' => inv (ForInStep.yield b') ∧ x b' < x b
              | ForInStep.done b' => inv (ForInStep.done b')) ∧
              inv_spec x_1)
          (fun x_1 ↦
            match x_1 with
            | ForInStep.yield b' => (inv (ForInStep.yield b') ∧ inv_spec (ForInStep.yield b')) ∧ x b' < x b
            | ForInStep.done b' => inv (ForInStep.done b') ∧ inv_spec (ForInStep.done b'))
          ]
        simp [loomLogicSimp, ←[totl| NonDetT.wp_eq_wp]] at v1
        exact v1
          (fun x => by
            match x with
            | .yield b' => intro hb hspec; simp [hb, hspec]
            | .done b' => intro hb hspec; simp [hb, hspec] )
          indr }
      simp [spec, LE.pure, loomLogicSimp, ←[totl| NonDetT.wp_eq_wp]] at hinv
      simp [spec, LE.pure, loomLogicSimp, ←[part| NonDetT.wp_eq_wp]] at hspec
      simp [spec, LE.pure, loomLogicSimp, ←[totl| NonDetT.wp_eq_wp]]
      simp [hinv, hspec]
      intro x inv_x inv_spec
      have h₁ := hinv.right x inv_x
      have h₂ := hspec.right.right x inv_spec
      have cont_ind := cont_ih x post₁ post₂
      simp [loomLogicSimp] at cont_ind
      exact cont_ind.mp (And.intro h₁ h₂) }
    intro hyp
    rcases hyp with ⟨inv, x_ex, h_inv⟩
    rcases x_ex with ⟨x, hx⟩
    simp [spec]
    simp [spec, LE.pure] at h_inv
    constructor <;> exists inv <;> constructor
    { exists x }
    { simp [h_inv, LE.pure]
      exact le_trans h_inv.right (by
        simp [←[totl| NonDetT.wp_eq_wp], ←[part| NonDetT.wp_eq_wp]]
        simp [loomLogicSimp]
        intro x and_wp
        have cont_ind := cont_ih x post₁ post₂
        simp [loomLogicSimp, and_wp] at cont_ind
        simp [cont_ind] ) }
    { intro b hb
      have hbx := hx b hb
      simp [←[totl| NonDetT.wp_eq_wp]] at hbx
      have hb_triv: True ≤ ([totl| wp (f b) fun x_1 ↦
        match x_1 with
        | ForInStep.yield b' => inv (ForInStep.yield b') ∧ x b' < x b
        | ForInStep.done b' => inv (ForInStep.done b')]) := by
        simp [loomLogicSimp]
        exact hbx
      have tr_intro: True ≤ ([part| NonDetT.wp (f b) inv]) := le_trans hb_triv (by
        simp [loomLogicSimp]
        intro wp_x
        simp [←[part| NonDetT.wp_eq_wp]]
        apply wp_mono_part (f b) (fun x_1 ↦
          match x_1 with
          | ForInStep.yield b' => inv (ForInStep.yield b') ∧ x b' < x b
          | ForInStep.done b' => inv (ForInStep.done b')) (fun x => inv x)
        { simp [loomLogicSimp]
          intro x1
          match x1 with
          | ForInStep.yield b' => simp; intros; simp [*]
          | ForInStep.done b' => simp }
        exact wp_x)
      simp at tr_intro
      simp [tr_intro] }
    simp [LE.pure, h_inv]
    exact le_trans h_inv.right (by
      simp [←[totl| NonDetT.wp_eq_wp], ←[part| NonDetT.wp_eq_wp]]
      simp [loomLogicSimp])

lemma VelvetM.total_decompose_triple {α : Type} {pre : Prop} {post : α -> Prop}
  (x y z: VelvetM α) (termination: [totl| triple pre x fun _ => True]) (postcondition: [part| triple pre y post]) {eqx: x = z} {eqy: y = z}:
  [totl| triple pre z post] := by
    simp [triple]
    intro pre
    simp [triple, pre, eqx] at termination
    simp [triple, pre, eqy] at postcondition
    have decomp := VelvetM.total_decompose z (fun x => True) post
    simp [loomLogicSimp, postcondition, termination] at decomp
    exact decomp
