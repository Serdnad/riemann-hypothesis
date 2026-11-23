module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle002
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.Up_operator_maps_lattice_of_control_values :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (Λ Λ' : Submodule O Ω), (∀ a ∈ maximalIdeal O, ∀ w ∈ Λ, a • w ∈ Λ') → ∀ F ∈ X.Lat m W Λ, (∀ g i, X.ctrl m W F g i ∈ Λ') → X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Lat m W Λ' := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m Λ Λ' h F hF hc
  have hu : ∀ i g k, X.unt m W F i g k ∈ Λ := (Frame.mem_lat X m W Λ F).mp hF
  have hu0 : ∀ i g, X.unt m W F i g 0 ∈ Λ' := fun i g => by
    rw [← Frame.ctrl_apply]
    exact hc g i
  have hF' : ∀ i g, F i g = (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ X.unt m W F i g := fun i g => by
    rw [Frame.unt_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hM : ∀ (M : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω),
      (∀ k l, M k l ∈ (algebraMap O Ω).range) → ∀ w : Fin (W.d + 1) → Ω, (∀ l, w l ∈ Λ') →
      ∀ k, (M *ᵥ w) k ∈ Λ' := by
    intro M hMi w hw k
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun l _ => ?_
    obtain ⟨y, hy⟩ := hMi k l
    rw [← hy, ← Algebra.smul_def]
    exact Λ'.smul_mem y (hw l)
  have main : ∀ c : Ω, (∀ l j, c * (W.ξ X.I.z : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) l j ∈ (algebraMap O Ω).range) →
      (∀ l j, j ≠ 0 → ∃ x ∈ maximalIdeal O, c * (W.ξ X.I.z : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) l j = algebraMap O Ω x) →
      (c • ∑ᶠ (q : ↥X.I.N ⧸ (X.I.Nconj X.I.z).subgroupOf X.I.N),
        X.rpF Ω (W.d + 1) m (↑(Quotient.out q) * X.I.z)) F ∈ X.Lat m W Λ' := by
    intro c hP hN
    refine finsum_induction (p := fun T : Module.End Ω (Fin m → X.Fn Ω (W.d + 1)) => (c • T) F ∈ X.Lat m W Λ') ?_ ?_ ?_
    · simp
    · intro S T hS hT
      simpa [smul_add] using add_mem hS hT
    · intro q
      have hn : ((Quotient.out q : ↥X.I.N) : Gp) ∈ X.I.N := (Quotient.out q).2
      generalize ((Quotient.out q : ↥X.I.N) : Gp) = n at hn ⊢
      rw [Frame.mem_lat]
      intro i g k
      have e : X.unt m W ((c • X.rpF Ω (W.d + 1) m (n * X.I.z)) F) i g
          = (W.ξ n : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ ((c • (W.ξ X.I.z : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)) *ᵥ
              X.unt m W F i (g * (1, n * X.I.z))) := by
        have e1 : X.rpF Ω (W.d + 1) m (n * X.I.z) F i g = F i (g * (1, n * X.I.z)) := by
          simp [Frame.rpF, Frame.rp, rtr]
        rw [Frame.unt_apply, LinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, e1,
          hF' i (g * (1, n * X.I.z))]
        simp only [Prod.snd_mul, mul_one, map_mul, Units.val_mul, Matrix.mulVec_smul,
          Matrix.mulVec_mulVec, ← mul_assoc]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, Matrix.mul_smul, Matrix.smul_mulVec]
      rw [e]
      refine hM _ (fun k l => W.int_N _ hn k l) _ (fun l => ?_) k
      simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : j = 0
      · subst hj
        obtain ⟨y, hy⟩ := hP l 0
        rw [← hy, ← Algebra.smul_def]
        exact Λ'.smul_mem y (hu0 _ _)
      · obtain ⟨x, hx, hxe⟩ := hN l j hj
        rw [hxe, ← Algebra.smul_def]
        exact h x hx _ (hu _ _ _)
  exact main _ (fun l j => W.int_P _ X.I.z_mem l j) (fun l j hj => W.nilpotent_central_action l j hj)
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem control_map_translate_trace {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type} [CommRing O]
    [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (F : Fin m → X.Fn Ω (W.d + 1))
    (g : Ga × Gp) (b : Gp) (i : Fin m) :
    X.ctrl m W F (g * (1, b)) i =
      ∑ j, (W.ξ b⁻¹).val 0 j * (((W.ξ g.2)⁻¹).val *ᵥ (X.rpF Ω (W.d + 1) m b F i g)) j := by
  rw [Frame.ctrl_apply, Frame.unt_apply]
  show _ = ∑ j, (W.ξ b⁻¹).val 0 j * (((W.ξ g.2)⁻¹).val *ᵥ F i (g * (1, b))) j
  rw [Prod.snd_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, map_inv]
  rfl

theorem UpperTheory.exists_integral_form_lifting_controlMap :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ) (θ : X.I.T →* Oˣ), Function.Injective (algebraMap O Ω) → (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) → ∀ F ∈ X.ClO W τ U c φ, F ∈ X.Lat m W (mIm O Ω 0) → ∃ f ∈ X.Sp τ θ U, X.mapFn (B := Ω) f = X.ctrl m W F ∧ ∀ k c' : ℕ, c ≤ c' → (∀ y ∈ X.I.Nm c', ∀ i j, ∃ a ∈ maximalIdeal O ^ k, W.ξ y i j = (if i = j then 1 else 0) + algebraMap O Ω a) → ∀ y ∈ X.I.Nm c', X.rp O m y f - f ∈ X.valIn O m k := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c θ hinj hθ F hF hL
  have hL' : ∀ i g k, X.unt m W F i g k ∈ mIm O Ω 0 := fun i g k => hL i g k
  have hv : ∀ i g k, ∃ a : O, algebraMap O Ω a = X.unt m W F i g k := by
    intro i g k
    obtain ⟨a, -, ha⟩ := mem_mIm.1 (hL' i g k)
    exact ⟨a, ha⟩
  choose v hv0 using hv
  have hu : ∀ i g j, ((W.ξ g.2)⁻¹.val *ᵥ F i g) j = algebraMap O Ω (v i g j) := by
    intro i g j
    rw [hv0, Frame.unt_apply]
  obtain ⟨f, hf⟩ : ∃ f : X.Fn O m, ∀ g i, algebraMap O Ω (f g i) = X.ctrl m W F g i :=
    ⟨fun g i => v i g 0, fun g i => by rw [Frame.ctrl_apply, hv0]⟩
  have hf0 : ∀ g i, algebraMap O Ω (f g i) = algebraMap O Ω (v i g 0) := by
    intro g i
    rw [hf, Frame.ctrl_apply, hv0]
  have hs : ∀ (b : Gp) (a : Ω), X.rpF Ω (W.d + 1) m b F = a • F → ∀ g i,
      algebraMap O Ω (f (g * (1, b)) i) = a * ∑ j, (W.ξ b⁻¹).val 0 j * algebraMap O Ω (v i g j) := by
    intro b a hb g i
    rw [hf, control_map_translate_trace, hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul, hu]
    ring
  have hE := hF.2
  have hUF := hF.1.2
  have hA : ∀ i (γ : Γ) (g : Ga × Gp), F i (X.glob γ * g) = (W.ξ (X.glob γ).2).val *ᵥ F i g :=
    fun i γ g => hF.1.1 i (Set.mem_univ i) γ g
  have key : ∀ k c' : ℕ, c ≤ c' → (∀ y ∈ X.I.Nm c', ∀ i j, ∃ a ∈ maximalIdeal O ^ k, W.ξ y i j = (if i = j then 1 else 0) + algebraMap O Ω a) → ∀ y ∈ X.I.Nm c', X.rp O m y f - f ∈ X.valIn O m k := by
    intro k c' hc hξ y hy g _ i _
    have hyc : y ∈ X.I.Nm c := X.I.Nm_anti hc hy
    choose a ha hae using fun j => hξ y⁻¹ (inv_mem hy) 0 j
    have h1 : f (g * (1, y)) i - f g i = ∑ j, a j * v i g j := by
      apply hinj

      rw [map_sub, hs y 1 (by rw [one_smul]; exact hE.2.1 y hyc) g i, hf0, one_mul, map_sum]
      simp only [hae, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul]
      ring
    show f (g * (1, y)) i - f g i ∈ maximalIdeal O ^ k
    rw [h1]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (ha j)
  refine ⟨f, ?_, ?_, key⟩
  · refine Submodule.mem_inf.2 ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro γ g
      funext i
      apply hinj
      rw [hf, hf, Frame.ctrl_apply, Frame.ctrl_apply, Frame.unt_apply, Frame.unt_apply, hA, Prod.snd_mul, map_mul,
        Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    · intro u hu'
      funext g i
      apply hinj
      show algebraMap O Ω (f (g * (1, u)) i) = algebraMap O Ω (f g i)
      rw [hs u 1 (by rw [one_smul]; exact hE.1 u hu') g i, hf0, one_mul]
      simp only [W.row_N _ (X.I.N_le (inv_mem hu')), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · intro t
      funext g i
      apply hinj
      show algebraMap O Ω (f (g * (1, (t : Gp))) i) = algebraMap O Ω (((θ t)⁻¹ : Oˣ) * f g i)
      rw [hs (t : Gp) _ (hE.2.2 t) g i, map_mul, hf0]
      have hr : ∀ j, (W.ξ (t : Gp)⁻¹).val 0 j = if j = 0 then (W.χ ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ : Ω) else 0 :=
        fun j => W.torusAction ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ j
      have hχ : (W.χ ⟨(t : Gp)⁻¹, X.I.T_le (inv_mem t.2)⟩ : Ω) = (W.χ ⟨t, X.I.T_le t.2⟩ : Ω)⁻¹ := by
        rw [← Units.val_inv_eq_inv_val, ← map_inv]
        rfl
      have hθ' : algebraMap O Ω (((θ t)⁻¹ : Oˣ) : O) = (algebraMap O Ω (θ t))⁻¹ := map_units_inv (algebraMap O Ω) (θ t)
      simp only [hr, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hχ, hθ', hθ t]
      simp only [MonoidHom.comp_apply, Units.coe_map, Units.val_inv_eq_inv_val, MonoidHom.coe_coe]
      rw [mul_inv, mul_assoc]
      rfl
    · intro k
      obtain ⟨c1, hc1⟩ := W.cont_Nm k
      refine ⟨max c c1, fun y hy g i => ?_⟩
      have h := key k (max c c1) (le_max_left _ _)
        (fun y hy => hc1 y (X.I.Nm_anti (le_max_right _ _) hy)) y hy g (Set.mem_univ _) i (Set.mem_univ _)
      exact h
    · intro u hu'
      funext g i
      apply hinj
      rw [Frame.ra_apply, hf, ← hUF u hu',
        (ctrlEq Γ Ga Gp X O Ω W m ((GeneralLinearGroup.map (algebraMap O Ω)).comp τ)).1 u F, Frame.ra_apply]
      simp [Matrix.mulVec, dotProduct, hf]
  · funext g i
    exact hf g i
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem detd_mulVec {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {n : ℕ} (L : Submodule O Ω)
    (M : Matrix (Fin n) (Fin n) Ω) (hM : ∀ i j, M i j ∈ (algebraMap O Ω).range) (v : Fin n → Ω)
    (hv : ∀ k, v k ∈ L) (k : Fin n) : (M *ᵥ v) k ∈ L := by
  rw [Matrix.mulVec, dotProduct]
  refine Submodule.sum_mem L fun j _ => ?_
  obtain ⟨r, hr⟩ := hM k j
  rw [← hr, ← Algebra.smul_def]
  exact L.smul_mem r (hv j)

theorem UpperTheory.mem_lattice_of_values_at_double_coset_reps :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ), W.c0 ≤ c → ∀ (N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → ∀ F ∈ X.ClO W τ U c φ, ∀ Λ : Submodule O Ω, (∀ n i k, X.unt m W F i (x n) k ∈ Λ) → F ∈ X.Lat m W Λ := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c hc N x hx F hF Λ hΛ
  simp only [Frame.ClO, Frame.Cl, Submodule.mem_inf] at hF
  obtain ⟨⟨hA, hU⟩, hE⟩ := hF
  obtain ⟨hN, hNm, hT⟩ := hE
  have hA' : ∀ i γ g, F i (X.glob γ * g) =
      ((W.ξ (X.glob γ).2 : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ F i g :=
    fun i γ g => (Submodule.mem_pi.mp hA i (Set.mem_univ i)) γ g
  have hU' : ∀ u ∈ U, ∀ i g k,
      (((((GeneralLinearGroup.map (algebraMap O Ω)).comp τ) u : GL _ Ω) : Matrix (Fin m) (Fin m) Ω) *ᵥ
        (fun j => F j (g * ((u : Ga), 1)) k)) i = F i g k :=
    fun u hu i g k => congrFun (congrFun (congrFun (hU u hu) i) g) k
  have key : ∀ (h : Ga × Gp) (b : Gp) (s : O),
      (∀ i j, ((W.ξ b⁻¹ : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) i j ∈
        (algebraMap O Ω).range) →
      (∀ i, F i (h * (1, b)) = algebraMap O Ω s • F i h) →
      (∀ i k, X.unt m W F i h k ∈ Λ) → ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b s hMb hFb hG i k
    have e : X.unt m W F i (h * (1, b)) =
        ((W.ξ b⁻¹ : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ
          (algebraMap O Ω s • X.unt m W F i h) := by
      simp only [Frame.unt_apply, hFb i, Prod.snd_mul, map_mul, map_inv, _root_.mul_inv_rev,
        GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul]
    rw [e]
    refine detd_mulVec Λ _ hMb _ (fun j => ?_) k
    rw [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]
    exact Λ.smul_mem s (hG i j)
  have stepN : ∀ h, ∀ b ∈ X.I.N, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b hb hG
    refine key h b 1 (W.int_N _ (X.I.N.inv_mem hb)) (fun i => ?_) hG
    rw [map_one, one_smul]
    exact congrFun (congrFun (hN b hb) i) h
  have stepM : ∀ h, ∀ b ∈ X.I.Nm c, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b hb hG
    refine key h b 1 (W.int_Nm _ (X.I.Nm_anti hc ((X.I.Nm c).inv_mem hb))) (fun i => ?_) hG
    rw [map_one, one_smul]
    exact congrFun (congrFun (hNm b hb) i) h
  have stepT : ∀ h, ∀ b ∈ X.I.T, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b hb hG
    refine key h b ((φ ⟨b, hb⟩)⁻¹ : Oˣ) (W.integral_torusCharacter _ (X.I.T.inv_mem hb)) (fun i => ?_) hG
    have := congrFun (congrFun (hT ⟨b, hb⟩) i) h
    refine this.trans ?_
    simp
  have stepU : ∀ h, ∀ u ∈ U, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * ((u : Ga), 1)) k ∈ Λ := by
    intro h u hu hG i k
    have hv : ∀ i, F i (h * ((u : Ga), 1)) =
        fun l => ∑ j, algebraMap O Ω (((τ u⁻¹ : GL _ O) : Matrix (Fin m) (Fin m) O) i j) * F j h l := by
      intro i
      funext l
      have := hU' u⁻¹ (U.inv_mem hu) i (h * ((u : Ga), 1)) l
      rw [← this]
      have hh : h * ((u : Ga), 1) * (((u⁻¹ : X.Ub) : Ga), (1 : Gp)) = h := by
        ext <;> simp
      simp only [Matrix.mulVec, dotProduct, hh]
      rfl
    have e : X.unt m W F i (h * ((u : Ga), 1)) k =
        ((Matrix.of fun a b => algebraMap O Ω (((τ u⁻¹ : GL _ O) : Matrix (Fin m) (Fin m) O) a b)) *ᵥ
          fun j => X.unt m W F j h k) i := by
      simp only [Frame.unt_apply, Prod.snd_mul, mul_one, hv, Matrix.mulVec, dotProduct, Finset.mul_sum,
        Matrix.of_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact detd_mulVec Λ _ (fun a b => ⟨_, rfl⟩) _ (fun j => hG j k) i
  have stepG : ∀ γ h, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (X.glob γ * h) k ∈ Λ := by
    intro γ h hG i k
    have e : X.unt m W F i (X.glob γ * h) = X.unt m W F i h := by
      rw [Frame.unt_apply, Frame.unt_apply, hA' i γ h]
      simp [Prod.snd_mul, Matrix.mulVec_mulVec, _root_.mul_inv_rev, mul_assoc]
    rw [e]
    exact hG i k
  show ∀ i g k, X.unt m W F i g k ∈ Λ
  intro i g k
  obtain ⟨γ, n, u, hu, b, hb, rfl⟩ := hx g
  obtain ⟨y1, hy1, t, ht, y2, hy2, rfl⟩ := ((iwMem Gp X.I c b).1).1 hb
  have eq : X.glob γ * x n * ((u : Ga), y1 * t * y2) =
      X.glob γ * (x n * ((u : Ga), 1) * (1, y1) * (1, t) * (1, y2)) := by
    ext <;> simp [mul_assoc]
  rw [eq]
  exact stepG γ _ (stepM _ y2 hy2 (stepT _ t ht (stepN _ y1 hy1
    (stepU _ u hu (fun i k => hΛ n i k))))) i k
end

section

open IsLocalRing UpperTheory.V.Hi UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

open TensorProduct in
private theorem UpperTheory.pi_scalar_right_tmul {O Ω ι : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    [Fintype ι] [DecidableEq ι] (a : Ω) (v : ι → O) :
    TensorProduct.piScalarRight O Ω Ω ι (a ⊗ₜ v) = a • fun i => algebraMap O Ω (v i) := by
  ext i
  simp [Algebra.smul_def, mul_comm]

private theorem UpperTheory.map_max_gen_eigenspace_of_intertwine {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (E : V ≃ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ x, g (E x) = E (f x)) (μ : K) :
    (f.maxGenEigenspace μ).map E.toLinearMap = g.maxGenEigenspace μ := by
  have hp : ∀ (k : ℕ) x, ((g - μ • 1) ^ k) (E x) = E (((f - μ • 1) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
      simp [h]
  ext y
  obtain ⟨x, rfl⟩ := E.surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Module.End.mem_maxGenEigenspace,
    Module.End.mem_maxGenEigenspace]
  simp only [hp, EmbeddingLike.map_eq_zero_iff]

theorem UpperTheory.span_ordinaryPart_eq_sup_unit_generalized_eigenspaces :
    ∀ (O Ω ι : Type) [CommRing O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] [Fintype ι] (T₀ : Module.End O (ι → O)) (T : Module.End Ω (ι → Ω)), (∀ v, T (fun i => algebraMap O Ω (v i)) = fun i => algebraMap O Ω (T₀ v i)) → ⨆ μ : {μ : Ω // IsIntUnit O μ}, T.maxGenEigenspace μ.1 = Submodule.span Ω ((fun (v : ι → O) i => algebraMap O Ω (v i)) '' (ordPart T₀ : Set (ι → O))) := by
  intro O Ω ι _ hO _ _ _ _ T₀ T hT
  classical
  haveI : IsAdicComplete (maximalIdeal O) O := hO.complete
  have hadm := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordAdm_maximalIdeal_and_finite_quotients (R := O) (M := ι → O)).1
  have hex := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hadm T₀
  have key := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt (K := Ω) hex.1
  set E := TensorProduct.piScalarRight O Ω Ω ι with hE
  have hEt : ∀ (a : Ω) (v : ι → O),
      E (a ⊗ₜ v) = a • fun i => algebraMap O Ω (v i) := UpperTheory.pi_scalar_right_tmul
  have hc : ∀ x, T (E x) = E (T₀.baseChange Ω x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rw [LinearMap.baseChange_tmul, hEt, hEt, map_smul, hT]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 := congrArg (Submodule.map E.toLinearMap) key
  simp only [Submodule.map_iSup, UpperTheory.map_max_gen_eigenspace_of_intertwine E _ T hc] at h1
  rw [iSup_subtype]
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEt]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      rw [← hex.2.1]
      exact ⟨v, rfl⟩
    | add x y hx hy => simp only [map_add] at ⊢; exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    rw [← hex.2.1] at hv
    obtain ⟨w, rfl⟩ := hv
    refine ⟨_, ⟨(1 : Ω) ⊗ₜ w, rfl⟩, ?_⟩
    rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEt, one_smul]
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.mem_valIn_of_invariant_and_values_mem_pow :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (k c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → ∀ f ∈ X.Sp τ θ U, (∀ y ∈ X.I.Nm c, X.rp A m y f - f ∈ X.valIn A m k) → (∀ i j, f (x i) j ∈ maximalIdeal A ^ k) → f ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ U k c N x hx f hf hy h0
  have hv : ∀ F : X.Fn A m, F ∈ X.valIn A m k ↔ ∀ g i, F g i ∈ maximalIdeal A ^ k := fun F => by
    simp [Frame.valIn, Submodule.mem_pi]
  have hrp : ∀ (b : Gp) (g : Ga × Gp), X.rp A m b f g = f (g * (1, b)) := fun _ _ => rfl
  obtain ⟨⟨h1, h2, h3, -⟩, h4⟩ := hf
  rw [hv]
  intro g
  obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hx g
  obtain ⟨n, hn, t, ht, y, hy', rfl⟩ := (iwMem Gp X.I c b).1.1 hb
  have a1 : ∀ j, f (x i * ((u : Ga), 1)) j ∈ maximalIdeal A ^ k := by
    intro j
    have e := congrFun (h4 u⁻¹ (inv_mem hu)) (x i * ((u : Ga), 1))
    rw [Frame.ra_apply] at e
    have e2 : x i * ((u : Ga), (1 : Gp)) * (((u⁻¹ : X.Ub) : Ga), (1 : Gp)) = x i := by
      ext <;> simp
    rw [← e, e2]
    simp only [mulVec, dotProduct]
    exact Submodule.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (h0 _ l)
  have a2 : ∀ j, f (x i * ((u : Ga), 1) * (1, n)) j ∈ maximalIdeal A ^ k := by
    intro j
    rw [← hrp, h2 n hn]
    exact a1 j
  have a3 : ∀ j, f (x i * ((u : Ga), 1) * (1, n) * (1, t)) j ∈ maximalIdeal A ^ k := by
    intro j
    rw [← hrp, h3 ⟨t, ht⟩]
    exact Ideal.mul_mem_left _ _ (a2 j)
  intro j
  have a4 := add_mem ((hv _).1 (hy y hy') (x i * ((u : Ga), 1) * (1, n) * (1, t)) j) (a3 j)
  rw [Pi.sub_apply, Pi.sub_apply, sub_add_cancel, hrp] at a4
  rw [mul_assoc, h1]
  convert a4 using 2
  ext <;> simp [mul_assoc]
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem torus_uniq {G : Type} [Group G] (I : Iwa G) {y y' x x' : G} {t t' : I.T} (hy : y ∈ I.Nm 0)
    (hy' : y' ∈ I.Nm 0) (hx : x ∈ I.N) (hx' : x' ∈ I.N) (h : y * t * x = y' * t' * x') : t' = t := by
  have h1 : x = (t : G)⁻¹ * y⁻¹ * (y' * t' * x') := by rw [← h]; group
  have h0 := (I.uniq (x * x'⁻¹) (I.N_le (mul_mem hx (inv_mem hx'))) ((t' : G)⁻¹ * t)
    (I.T_le (mul_mem (inv_mem t'.2) t.2)) ((t : G)⁻¹ * (y'⁻¹ * y) * (t : G)⁻¹⁻¹)
    (I.T_Nm 0 _ (inv_mem t.2) _ (mul_mem (inv_mem hy') hy)) (by rw [h1]; group)).2
  exact Subtype.ext (inv_mul_eq_one.1 h0)

private theorem torus_ex {G : Type} [Group G] (I : Iwa G) {b : G} (hb : b ∈ I.Iw 0) :
    ∃ t : I.T, ∃ y ∈ I.Nm 0, ∃ x ∈ I.N, b = y * t * x := by
  obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I 0 b⁻¹).1.1 (inv_mem hb)
  refine ⟨⟨t⁻¹, inv_mem ht⟩, y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, ?_⟩
  rw [← inv_inv b, h]
  group

private theorem torus_fn {G : Type} [Group G] (I : Iwa G) :
    ∃ tt : G → I.T, ∀ (t : I.T), ∀ y ∈ I.Nm 0, ∀ x ∈ I.N, tt (y * t * x) = t := by
  classical
  refine ⟨fun b => if h : ∃ t : I.T, ∃ y ∈ I.Nm 0, ∃ x ∈ I.N, b = y * t * x then h.choose else 1, ?_⟩
  intro t y hy x hx
  have h : ∃ t' : I.T, ∃ y' ∈ I.Nm 0, ∃ x' ∈ I.N, y * t * x = y' * t' * x' := ⟨t, y, hy, x, hx, rfl⟩
  simp only [dif_pos h]
  obtain ⟨y', hy', x', hx', e⟩ := h.choose_spec
  exact torus_uniq I hy hy' hx hx' e

theorem UpperTheory.exists_iwahori_torus_projection :
    ∀ (G : Type) [Group G] (I : Iwa G), ∃ tt : G → I.T, tt 1 = 1 ∧ ∀ b ∈ I.Iw 0, (∀ s : I.T, tt (s * b) = s * tt b ∧ tt (b * s) = tt b * s) ∧ (∀ x ∈ I.N, tt (b * x) = tt b) ∧ ∀ c, ∀ y ∈ I.Nm c, ∃ s : I.T, (s : G) ∈ I.Tc c ∧ tt (b * y) = tt b * s := by
  intro G _ I
  obtain ⟨tt, htt⟩ := torus_fn I
  refine ⟨tt, by simpa using htt 1 1 (one_mem _) 1 (one_mem _), fun b hb => ?_⟩
  obtain ⟨t, y, hy, x, hx, rfl⟩ := torus_ex I hb
  rw [htt t y hy x hx]
  refine ⟨fun s => ⟨?_, ?_⟩, fun x' hx' => ?_, fun c y' hy' => ?_⟩
  · rw [← htt (s * t) _ (I.T_Nm 0 s s.2 y hy) x hx]
    congr 1
    rw [Subgroup.coe_mul]
    group
  · rw [← htt (t * s) y hy _ (I.T_N _ (inv_mem s.2) x hx)]
    congr 1
    rw [Subgroup.coe_mul]
    group
  · rw [mul_assoc]
    exact htt t y hy _ (mul_mem hx hx')
  · obtain ⟨x2, hx2, s, hs, y2, hy2, h⟩ := I.swap c y'⁻¹ (inv_mem hy') x⁻¹ (inv_mem hx)
    refine ⟨⟨s⁻¹, inv_mem (I.Tc_le c hs)⟩, inv_mem hs, ?_⟩
    rw [← htt (t * ⟨s⁻¹, inv_mem (I.Tc_le c hs)⟩) _
      (mul_mem hy (I.T_Nm 0 t t.2 _ (inv_mem (I.Nm_anti (Nat.zero_le c) hy2)))) _ (inv_mem hx2)]
    congr 1
    have e : x * y' = (x2 * s * y2)⁻¹ := by rw [← h]; group
    rw [mul_assoc, e, Subgroup.coe_mul]
    group
end
