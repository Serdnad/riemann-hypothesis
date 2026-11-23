module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle005
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

noncomputable section

open Formalism.REAL

namespace PositivityTheory.Rg.Cz

namespace WQ

section Alg

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

theorem qdet_map (f : A →ₐ[ℂ] B) {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    f (qdet E u) = qdet (fun a b => f (E a b)) u := by
  unfold qdet qminor

  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
  simp only [Function.comp, Tm, map_add (f := _), apply_ite f, map_zero, AlgHom.commutes]

theorem glRel_map (f : A →ₐ[ℂ] B) {n : ℕ} {E : Fin n → Fin n → A} (h : GlRel E) : GlRel fun a b => f (E a b) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simpa [map_sub, map_mul, apply_ite f] using this

theorem glRel_of_inj (f : A →ₐ[ℂ] B) (hf : Function.Injective f) {n : ℕ} {E : Fin n → Fin n → A}
    (h : GlRel fun a b => f (E a b)) : GlRel E := by
  intro a b c d
  apply hf
  simpa [map_sub, map_mul, apply_ite f] using h a b c d

theorem comm_qdet {n : ℕ} (E : Fin n → Fin n → A) (x : A) (h : ∀ a b, Commute x (E a b)) (u : ℂ) :
    Commute x (qdet E u) := by
  unfold qdet qminor
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Tm
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_right _ _
  · exact Commute.zero_right _

end Alg

section Quot

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {X | ∀ y ∈ N, X y ∈ N}
  mul_mem' hX hY y hy := hX _ (hY y hy)
  add_mem' hX hY y hy := N.add_mem (hX y hy) (hY y hy)
  algebraMap_mem' c y hy := by simpa [Module.algebraMap_end_apply] using N.smul_mem c hy

def qmap (N : Submodule ℂ M) : stab N →ₐ[ℂ] Module.End ℂ (M ⧸ N) where
  toFun X := N.mapQ N X.1 (fun y hy => X.2 y hy)
  map_one' := by ext y; simp
  map_mul' X Y := by ext y; simp
  map_zero' := by ext y; simp
  map_add' X Y := by ext y; simp
  commutes' c := by ext y; simp [Module.algebraMap_end_apply]

end Quot

end WQ

open WQ

theorem wallQuot_of (hQ : QdetFacts) : WallQuot := by
  intro n M _ _ ι E hgl hcomm l φ hφ
  let N : Submodule ℂ M :=
    { carrier := {y | ∀ w ∈ envAlg E, φ (w y) = 0}
      add_mem' := fun {x y} hx hy w hw => by
        show φ (w (x + y)) = 0
        rw [map_add (f := _), map_add (f := _), hx w hw, hy w hw, add_zero]
      zero_mem' := fun w _ => by simp
      smul_mem' := fun c y hy w hw => by
        show φ (w (c • y)) = 0
        rw [map_smul, map_smul, hy w hw, smul_zero] }
  have hgen : ∀ τ a b, E τ a b ∈ envAlg E := fun τ a b => Algebra.subset_adjoin ⟨τ, a, b, rfl⟩
  have hstab : ∀ τ a b, E τ a b ∈ stab N := fun τ a b y hy w hw =>
    hy (w * E τ a b) (Subalgebra.mul_mem _ hw (hgen τ a b))
  let E' : ι → Fin n → Fin n → stab N := fun τ a b => ⟨E τ a b, hstab τ a b⟩
  let F : ι → Fin n → Fin n → Module.End ℂ (M ⧸ N) := fun τ a b => qmap N (E' τ a b)
  have hgl' : ∀ τ, GlRel (E' τ) := fun τ => glRel_of_inj (stab N).val Subtype.val_injective (hgl τ)
  have hcent : ∀ τ (u : ℂ), ∀ w ∈ envAlg E, Commute w (qdet (E τ) u) := by
    intro τ u w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨τ', a, b, rfl⟩ := hx
      by_cases h : τ' = τ
      · subst h
        exact ((hQ n M (E τ') (hgl τ')).1 u a b).symm
      · exact comm_qdet _ _ (fun c d => hcomm τ' τ h a b c d) u
    | algebraMap c => exact Algebra.commute_algebraMap_left _ _
    | add x y _ _ hx hy => exact hx.add_left hy
    | mul x y _ _ hx hy => exact hx.mul_left hy
  have hq : ∀ τ (u : ℂ) y, qdet (F τ) u (N.mkQ y) = N.mkQ (qdet (E τ) u y) := by
    intro τ u y
    rw [show qdet (F τ) u = qmap N (qdet (E' τ) u) from (qdet_map _ _ _).symm,
      show qdet (E τ) u = (stab N).val (qdet (E' τ) u) from (qdet_map (stab N).val (E' τ) u).symm]
    rfl
  refine ⟨N, F, fun τ => glRel_map (qmap N) (hgl' τ), fun τ τ' h a b c d => ?_, fun τ u => ?_,
    fun τ a b => LinearMap.ext fun y => rfl, fun y => Iff.rfl⟩
  · exact (show Commute (E' τ a b) (E' τ' c d) from Subtype.ext (hcomm τ τ' h a b c d).eq).map (qmap N)
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq, Module.algebraMap_end_apply, ← N.mkQ.map_smul,
      Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    intro w hw
    show φ (w (qdet (E τ) u y - (∏ k, (u + l τ k)) • y)) = 0
    have hc := congrArg (fun T : Module.End ℂ M => φ (T y)) (hcent τ u w hw).eq
    simp only [Module.End.mul_apply] at hc
    have h2 := LinearMap.congr_fun (hφ τ u) (w y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h2
    rw [map_sub, map_sub, map_smul, map_smul, hc, h2, sub_self]

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace LieInverse

theorem exists_ne_of_ne_one {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (i : Fin n) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra h
  push Not at h
  apply hσ
  have hi : σ i = i := by
    by_contra hne
    have := h (σ i) hne
    exact hne (σ.injective this)
  ext j
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [h j hj]

theorem hasDerivAt_det {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : A 0 = 1) (hA : ∀ i j, HasDerivAt (fun t => A t i j) (Y i j) 0) :
    HasDerivAt (fun t => (A t).det) Y.trace 0 := by
  have key : ∀ σ : Equiv.Perm (Fin n), HasDerivAt (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, A 0 (σ j) j) * Y (σ i) i) 0 := by
    intro σ
    have := (HasDerivAt.finsetProd (u := Finset.univ) (fun i _ => hA (σ i) i)).const_mul
      ((Equiv.Perm.sign σ : ℤ) : ℂ)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [Finset.prod_apply]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun σ _ => key σ)
  refine (hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp [Matrix.det_apply', Finset.sum_apply]
  · simp only [Finset.mul_sum, smul_eq_mul]
    rw [Finset.sum_comm, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp [h0]
    · intro σ _ hσ
      obtain ⟨j, hji, hj⟩ := exists_ne_of_ne_one σ hσ i
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) (by rw [h0]; exact Matrix.one_apply_ne hj)]
      simp
    · simp

def Sop {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ M :=
  ∑ a, ∑ b, (X a b • E τ a b + star (X a b) • E (bar τ) a b)

theorem Sop_add {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (bar : ι → ι) (τ : ι) (X Y : Matrix (Fin n) (Fin n) ℂ) : Sop E bar τ (X + Y) = Sop E bar τ X + Sop E bar τ Y := by
  simp only [Sop, Matrix.add_apply, add_smul, star_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by abel

theorem Sop_single {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : ι → Fin n → Fin n → Module.End ℂ M) (bar : ι → ι) (τ : ι) (p q : Fin n) (z : ℂ) :
    Sop E bar τ (Matrix.single p q z) = z • E τ p q + star z • E (bar τ) p q := by
  unfold Sop
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp [Matrix.single_apply]
  · intro b _ hb; simp [Matrix.single_apply, hb, Ne.symm hb]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => by simp [Matrix.single_apply, ha, Ne.symm ha]
  · simp

end LieInverse

open LieInverse in
theorem lieInv_holds : LieInv := by
  intro n M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG c ξ hξ τ a b
  have hbt : bar τ ≠ τ := hK.ne τ
  have hD : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X →
      Sop E bar τ X ξ = ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) • ξ := by
    intro X hX
    obtain ⟨cv, hc0, hcd, hcoth, hρ⟩ := hG.der τ X hX
    let D : ι → ℂ := fun τ' => if τ' = τ then X.trace else if τ' = bar τ then star X.trace else 0
    have hdet : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det) (D τ') 0 := by
      intro τ'
      by_cases h1 : τ' = τ
      · subst h1
        simp only [D, if_true]
        exact hasDerivAt_det _ X (by rw [hc0, hK.one]) hcd
      · by_cases h2 : τ' = bar τ
        · subst h2
          simp only [D, if_neg h1, if_true]
          have ht : (X.map star).trace = star X.trace := by simp [Matrix.trace, star_sum]
          rw [← ht]
          refine hasDerivAt_det _ _ (by rw [hc0, hK.one]) fun i j => ?_
          simp only [hK.conj, Matrix.map_apply]
          exact (hcd i j).star
        · simp only [D, if_neg h1, if_neg h2]
          have hf : (fun t => (κ τ' (cv t)).det) = fun _ => 1 := by
            funext t; rw [hcoth τ' h1 h2 t, Matrix.det_one]
          rw [hf]; exact hasDerivAt_const _ _
    have h1 : ∀ τ', (κ τ' (cv 0)).det = 1 := fun τ' => by rw [hc0, hK.one, Matrix.det_one]
    have hz : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det ^ c τ') ((c τ' : ℂ) * D τ') 0 := by
      intro τ'
      have := (hasDerivAt_zpow (c τ') ((κ τ' (cv 0)).det) (Or.inl (by rw [h1]; exact one_ne_zero))).comp
        (0 : ℝ) (hdet τ')
      rw [h1, _root_.one_zpow, mul_one] at this
      exact this
    have hχ : HasDerivAt (fun t => ∏ τ', (κ τ' (cv t)).det ^ c τ')
        ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) 0 := by
      have := HasDerivAt.finsetProd (u := Finset.univ) (fun τ' _ => hz τ')
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp [Finset.prod_apply])).congr_deriv ?_
      simp only [h1, _root_.one_zpow, Finset.prod_const_one, one_smul]
      rw [Finset.sum_eq_add_of_mem τ (bar τ) (Finset.mem_univ _) (Finset.mem_univ _) hbt.symm]
      · simp [D, hbt]
      · intro x _ hx; simp [D, hx.1, hx.2]
    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro lam
    have h2 : HasDerivAt (fun t => lam (ρ (cv t) ξ))
        (((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) * lam ξ) 0 := by
      refine (hχ.mul_const (lam ξ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [hξ, map_smul, smul_eq_mul]
    have hu : lam (Sop E bar τ X ξ) = _ := (hρ ξ lam).unique h2
    rw [map_sub, hu, map_smul, smul_eq_mul, sub_self]
  have hsI : star Complex.I = -Complex.I := Complex.conj_I
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have hX : (Matrix.single a a Complex.I)ᴴ = -Matrix.single a a Complex.I := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.single_apply]
      split_ifs with h1 h2 h2
      · simp [hsI]
      · exact (h2 ⟨h1.2, h1.1⟩).elim
      · exact (h1 ⟨h2.2, h2.1⟩).elim
      · simp
    have e := hD _ hX
    rw [Sop_single, Matrix.trace_single_eq_same, hsI] at e
    have e' : Complex.I • (E τ a a ξ - E (bar τ) a a ξ - ((c τ - c (bar τ) : ℤ) : ℂ) • ξ) = 0 := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply] at e
      push_cast
      linear_combination (norm := module) e
    rcases smul_eq_zero.mp e' with h | h
    · exact absurd h Complex.I_ne_zero
    · exact sub_eq_zero.mp h
  · rw [if_neg hab]
    have hX1 : (Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))ᴴ =
        -(Matrix.single a b (1 : ℂ) + Matrix.single b a (-1)) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    have hX2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
        -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    have e1 := hD _ hX1
    have e2 := hD _ hX2
    rw [Sop_add, Sop_single, Sop_single, Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ hab,
      Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)] at e1 e2
    simp only [LinearMap.add_apply, LinearMap.smul_apply, add_zero, star_zero, mul_zero, zero_smul, hsI,
      star_one, star_neg] at e1 e2
    have e2' : Complex.I • (E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ) = 0 := by
      linear_combination (norm := module) e2
    have e3 : E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ = 0 :=
      (smul_eq_zero.mp e2').resolve_left Complex.I_ne_zero
    linear_combination (norm := module) (1 / 2 : ℂ) • e1 + (1 / 2 : ℂ) • e3

end PositivityTheory.Rg.Cz

end
end
