module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvIrrPre
public import Development.DiscreteGroups.GlobalIrreducibility.MulRowOfGood
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKMCore
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open ValuativeRel

namespace DiscreteGroups.sglob.LConv

theorem countable_quotient_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace.SeparableSpace G] (K : Subgroup G) (hK : IsOpen (K : Set G)) : Countable (G ⧸ K) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable D := hDc.to_subtype
  refine Function.Surjective.countable (f := fun d : D => ((d : G) : G ⧸ K)) fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have ho : IsOpen ((fun x => x⁻¹ * g) ⁻¹' (K : Set G)) := hK.preimage (continuous_inv.mul continuous_const)
  obtain ⟨d, hd, hdD⟩ := hDd.inter_open_nonempty _ ho ⟨g, by simp⟩
  exact ⟨⟨d, hdD⟩, QuotientGroup.eq.2 hd⟩

theorem separableSpace_GL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m : ℕ) : TopologicalSpace.SeparableSpace (GL (Fin m) k) := by
  have : SecondCountableTopology (GL (Fin m) k) := inferInstance
  infer_instance

theorem unitOfUnif : UnitOfUnif := by
  intro hAlt hFin hUnif k _ _ _ _ m K hKo hKc H _ _ _ π hπ hcomm
  have := separableSpace_GL k m
  obtain ⟨N, hN⟩ := hUnif k m K hKo
  let F : Submodule ℂ H :=
    { carrier := {x | ∀ κ ∈ K, π κ x = x}
      add_mem' := fun {a b} ha hb κ hκ => by rw [map_add (f := _), ha κ hκ, hb κ hκ]
      zero_mem' := fun κ _ => map_zero _
      smul_mem' := fun c x hx κ hκ => by rw [map_smul, hx κ hκ] }
  have hF : IsClosed (F : Set H) := by
    have : (F : Set H) = ⋂ κ ∈ K, {x | π κ x = x} := by
      ext x
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_biInter fun κ _ => isClosed_eq (π κ).continuous continuous_id
  have : CompleteSpace F := hF.completeSpace_coe
  have h1 : ∀ x, F.starProjection x ∈ F := fun x => F.starProjection_apply_mem x
  have h2 : ∀ x ∈ F, F.starProjection x = x := fun x hx => Submodule.starProjection_eq_self_iff.2 hx
  obtain ⟨s, hs⟩ := hFin _ H π hπ hcomm F.starProjection (by ext x; exact h2 _ (h1 x)) (N ^ 2 + 1)
    (hAlt _ K hKo hKc (countable_quotient_of_isOpen K hKo) N hN H π hπ F.starProjection
      (isSelfAdjoint_starProjection F) h1 h2 _ (Nat.lt_succ_self _))
  exact ⟨s, fun x hx => h2 x hx ▸ hs x⟩

end DiscreteGroups.sglob.LConv

end
end

section

namespace DiscreteGroups.sglob.LConv

theorem extremeExists : ExtremeExists := by
  intro G M _ _ _ ρ hspan B₀ hB₀ f hf
  obtain ⟨B, ⟨hB, hext⟩, hBf⟩ := DiscreteGroups.sglob.LConvKM.extreme_exists_core ρ hspan B₀ hB₀ f hf
  exact ⟨B, ⟨hB, hext⟩, hBf⟩

end DiscreteGroups.sglob.LConv
end

section

noncomputable section

open scoped InnerProductSpace
open UniformSpace

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

theorem comm_apply {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {S T : E →L[ℂ] E}
    (h : S * T = T * S) (v : E) : S (T v) = T (S v) := by
  have := congrArg (fun A : E →L[ℂ] E => A v) h
  exact this

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)

def formOf (S : Hs B hB →L[ℂ] Hs B hB) : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ⟪iota B hB x, S (iota B hB y)⟫_ℂ)
    (fun x₁ x₂ y => by simp [map_add (f := _), inner_add_left])
    (fun c x y => by simp [map_smul, inner_smul_left])
    (fun x y₁ y₂ => by simp [map_add (f := _), inner_add_right])
    (fun c x y => by simp [map_smul, inner_smul_right])

theorem formOf_apply (S : Hs B hB →L[ℂ] Hs B hB) (x y : M) :
    formOf B hB S x y = ⟪iota B hB x, S (iota B hB y)⟫_ℂ := rfl

variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

theorem scalar_sa (hext : IsExtremeForm ρ B) (S : Hs B hB →L[ℂ] Hs B hB) (hS : IsSelfAdjoint S)
    (hc : ∀ g, S * pi B hB ρ hinv g = pi B hB ρ hinv g * S) : ∃ c : ℂ, S = c • 1 := by
  set a : ℝ := (2 * (‖S‖ + 1))⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have hsym : ∀ u v, ⟪S u, v⟫_ℂ = ⟪u, S v⟫_ℂ := fun u v => by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hS.star_eq]
  have hherm : ∀ x y, starRingEnd ℂ (formOf B hB S x y) = formOf B hB S y x := fun x y => by
    rw [formOf_apply, formOf_apply, inner_conj_symm, hsym]
  have hinvQ : ∀ g x y, formOf B hB S (ρ g x) (ρ g y) = formOf B hB S x y := fun g x y => by
    rw [formOf_apply, formOf_apply, ← pi_iota B hB ρ hinv, ← pi_iota B hB ρ hinv, comm_apply (hc g), pi_inner]
  have hbd : ∀ x, |(formOf B hB S x x).re| ≤ ‖S‖ * ‖iota B hB x‖ ^ 2 := fun x => by
    rw [formOf_apply]
    calc _ ≤ ‖⟪iota B hB x, S (iota B hB x)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖iota B hB x‖ * ‖S (iota B hB x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖iota B hB x‖ * (‖S‖ * ‖iota B hB x‖) := by gcongr; exact S.le_opNorm _
      _ = _ := by ring
  have key : ∀ x, |a * (formOf B hB S x x).re| ≤ (B x x).re / 2 := fun x => by
    rw [re_B B hB, abs_mul, abs_of_pos ha]
    calc a * |(formOf B hB S x x).re| ≤ a * ((‖S‖ + 1) * ‖iota B hB x‖ ^ 2) := by
          gcongr; exact (hbd x).trans (by gcongr; linarith)
      _ = _ := by rw [ha_def]; field_simp
  have h1 : IsInvForm ρ (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S) := by
    refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    · rw [map_add (f := _), map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]
    · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have := abs_le.1 (key x); linarith
    · rw [hext.1.2.2, hinvQ]
  have h2 : IsInvForm ρ (B - (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S)) := by
    refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    · rw [map_sub, map_add (f := _), map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]
    · rw [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have := abs_le.1 (key x); linarith
    · rw [hext.1.2.2, hinvQ]
  obtain ⟨c, hc'⟩ := hext.2 _ h1 h2
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hQ : ∀ x y, formOf B hB S x y = ((a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))) * B x y := fun x y => by
    have h := hc' x y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ ha']
    linear_combination h
  set d := (a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))
  have hQ' : ∀ x y : M, ⟪iota B hB x, S (iota B hB y)⟫_ℂ = d * ⟪iota B hB x, iota B hB y⟫_ℂ := fun x y => by
    rw [inner_iota, ← formOf_apply]; exact hQ x y
  have hall : ∀ u v : Hs B hB, ⟪u, S v⟫_ℂ = d * ⟪u, v⟫_ℂ := by
    intro u v
    refine Completion.induction_on₂ u v ?_ fun p q => ?_
    · exact isClosed_eq (continuous_fst.inner (S.continuous.comp continuous_snd))
        (continuous_const.mul (continuous_fst.inner continuous_snd))
    · exact hQ' p q
  refine ⟨d, ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_⟩
  rw [hall, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]

theorem commutant (hext : IsExtremeForm ρ B) (T : Hs B hB →L[ℂ] Hs B hB)
    (hT : ∀ g, T * pi B hB ρ hinv g = pi B hB ρ hinv g * T) : ∃ c : ℂ, T = c • 1 := by
  have hT' : ∀ g, star T * pi B hB ρ hinv g = pi B hB ρ hinv g * star T := fun g => by
    have h := congrArg star (hT g⁻¹)
    simp only [star_mul, star_pi, inv_inv] at h
    exact h.symm
  have hre : ∀ g, (realPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g =
      pi B hB ρ hinv g * realPart T := fun g => by
    simp only [realPart_apply_coe, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hT, hT']
  have him : ∀ g, (imaginaryPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g =
      pi B hB ρ hinv g * imaginaryPart T := fun g => by
    simp only [imaginaryPart_apply_coe, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, hT, hT']
  obtain ⟨c₁, h₁⟩ := scalar_sa B hB ρ hinv hext _ (realPart T).prop hre
  obtain ⟨c₂, h₂⟩ := scalar_sa B hB ρ hinv hext _ (imaginaryPart T).prop him
  refine ⟨c₁ + Complex.I * c₂, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [h₁, h₂, smul_smul, add_smul]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
end
end

section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem good_colU (j : ℕ) (c : Fin n → k) : Good j ((colU j c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  rw [val_colU, Matrix.add_apply, colM_apply, if_neg (by omega), add_zero]

theorem good_colU_inv (j : ℕ) (c : Fin n → k) :
    Good j (((colU j c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [colU_inv]; exact good_colU j _

theorem peel_apply (j : ℕ) (hj : j < n) (g : GL (Fin n) k) (i l : Fin n) :
    ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l =
      (g : Matrix (Fin n) (Fin n) k) i l + (if i.val < j then
        -(g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ * (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l else 0) := by
  rw [Units.val_mul, colU_mul_apply j hj]
  rfl

theorem peel_N (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) {g : GL (Fin n) k} (hg : g ∈ Nset j) :
    colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g ∈ Nset (j + 1) ∧
    sdS j (g : Matrix (Fin n) (Fin n) k) =
      sdS (j + 1) ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) + (g : Matrix (Fin n) (Fin n) k) ⟨j - 1, by omega⟩ ⟨j, hj⟩ := by
  have hg' : ∀ i l : Fin n, (l ≤ i ∨ l.val < j) → (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := hg
  have hjj : (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ ⟨j, hj⟩ = 1 := by rw [hg' _ _ (Or.inl le_rfl), one_apply_eq]
  have hrow : ∀ l : Fin n, l.val < j → (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l = 0 := fun l hl => by
    rw [hg' _ _ (Or.inr hl), one_apply_ne]; intro h; rw [← h] at hl; simp at hl
  have hhi : ∀ i l : Fin n, j ≤ i.val → ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) i l = (g : Matrix (Fin n) (Fin n) k) i l := fun i l hi => by
    rw [peel_apply, if_neg (by omega), add_zero]
  refine ⟨fun i l hil => ?_, ?_⟩
  · rw [peel_apply]
    by_cases hl : l.val < j
    · rw [hg' i l (Or.inr hl), hrow l hl]; simp
    · by_cases hlj : l.val = j
      · have hl' : l = ⟨j, hj⟩ := Fin.ext hlj
        subst hl'
        by_cases hi : i.val < j
        · rw [if_pos hi, hjj, mul_one, add_neg_cancel, one_apply_ne]
          intro h; rw [h] at hi; simp at hi
        · rw [if_neg hi, add_zero]
          exact hg' i _ (Or.inl (by rw [Fin.le_iff_val_le_val]; simp; omega))
      · have hli : l ≤ i := hil.resolve_right (by omega)
        rw [if_neg (by rw [Fin.le_iff_val_le_val] at hli; omega), add_zero]
        exact hg' i l (Or.inl hli)
  · have key : ∀ i l : Fin n, (if l.val = i.val + 1 ∧ j ≤ l.val then (g : Matrix (Fin n) (Fin n) k) i l else 0) =
        (if l.val = i.val + 1 ∧ j + 1 ≤ l.val then ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k) i l else 0) +
        (if i = (⟨j - 1, by omega⟩ : Fin n) then (if l = (⟨j, hj⟩ : Fin n) then (g : Matrix (Fin n) (Fin n) k) i l else 0) else 0) := by
      intro i l
      by_cases h2 : l.val = i.val + 1 ∧ j + 1 ≤ l.val
      · rw [if_pos ⟨h2.1, by omega⟩, if_pos h2, hhi i l (by omega),
          if_neg (fun h => by rw [Fin.ext_iff] at h; simp at h; omega), add_zero]
      · rw [if_neg h2, zero_add]
        by_cases h1 : l.val = i.val + 1 ∧ j ≤ l.val
        · have e1 : i = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
          have e2 : l = ⟨j, hj⟩ := Fin.ext (by simp; omega)
          rw [if_pos h1, if_pos e1, if_pos e2]
        · rw [if_neg h1]
          by_cases e1 : i = ⟨j - 1, by omega⟩
          · by_cases e2 : l = ⟨j, hj⟩
            · exfalso; apply h1; rw [e1, e2]; simp; omega
            · rw [if_pos e1, if_neg e2]
          · rw [if_neg e1]
    rw [sdS, sdS]
    simp only [key, Finset.sum_add_distrib]
    congr 1
    simp

end DiscreteGroups.sglob.LConvGenM
end
end
