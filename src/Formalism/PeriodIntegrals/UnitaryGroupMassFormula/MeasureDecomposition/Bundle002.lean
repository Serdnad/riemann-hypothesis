module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem generic_haar_subgroup : GenHaarSub := by
  intro G _ _ _ _ _ _ _ _ K hK
  haveI : LocallyCompactSpace K := hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hm : haarSub K hK = (Measure.haar : Measure K).map Subtype.val := rfl
  have hmeas : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  have hcpt : ∀ C : Set G, IsCompact C → haarSub K hK C < ⊤ := by
    intro C hC
    rw [hm, Measure.map_apply hmeas hC.isClosed.measurableSet]
    exact (hK.isClosedEmbedding_subtypeVal.isCompact_preimage hC).measure_lt_top
  haveI : IsFiniteMeasureOnCompacts (haarSub K hK) := ⟨hcpt⟩
  refine ⟨inferInstance, ?_, ?_, ?_, hcpt, ?_⟩
  · intro h0
    rw [hm, Measure.map_eq_zero_iff hmeas.aemeasurable] at h0
    exact isOpen_univ.measure_ne_zero (Measure.haar : Measure K) Set.univ_nonempty (by simp [h0])
  · rw [hm, Measure.map_apply hmeas hK.isOpen_compl.measurableSet]
    have hpre : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false,
        iff_false, not_not]
      exact x.2
    rw [hpre, measure_empty]
  · intro s hs
    rw [hm, Measure.map_map (measurable_const_mul s) hmeas]
    have hcomp : (fun x => s * x) ∘ (Subtype.val : K → G) =
        Subtype.val ∘ (fun y : K => (⟨s, hs⟩ : K) * y) := by
      funext y
      rfl
    rw [hcomp, ← Measure.map_map hmeas (measurable_const_mul _)]
    congr 1
    first
      | exact map_mul_left_eq_self (Measure.haar : Measure K) _
      | exact Measure.IsMulLeftInvariant.map_mul_left_eq_self _
  · intro U hU h1
    rw [hm, Measure.map_apply hmeas hU.measurableSet]
    exact (hU.preimage continuous_subtype_val).measure_pos (Measure.haar : Measure K) ⟨1, by simpa using h1⟩

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PI.ScMuExists.UnitaryGroupMassFormula

instance instSFiniteMuInf (I : Formalism.MainNotions.S.AutInst) : SFinite (muInf I) := by
  unfold muInf; infer_instance

instance instLeftInvMuInf (I : Formalism.MainNotions.S.AutInst) : (muInf I).IsMulLeftInvariant := by
  unfold muInf; infer_instance

theorem instConj_of (hm : GenModOne) (hd : InstDecomp) (h4 : SubFacts) : InstConj := by
  intro I r e f z hfr N H hN hNset hHset h hh
  obtain ⟨N', H', hN', hH', -, -, hnorm'⟩ := h4 I r e f z
  have hmemN : ∀ x, x ∈ N ↔ x ∈ N' := fun x => by
    rw [← SetLike.mem_coe, hNset, ← hN', SetLike.mem_coe]
  have hmemH : ∀ x, x ∈ H ↔ x ∈ Hset I (frameSet I e f z) := fun x => by
    rw [← SetLike.mem_coe, hHset]
  have hmemH' : ∀ x, x ∈ H ↔ x ∈ H' := fun x => by
    rw [hmemH, ← hH', SetLike.mem_coe]
  refine hm I.Ginf N H hN ?_ ?_ h hh
  · intro g hg x hx
    exact (hmemN _).mpr (hnorm' g ((hmemH' g).mp hg) x ((hmemN x).mp hx))
  · intro g hg
    obtain ⟨k, hk, p, hp, σ, hσ, hkp, hσp, C, hC⟩ := hd I r e f z hfr g ((hmemH g).mp hg)
    exact ⟨k, (hmemH k).mpr hk, p, (hmemH p).mpr hp, σ, (hmemH σ).mpr hσ, hkp, hσp, C, hC⟩

theorem target_of (h1 : GenHaarSub) (h2 : GenSemi) (h3 : GenWeil) (h4 : SubFacts) (h5 : InstConj)
    (h6 : InstProper) : PI.ScMuExists.Target := by
  intro I r e f z hee hff hef hz hzz
  have hfr : IsFrame I e f z := ⟨hee, hff, hef, hz, hzz⟩
  obtain ⟨N, H, hNset, hHset, hN, hH, hnorm⟩ := h4 I r e f z
  obtain ⟨hNσ, hN0, hNc, hNinv, -, -⟩ := h1 I.Ginf N hN
  obtain ⟨hHσ, hH0, hHc, hHinv, -, -⟩ := h1 I.Ginf H hH
  have hconj := h5 I r e f z hfr N H hN hNset hHset
  have hprop := h6 I r e f z hfr N H hNset hHset
  obtain ⟨hSf, hSmeas, hSc, hSinv, hSpos, hScpt⟩ := h2 I.Ginf N H hN hH hnorm hconj hprop
  have := hSf
  obtain ⟨ν, hν⟩ := h3 I.Ginf (muInf I) (mulMeas (haarSub N hN) (haarSub H hH))
    ((N : Set I.Ginf) * (H : Set I.Ginf)) hSmeas hSc hSinv hSpos hScpt
  refine ⟨haarSub N hN, haarSub H hH, ν, ?_, ?_, hν⟩
  · refine ⟨hNσ, hN0, ?_, ?_⟩
    · rw [← hNset]
      exact hNc
    · intro s hs
      rw [← hNset] at hs
      exact hNinv s hs
  · refine ⟨hHσ, hH0, ?_, ?_⟩
    · rw [show Set.range e ∪ Set.range f ∪ {z} = frameSet I e f z from rfl, ← hHset]
      exact hHc
    · intro s hs
      rw [show Set.range e ∪ Set.range f ∪ {z} = frameSet I e f z from rfl, ← hHset] at hs
      exact hHinv s hs

theorem target_of_steps (h1 : GenHaarSub) (h2 : GenSemi) (h3 : GenWeil) (h4 : SubFacts) (hm : GenModOne)
    (hd : InstDecomp) (h6 : InstProper) : PI.ScMuExists.Target := by
  have h5 : InstConj := instConj_of hm hd h4
  exact target_of h1 h2 h3 h4 h5 h6

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

section

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

variable (I : Formalism.MainNotions.S.AutInst)

theorem phi_star (v : NumberField.InfinitePlace I.F) (a : I.E) : I.φ v (star a) = star (I.φ v a) :=
  I.cm.cmUnram.2.1 (I.φ v) a

theorem gram_real (v : NumberField.InfinitePlace I.F) :
    ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = I.J.map (I.φ v) := by
  have h : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have e : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h, Matrix.conjTranspose_one]
  rw [← I.P_spec v]
  calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹
      = (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = I.J.map (I.φ v) := by rw [e, h, Matrix.one_mul, Matrix.mul_one]

theorem hJ_mulVec_gen {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℂ) :
    hJ ε (A *ᵥ u) (A *ᵥ w) = star u ⬝ᵥ ((Aᴴ * Formalism.REAL.Jm ε * A) *ᵥ w) := by
  simp only [hJ, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem rv_hJ (v : NumberField.InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  simp only [rv]
  rw [hJ_mulVec_gen, gram_real I v]

  simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Pi.star_apply,
  Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, phi_star I v]
  ring

variable {I}

theorem rv_frame {r : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E} (hF : IsFrame I e f z)
    (v : NumberField.InfinitePlace I.F) :
    (∀ a b, hJ (I.ε v) (rv I v (e a)) (rv I v (e b)) = 0) ∧
    (∀ a b, hJ (I.ε v) (rv I v (f a)) (rv I v (f b)) = 0) ∧
    (∀ a b, hJ (I.ε v) (rv I v (e a)) (rv I v (f b)) = if a = b then 1 else 0) ∧
    (∀ a, hJ (I.ε v) (rv I v (e a)) (rv I v z) = 0 ∧ hJ (I.ε v) (rv I v (f a)) (rv I v z) = 0) ∧
    hJ (I.ε v) (rv I v z) (rv I v z) ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, ?_⟩
  · rw [rv_hJ, h1, map_zero]
  · rw [rv_hJ, h2, map_zero]
  · rw [rv_hJ, h3]
    split_ifs <;> simp
  · rw [rv_hJ, rv_hJ, (h4 a).1, (h4 a).2, map_zero]
    exact ⟨rfl, rfl⟩
  · rw [rv_hJ]
    exact (map_ne_zero _).mpr h5

end PI.ScMuExists.UnitaryGroupMassFormula
end
end
