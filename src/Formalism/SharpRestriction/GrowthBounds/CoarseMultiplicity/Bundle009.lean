module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle004
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle008
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle017
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Loc4ResOfLine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem hom_of_ssz {O : Type} [CommRing O] [IsDomain O] (b : SegBlock (segS X.TT j) X.m) (mm : ℝ)
    (u : MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) (hu : u ∈ sszB O C0 CE1 CE2 X j mm b) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (hμ : μ ∈ u.support) : HomExp C0 CE1 CE2 X j b μ := by
  intro ω ωL hB
  obtain ⟨h1, h2, h3⟩ := hB
  have hw := ssz_wh O X.p _ _ _ mm b ω ωL h1 h2 h3 u hu (mem_support_iff.1 hμ)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ (fun i c => c • ω i) (fun _ => zero_smul _ _)] at hw
  simpa [smul_eq_mul] using hw

theorem sep (hp : 0 < X.p) (b b' : SegBlock (segS X.TT j) X.m)
    (hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (hb' : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b') (μ μ' : BV C0 CE1 CE2 X j →₀ ℕ)
    (hμ : HomExp C0 CE1 CE2 X j b μ) (hμ' : HomExp C0 CE1 CE2 X j b' μ')
    (he : ioExp C0 CE1 CE2 X j b μ = ioExp C0 CE1 CE2 X j b' μ') : b = b' := by
  classical
  have hrz : ∀ i c, b.rz i c = b'.rz i c := by
    intro i c
    have h1 := ioExp_mod C0 CE1 CE2 X j b hb μ i true c
    have h2 := ioExp_mod C0 CE1 CE2 X j b' hb' μ' i true c
    rw [he, if_pos rfl] at h1
    rw [if_pos rfl] at h2
    exact h1.symm.trans h2
  have hry : ∀ i c, b.ry i c = b'.ry i c := by
    intro i c
    have h1 := ioExp_mod C0 CE1 CE2 X j b hb μ i false c
    have h2 := ioExp_mod C0 CE1 CE2 X j b' hb' μ' i false c
    rw [he, if_neg Bool.false_ne_true] at h1
    rw [if_neg Bool.false_ne_true] at h2
    exact h1.symm.trans h2
  have hrz' : b.rz = b'.rz := funext fun i => funext fun c => hrz i c
  have hry' : b.ry = b'.ry := funext fun i => funext fun c => hry i c
  have hA : ∀ i, coarseA X.p (X.seg C0 CE1 CE2 j) b i = coarseA X.p (X.seg C0 CE1 CE2 j) b' i := by
    intro i; unfold coarseA; rw [hrz']
  have hC : ∀ i, coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i =
      coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b' i := by
    intro i; unfold coarseC; rw [hry']
  have hS : ∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma → b.w i = b'.w i ∧ b.sg i = b'.sg i := by
    intro i hi
    have hP : 0 < (X.seg C0 CE1 CE2 j).P X.p i := pow_pos hp _
    have k1 := hb.2.2.1 i hi
    have k1' := hb'.2.2.1 i hi
    have v1 := congrArg (fun e => e ((topOdd X j i, true), (0 : Fin (X.m + 1)))) he
    have v2 := congrArg (fun e => e ((topOdd X j i, false), (0 : Fin (X.m + 1)))) he
    simp only [ioExp, Finsupp.add_apply] at v1 v2
    rw [coarse_spec C0 CE1 CE2 X j μ i true hi, coarse_spec C0 CE1 CE2 X j μ' i true hi, add_zero, add_zero,
      baseExp_odd, baseExp_odd, if_pos rfl, if_pos rfl, if_pos (⟨hi, rfl⟩ : _ ∧ _), if_pos (⟨hi, rfl⟩ : _ ∧ _),
      if_pos rfl, if_pos rfl, hrz i 0, hA i] at v1
    rw [coarse_spec C0 CE1 CE2 X j μ i false hi, coarse_spec C0 CE1 CE2 X j μ' i false hi, add_zero, add_zero,
      baseExp_odd, baseExp_odd, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_pos (⟨hi, rfl⟩ : _ ∧ _),
      if_pos (⟨hi, rfl⟩ : _ ∧ _), if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hry i 0] at v2
    have w1 := Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel v1)
    have w2 := Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel v2)
    have a1 := k1.2.1
    have a2 := k1'.2.1
    rw [hA i] at a1
    exact ⟨by omega, w2⟩
  have hbase : baseExp C0 CE1 CE2 X j b = baseExp C0 CE1 CE2 X j b' := by
    unfold baseExp
    rw [hrz', hry']
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [(hS i hi).1, (hS i hi).2, hA i]
    · rfl
  have hμμ : μ = μ' := by
    unfold ioExp at he
    rw [hbase] at he
    have h' := add_left_cancel he
    ext v0
    have := DFunLike.congr_fun h' (symVar C0 CE1 CE2 X j v0)
    rw [coarse_eval, coarse_eval] at this
    exact Nat.eq_of_mul_eq_mul_left (symLev_pos C0 CE1 CE2 X hp j v0) this
  subst hμμ
  have ho : ∀ l, b.o (uTop (X.seg C0 CE1 CE2 j) l) = b'.o (uTop (X.seg C0 CE1 CE2 j) l) := by
    intro l
    rw [← omB_ωo C0 CE1 CE2 X j b l, ← omB_ωo C0 CE1 CE2 X j b' l, ← hμ _ _ (ωo_bal C0 CE1 CE2 X j l),
      ← hμ' _ _ (ωo_bal C0 CE1 CE2 X j l)]
  have hoP : b.oPlus = b'.oPlus := by
    rw [← omB_ωp C0 CE1 CE2 X j b, ← omB_ωp C0 CE1 CE2 X j b', ← hμ _ _ (ωp_bal C0 CE1 CE2 X j),
      ← hμ' _ _ (ωp_bal C0 CE1 CE2 X j)]
  have hofun : b.o = b'.o := funext fun i => by
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [(hb.2.2.1 i hi).1, (hb'.2.2.1 i hi).1]
    · have hl : (i : ℕ) - (X.seg C0 CE1 CE2 j).sigma < (X.seg C0 CE1 CE2 j).t := by
        have := i.2; unfold SegData.t; omega
      have e : uTop (X.seg C0 CE1 CE2 j) ⟨(i : ℕ) - (X.seg C0 CE1 CE2 j).sigma, hl⟩ = i :=
        Fin.ext (by show (X.seg C0 CE1 CE2 j).sigma + ((i : ℕ) - (X.seg C0 CE1 CE2 j).sigma) = i; omega)
      rw [← e]
      exact ho _
  have hwfun : b.w = b'.w := funext fun i => by
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · exact (hS i hi).1
    · rw [(hb.2.1 i (not_lt.1 hi)).2.2.1, (hb'.2.1 i (not_lt.1 hi)).2.2.1]
  have hsgfun : b.sg = b'.sg := funext fun i => by
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · exact (hS i hi).2
    · rw [(hb.2.1 i (not_lt.1 hi)).2.2.2, (hb'.2.1 i (not_lt.1 hi)).2.2.2]
  cases b
  cases b'
  simp only at hrz' hry' hofun hwfun hsgfun hoP
  rw [hrz', hry', hofun, hwfun, hsgfun, hoP]

theorem ioBlock_eq_sum (K : Type) [Field K] (b : SegBlock (segS X.TT j) X.m) (t : MvPolynomial (BV C0 CE1 CE2 X j) K) :
    ioBlock K X.p C0 CE1 CE2 X j b t = ∑ μ ∈ t.support, monomial (ioExp C0 CE1 CE2 X j b μ) (t.coeff μ) := by
  let f : MvPolynomial (BV C0 CE1 CE2 X j) K →ₗ[K] MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
    (LinearMap.mulLeft K (digitMon K C0 CE1 CE2 X j b * sTopMon K X.p C0 CE1 CE2 X j b)).comp
      (aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
        MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v)).toLinearMap
  have hf : ∀ t, ioBlock K X.p C0 CE1 CE2 X j b t = f t := fun _ => rfl

  conv_lhs => rw [hf, ← t.support_sum_monomial_coeff, map_sum]
  exact Finset.sum_congr rfl fun μ _ => by rw [← hf, ioBlock_monomial]

end

theorem orthAt (C0 CE1 CE2 : ℝ) : OrthAt C0 CE1 CE2 := by
  classical
  intro X _ O _ _ mm hD1 j b b' hb hb' hne s hs s' hs'
  have hp : 0 < X.p := hD1.1.pos
  rw [ioBlock_eq_sum C0 CE1 CE2 X j (KK O) b s, Formalism.MainNotions.G.GLWeightTheory.fock_form_finset_sum _ _ _ (support_sum)]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨μ, hμ, he'⟩ := Finset.mem_biUnion.1 he
  have hem := support_monomial_subset he'
  rw [Finset.mem_singleton] at hem
  subst hem
  have h0 : AddMonoidAlgebra.coeff (ioBlock (KK O) X.p C0 CE1 CE2 X j b' s') (ioExp C0 CE1 CE2 X j b μ) = 0 := by
    rw [ioBlock_eq_sum C0 CE1 CE2 X j (KK O) b' s', coeff_sum]
    refine Finset.sum_eq_zero fun μ' hμ' => ?_
    rw [coeff_monomial, if_neg]
    intro h
    exact hne (sep C0 CE1 CE2 X j hp b' b hb' hb μ' μ (hom_of_ssz C0 CE1 CE2 X j b' mm s' hs' μ' hμ')
      (hom_of_ssz C0 CE1 CE2 X j b mm s hs μ hμ) h).symm
  rw [h0, mul_zero, zero_mul]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

theorem psiRes0_ne {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
    (a : Fin (X.m + 1)) (h : WittVector.constantCoeff (g⁻¹ 0 a) ≠ 0) : psiRes0 X O S.w g a ≠ 0 := by
  intro h0
  unfold psiRes0 at h0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
  have hu : IsUnit (g⁻¹ 0 a) := WittVector.isUnit_of_coeff_zero_ne_zero _ h
  have hu' : IsUnit (psiO X.p X.n' O 0 (g⁻¹ 0 a)) := hu.map _
  exact S.w_irr.not_isUnit (isUnit_of_dvd_unit h0 hu')

theorem resLineAt : ResLineAt := by
  intro X _ O _ _ _ _ S _ _ g _ hne h0
  by_contra hall
  push_neg at hall
  apply hne
  have hcc : ∀ c : Fin X.m, WittVector.constantCoeff (g⁻¹ 0 c.succ) = 0 := by
    intro c
    by_contra hc
    exact psiRes0_ne S g c.succ hc (hall c)
  have hv0 : WittVector.constantCoeff (g⁻¹ 0 0) ≠ 0 := by
    intro hz
    apply h0
    unfold psiRes0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    by_cases hx : g⁻¹ 0 0 = 0
    · rw [hx, map_zero]
      exact dvd_zero _
    · obtain ⟨m, b, hb, hab⟩ := WittVector.exists_eq_pow_p_mul (g⁻¹ 0 0) hx
      have hm : m ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hab
        exact hb (hab ▸ hz)
      rw [hab, map_mul, map_pow, map_natCast]
      have hwp : S.w ∣ (X.p : O) := by
        have h1 := S.p_mem
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer S.w).mp S.w_irr,
          Ideal.mem_span_singleton] at h1
        exact h1
      exact Dvd.dvd.mul_right (dvd_pow hwp hm) _
  have hset : ∀ h : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'),
      ratPlane X.p X.n' 1 h =
        Submodule.span (GaloisField X.p X.n') {fun c => WittVector.constantCoeff (h⁻¹ 0 c)} := by
    intro h
    unfold ratPlane
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi0 : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [hi0]
    · rintro rfl
      exact ⟨0, by simp, rfl⟩
  rw [hset g, hset 1, inv_one]
  have hv : (fun c => WittVector.constantCoeff (g⁻¹ 0 c)) = WittVector.constantCoeff (g⁻¹ 0 0) •
      (fun c => WittVector.constantCoeff ((1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) 0 c)) := by
    funext c
    refine Fin.cases ?_ (fun c' => ?_) c
    · simp
    · simp [hcc c', Matrix.one_apply_ne (Fin.succ_ne_zero c').symm]
  rw [hv, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hv0)]

theorem loc4Res : LocalResidueBound := loc4Res_of_line resLineAt

end Formalism.MainNotions.ColumnSystems.Pf
end
end
