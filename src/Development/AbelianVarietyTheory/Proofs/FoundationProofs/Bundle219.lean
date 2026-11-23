module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle008
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle002
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle211
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
public import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.GaussPhase

theorem finite_quot {G : Type} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G] (P : AddSubgroup G)
    [P.FiniteIndex] (φ : P →+ G) (hφ : Function.Injective φ) : Finite (G ⧸ φ.range) := by
  have h1 : Finite (G ⧸ P.toIntSubmodule) := (inferInstance : Finite (G ⧸ P))
  have h2 := (Submodule.finiteQuotient_iff _).1 h1
  let ψ : P.toIntSubmodule →ₗ[ℤ] G := φ.toIntLinearMap
  have h3 : Module.finrank ℤ (LinearMap.range ψ) = Module.finrank ℤ G := by
    have hψ : Function.Injective ψ := fun x y h => hφ h
    exact (LinearMap.finrank_range_of_inj hψ).trans h2
  have h4 : Finite (G ⧸ (LinearMap.range ψ).toAddSubgroup) :=
    Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range ψ) h3
  have h5 : (LinearMap.range ψ).toAddSubgroup = φ.range := by
    ext x; exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  rwa [h5] at h4

noncomputable def ex (t : ℝ) : ℂ := cexp (-((π : ℂ) * I) * (t : ℂ))

theorem ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  simp only [ex, ← Complex.exp_add]; congr 1; push_cast; ring

theorem ex_zero : ex 0 = 1 := by simp [ex]

theorem ex_two (m : ℤ) : ex (2 * m) = 1 := by
  rw [ex, ← Complex.exp_int_mul_two_pi_mul_I (-m)]; congr 1; push_cast; ring

theorem ex_pow (t : ℝ) (k : ℕ) : ex t ^ k = ex (k * t) := by
  simp only [ex, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem gauss_phase : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsPosHerm H → ∀ (a : V ≃ₗ[ℂ] V), (∀ z w, H (a z) (a w) = H z w) → ∀ (B : V →ₗ[ℂ] V), (∀ x, B x - a (B x) = x) → (∀ x, B (x - a x) = x) → ∀ (Λ Λ' : AddSubgroup V), Λ.FG → Λ' ≤ Λ → (Λ'.addSubgroupOf Λ).FiniteIndex → (∀ y ∈ Λ', a y ∈ Λ) → ∀ α : V → ℂ, IsSemichar H Λ α → (∀ y ∈ Λ', α (a y) = α y) → ∃ (M : Type) (_ : Fintype M) (s : M → V), (∀ m, s m ∈ Λ) ∧ (∀ x ∈ Λ, ∃! p : M × Λ', x = s p.1 - ((p.2 : V) - a p.2)) ∧ GlobalTheory.Phase.Ph (∑ m, α (s m) * cexp (-((π : ℂ) * I) * ((H (B (s m)) (s m)).im : ℂ))) := by
  intro V _ _ H hH a ha B hB1 hB2 Λ Λ' hfg hle hfi haΛ α hα hαa
  obtain ⟨hα1, hint, hadd⟩ := hα
  have hanti : ∀ x y, (H x y).im = -(H y x).im := fun x y => by rw [hH.1 x y]; simp
  have hself : ∀ x, (H x x).im = 0 := fun x => by have := hanti x x; linarith
  have hadj : ∀ x y, (H (B x) y).im - (H (B y) x).im = (H x y).im := by
    intro x y
    have h1 : H (B x) y + H x (B y) = H x y := by
      have hx := hB1 x
      have hy := hB1 y
      generalize B x = u at hx ⊢
      generalize B y = v at hy ⊢
      subst hx hy
      simp only [map_sub, LinearMap.sub_apply, ha]
      ring
    have h2 := congrArg Complex.im h1
    rw [Complex.add_im, hanti x (B y)] at h2
    linarith
  let ph : V → ℂ := fun x => α x * ex (H (B x) x).im
  have hadd' : ∀ x ∈ Λ, ∀ y ∈ Λ, α (x + y) = α x * α y * ex (H x y).im := hadd
  have hsq : ∀ x ∈ Λ, α x ^ 2 = 1 := fun x hx => by rcases hα1 x hx with h | h <;> simp [h]
  have hne : ∀ x ∈ Λ, α x ≠ 0 := fun x hx => by rcases hα1 x hx with h | h <;> simp [h]
  have hα0 : α 0 = 1 := by
    have := hadd' 0 Λ.zero_mem 0 Λ.zero_mem
    rw [add_zero, hself, ex_zero, mul_one] at this
    exact (mul_eq_left₀ (hne 0 Λ.zero_mem)).1 this.symm
  have hph0 : ph 0 = 1 := by simp [ph, hα0, ex_zero]
  have hph : ∀ x ∈ Λ, ∀ y ∈ Λ, ph (x + y) = ph x * ph y * ex (2 * (H (B x) y).im) := by
    intro x hx y hy
    have e : (H (B (x + y)) (x + y)).im + (H x y).im =
        (H (B x) x).im + (H (B y) y).im + 2 * (H (B x) y).im := by
      simp only [map_add (f := _), LinearMap.add_apply, Complex.add_im, ← hadj x y]; ring
    have e' := congrArg ex e
    rw [ex_add, ex_add, ex_add] at e'
    simp only [ph, hadd' x hx y hy]
    linear_combination α x * α y * e'
  have hmem : ∀ y ∈ Λ', y - a y ∈ Λ := fun y hy => Λ.sub_mem (hle hy) (haΛ y hy)
  have hphA : ∀ y ∈ Λ', ph (y - a y) = 1 := by
    intro y hy
    have h := hadd' _ (hmem y hy) _ (haΛ y hy)
    rw [sub_add_cancel, hαa y hy] at h
    have h' : α (y - a y) * ex (H (y - a y) (a y)).im = 1 :=
      (mul_eq_left₀ (hne y (hle hy))).1 (by linear_combination -h)
    obtain ⟨m, hm⟩ := hint y (hle hy) (a y) (haΛ y hy)
    have e1 : (H (y - a y) (a y)).im = m := by
      simp only [map_sub, LinearMap.sub_apply, Complex.sub_im, hself, hm, sub_zero]
    have e2 : (H (B (y - a y)) (y - a y)).im = m + 2 * ((-m : ℤ) : ℝ) := by
      rw [hB2]
      simp only [map_sub, Complex.sub_im, hself, hm]; push_cast; ring
    simp only [ph]
    rw [e2, ex_add, ex_two, mul_one, ← e1, h']
  have hper : ∀ x ∈ Λ, ∀ y ∈ Λ', ph (y - a y + x) = ph x := by
    intro x hx y hy
    obtain ⟨m, hm⟩ := hint y (hle hy) x hx
    rw [hph _ (hmem y hy) x hx, hphA y hy, hB2, hm, ex_two, one_mul, mul_one]
  let φ : Λ'.addSubgroupOf Λ →+ Λ := AddMonoidHom.mk'
    (fun y => ⟨((y : Λ) : V) - a ((y : Λ) : V), hmem _ y.2⟩)
    (fun y z => Subtype.ext (by simp only [AddSubgroup.coe_add, map_add (f := _)]; abel))
  have hφ : ∀ y, ((φ y : Λ) : V) = ((y : Λ) : V) - a ((y : Λ) : V) := fun _ => rfl
  have hinj : Function.Injective φ := by
    intro y z h
    have := congrArg (fun t : Λ => B (t : V)) h
    simp only [hφ, hB2] at this
    exact Subtype.ext (Subtype.ext this)
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg _).2 hfg)
  have : HasUniqueDiv V := .of_isTorsionFree ℂ V
  have : Module.Free ℤ Λ := inferInstance
  have := finite_quot _ φ hinj
  let _ : Fintype (Λ ⧸ φ.range) := Fintype.ofFinite _
  have hrel : ∀ x x' : Λ, (x : Λ ⧸ φ.range) = x' ↔ ∃ y ∈ Λ', (x' : V) = y - a y + x := by
    intro x x'
    rw [QuotientAddGroup.eq]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨_, y.2, ?_⟩
      have := congrArg Subtype.val hy
      rw [hφ] at this
      erw [this]; simp
    · rintro ⟨y, hy, h⟩
      refine ⟨⟨⟨y, hle hy⟩, hy⟩, Subtype.ext ?_⟩
      rw [hφ]; simp [h]
  have hf : ∀ x : Λ, ph ((Quotient.out (x : Λ ⧸ φ.range) : Λ) : V) = ph x := by
    intro x
    obtain ⟨y, hy, h⟩ := (hrel x _).1 (QuotientAddGroup.out_eq' _).symm
    rw [h, hper _ x.2 y hy]
  refine ⟨Λ ⧸ φ.range, inferInstance, fun m => ((Quotient.out m : Λ) : V), fun m => (Quotient.out m).2, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, h⟩ := (hrel ⟨x, hx⟩ _).1 (QuotientAddGroup.out_eq' _).symm
    refine ⟨(((⟨x, hx⟩ : Λ) : Λ ⧸ φ.range), ⟨y, hy⟩), by simp only [h]; abel, ?_⟩
    rintro ⟨m, z, hz⟩ h'
    simp only at h'
    have hm : ((⟨x, hx⟩ : Λ) : Λ ⧸ φ.range) = m := by
      rw [← QuotientAddGroup.out_eq' m, hrel]
      exact ⟨z, hz, by simp only [h']; abel⟩
    subst hm
    refine Prod.ext rfl (Subtype.ext ?_)
    rw [h] at h'
    have : z - a z = y - a y := by
      have h'' : x = y - a y + x - (z - a z) := h'
      rw [← sub_eq_zero] at h'' ⊢
      rw [← h'']; abel
    simpa only [hB2] using congrArg B this
  · refine GlobalTheory.Phase.GaussSum.ph_sum _ (fun m : Λ ⧸ φ.range => ph ((Quotient.out m : Λ) : V)) ⟨?_, ?_⟩
    · intro m _
      beta_reduce
      generalize Quotient.out m = x
      set k := Fintype.card (Λ ⧸ φ.range)
      have hk : 0 < k := Fintype.card_pos
      have h0 : ((0 : Λ) : Λ ⧸ φ.range) = ((k • x : Λ) : Λ ⧸ φ.range) := by
        rw [QuotientAddGroup.mk_nsmul, card_nsmul_eq_zero]; rfl
      obtain ⟨y, hy, h⟩ := (hrel _ _).1 h0
      obtain ⟨n, hn⟩ := hint y (hle hy) x x.2
      have hy' : k • B (x : V) = y := by
        rw [← map_nsmul, ← hB2 y]; congr 1; simpa using h
      have e : ((2 * k : ℕ) : ℝ) * (H (B x) x).im = 2 * n := by
        rw [← hn, ← hy', map_nsmul]; simp; ring
      refine ⟨2 * k, by omega, ?_⟩
      simp only [ph]
      rw [mul_pow, ex_pow, e, ex_two, pow_mul, hsq _ x.2]; simp
    · intro x _ y _ z _
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective z
      simp only [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_zero, hf, AddSubgroup.coe_add,
        AddSubgroup.coe_zero]
      rw [hph _ (Λ.add_mem x.2 y.2) _ z.2, hph _ y.2 _ z.2, hph _ x.2 _ z.2, hph0]
      simp only [map_add (f := _), LinearMap.add_apply, Complex.add_im, mul_add, ex_add]
      ring

end GlobalTheory.UnitaryTheta.GaussPhase
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.GaussSumm

theorem exists_mul_norm_sq_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) : ∃ c : ℝ, 0 < c ∧ ∀ x : V, c * ‖x‖ ^ 2 ≤ (H x x).re := by
  have hcont : Continuous fun x : V => (H x x).re := by
    let b := Module.finBasis ℂ V
    have e : (fun x : V => H x x) = fun x => ∑ i, H x (b i) * conj (b.repr x i) := by
      funext x
      conv_lhs => rw [show H x x = H x (∑ i, b.repr x i • b i) by rw [b.sum_repr]]

      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, smul_eq_mul, mul_comm]
    have : Continuous fun x : V => H x x := by
      rw [e]
      refine continuous_finsetSum _ fun i _ => ?_
      have h1 : Continuous fun x : V => H x (b i) :=
        (H.flip (b i)).continuous_of_finiteDimensional
      have h2 : Continuous fun x : V => b.repr x i :=
        (b.coord i).continuous_of_finiteDimensional
      exact h1.mul (continuous_conj.comp h2)
    exact continuous_re.comp this
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Metric.sphere (0 : V) 1, c ≤ (H x x).re := by
    refine (isCompact_sphere (0 : V) 1).exists_forall_le' hcont.continuousOn fun x hx => hH.2 x ?_
    rintro rfl
    simp at hx
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h1 := hle (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne'])
  have e : H (((‖x‖⁻¹ : ℝ) : ℂ) • x) (((‖x‖⁻¹ : ℝ) : ℂ) • x) = ((‖x‖⁻¹ ^ 2 : ℝ) : ℂ) * H x x := by
    rw [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, conj_ofReal, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [e, re_ofReal_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
  have e2 : ‖x‖⁻¹ ^ 2 * (H x x).re * ‖x‖ ^ 2 = (H x x).re := by field_simp
  rwa [e2] at h2

theorem exp_le_inv_pow {a : ℝ} (ha : 0 < a) (C : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(a * t ^ 2) + C * t) ≤ (k.factorial * Real.exp ((C + 1) ^ 2 / (4 * a))) * t⁻¹ ^ k := by
  have h1 : t ^ k / k.factorial ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hk] at h1
  have h2 : -(a * t ^ 2) + C * t + t ≤ (C + 1) ^ 2 / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a * t - (C + 1))]
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc Real.exp (-(a * t ^ 2) + C * t) * t ^ k
      ≤ Real.exp (-(a * t ^ 2) + C * t) * (Real.exp t * k.factorial) := by gcongr
    _ = k.factorial * Real.exp (-(a * t ^ 2) + C * t + t) := by rw [Real.exp_add _ t]; ring
    _ ≤ _ := by gcongr

theorem summable_exp_neg_herm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (C : ℝ), Summable (fun x : Λ => Real.exp (-(π / 2) * (H x x).re + C * ‖(x : V)‖)) := by
  intro V _ _ _ H hH Λ _ C
  obtain ⟨c, hc, hle⟩ := exists_mul_norm_sq_le H hH
  letI : NormedSpace ℝ V := NormedSpace.complexToReal
  haveI : FiniteDimensional ℝ V := FiniteDimensional.complexToReal V
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := ‹DiscreteTopology Λ›
  have hs : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (Module.finrank ℤ L + 1) :=
    ZLattice.summable_norm_pow_inv L (Module.finrank ℤ L + 1) (Nat.lt_succ_self _)
  have ha : 0 < π / 2 * c := by have := Real.pi_pos; positivity
  refine Summable.of_norm_bounded_eventually (hs.mul_left
    ((Module.finrank ℤ L + 1).factorial * Real.exp ((C + 1) ^ 2 / (4 * (π / 2 * c))))) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : Λ)] with x hx
  have hn : 0 < ‖(x : V)‖ := norm_pos_iff.2 fun h => hx (Subtype.ext h)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine le_trans (Real.exp_le_exp.2 ?_) (exp_le_inv_pow ha C _ hn)
  have := mul_le_mul_of_nonneg_left (hle x) (by have := Real.pi_pos; positivity : 0 ≤ π / 2)
  linarith

end GlobalTheory.UnitaryTheta.GaussSumm
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NegOneNorm

theorem exists_dvd_mul_involution_add_one {R : Type} [CommRing R] [IsDedekindDomain R] (s : R →+* R)
    (hs : ∀ x, s (s x) = x) (n : R) (hn : n ≠ 0) (hsn : s n = n)
    (hfin : ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P))
    (hne : ∀ P : Ideal R, P.IsMaximal → ∃ x, s x - x ∉ P)
    (h2 : ∀ P : Ideal R, P.IsMaximal → (∀ x ∈ P, s x ∈ P) → (2 : R) ∉ P) :
    ∃ l : R, n ∣ l * s l + 1 := by
  have hn' : Ideal.span {n} ≠ (⊥ : Ideal R) := by simpa using hn
  let S : Finset (Ideal R) := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).toFinset
  have hS : ∀ P : Ideal R, P ∈ S ↔ P.IsPrime ∧ n ∈ P := fun P => by
    simp only [S, Multiset.mem_toFinset]
    rw [Ideal.mem_normalizedFactors_iff hn', Ideal.span_singleton_le_iff_mem]
  have hbot : ∀ P ∈ S, P ≠ ⊥ := fun P hP => by
    rintro rfl
    exact hn (by simpa using ((hS _).1 hP).2)
  have hpr : ∀ P ∈ S, Prime P := fun P hP => Ideal.prime_of_isPrime (hbot P hP) ((hS P).1 hP).1
  have hrad : ∏ P ∈ S, P ≤ (Ideal.span {n}).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨h1, h3⟩
    exact Ideal.prod_le_inf.trans
      (Finset.inf_le (f := fun P => P) ((hS P).2 ⟨h3, (Ideal.span_singleton_le_iff_mem _).1 h1⟩))
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hcc : ∀ P : Ideal R, (P.comap s).comap s = P := fun P => by
    ext x; simp [Ideal.mem_comap, hs]
  have hz : ∀ P : Ideal R, ∃ z : R, P ∈ S → P.comap s = P → z * s z + 1 ∈ P ^ N := fun P => by
    by_cases h : P ∈ S ∧ P.comap s = P
    · obtain ⟨hP, hfix⟩ := h
      haveI hM : P.IsMaximal := ((hS P).1 hP).1.isMaximal (hbot P hP)
      haveI := hfin P hM
      have hsP : ∀ x ∈ P, s x ∈ P := fun x hx => by rwa [← hfix] at hx
      have : ∀ k : ℕ, ∃ z : R, k = 0 ∨ z * s z + 1 ∈ P ^ k := fun k => by
        induction k with
        | zero => exact ⟨0, Or.inl rfl⟩
        | succ k ih =>
          obtain ⟨z0, hz0⟩ := ih
          obtain ⟨z, hz, -⟩ := GlobalTheory.NormResidue.exists_mul_involution_add_one_mem_pow R s hs P hsP
            (hne P hM) (h2 P hM hsP) k z0 hz0
          exact ⟨z, Or.inr hz⟩
      obtain ⟨z, hz⟩ := this (N + 1)
      exact ⟨z, fun _ _ => Ideal.pow_le_pow_right (Nat.le_succ N) (hz.resolve_left (Nat.succ_ne_zero N))⟩
    · exact ⟨0, fun h1 h3 => (h ⟨h1, h3⟩).elim⟩
  choose z hz using hz
  let a : Ideal R → R := fun P =>
    if P.comap s = P then z P else if WellOrderingRel P (P.comap s) then 1 else -1
  have ha : ∀ P ∈ S, a P * s (a (P.comap s)) + 1 ∈ P ^ N := fun P hP => by
    by_cases hfix : P.comap s = P
    · simp only [a, hfix, if_true]
      exact hz P hP hfix
    · have hfix' : ¬ P = P.comap s := fun h => hfix h.symm
      simp only [a, hcc, if_neg hfix, if_neg hfix']
      rcases trichotomous_of WellOrderingRel P (P.comap s) with h | h | h
      · rw [if_pos h, if_neg (asymm h)]; simp
      · exact (hfix' h).elim
      · rw [if_pos h, if_neg (asymm h)]; simp
  obtain ⟨l, hl⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun P => P) (fun _ => N)
    hpr (fun _ _ _ _ h => h) (fun P => a P.1)
  have hmem : ∀ P ∈ S, l * s l + 1 ∈ P ^ N := fun P hP => by
    obtain ⟨h1, h3⟩ := (hS P).1 hP
    have hP' : P.comap s ∈ S := (hS _).2 ⟨Ideal.comap_isPrime s P, by rwa [Ideal.mem_comap, hsn]⟩
    have e1 : l - a P ∈ P ^ N := hl P hP
    have e2 : s (l - a (P.comap s)) ∈ P ^ N := Ideal.le_comap_pow s N (hl _ hP')
    have : l * s l + 1 = s l * (l - a P) + a P * s (l - a (P.comap s)) + (a P * s (a (P.comap s)) + 1) := by
      rw [map_sub]; ring
    rw [this]
    exact add_mem (add_mem (Ideal.mul_mem_left _ _ e1) (Ideal.mul_mem_left _ _ e2)) (ha P hP)
  refine ⟨l, Ideal.mem_span_singleton.1 (hN ?_)⟩
  rw [← Finset.prod_pow, ← IsDedekindDomain.inf_pow_eq_prod_of_prime S (fun P => P) (fun _ => N) hpr
    (fun _ _ _ _ h => h), Submodule.mem_finsetInf]
  exact hmem

theorem exists_norm_eq_neg_one : ∀ (D : D7) (m : ℕ), 0 < m → ∃ l b : 𝓞 D.host.E, (l : D.host.E) * D.host.conj (l : D.host.E) = -1 + (m : D.host.E) * (b : D.host.E) := by
  intro D m hm
  have hc : ∀ x, D.host.conj (D.host.conj x) = x := by
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    refine fun x => φ.injective ?_
    have h1 := D.host.conjE_apply φ
    exact (h1 _).trans ((congrArg _ (h1 x)).trans (Complex.conj_conj _))
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := (Formalism.L2.Pj.barE D).toRingHom
  have hs : ∀ x, ((s x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := Formalism.L2.Pj.barE_eq_conj D
  obtain ⟨l, b, hb⟩ := exists_dvd_mul_involution_add_one s
    (fun x => RingOfIntegers.ext (by rw [hs, hs, hc])) (m : 𝓞 D.host.E) (by exact_mod_cast hm.ne')
    (map_natCast s m)
    (fun P hP => Ideal.finiteQuotientOfFreeOfNeBot P
      (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)))
    (fun P hP => by
      obtain ⟨θ, hθ⟩ := Formalism.L2.Pj.cmUnram_conj D P hP
      exact ⟨θ, fun h => hθ (by
        have h' := P.neg_mem h
        rw [neg_sub] at h'
        exact h')⟩)
    (fun P hP hsP h2 => by
      have hw : s (Formalism.L2.Pj.w0E D) = 1 - Formalism.L2.Pj.w0E D := Formalism.L2.Pj.conj_w0E D
      have hsq := Formalism.L2.Pj.w0E_sq D
      obtain ⟨k, hk⟩ : ∃ k, Formalism.L2.Pj.mE D = 2 * k := by
        have h1 := D.host.hyp.2.2.2.1
        have h3 := Formalism.L2.Pj.mE_spec D
        exact ⟨Formalism.L2.Pj.mE D / 2, by omega⟩
      rw [hk] at hsq
      push_cast at hsq
      set w := Formalism.L2.Pj.w0E D
      have hm : w * (1 - w) ∈ P := by
        have : w * (1 - w) = k * 2 := by linear_combination -hsq
        rw [this]; exact P.mul_mem_left _ h2
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      rcases hP.isPrime.mem_or_mem hm with h | h
      · have h' := hsP _ h
        rw [hw] at h'
        simpa using P.add_mem h h'
      · have h' := hsP _ h
        rw [map_sub, map_one, hw] at h'
        simpa using P.add_mem h h')
  refine ⟨l, b, ?_⟩
  have := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hb
  simp only [map_add (f := _), map_mul, map_one, map_natCast] at this
  rw [← hs]
  linear_combination this

end GlobalTheory.NegOneNorm
end

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open GlobalTheory.NormSum

namespace GlobalTheory.NormSum.Compare

theorem sqrt_le_rd (D : D7) : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
  (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1

theorem three_le (D : D7) : (3 : ℝ) ≤ D.host.q ∧ (3 : ℝ) ≤ D.host.d := by
  obtain ⟨hq, hd, -, hq2, hd2⟩ := D.host.hypOdd
  have := hq.two_le
  have := hd.two_le
  constructor
  · exact_mod_cast (show 3 ≤ D.host.q by omega)
  · exact_mod_cast (show 3 ≤ D.host.d by omega)

theorem log_d_le (D : D7) : Real.log D.host.d ≤ 2 * Real.log D.host.rdE := by
  obtain ⟨hq, hd⟩ := three_le D
  have h2 := sqrt_le_rd D
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d by positivity)
  have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  have h5 : (D.host.d : ℝ) ≤ D.host.rdE ^ 2 := by nlinarith
  have := Real.log_le_log (by linarith) h5
  rwa [Real.log_pow, Nat.cast_ofNat] at this

section Places

open Formalism.DivisionValues (vw lw)
open Formalism.PairingDivisionLocalBalance (Pl)
open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

end Places

end GlobalTheory.NormSum.Compare
end
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam), actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  first | exact @GlobalTheory.NabStab.polyAction_mem_locP_nabStd | exact GlobalTheory.NabStab.polyAction_mem_locP_nabStd | (intros; apply GlobalTheory.NabStab.polyAction_mem_locP_nabStd <;> assumption)
end
