module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootEqOfNormLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle487
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormula
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle486
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle221
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle488
public import GroundTheory.LocalFields.HerbrandFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle489
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.UnramSpan

open GlobalTheory.UnramValue

variable {l : ℕ} [Fact l.Prime]

theorem fg_rootRing {m : ℕ} (hm : 0 < m) : (rootRing l m).toSubmodule.FG := by
  classical
  have hfin : {x : Om l | x ^ m = 1}.Finite := by
    refine (Polynomial.nthRoots m (1 : Om l)).toFinset.finite_toSet.subset ?_
    intro x hx
    simpa [Polynomial.mem_nthRoots hm] using hx
  refine fg_adjoin_of_finite hfin ?_
  intro x hx
  refine IsIntegral.of_pow hm ?_
  rw [show x ^ m = 1 from hx]; exact isIntegral_one

theorem exists_mem_rootRing {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ∈ rootRing l m := by
  apply GlobalTheory.TiltInvariants.mem_rootRing <;> assumption

theorem norm_pow_sub_pow_le {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : k ≠ 0) {a b : Om l}
    (ha : a ∈ rootRing l m) (hb : b ∈ rootRing l m) (h : ‖a - b‖ ≤ (l : ℝ)⁻¹) :
    ‖a ^ (l ^ k) - b ^ (l ^ k)‖ ≤ (l : ℝ)⁻¹ * ‖a - b‖ := by
  have hp : l.Prime := Fact.out
  have hd := sub_mem ha hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨b, hb⟩ : rootRing l m) ⟨a - b, hd⟩ k
  have hr' := congrArg Subtype.val hr
  simp only [MulMemClass.coe_mul, AddMemClass.coe_add, SubmonoidClass.coe_pow,
    SubringClass.coe_natCast, add_sub_cancel] at hr'
  have e : a ^ (l ^ k) - b ^ (l ^ k) = (a - b) ^ (l ^ k) + l * (a - b) * (b * r) := by
    rw [hr']; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · obtain ⟨j, hj⟩ : ∃ j, l ^ k = j + 2 :=
      ⟨l ^ k - 2, by have := Nat.one_lt_pow hk hp.one_lt; omega⟩
    have h1 := norm_le_one hm hd
    have h2 : ‖a - b‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
    rw [hj, norm_pow, pow_add, sq]
    calc _ ≤ 1 * ((l : ℝ)⁻¹ * ‖a - b‖) := by gcongr
      _ = _ := one_mul _
  · rw [norm_mul, norm_mul, norm_l]
    have h1 := norm_le_one hm (mul_mem hb r.2)
    calc _ ≤ (l : ℝ)⁻¹ * ‖a - b‖ * 1 := by gcongr
      _ = _ := mul_one _

def part (F : IntermediateField ℚ_[l] (Om l)) (m : ℕ) : Submodule ℤ_[l] (Om l) :=
  (rootRing l m).toSubmodule ⊓ F.toSubalgebra.toSubmodule.restrictScalars ℤ_[l]

theorem mem_part {F : IntermediateField ℚ_[l] (Om l)} {m : ℕ} {x : Om l} :
    x ∈ part F m ↔ x ∈ rootRing l m ∧ x ∈ F := Iff.rfl

theorem fg_part (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) : (part F m).FG :=
  (fg_rootRing hm).of_le inf_le_left

theorem exists_teich (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m)
    {x : Om l} (hx : x ∈ part F m) :
    ∃ w ∈ part F m, w ^ (l ^ m.totient) = w ∧ ‖x - w‖ < 1 := by
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hli : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have : ContinuousSMul ℤ_[l] (Om l) := by
    refine continuousSMul_of_algebraMap ℤ_[l] (Om l) ?_
    exact (AddMonoidHomClass.isometry_of_norm _ norm_algebraMap_int).continuous
  have hc : IsCompact ((part F m : Set (Om l)) ∩ Metric.closedBall x (l : ℝ)⁻¹) :=
    (Submodule.isCompact_of_fg (fg_part F hm)).inter_right Metric.isClosed_closedBall
  have hstep : ∀ y ∈ rootRing l m, ‖y ^ (l ^ m.totient) - y‖ ≤ (l : ℝ)⁻¹ := by
    intro y hy
    obtain ⟨z, hz, ez⟩ := pow_sub_mem hl hy
    rw [ez, add_sub_cancel_left, norm_mul, norm_l]
    have h1 := norm_le_one hm hz
    calc _ ≤ (l : ℝ)⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  obtain ⟨w, ⟨hw, hwx⟩, hmin⟩ := hc.exists_isMinOn
    (f := fun y : Om l => ‖y ^ (l ^ m.totient) - y‖)
    ⟨x, hx, Metric.mem_closedBall_self (by positivity)⟩ (by fun_prop)
  rw [Metric.mem_closedBall, dist_eq_norm] at hwx
  have hw' := mem_part.mp hw
  refine ⟨w, hw, ?_, by rw [norm_sub_rev]; exact hwx.trans_lt hli⟩
  have hmem : w ^ (l ^ m.totient) ∈ (part F m : Set (Om l)) ∩ Metric.closedBall x (l : ℝ)⁻¹ := by
    refine ⟨mem_part.mpr ⟨pow_mem hw'.1 _, pow_mem hw'.2 _⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm,
      show w ^ (l ^ m.totient) - x = (w ^ (l ^ m.totient) - w) + (w - x) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hstep w hw'.1) hwx)
  have h1 : ‖w ^ (l ^ m.totient) - w‖ ≤ ‖(w ^ (l ^ m.totient)) ^ (l ^ m.totient) - w ^ (l ^ m.totient)‖ :=
    hmin hmem
  have h2 := norm_pow_sub_pow_le hm (Nat.totient_pos.mpr hm).ne' (pow_mem hw'.1 (l ^ m.totient))
    hw'.1 (hstep w hw'.1)
  have h3 := norm_nonneg (w ^ (l ^ m.totient) - w)
  have h4 : ‖w ^ (l ^ m.totient) - w‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

theorem part_le_span (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) :
    part F m ≤ Submodule.span ℤ_[l]
      {w : Om l | w ∈ F ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ w ^ m = 1} := by
  have hp : l.Prime := Fact.out
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal ℤ_[l])
    (fg_part F hm) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro x hx
  obtain ⟨w, hw, ew, hxw⟩ := exists_teich F hm hl hx
  have hd := mem_part.mp (sub_mem hx hw)
  obtain ⟨z, hz, ez⟩ := exists_eq_mul hm hl hd.1 hxw
  have hzF : z ∈ F := by
    have : z = (x - w) / l := by rw [ez]; field_simp
    rw [this]
    exact div_mem hd.2 (natCast_mem F l)
  have e : x = w + (l : ℤ_[l]) • z := by
    rw [Algebra.smul_def, map_natCast, ← ez]; ring
  rw [e]
  refine Submodule.add_mem_sup ?_ (Submodule.smul_mem_smul ?_ (mem_part.mpr ⟨hz, hzF⟩))
  · by_cases h0 : w = 0
    · rw [h0]; exact zero_mem _
    · have hq : 1 < l ^ m.totient := Nat.one_lt_pow (Nat.totient_pos.mpr hm).ne' hp.one_lt
      refine Submodule.subset_span ⟨(mem_part.mp hw).2, l ^ m.totient - 1, by omega, ?_, ?_⟩
      · intro hd
        have h1 : l ∣ l ^ m.totient := dvd_pow_self l (Nat.totient_pos.mpr hm).ne'
        have h2 := Nat.dvd_sub h1 hd
        rw [show l ^ m.totient - (l ^ m.totient - 1) = 1 by omega] at h2
        exact hp.not_dvd_one h2
      · apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel hq.le, ew, one_mul]
  · rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _

theorem exists_sum_rootsOfUnity : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (ω : Fin n → Om l), (∀ i, ω i ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ω i ^ m = 1) ∧ c = ∑ i, algebraMap ℚ_[l] (Om l) (z i : ℚ_[l]) * ω i := by
  intro l _ K c hc h1
  obtain ⟨m, hm, hl, h⟩ := exists_mem_rootRing (x := c) (show c ∈ K.1 ⊓ MaximalUnramifiedExtension l from hc).2 h1
  obtain ⟨n, z, g, e⟩ := Submodule.mem_span_set'.mp (part_le_span (K0 K) hm hl (mem_part.mpr ⟨h, hc⟩))
  refine ⟨n, z, fun i => g i, fun i => (g i).2, ?_⟩
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l)]
  rfl

end GlobalTheory.UnramSpan
end
end

section

open Formalism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobXi_div_prime_unit_tendsto_one : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l), ∃ u : Per.Acris l, IsUnit u ∧ (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (GlobalTheory.MemLoc.xi C.ε)) ∧ ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑(GlobalTheory.MemLoc.phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  first | exact @GlobalTheory.MemLoc.phi_xi_unit_tendsto | exact GlobalTheory.MemLoc.phi_xi_unit_tendsto | (intros; apply GlobalTheory.MemLoc.phi_xi_unit_tendsto <;> assumption)
end

section

open Formalism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobeniusEigen_fil_one_isUnit_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (n : ℕ), 0 < n → ∀ x : Per.Bcris l, (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x → x ≠ 0 → C.ι x ∈ Per.FilD l 1 → (∀ j : ℕ, j < n → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0) → IsUnit x ∧ C.ι x ∉ Per.FilD l 2 ∧ ∀ j : ℕ, 0 < j → j < n → C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  first | exact @GlobalTheory.MemLoc.EigenDegree.main | exact GlobalTheory.MemLoc.EigenDegree.main | (intros; apply GlobalTheory.MemLoc.EigenDegree.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_log_tilt_kummerCoboundary_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ u : P.R.BdR, ∀ g : GQ l, P.actQdR g u = u + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
  first | exact @GlobalTheory.PMon.exists_log_tilt_BdR | exact GlobalTheory.PMon.exists_log_tilt_BdR | (intros; apply GlobalTheory.PMon.exists_log_tilt_BdR <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WhitTorus

theorem eq_zero_of_not_antitone_int (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (ψ : AddChar (w.adicCompletion E) ℂ)
    (hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w)
    (W : GL (Fin n) (w.adicCompletion E) → ℂ)
    (hWN : ∀ u ∈ unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (superDiag u) * W g)
    (hWK : ∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (l : Fin n → ℤ) (hl : ¬ Antitone l)
    (D : GL (Fin n) (w.adicCompletion E))
    (hDv : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ ^ l a : (w.adicCompletion E)ˣ) : w.adicCompletion E)) :
    W D = 0 := by
  obtain ⟨i, j, hij, hlt⟩ : ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ l i < l j := by
    by_contra h
    push_neg at h
    apply hl
    cases n with
    | zero => exact fun a => a.elim0
    | succ m =>
      rw [Fin.antitone_iff_succ_le]
      intro k
      exact h k.castSucc k.succ (by simp)
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hlt' : i < j := Fin.lt_def.2 (by omega)
  have hnot : ((ϖ : w.adicCompletion E))⁻¹ ∉ Ov E w := by
    intro h
    change Valued.v (((ϖ : w.adicCompletion E))⁻¹) ≤ 1 at h
    rw [map_inv₀, hϖ, ← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe] at h
    exact absurd (Multiplicative.ofAdd_le.1 (h.trans_eq (ofAdd_zero).symm)) (by norm_num)
  obtain ⟨y, hy, hψy⟩ : ∃ y ∈ Ov E w, ψ (((ϖ : w.adicCompletion E))⁻¹ * y) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hnot ((hψ _).1 h)
  set x : w.adicCompletion E := ((ϖ : w.adicCompletion E))⁻¹ * y with hx
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  set m : ℕ := (l j - l i).toNat with hm
  have hlj : l j = l i + (m : ℤ) := by omega
  have hm1 : 1 ≤ m := by omega
  have hdj : ((ϖ ^ l j : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      ((ϖ ^ l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * (ϖ : w.adicCompletion E) ^ m := by
    rw [hlj, _root_.zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  set c : w.adicCompletion E := (ϖ : w.adicCompletion E) ^ m * x with hc
  have hcO : c ∈ Ov E w := by
    have hϖO : (ϖ : w.adicCompletion E) ∈ Ov E w := mem_Ov_of_isUnifV hϖ
    have : c = (ϖ : w.adicCompletion E) ^ (m - 1) * y := by
      rw [hc, hx, ← mul_assoc, show m = (m - 1) + 1 by omega, pow_succ, mul_assoc _ (ϖ : w.adicCompletion E),
        mul_inv_cancel₀ hϖ0, mul_one, Nat.add_sub_cancel]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hϖO _) hy
  let T : w.adicCompletion E → GL (Fin n) (w.adicCompletion E) := fun a =>
    ⟨Matrix.transvection i j a, Matrix.transvection i j (-a),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩
  have hT : ∀ a, ((T a : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.transvection i j a := fun a => rfl
  have hentry : ∀ {R : Type} [CommRing R] (a : R) (p q : Fin n), Matrix.transvection i j a p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then a else 0) := by
    intro R _ a p q
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
  have hu : T x ∈ unipB (w.adicCompletion E) (Fin n) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hT, hentry, if_neg (fun h => by rw [h] at hqp; exact lt_irrefl _ hqp), if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hqp hlt'
    · rw [hT, hentry, if_pos rfl, if_neg, add_zero]
      rintro ⟨rfl, h⟩
      exact hne h.symm
  have hsd : superDiag (T x) = x := by
    unfold GlobalTheory.Whittaker.superDiag
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [hT, hentry, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
      · intro b hb hbj
        have hb' := (Finset.mem_filter.1 hb).2
        rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hbj h.2.symm), add_zero]
      · intro hj
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, hij⟩) hj
    · intro a _ hai
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' := (Finset.mem_filter.1 hb).2
      rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hai h.1.symm), add_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hk : T c ∈ KGL w (n := n) := by
    refine ⟨⟨Matrix.transvection i j ⟨c, hcO⟩, Matrix.transvection i j (-⟨c, hcO⟩),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩, ?_⟩
    apply Units.ext
    ext p q
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hT]
    rw [hentry, hentry]
    split_ifs <;> simp
  have hkey : D * T c = T x * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hDv, hT, hT]
    ext p q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hentry, hentry]
    by_cases hpq : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [if_neg hne, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, zero_add, zero_add, hc, hdj]
      ring_nf
    · simp only [if_neg hpq, add_zero]
      split_ifs with h
      · subst h
        simp
      · simp
  have h1 := hWK D (T c) hk
  rw [hkey, hWN (T x) hu D, hsd] at h1
  have h2 : (ψ x - 1) * W D = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hψy)

end GlobalTheory.WhitTorus
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

theorem _root_.GlobalTheory.T.isIntegral_or_isIntegral_inv_in_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f → (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f → IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := by
  first | exact @GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor | exact GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor | (intros; apply GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.zg_formula_alt : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (y z : ((HW l).W K s LL h).DD T), z ∈ aN ((HW l).W K s LL h) T letπ → ∀ hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T, ∃ zz : ↥((HW l).W K s LL h).GKs → ((HW l).W K s LL h).DD T, (∀ g, zz g ∈ aN ((HW l).W K s LL h) T letπ) ∧ (∀ g, ((HW l).W K s LL h).γ T (zz g) - zz g = ((HW l).W K s LL h).γD T (((HW l).W K s LL h).resΓ g) z - z) ∧ ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → ∃ c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)), Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧ ∀ g : ↥((HW l).W K s LL h).GKs, ∃ t : ↥T.L.T, (t : T.V) = (c : ↥((HW l).W K s LL h).GKs → T.V) g ∧ (1 : RW LL) ⊗ₜ[↥(OL LL)] t = ((F l).E K s LL h).tie.jD T (zz g) - (TWact ((D.locA l).gRW LL ((g : ↥(GK K)) : GQ l)) T g b - b) := by
  first | exact @GlobalTheory.NL.ZgAll.zg_formula | exact GlobalTheory.NL.ZgAll.zg_formula | (intros; apply GlobalTheory.NL.ZgAll.zg_formula <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_acris_phi_pow_eigenvector_double_series : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (y : ℕ → Fl l), 2 ≤ h → (∀ k, ‖sh (y k)‖ ≤ ‖(l : ℂ_[l])‖) → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = abelian₂ h j y := by
  first | exact @GlobalTheory.PSer.exists_acris_Lam | exact GlobalTheory.PSer.exists_acris_Lam | (intros; apply GlobalTheory.PSer.exists_acris_Lam <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem tilt_orth_of_untilt_orth : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (m : Fin h → Fl l), (∀ i j, ‖sh (m i)‖ < l * ‖sh (m j)‖) →
    (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖sh (m j)‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * sh (m i)‖) →
    ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (l : ℤ) ∣ c j → ‖sh (m j)‖ ≤ ‖sh (∑ i, (c i : Fl l) * m i)‖ := by
  intro l _ h m hrat horth c j hj
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl0 : (0 : ℤ) < l := by exact_mod_cast (Fact.out : l.Prime).pos

  have hne : (Finset.univ : Finset (Fin h)).Nonempty := ⟨j, Finset.mem_univ _⟩
  set M : ℝ := Finset.univ.sup' hne (fun i => ‖sh (m i)‖) with hM
  have hMle : ∀ i, ‖sh (m i)‖ ≤ M := fun i => Finset.le_sup' (fun i => ‖sh (m i)‖) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMle j)
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' hne (fun i => ‖sh (m i)‖)
  have hsmall : ‖(l : ℂ_[l])‖ * M < ‖sh (m j)‖ := by
    rw [GlobalTheory.PSer.Laws.norm_l, hM, hi0, inv_mul_lt_iff₀ hl]
    exact hrat i0 j

  set n : Fin h → ℕ := fun i => (c i % (l : ℤ)).toNat with hn
  have hnc : ∀ i, ((n i : ℕ) : ℤ) = c i % (l : ℤ) := fun i =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hl0.ne')
  have hcast : ∀ i, (c i : Fl l) = (n i : Fl l) := by
    intro i
    have : ((n i : ℤ) : Fl l) = (n i : Fl l) := Int.cast_natCast _
    rw [← this, CharP.intCast_eq_intCast (Fl l) l, hnc]
    exact (Int.mod_modEq _ _).symm
  have hnj : ‖((n j : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
    intro hd
    apply hj
    have h1 : (l : ℤ) ∣ c j % (l : ℤ) := by rw [← hnc]; exact_mod_cast hd
    have h2 := (Int.dvd_iff_emod_eq_zero ..).1 h1
    rw [Int.emod_emod_of_dvd _ (dvd_refl _)] at h2
    exact Int.dvd_of_emod_eq_zero h2

  have hsum : (∑ i, (c i : Fl l) * m i) =
      ∑ p ∈ (Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)), m p.1 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hcast]
  have hsum2 : (∑ p ∈ (Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)), sh (m p.1)) =
      ∑ i, algebraMap ℚ_[l] ℂ_[l] ((n i : ℕ) : ℚ_[l]) * sh (m i) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, map_natCast]
  obtain ⟨hd, -⟩ := GlobalTheory.T.norm_sh_sum_sub_sum_sh_le l ((_ : Fin h) × ℕ) ((Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)))
    M (fun p => m p.1) hM0 (fun p _ => hMle p.1)
  rw [← hsum, hsum2] at hd
  have ho := horth (fun i => ((n i : ℕ) : ℚ_[l])) j
  simp only [hnj, one_mul] at ho

  by_contra hlt
  push_neg at hlt
  set b := sh (∑ i, (c i : Fl l) * m i)
  set a := ∑ i, algebraMap ℚ_[l] ℂ_[l] ((n i : ℕ) : ℚ_[l]) * sh (m i)
  have : ‖a‖ ≤ max ‖b‖ ‖b - a‖ := by
    have := IsUltrametricDist.norm_add_le_max b (-(b - a))
    rwa [norm_neg, show b + -(b - a) = a by ring] at this
  have hba : ‖b - a‖ < ‖sh (m j)‖ := hd.trans_lt hsmall
  exact absurd (ho.trans this) (not_le.2 (max_lt hlt hba))

end GlobalTheory
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (α : Type) (s : Finset α) (z : α → F) (R : ℝ), 0 ≤ R → (∀ a ∈ s, ‖z a‖ ≤ R) →
      ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖(l : ℂ_[l])‖ * R := by
  first | exact @GlobalTheory.untilt_ext_sum_sub_le | exact GlobalTheory.untilt_ext_sum_sub_le | (intros; apply GlobalTheory.untilt_ext_sum_sub_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.pow_mem_upperRamificationGroup_of_comm' : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ) (v : ℝ), (∀ σ τ : M ≃ₐ[F] M, σ * τ = τ * σ) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F M v, σ ^ p ∈ upperRamificationGroup F M (min (2 * v) (v + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm | exact GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm <;> assumption)
end
