module

public import GroundTheory.PAdicHodge.BdRSeries
public import Mathlib.RingTheory.Nilpotent.Exp
public import GroundTheory.PAdicHodge.Bundle002
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Completion
public import GroundTheory.PAdicHodge.Bundle001
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open PowerSeries

section Formal

theorem exp_subst_log : (exp ℚ).subst (log ℚ) = (1 + X : ℚ⟦X⟧) :=
  PowerSeries.subst_exp_log ℚ

end Formal

section Nilpotent

variable {S : Type*} [CommRing S] [Algebra ℚ S]

theorem truncEval_pow_eq_zero {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧}
    (hg : constantCoeff g = 0) : (truncEval s hs g) ^ n = 0 := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.2 hg
  rw [← map_pow, mul_pow, map_mul, map_pow, truncEval_X, hs, zero_mul]

theorem truncEval_subst {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧} (hg : constantCoeff g = 0)
    (f : ℚ⟦X⟧) :
    truncEval s hs (f.subst g) = truncEval (truncEval s hs g) (truncEval_pow_eq_zero hs hg) f := by
  have hS := HasSubst.of_constantCoeff_zero' hg
  have key := truncEval_unique ((truncEval s hs).comp (substAlgHom hS)) (truncEval s hs g)
    (truncEval_pow_eq_zero hs hg) (by rw [AlgHom.comp_apply, coe_substAlgHom, subst_X hS])
  rw [← key, AlgHom.comp_apply, coe_substAlgHom]

theorem truncEval_exp {n : ℕ} {s : S} (hs : s ^ n = 0) :
    truncEval s hs (exp ℚ) = IsNilpotent.exp s := by
  rw [truncEval_eq_sum, IsNilpotent.exp_eq_sum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_exp, Algebra.smul_def, one_div]
  simp

theorem isNilpotent_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent (truncEval s hs (log ℚ)) :=
  ⟨n, truncEval_pow_eq_zero hs constantCoeff_log⟩

theorem exp_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent.exp (truncEval s hs (log ℚ)) = 1 + s := by
  rw [← truncEval_exp (truncEval_pow_eq_zero hs constantCoeff_log),
    ← truncEval_subst hs (g := log ℚ) constantCoeff_log,
    exp_subst_log, map_add, map_one, truncEval_X]

theorem eq_zero_of_exp_eq_one {c : S} (hc : IsNilpotent c) (h : IsNilpotent.exp c = 1) : c = 0 := by
  obtain ⟨k, hk⟩ := hc
  set w : S := ∑ i ∈ Finset.range k, ((i + 1).factorial : ℚ)⁻¹ • c ^ i with hw
  have hexp : IsNilpotent.exp c = 1 + c * w := by
    rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_succ k) hk), Finset.sum_range_succ',
      hw, Finset.mul_sum]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, pow_succ, mul_comm c]
  have hw1 : IsUnit w := by
    rcases k with _ | k
    · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hk.symm)
      exact isUnit_of_subsingleton w
    · have hsplit : w = 1 + c * ∑ i ∈ Finset.range k, ((i + 2).factorial : ℚ)⁻¹ • c ^ i := by
        rw [hw, Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, pow_succ, mul_comm c]
      rw [hsplit]
      exact IsNilpotent.isUnit_one_add ⟨k + 1, by rw [mul_pow, hk, zero_mul]⟩
  have h0 : c * w = 0 := by
    have := hexp.symm.trans h
    rwa [add_eq_left] at this
  simpa using (hw1.mul_left_eq_zero).1 h0

theorem eq_of_exp_eq {a b : S} (ha : IsNilpotent a) (hb : IsNilpotent b)
    (h : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  have hnb : IsNilpotent (-b) := hb.neg
  have h1 : IsNilpotent.exp (a + -b) = 1 := by
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) ha hnb, h,
      IsNilpotent.exp_mul_exp_neg_self hb]
  have h2 := eq_zero_of_exp_eq_one (Commute.isNilpotent_add (Commute.all _ _) ha hnb) h1
  rw [← sub_eq_add_neg, sub_eq_zero] at h2
  exact h2

theorem truncEval_log_mul {l m n : ℕ} {x y z : S} (hx : x ^ l = 0) (hy : y ^ m = 0)
    (hz : z ^ n = 0) (hxyz : 1 + z = (1 + x) * (1 + y)) :
    truncEval z hz (log ℚ) = truncEval x hx (log ℚ) + truncEval y hy (log ℚ) := by
  have hnx := isNilpotent_truncEval_log hx
  have hny := isNilpotent_truncEval_log hy
  apply eq_of_exp_eq (isNilpotent_truncEval_log hz) (Commute.isNilpotent_add (Commute.all _ _) hnx hny)
  rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hny, exp_truncEval_log,
    exp_truncEval_log, exp_truncEval_log, hxyz]

end Nilpotent

section Complete

variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]

theorem mk_seriesEval_eq_truncEval {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (seriesEval I z hz f) =
      truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n) f :=
  IsAdicComplete.mk_liftAlgHom I
    (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n))
    (fun hle => factorₐ_comp_truncEval I hz hle) n f

theorem logOnePlus_mul {x y z : B} (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I)
    (hxyz : 1 + z = (1 + x) * (1 + y)) :
    logOnePlus I z hz = logOnePlus I x hx + logOnePlus I y hy := by
  refine eq_of_forall_sub_mem_pow I fun n => ?_
  rw [← Ideal.Quotient.eq, map_add (f := _), logOnePlus, logOnePlus, logOnePlus,
    mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval]
  exact truncEval_log_mul _ _ _ (by rw [← map_one (Ideal.Quotient.mk (I ^ n)), ← map_add (f := _), hxyz,
    map_mul, map_add, map_add, map_one])

end Complete

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

structure AnnulusRing (I : Set ℝ) where

@[ext]
structure Robba where

  coeff : ℤ → K
  exists_convergesAt' : ∃ r < 1, ∀ ρ, r ≤ ρ → ρ < 1 → 0 < ρ → ConvergesAt coeff ρ

variable {K}

namespace AnnulusRing

variable {I : Set ℝ}

variable [hI : Fact (∃ ρ ∈ I, 0 < ρ)]

end AnnulusRing

namespace Robba

end Robba

namespace AnnulusRing

variable {r : ℝ} [Fact (r < 1)]

end AnnulusRing

namespace Robba

end Robba

namespace Laurent

end Laurent

namespace Robba

end Robba

namespace Laurent

end Laurent

namespace Robba

end Robba

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open WittVector

section WittGeneral

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

variable [CharP R p]

theorem WittVector.frobenius_teichmuller (a : R) :
    frobenius (teichmuller p a) = teichmuller p (a ^ p) := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def]


def WittVector.teichmullerSeries (a : ℕ → R) : WittVector p R :=
  WittVector.mk p fun n => a n ^ p ^ n

omit hp [CharP R p] in
theorem WittVector.teichmullerSeries_coeff (a : ℕ → R) (n : ℕ) :
    (WittVector.teichmullerSeries (p := p) a).coeff n = a n ^ p ^ n := rfl

theorem WittVector.coeff_sum_teichmuller_mul_pow (a : ℕ → R) (n j : ℕ) :
    (∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i).coeff j =
      if j ≤ n then a j ^ p ^ j else 0 := by
  rw [WittVector.sum_coeff_eq_coeff_sum]
  · split_ifs with hj
    · rw [Finset.sum_eq_single_of_mem j (Finset.mem_Iic.2 hj) fun i _ hij =>
        teichmuller_mul_pow_coeff_of_ne _ (Ne.symm hij), teichmuller_mul_pow_coeff]
    · refine Finset.sum_eq_zero fun i hi => teichmuller_mul_pow_coeff_of_ne _ ?_
      rintro rfl
      exact hj (Finset.mem_Iic.1 hi)
  · refine fun m => ⟨fun ⟨i, _, hi⟩ ⟨k, _, hk⟩ => ?_⟩
    ext
    dsimp only [ne_eq, Set.mem_ofPred_eq] at hi hk ⊢
    rw [← Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) hi]
    exact Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) hk

variable [PerfectRing R p]

theorem WittVector.eq_teichmullerSeries_iff (a : ℕ → R) (x : WittVector p R) :
    x = WittVector.teichmullerSeries a ↔
      ∀ n, (p : WittVector p R) ^ (n + 1) ∣
        x - ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i := by
  have key : ∀ (n : ℕ) (d : WittVector p R), (p : WittVector p R) ^ (n + 1) ∣ d ↔
      ∀ j < n + 1, d.coeff j = 0 := fun n d => by
    rw [← Ideal.mem_span_singleton, mem_span_p_pow_iff_le_coeff_eq_zero]
  simp_rw [key, ← le_coeff_eq_iff_le_sub_coeff_eq_zero]
  constructor
  · rintro rfl n j hj
    rw [WittVector.coeff_sum_teichmuller_mul_pow, if_pos (Nat.lt_succ_iff.1 hj),
      WittVector.teichmullerSeries_coeff]
  · intro h
    ext j
    rw [h j j (Nat.lt_succ_self j), WittVector.coeff_sum_teichmuller_mul_pow, if_pos le_rfl,
      WittVector.teichmullerSeries_coeff]

theorem WittVector.dvd_sub_sum_teichmullerSeries (a : ℕ → R) (n : ℕ) :
    (p : WittVector p R) ^ (n + 1) ∣ WittVector.teichmullerSeries a -
      ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i :=
  (WittVector.eq_teichmullerSeries_iff a _).1 rfl n

theorem frobeniusEquiv_pow_apply (y : R) (n : ℕ) :
    ((_root_.frobeniusEquiv R p) ^ n) y = y ^ p ^ n := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, ih, _root_.frobeniusEquiv_apply, frobenius_def, ← pow_mul,
      ← pow_succ']

theorem frobeniusEquiv_symm_pow_apply_pow (y : R) (n : ℕ) :
    ((_root_.frobeniusEquiv R p).symm ^ n) y ^ p ^ n = y := by
  rw [← frobeniusEquiv_pow_apply]
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ', RingAut.mul_apply, RingAut.mul_apply, RingEquiv.apply_symm_apply, ih]

theorem WittVector.teichmullerSeries_coeff_eq (x : WittVector p R) :
    WittVector.teichmullerSeries (fun n => ((_root_.frobeniusEquiv R p).symm ^ n) (x.coeff n)) =
      x := by
  ext n
  rw [WittVector.teichmullerSeries_coeff, frobeniusEquiv_symm_pow_apply_pow]

end WittGeneral

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]



theorem WittVector.frobeniusEquiv_coeff (x : WittVector p R) (n : ℕ) :
    (WittVector.frobeniusEquiv p R x).coeff n = x.coeff n ^ p := by
  rw [WittVector.frobeniusEquiv_apply, coeff_frobenius_charP]

theorem WittVector.frobeniusEquiv_teichmuller (a : R) :
    WittVector.frobeniusEquiv p R (teichmuller p a) = teichmuller p (a ^ p) := by
  rw [WittVector.frobeniusEquiv_apply, WittVector.frobenius_teichmuller]

theorem WittVector.frobeniusEquiv_symm_teichmuller (a : R) :
    (WittVector.frobeniusEquiv p R).symm (teichmuller p a) =
      teichmuller p ((_root_.frobeniusEquiv R p).symm a) := by
  apply (WittVector.frobeniusEquiv p R).injective
  rw [RingEquiv.apply_symm_apply, WittVector.frobeniusEquiv_teichmuller, frobeniusEquiv_symm_pow_p]

theorem WittVector.frobeniusEquiv_symm_pow_teichmuller (a : R) (n : ℕ) :
    ((WittVector.frobeniusEquiv p R).symm ^ n) (teichmuller p a) =
      teichmuller p (((_root_.frobeniusEquiv R p).symm ^ n) a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, WittVector.frobeniusEquiv_symm_teichmuller, pow_succ',
      RingAut.mul_apply]

theorem WittVector.frobeniusEquiv_pow_teichmuller (a : R) (n : ℕ) :
    (WittVector.frobeniusEquiv p R ^ n) (teichmuller p a) = teichmuller p (a ^ p ^ n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, WittVector.frobeniusEquiv_teichmuller, ← pow_mul,
      ← pow_succ]

end Frobenius

abbrev AInf (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] (p : ℕ) [Fact p.Prime] :=
  WittVector p (PreTilt (normInteger K) p)

namespace AInf

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]


end AInf

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open UniformSpace

variable {p : ℕ} [Fact p.Prime]

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem algebraMap_intermediateField_cp (k : K) :
    algebraMap K ℂ_[p] k = ((k : PadicAlgCl p) : ℂ_[p]) := rfl

theorem gal_smul_algebraMap_intermediateField (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • algebraMap K ℂ_[p] k = algebraMap K ℂ_[p] k :=
  gal_smul_coe_of_mem σ k

theorem gal_smul_smul_intermediateField (σ : Gal(PadicAlgCl p/K)) (k : K) (x : ℂ_[p]) :
    σ • (k • x) = k • (σ • x) := by
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', gal_smul_algebraMap_intermediateField]

noncomputable def cycloChar : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut Gal(PadicAlgCl p/K) (PadicAlgCl p))

theorem continuous_cycloChar : Continuous (cycloChar K) :=
  cyclotomicCharacter.continuous p K (PadicAlgCl p)

theorem cycloChar_spec (σ : Gal(PadicAlgCl p/K)) {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ p ^ n = 1) :
    σ ζ = ζ ^ ((cycloChar K σ : ℤ_[p]).toZModPow n).val :=
  cyclotomicCharacter.spec p (MulSemiringAction.toRingAut Gal(PadicAlgCl p/K) (PadicAlgCl p) σ) ζ hζ

noncomputable def twistScalar (j : ℤ) (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] :=
  algebraMap ℚ_[p] ℂ_[p] (((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])

theorem twistScalar_one (j : ℤ) : twistScalar K j 1 = 1 := by
  simp [twistScalar]

theorem twistScalar_mul (j : ℤ) (σ τ : Gal(PadicAlgCl p/K)) :
    twistScalar K j (σ * τ) = twistScalar K j σ * twistScalar K j τ := by
  simp only [twistScalar, map_mul, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem twistScalar_zero (σ : Gal(PadicAlgCl p/K)) : twistScalar K 0 σ = 1 := by
  simp [twistScalar]

theorem gal_smul_twistScalar (j : ℤ) (σ τ : Gal(PadicAlgCl p/K)) :
    σ • twistScalar K j τ = twistScalar K j τ :=
  gal_smul_algebraMap σ _

noncomputable def cpTwistMap (j : ℤ) (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] →L[K] ℂ_[p] where
  toFun x := twistScalar K j σ * (σ • x)
  map_add' x y := by rw [smul_add, mul_add]
  map_smul' k x := by
    rw [gal_smul_smul_intermediateField, RingHom.id_apply, mul_smul_comm]
  cont := continuous_const.mul (continuous_const_smul σ)

theorem cpTwistMap_apply (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    cpTwistMap K j σ x = twistScalar K j σ * (σ • x) := rfl

noncomputable def cpTwistRep (j : ℤ) : ContRepresentation K Gal(PadicAlgCl p/K) ℂ_[p] :=
  .ofMonoidHom
    { toFun := cpTwistMap K j
      map_one' := by
        ext x
        simp [cpTwistMap_apply, twistScalar_one]
      map_mul' := fun σ τ => by
        ext x
        change cpTwistMap K j (σ * τ) x = cpTwistMap K j σ (cpTwistMap K j τ x)
        simp only [cpTwistMap_apply, twistScalar_mul, smul_mul', gal_smul_twistScalar, mul_smul]
        ring }

theorem cpTwistRep_apply (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    cpTwistRep K j σ x = twistScalar K j σ * (σ • x) := rfl

end GroundTheory.PAdicHodge
end
