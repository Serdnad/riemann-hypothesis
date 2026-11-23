module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle140
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle415
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FrobEis

theorem factorial_pow_dvd (r : ℕ) : ∀ k : ℕ, r.factorial ^ k ∣ (k * r).factorial
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, add_mul, one_mul]
    exact (Nat.mul_dvd_mul_right (factorial_pow_dvd r k) _).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem factorial_pow_mul_dvd {l : ℕ} (hl : 1 ≤ l) : l.factorial ^ l * l ∣ (l * l).factorial := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have h1 : (k + 1) * (k + 1) = (k * (k + 1) + k) + 1 := by ring
  have h3 := (Nat.mul_dvd_mul_right (factorial_pow_dvd (k + 1) k) k.factorial).trans
    (Nat.factorial_mul_factorial_dvd_factorial_add (k * (k + 1)) k)
  have h4 : (k + 1).factorial ^ (k + 1) * (k + 1) =
      (k + 1).factorial ^ k * k.factorial * (k * (k + 1) + k + 1) := by
    rw [Nat.factorial_succ k, pow_succ]; ring
  rw [h1, Nat.factorial_succ (k * (k + 1) + k), h4, mul_comm (k * (k + 1) + k + 1)]
  exact Nat.mul_dvd_mul_right h3 _

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_one_add {y z : Per.Acris l} {n : ℕ} (h : y ^ n = (l : Per.Acris l) * z) : IsUnit (1 + y) := by
  have := (GlobalTheory.MemLoc.acris_torsionFree_complete l).2
  have hJ : -(-y) ^ n ∈ Ideal.jacobson (⊥ : Ideal (Per.Acris l)) := by
    refine IsAdicComplete.le_jacobson_bot (Ideal.span {((l : ℕ) : Per.Acris l)}) (Ideal.mem_span_singleton.2 ⟨-((-1) ^ n * z), ?_⟩)
    rw [neg_pow, h]; ring
  have h1 := Ideal.mem_jacobson_bot.1 hJ 1
  rw [mul_one, neg_add_eq_sub] at h1
  have h2 := mul_neg_geom_sum (-y) n
  rw [sub_neg_eq_add] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ h1)

theorem isUnit_teich_pow_add {e : ℕ} (ϖ : PiSys l e) :
    IsUnit (acrisToBcris l (ainfToAcris l (ϖ.teich ^ (e * l) + l))) := by
  obtain ⟨d, hd⟩ := ϖ.exists_dpow_teich l
  obtain ⟨d₂, hd₂⟩ := ϖ.exists_dpow_teich (l * l)
  obtain ⟨m, hm⟩ := factorial_pow_mul_dvd hl.out.one_lt.le
  have hm' : ((l * l).factorial : Per.Acris l) = (l.factorial : Per.Acris l) ^ l * l * m := by
    rw [hm]; push_cast; ring
  have h3 : ((l.factorial : Per.Acris l) * d) ^ l = ainfToAcris l ϖ.teich ^ (e * (l * l)) := by
    rw [hd, ← pow_mul, mul_assoc]
  have hdl : d ^ l = l * (m * d₂) := by
    refine sub_eq_zero.1 (acris_nat_cancel (pow_ne_zero l l.factorial_ne_zero) ?_)
    push_cast
    linear_combination h3 - hd₂ + d₂ * hm'
  have hp : ((l.factorial : ℕ) : Per.Acris l) = l * ((l - 1).factorial : ℕ) := by
    rw [← Nat.mul_factorial_pred hl.out.ne_zero]; push_cast; ring
  have h1 : ainfToAcris l (ϖ.teich ^ (e * l) + l) = l * (1 + ((l - 1).factorial : Per.Acris l) * d) := by
    rw [map_add (f := _), map_pow, map_natCast, ← hd, hp]; ring
  have hy : (((l - 1).factorial : Per.Acris l) * d) ^ l =
      l * (((l - 1).factorial : Per.Acris l) ^ l * (m * d₂)) := by
    rw [mul_pow, hdl]; ring
  rw [h1, map_mul, map_natCast]
  exact (GlobalTheory.MemLoc.isUnit_l_Bcris l).mul ((isUnit_one_add hy).map _)

theorem isUnit_toB_frob_eis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ϖ : PiSys l e),
    IsUnit (toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)))) := by
  intro l _ a e _ _ O _ _ _ _ ϖ
  have hE : WittVector.frobenius (ϖ.ev a (eis l a e)) = ϖ.teich ^ (e * l) + l := by
    rw [← ϖ.ev_frobS a, eis, map_add (f := _), map_pow, frobS_X, map_natCast, map_add (f := _), map_pow, map_pow, PiSys.ev_X,
      map_natCast, ← pow_mul, mul_comm l e]
  have h : toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) =
      (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (ϖ.teich ^ (e * l) + l))) := by
    rw [frobOA_tmul, hE]; rfl
  rw [h]
  exact (isUnit_teich_pow_add ϖ).map _

end GlobalTheory.BKGal.FrobEis
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TContInj

theorem bcris_nontrivial (l : ℕ) [Fact l.Prime] : Nontrivial (Per.Bcris l) := by
  obtain ⟨j, hj⟩ := GlobalTheory.MemLoc.exists_isCrisP l
  obtain ⟨ι, -, -⟩ := GlobalTheory.MemLoc.exists_iota_cris_dR l j hj
  haveI : Nontrivial (Per.BdR l) := ⟨(GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.2.1.exists_pair_ne⟩
  exact ι.domain_nontrivial

theorem zl_bcris_injective (l : ℕ) [Fact l.Prime] : Function.Injective (algebraMap ℤ_[l] (Per.Bcris l)) := by
  haveI := bcris_nontrivial l
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra h0
  have hu : IsUnit (algebraMap ℤ_[l] (Per.Bcris l) z) := by
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]
    exact ((PadicInt.unitCoeff h0).isUnit.map _).mul ((GlobalTheory.MemLoc.isUnit_l_Bcris l).pow _)
  exact hu.ne_zero hz

theorem includeLeft_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] : Function.Injective (algebraMap O (OB l O)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ_[l] (Per.Bcris l)) (zl_bcris_injective l)
  intro x y hxy
  apply (TensorProduct.rid ℤ_[l] O).symm.injective
  apply h
  simpa [Algebra.TensorProduct.algebraMap_apply] using hxy

theorem one_tmul_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M] :
    Function.Injective (fun x : M => (1 : OB l O) ⊗ₜ[O] x) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := M)
    (Algebra.linearMap O (OB l O)) (includeLeft_injective l O)
  intro x y hxy
  apply (TensorProduct.lid O M).symm.injective
  apply h
  simpa [← Algebra.TensorProduct.one_def] using hxy

end GlobalTheory.TContInj

theorem GlobalTheory.TContInj.main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL), Function.Injective (fun x : ↥T.L.T => (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) := by
  intro l _ LL T
  haveI : Module.Free (↥(OL LL)) ↥T.L.T := T.L.free
  exact GlobalTheory.TContInj.one_tmul_injective l ↥(OL LL) ↥T.L.T
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.IdentRank

theorem basis_of_baseChange {O R N ι : Type} [CommRing O] [CommRing R] [Algebra O R] [Nontrivial R]
    [AddCommGroup N] [Module O N] [Module.Free O N] [Module.Finite O N] [Fintype ι]
    (j : (ι → R) ≃ₗ[R] R ⊗[O] N) : Nonempty (Module.Basis ι O N) := by
  classical
  have : Nontrivial O := (algebraMap O R).domain_nontrivial
  let b := Module.Free.chooseBasis O N
  have h1 := Module.finrank_eq_card_basis (Algebra.TensorProduct.basis R b)
  have h2 := j.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, h1] at h2
  exact ⟨b.reindex (Fintype.equivOfCardEq h2.symm)⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL), Ident (thetaW a LL) ϖ P T → Nonempty (Module.Basis ι ↥(OL LL) ↥T.L.T) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I
  have := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  obtain ⟨hs, hk, -⟩ := GlobalTheory.ArtinSchreierWitt.main l
  haveI : Module.Flat ℤ_[l] ↥(OL LL) := Module.Flat.of_free
  obtain ⟨-, -, h3⟩ := GlobalTheory.WittTensorFixed.baseChange_flat (O := ↥(OL LL)) (frobW l) hs hk
    (GlobalTheory.WittTensorFixed.algebraMap_WCb_injective l)
  have : Nontrivial (OW l ↥(OL LL)) := h3.nontrivial
  exact basis_of_baseChange I.j

end GlobalTheory.BKGal.IdentRank
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TContNbhd

theorem norm_le_one_of_isIntegral' {R C : Type} [CommRing R] [NormedField C] [IsUltrametricDist C]
    [Algebra R C] (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {x : C} (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  let f : R →+* (NormedField.valuation (K := C)).integer :=
    (algebraMap R C).codRestrict _ (fun r => by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
      exact hR r)
  have h1 : IsIntegral (NormedField.valuation (K := C)).integer x :=
    hx.map_of_comp_eq f (RingHom.id C) (by ext r; rfl)
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h1
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe] at h2
  exact h2

variable {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_le (LL : FinExt l) (r : ℤ_[l]) : ‖algebraMap ℤ_[l] ↥LL.1 r‖ ≤ 1 := by
  change ‖((algebraMap ℤ_[l] ↥LL.1 r : ↥LL.1) : PadicAlgCl l)‖ ≤ 1
  have : ((algebraMap ℤ_[l] ↥LL.1 r : ↥LL.1) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (r : ℚ_[l]) := rfl
  rw [this, norm_algebraMap']
  exact PadicInt.norm_le_one r

theorem norm_le_one_of_mem (LL : FinExt l) (c : ↥(OL LL)) : ‖(c : ↥LL.1)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' (R := ℤ_[l]) (norm_algebraMap_le LL) c.2

theorem norm_natCast_lt_one (LL : FinExt l) : ‖(l : ↥LL.1)‖ < 1 := by
  change ‖((l : ↥LL.1) : PadicAlgCl l)‖ < 1
  have : ((l : ↥LL.1) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (U : Set T.V), U ∈ nhds (0 : T.V) → ∃ m : ℕ, ∀ x ∈ T.L.T, ((l : ↥LL.1) ^ m) • x ∈ U := by
  intro l _ LL T U hU
  classical
  obtain ⟨s, hs⟩ := T.L.fg
  let f : (↥s → ↥LL.1) → T.V := fun a => ∑ t : ↥s, a t • (t : T.V)
  have hf : Continuous f := continuous_finsetSum _ fun t _ => (continuous_apply t).smul continuous_const
  have h0 : f 0 = 0 := by simp [f]
  have hpre : f ⁻¹' U ∈ nhds (0 : ↥s → ↥LL.1) := hf.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_lt_one LL)
  refine ⟨m, fun x hx => ?_⟩
  rw [← hs] at hx
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hx
  let a : ↥s → ↥LL.1 := fun t => (l : ↥LL.1) ^ m * ((c t : ↥(OL LL)) : ↥LL.1)
  have ha : ‖a‖ < ε := by
    refine (pi_norm_lt_iff hε).2 fun t => ?_
    calc ‖a t‖ = ‖(l : ↥LL.1)‖ ^ m * ‖((c t : ↥(OL LL)) : ↥LL.1)‖ := by simp [a, norm_pow]
      _ ≤ ‖(l : ↥LL.1)‖ ^ m * 1 := by gcongr; exact norm_le_one_of_mem LL (c t)
      _ < ε := by rw [mul_one]; exact hm
  have hfa : f a = ((l : ↥LL.1) ^ m) • x := by
    rw [← hc, Finset.smul_sum]
    simp only [f, a]
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_smul]
    congr 1
    exact algebraMap_smul (↥LL.1) (c t) (t : T.V)
  have : a ∈ f ⁻¹' U := hball (mem_ball_zero_iff.2 ha)
  rw [Set.mem_preimage, hfa] at this
  exact this
end GlobalTheory.TContNbhd
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.IntegralPowerScalar

theorem exists_pow_mul_integral {l : ℕ} [Fact (Nat.Prime l)] (LL : FinExt l) (c : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * c ∈ OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h1 : IsAlgebraic ℚ_[l] c := IsAlgebraic.of_finite ℚ_[l] c
  have h2 : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have hs := PadicInt.unitCoeff_spec hy
  have hm : y • c ∈ OL LL := hint
  have hm2 := (OL LL).smul_mem hm (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  have he : (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * y = (l : ℤ_[l]) ^ y.valuation := by
    exact (Units.inv_mul_eq_iff_eq_mul _).2 hs
  rw [smul_smul, he, Algebra.smul_def, map_pow, map_natCast] at hm2
  exact hm2

theorem smul_mem_of_mem {l : ℕ} [Fact (Nat.Prime l)] {LL : FinExt l} (T : GlobalTheory.BKGal.QLat LL)
    {c : ↥LL.1} (hc : c ∈ OL LL) {x : T.V} (hx : x ∈ T.L.T) : c • x ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(OL LL)) hx
  rw [← algebraMap_smul ↥LL.1 (⟨c, hc⟩ : ↥(OL LL)) x] at h
  exact h

theorem exists_pow_smul_mem {l : ℕ} [inst : Fact (Nat.Prime l)] {LL : FinExt l}
    (T : GlobalTheory.BKGal.QLat LL) (v : T.V) : ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  have hl : ∀ k : ℕ, (l : ↥LL.1) ^ k ∈ OL LL := fun k => pow_mem (natCast_mem (OL LL) l) k
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h1 := smul_mem_of_mem T (hl n) hm
    have h2 := smul_mem_of_mem T (hl m) hn
    rw [smul_smul, ← pow_add, Nat.add_comm] at h1
    rw [smul_smul, ← pow_add] at h2
    rw [smul_add]
    exact T.L.T.add_mem h1 h2
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := exists_pow_mul_integral LL c
    refine ⟨n + m, ?_⟩
    have h := smul_mem_of_mem T hn hm
    have e : (l : ↥LL.1) ^ (n + m) * c = (l : ↥LL.1) ^ n * c * (l : ↥LL.1) ^ m := by ring
    have e2 : (l : ↥LL.1) ^ (n + m) • c • x = ((l : ↥LL.1) ^ n * c) • (l : ↥LL.1) ^ m • x :=
      (smul_smul _ _ x).trans ((congrArg (fun a : ↥LL.1 => a • x) e).trans (smul_smul _ _ x).symm)
    exact Eq.mpr (congrArg (fun w : T.V => w ∈ T.L.T) e2) h

end GlobalTheory.IntegralPowerScalar
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LatticePowerScalar

theorem exists_pow_mul_isIntegral {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K]
    [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] {c : K} (hc : IsAlgebraic ℚ_[l] c) :
    ∃ n : ℕ, IsIntegral ℤ_[l] ((l : K) ^ n * c) := by
  have h1 : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] K).2 hc
  obtain ⟨y, hy, hyc⟩ := h1.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have h2 : (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * y = (l : ℤ_[l]) ^ y.valuation := by
    rw [Units.inv_mul_eq_iff_eq_mul]
    exact PadicInt.unitCoeff_spec hy
  have h3 : (l : K) ^ y.valuation * c = (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (y • c) := by
    rw [← mul_smul, h2, Algebra.smul_def, map_pow, map_natCast]
  rw [h3]
  exact hyc.smul _

theorem exists_pow_smul_mem {O K V : Type} [CommRing O] [CommRing K] [Algebra O K] [AddCommGroup V]
    [Module K V] [Module O V] [IsScalarTower O K V] (p : O)
    (hp : ∀ c : K, ∃ (n : ℕ) (o : O), algebraMap O K p ^ n * c = algebraMap O K o)
    (M : Submodule O V) (v : V) (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ n : ℕ, algebraMap O K p ^ n • v ∈ M := by
  have up : ∀ (n k : ℕ) (x : V), algebraMap O K p ^ n • x ∈ M → algebraMap O K p ^ (k + n) • x ∈ M := by
    intro n k x hx
    rw [pow_add, mul_smul, ← map_pow, algebraMap_smul]
    exact M.smul_mem _ hx
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rwa [pow_zero, one_smul]⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    rw [smul_add]
    exact M.add_mem (add_comm n m ▸ up m n x hm) (up n m y hn)
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, o, ho⟩ := hp c
    refine ⟨n + m, ?_⟩
    have h : algebraMap O K p ^ (n + m) • c • x = o • (algebraMap O K p ^ m • x) := by
      rw [← algebraMap_smul K o, ← ho, smul_smul, smul_smul, pow_add]
      congr 1
      ring
    rw [h]
    exact M.smul_mem _ hm

theorem exists_pow_smul_mem_lattice {l : ℕ} [Fact (Nat.Prime l)] (LL : FinExt l) (T : GlobalTheory.BKGal.QLat LL) :
    ∀ v ∈ Submodule.span ↥LL.1 ((T.L.T : Submodule ↥(OL LL) T.V) : Set T.V),
      ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  intro v hv
  have hl : algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL)) = (l : ↥LL.1) := map_natCast _ l
  rw [← hl]
  refine exists_pow_smul_mem (l : ↥(OL LL)) (fun c => ?_) T.L.T v hv
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨n, hn⟩ := exists_pow_mul_isIntegral (l := l) (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) c)
  exact ⟨n, ⟨(l : ↥LL.1) ^ n * c, hn⟩, by rw [hl]; rfl⟩

end GlobalTheory.LatticePowerScalar
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.BKGal

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]

theorem inclL_smul_coord (P : PhiMod O K l e a ι) (m : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (fun i => m * c i) = inclO l O m • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply]
  have h : (fun i => inclO l O (m * c i)) = inclO l O m • fun i => inclO l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  rw [h, Matrix.mulVec_smul]

theorem IsCrisVal.sub {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w w' : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w' b') : IsCrisVal t ϖ P jB (w - w') (b - b') := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  obtain ⟨m', c', hu', hc', hb'⟩ := h'
  refine ⟨m * m', fun i => m' * c i - m * c' i, by rw [map_mul]; exact hu.mul hu', ?_, ?_⟩
  · have e1 : (fun i => m' * c i - m * c' i) = (fun i => m' * c i) - (fun i => m * c' i) := rfl
    rw [e1, map_sub, inclL_smul_coord, inclL_smul_coord, ← hc, ← hc', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (inclO l O m')]
  · have e2 : (fun i => toB l O (m' * c i - m * c' i)) =
        toB l O m' • (fun i => toB l O (c i)) - toB l O m • (fun i => toB l O (c' i)) :=
      funext fun i => by simp only [map_sub, map_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e2, map_sub, map_smul, map_smul, ← hb, ← hb', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (toB l O m')]

end GlobalTheory.BKGal
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.IKRes

theorem norm_gal_ql {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv g x).symm

theorem mem_IK_ql_iff : ∀ (l : ℕ) [Fact l.Prime] (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖(g : GQ l) x - x‖ < 1 := by
  intro l _ g
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem σ hσ => exact hσ
    | one => intro x _; simp
    | mul σ τ _ _ hσ hτ =>
      intro x hx
      have h1 : ‖(σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x‖ < 1 :=
        hσ _ (by rwa [norm_gal_ql])
      have h2 := hτ x hx
      have he : ((σ * τ : Gl l) : GQ l) x - x =
          ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) + ((τ : GQ l) x - x) := by
        rw [Subgroup.coe_mul, AlgEquiv.mul_apply]; abel
      rw [he]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
    | inv σ _ hσ =>
      intro x hx
      have hy : ‖((σ : GQ l)⁻¹) x‖ ≤ 1 := by rwa [norm_gal_ql]
      have h := hσ _ hy
      have hx' : (σ : GQ l) (((σ : GQ l)⁻¹) x) = x := by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
      rw [hx', norm_sub_rev] at h
      simpa [Subgroup.coe_inv] using h
  · intro h
    exact Subgroup.subset_closure h

end GlobalTheory.IKRes
end
end
