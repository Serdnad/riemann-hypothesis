module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle321
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle355
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle356
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.RatioUnit

theorem natCast_notMem_of_primes {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ m : ℕ, m ≠ 0 → (∀ p : ℕ, p.Prime → p ∣ m → (p : R) ∉ P) → (m : R) ∉ P := by
  intro m
  induction m using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; rw [Nat.cast_one]; exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  | prime p hp => intro _ h; exact h p hp dvd_rfl
  | mul a b ha hb =>
    intro hab h hmem
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact ha (left_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_left hd b)) h1
    · exact hb (right_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_right hd a)) h1

theorem not_dvd_both {r : ℚ} {p : ℕ} (hp : p.Prime) (h1 : p ∣ r.num.natAbs) (h2 : p ∣ r.den) : False :=
  hp.not_dvd_one (by simpa [Nat.Coprime.gcd_eq_one r.reduced] using Nat.dvd_gcd h1 h2)

theorem padicValRat_ne_zero_of_dvd_num {r : ℚ} (hr : r ≠ 0) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ r.num.natAbs) : padicValRat p r ≠ 0 := by
  haveI := Fact.mk hp
  have hnd : ¬ p ∣ r.den := fun hd' => not_dvd_both hp hd hd'
  have h0 : r.num.natAbs ≠ 0 := by simpa using hr
  have h1 := one_le_padicValNat_of_dvd h0 hd
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]
  omega

theorem padicValRat_ne_zero_of_dvd_den {r : ℚ} {p : ℕ} (hp : p.Prime)
    (hd : p ∣ r.den) : padicValRat p r ≠ 0 := by
  haveI := Fact.mk hp
  have hnd : ¬ p ∣ r.num.natAbs := fun hd' => not_dvd_both hp hd' hd
  have h1 := one_le_padicValNat_of_dvd r.den_nz hd
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]
  omega

end GlobalTheory.Fam.RatioUnit

namespace GlobalTheory.Fam
open Formalism.DivisionValues GlobalTheory.Fam.RatioUnit

theorem RatioUnit.intCast_notMem_of_natAbs {R : Type} [CommRing R] (P : Ideal R) (z : ℤ)
    (h : ((z.natAbs : ℕ) : R) ∉ P) : ((z : ℤ) : R) ∉ P := by
  rcases Int.natAbs_eq z with e | e
  · rw [e]; simpa using h
  · rw [e]; simpa [Ideal.neg_mem_iff] using h

theorem vw_eq_zero_of_unitRatio : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (S : ℕ → Prop) (x y : ℂ), GlobalTheory.Fam.UnitRatio S x y → (∀ p : ℕ, p.Prime → S p → (p : 𝓞 K) ∉ w.asIdeal) → ∀ a : K, σ a = x / y → Formalism.DivisionValues.vw w a = 0 := by
  intro K _ _ σ w S x y hU hS a ha

  letI : StarRing K := starRingOfComm
  obtain ⟨_, n, hn, r, hr0, hpow, hrS⟩ := hU
  have hpow' : a ^ n = (r : K) := by
    apply σ.injective
    rw [map_pow, ha, hpow, map_ratCast]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hpow'
    exact hr0 (by exact_mod_cast hpow'.symm)
  have hnum : ((r.num : ℤ) : 𝓞 K) ∉ w.asIdeal := by
    refine intCast_notMem_of_natAbs _ _ (natCast_notMem_of_primes w.asIdeal _ (by simpa using hr0) ?_)
    intro p hp hd
    exact hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_num hr0 hp hd))
  have hden : ((r.den : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    refine natCast_notMem_of_primes w.asIdeal _ r.den_nz ?_
    intro p hp hd
    exact hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_den hp hd))
  have vnum := ReductionFirst.vw_unit w _ hnum
  have vden := ReductionFirst.vw_unit w _ hden
  rw [show (((r.num : ℤ) : 𝓞 K) : K) = (r.num : K) from map_intCast (algebraMap (𝓞 K) K) _] at vnum
  rw [show (((r.den : ℕ) : 𝓞 K) : K) = (r.den : K) from map_natCast (algebraMap (𝓞 K) K) _] at vden
  have hd0 : (r.den : K) ≠ 0 := by exact_mod_cast r.den_nz
  have hrK0 : (r : K) ≠ 0 := by exact_mod_cast hr0
  have key : (r : K) * (r.den : K) = (r.num : K) := by
    rw [Rat.cast_def]; field_simp
  have h1 := ReductionFirst.vw_mul w hrK0 hd0
  rw [key, vnum, vden] at h1
  have h2 := ReductionFirst.vw_pow w a n
  rw [hpow'] at h2
  have h3 : (n : ℤ) * vw w a = 0 := by rw [← h2]; omega
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (by exact_mod_cast h) hn.ne'
  · exact h

end GlobalTheory.Fam
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem padicValRat_pow_mul_pow_ne_zero_imp {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (a b : ℕ) (p : ℕ) (hp : p.Prime)
    (h : padicValRat p (r ^ a * s ^ b) ≠ 0) : padicValRat p r ≠ 0 ∨ padicValRat p s ≠ 0 := by
  haveI := Fact.mk hp
  by_contra hc
  push_neg at hc
  apply h
  rw [padicValRat.mul (pow_ne_zero _ hr) (pow_ne_zero _ hs), padicValRat.pow r, padicValRat.pow s, hc.1, hc.2]
  simp

theorem padicValRat_pow_div_pow_ne_zero_imp {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (a b : ℕ) (p : ℕ) (hp : p.Prime)
    (h : padicValRat p (r ^ a / s ^ b) ≠ 0) : padicValRat p r ≠ 0 ∨ padicValRat p s ≠ 0 := by
  haveI := Fact.mk hp
  by_contra hc
  push_neg at hc
  apply h
  rw [padicValRat.div (pow_ne_zero _ hr) (pow_ne_zero _ hs), padicValRat.pow r, padicValRat.pow s, hc.1, hc.2]
  simp

theorem unitRatio_ne_zero {S : ℕ → Prop} {x y : ℂ} (h : UnitRatio S x y) : x ≠ 0 := by
  obtain ⟨hy, n, hn, r, hr, he, -⟩ := h
  intro hx
  rw [hx, zero_div, zero_pow hn.ne'] at he
  exact hr (by exact_mod_cast he.symm)

theorem unitRatio_refl (S : ℕ → Prop) {y : ℂ} (hy : y ≠ 0) : UnitRatio S y y :=
  ⟨hy, 1, one_pos, 1, one_ne_zero, by simp [div_self hy], fun p _ h => by simp at h⟩

theorem unitRatio_mul {S : ℕ → Prop} {x y x' y' : ℂ} (h : UnitRatio S x y) (h' : UnitRatio S x' y') :
    UnitRatio S (x * x') (y * y') := by
  obtain ⟨hy, n, hn, r, hr, he, hS⟩ := h
  obtain ⟨hy', n', hn', r', hr', he', hS'⟩ := h'
  refine ⟨mul_ne_zero hy hy', n * n', Nat.mul_pos hn hn', r ^ n' * r' ^ n,
    mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hr'), ?_, ?_⟩
  · have : x * x' / (y * y') = (x / y) * (x' / y') := by field_simp
    rw [this, mul_pow, pow_mul, pow_mul, he, ← pow_mul, mul_comm n n', pow_mul, he']
    push_cast; ring
  · intro p hp hv
    rcases padicValRat_pow_mul_pow_ne_zero_imp hr hr' n' n p hp hv with h1 | h1
    · exact hS p hp h1
    · exact hS' p hp h1

theorem unitRatio_div {S : ℕ → Prop} {x y x' y' : ℂ} (h : UnitRatio S x y) (h' : UnitRatio S x' y') :
    UnitRatio S (x / x') (y / y') := by
  have hx' := unitRatio_ne_zero h'
  obtain ⟨hy, n, hn, r, hr, he, hS⟩ := h
  obtain ⟨hy', n', hn', r', hr', he', hS'⟩ := h'
  refine ⟨div_ne_zero hy hy', n * n', Nat.mul_pos hn hn', r ^ n' / r' ^ n,
    div_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hr'), ?_, ?_⟩
  · have : x / x' / (y / y') = (x / y) / (x' / y') := by field_simp
    rw [this, div_pow, pow_mul, pow_mul, he, ← pow_mul, mul_comm n n', pow_mul, he']
    push_cast; ring
  · intro p hp hv
    rcases padicValRat_pow_div_pow_ne_zero_imp hr hr' n' n p hp hv with h1 | h1
    · exact hS p hp h1
    · exact hS' p hp h1

theorem unitRatio_of_pow_eq (S : ℕ → Prop) {x y : ℂ} {n : ℕ} (hy : y ≠ 0) (hn : 0 < n) (h : x ^ n = y ^ n) :
    UnitRatio S x y :=
  ⟨hy, n, hn, 1, one_ne_zero, by rw [div_pow, h, div_self (pow_ne_zero _ hy)]; simp, fun p _ h => by simp at h⟩

theorem unitRatio_prod (S : ℕ → Prop) {I : Type} (s : Finset I) (x y : I → ℂ)
    (h : ∀ i ∈ s, UnitRatio S (x i) (y i)) : UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitRatio_refl S one_ne_zero
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact unitRatio_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitRatio_laws : ∀ S : ℕ → Prop, (∀ y : ℂ, y ≠ 0 → UnitRatio S y y) ∧ (∀ x y x' y' : ℂ, UnitRatio S x y → UnitRatio S x' y' → UnitRatio S (x * x') (y * y') ∧ UnitRatio S (x / x') (y / y') ∧ x ≠ 0) ∧ (∀ (x y : ℂ) (n : ℕ), y ≠ 0 → 0 < n → x ^ n = y ^ n → UnitRatio S x y) ∧ ∀ (I : Type) (s : Finset I) (x y : I → ℂ), (∀ i ∈ s, UnitRatio S (x i) (y i)) → UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) :=
  fun S => ⟨fun y hy => unitRatio_refl S hy,
    fun x y x' y' h h' => ⟨unitRatio_mul h h', unitRatio_div h h', unitRatio_ne_zero h⟩,
    fun x y n hy hn h => unitRatio_of_pow_eq S hy hn h,
    fun I s x y h => unitRatio_prod S s x y h⟩

end GlobalTheory.Fam
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.WeilSumScalar
variable {D : D7} {S A B T : HSp D} (o : OrthDec S A B)

def opA (M : Module.End ℂ (WO A T → ℂ)) : Module.End ℂ (WO S T → ℂ) where
  toFun f x := M (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1
  map_add' f g := by funext x; show M (_ + _) _ = _; rw [map_add (f := _)]; rfl
  map_smul' c f := by funext x; show M (c • _) _ = _; rw [map_smul]; rfl

def opB (M : Module.End ℂ (WO B T → ℂ)) : Module.End ℂ (WO S T → ℂ) where
  toFun f x := M (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2
  map_add' f g := by funext x; show M (_ + _) _ = _; rw [map_add (f := _)]; rfl
  map_smul' c f := by funext x; show M (c • _) _ = _; rw [map_smul]; rfl

theorem opA_apply (M : Module.End ℂ (WO A T → ℂ)) (f : WO S T → ℂ) (x : WO S T) :
    opA o M f x = M (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 := rfl

theorem opB_apply (M : Module.End ℂ (WO B T → ℂ)) (f : WO S T → ℂ) (x : WO S T) :
    opB o M f x = M (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2 := rfl

theorem heisO_sum (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WO S T → ℂ) (u : WO A T) (v : WO B T) :
    heisO ψ S T w f ((o.resS T).symm (u, v)) =
      ψ (symplOH A T u (o.resS T w).1) * ψ (symplOH B T v (o.resS T w).2) *
        f ((o.resS T).symm (u + (o.resS T w).1, v + (o.resS T w).2)) := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddChar.map_add_eq_mul]
  congr 2
  rw [← Prod.mk_add_mk, map_add (f := _), AddEquiv.symm_apply_apply]

theorem opB_heisO {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle} {om : Om B T}
    (hom : IsWeilDatumO ψ B T χ χ' om) (b : GA D B) (h : GA D T) (w : WO S T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    opB o (om (b, h)) (heisO ψ S T w f) =
      heisO ψ S T ((o.resS T).symm ((o.resS T w).1, actO B T b h (o.resS T w).2)) (opB o (om (b, h)) f) := by
  funext x
  obtain ⟨⟨u, v⟩, rfl⟩ := (o.resS T).symm.surjective x
  have hg := ((GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hom.std S A B T o).2.2.2 f hf).2 (u + (o.resS T w).1)
  have e : (fun v' => heisO ψ S T w f ((o.resS T).symm (u, v'))) =
      ψ (symplOH A T u (o.resS T w).1) •
        heisO ψ B T (o.resS T w).2 (fun v' => f ((o.resS T).symm (u + (o.resS T w).1, v'))) := by
    funext v'
    rw [heisO_sum, Pi.smul_apply, smul_eq_mul, heisO]
    ring
  rw [heisO_sum, opB_apply, opB_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  simp only [AddEquiv.apply_symm_apply]
  rw [e, map_smul, hom.om_heis b h _ _ hg, Pi.smul_apply, smul_eq_mul, heisO]
  ring

theorem opA_heisO {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle} {om : Om A T}
    (hom : IsWeilDatumO ψ A T χ χ' om) (a : GA D A) (h : GA D T) (w : WO S T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    opA o (om (a, h)) (heisO ψ S T w f) =
      heisO ψ S T ((o.resS T).symm (actO A T a h (o.resS T w).1, (o.resS T w).2)) (opA o (om (a, h)) f) := by
  funext x
  obtain ⟨⟨u, v⟩, rfl⟩ := (o.resS T).symm.surjective x
  have hg := ((GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hom.std S A B T o).2.2.2 f hf).1 (v + (o.resS T w).2)
  have e : (fun u' => heisO ψ S T w f ((o.resS T).symm (u', v))) =
      ψ (symplOH B T v (o.resS T w).2) •
        heisO ψ A T (o.resS T w).1 (fun u' => f ((o.resS T).symm (u', v + (o.resS T w).2))) := by
    funext u'
    rw [heisO_sum, Pi.smul_apply, smul_eq_mul, heisO]
    ring
  rw [heisO_sum, opA_apply, opA_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  simp only [AddEquiv.apply_symm_apply]
  rw [e, map_smul, hom.om_heis a h _ _ hg, Pi.smul_apply, smul_eq_mul, heisO]
  ring

def opAB (omA : Om A T) (omB : Om B T) (a : GA D A) (b : GA D B) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  opA o (omA (a, h)) * opB o (omB (b, h))

end GlobalTheory.WeilSumScalar


open GlobalTheory.WeilSumScalar in
theorem GlobalTheory.WeilSumScalar.omS_eq_smul_prod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χA χB χT : (AE D)ˣ →* Circle) (omS : Om S T) (omA : Om A T) (omB : Om B T), IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB → ∀ a b h, ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → ∀ u v, omS (o.emb (a, b), h) f ((o.resS T).symm (u, v)) = (c : ℂ) * omA (a, h) (fun u' => omB (b, h) (fun v' => f ((o.resS T).symm (u', v'))) v) u := by
  intro D ψ S A B T o χA χB χT omS omA omB hS hA hB a b h
  set N := opAB o omA omB a b h with hN
  set p : GA D S × GA D T := (o.emb (a, b), h) with hp
  have hNapp : ∀ f, N f = opA o (omA (a, h)) (opB o (omB (b, h)) f) := fun f => rfl

  have hNpres : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (N f) := by
    intro f hf
    have h1 : IsThetaFunO ψ S T (opB o (omB (b, h)) f) := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o f hf).2 _ _ _ hB (b, h)
    rw [hNapp]
    exact (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o _ h1).1 _ _ _ hA (a, h)

  have hNheis : ∀ w f, IsThetaFunO ψ S T f → N (heisO ψ S T w f) = heisO ψ S T (actO S T (o.emb (a, b)) h w) (N f) := by
    intro w f hf
    have h1 : IsThetaFunO ψ S T (opB o (omB (b, h)) f) := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o f hf).2 _ _ _ hB (b, h)
    rw [hNapp, hNapp, opB_heisO o hB b h w hf, opA_heisO o hA a h _ h1]
    congr 1
    rw [AddEquiv.apply_symm_apply, ← o.resS_actO T a b h w, AddEquiv.symm_apply_apply]

  have hNunit : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖N f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
    intro μ 𝓕 hμ h𝓕 f hf
    have h1 : IsThetaFunO ψ S T (opB o (omB (b, h)) f) := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o f hf).2 _ _ _ hB (b, h)
    rw [hNapp]
    exact ((GlobalTheory.T.weil_operator_one_variable_preserves_sq_norm_orthogonal_sum D ψ S A B T o μ 𝓕 hμ h𝓕 _ h1).1 _ _ _ hA (a, h)).trans
      ((GlobalTheory.T.weil_operator_one_variable_preserves_sq_norm_orthogonal_sum D ψ S A B T o μ 𝓕 hμ h𝓕 f hf).2 _ _ _ hB (b, h))

  have hinv : ∀ g, omS p (omS p⁻¹ g) = g := by
    intro g
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨c, hc, hM⟩ := GlobalTheory.ThetaSchur.schur D ψ hS.std S T (omS p⁻¹ * N)
    (fun f hf => hS.om_pres _ _ (hNpres f hf))
    (fun w f hf => by
      have hpi : p⁻¹ = ((o.emb (a, b))⁻¹, h⁻¹) := rfl
      have hw := GlobalTheory.AdelicLatMove.actO_actO_inv S T (o.emb (a, b))⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at hw
      rw [Module.End.mul_apply, Module.End.mul_apply, hNheis w f hf, hpi,
        hS.om_heis _ _ _ _ (hNpres f hf), hw])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hS.om_unit μ 𝓕 hμ h𝓕 _ _ (hNpres f hf), hNunit μ 𝓕 hμ h𝓕 f hf])
  have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc
  refine ⟨⟨c⁻¹, by simp [Submonoid.unitSphere, hc]⟩, fun f hf u v => ?_⟩
  have e : N f = c • omS p f := by
    have := congrArg (omS p) (hM f hf)
    rwa [Module.End.mul_apply, hinv, map_smul] at this
  have e2 : omS p f = c⁻¹ • N f := by rw [e, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e2, Pi.smul_apply, smul_eq_mul, hNapp, opA_apply]
  simp only [AddEquiv.apply_symm_apply, opB_apply]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FinPl.PutIn.Factor

variable {D : D7}

theorem half_nsmul {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := fun i j => by
  have h := hx i j
  simp only [Matrix.smul_apply, nsmul_eq_mul]
  linear_combination (k : AE D) * h

theorem isSBHalf_of_half_eq {S T : HSp D} {b : AE D} {Λ Λ' : AddSubgroup (WO S T)} {Ψ : WO S T → ℂ}
    (hΛ : ∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) (hΨ : IsSBHalf b Λ' Ψ) : IsSBHalf b Λ Ψ := by
  obtain ⟨hsupp, k, hk, hinv, hfin⟩ := hΨ
  refine ⟨hsupp, k, hk, fun u hu hub t => hinv u ((hΛ u hub).2 hu) hub t, fun t ht => ?_⟩
  exact (hΛ _ (half_nsmul (hsupp t ht) k)).1 (hfin t ht)

theorem half_smul_self {m n : ℕ} {b : AE D} {x : Mx D m n} (hx : IsHalf b x) : b • x = x := by
  ext i j; exact hx i j

theorem half_of_idem {m n : ℕ} {b : AE D} (hb : b * b = b) (t : Mx D m n) : IsHalf b (b • t) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination (t i j) * hb

theorem isSBHalf_tens {S T : HSp D} {a b : AE D} {Λ : AddSubgroup (WO S T)} {Φ Ψ : WO S T → ℂ}
    (hab : a * b = 0) (hb : b * b = b) (hbΛ : ∀ u ∈ Λ, b • u ∈ Λ) (hΦ : IsSBHalf a Λ Φ) (hΨ : IsSBHalf b Λ Ψ) :
    IsSBHalf (a + b) Λ (tens b Φ Ψ) := by
  obtain ⟨sΦ, kΦ, hkΦ, iΦ, fΦ⟩ := hΦ
  obtain ⟨sΨ, kΨ, hkΨ, iΨ, fΨ⟩ := hΨ
  have hne : ∀ t, tens b Φ Ψ t ≠ 0 → Φ (t - b • t) ≠ 0 ∧ Ψ (b • t) ≠ 0 := fun t ht => by
    rw [tens_apply] at ht
    exact ⟨left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩
  refine ⟨fun t ht => ?_, kΦ * kΨ, Nat.mul_pos hkΦ hkΨ, fun u hu hua t => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, -⟩ := hne t ht
    intro i j
    have h := sΦ _ h1 i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    linear_combination h + (t i j) * hab
  · have hbu : b • u ∈ Λ := hbΛ u hu
    have hsub : u - b • u ∈ Λ := Λ.sub_mem hu hbu
    have hau : IsHalf a (u - b • u) := fun i j => by
      have e1 := hua i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination e1 - (u i j) * hab - (u i j) * hb + (u i j) * hb
    have hA : (t + (kΦ * kΨ) • u) - b • (t + (kΦ * kΨ) • u) = (t - b • t) + kΦ • (kΨ • (u - b • u)) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    have hB : b • (t + (kΦ * kΨ) • u) = b • t + kΨ • (kΦ • (b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [tens_apply, tens_apply, hA, hB,
      iΦ _ (AddSubgroup.nsmul_mem Λ hsub kΨ) (half_nsmul hau kΨ),
      iΨ _ (AddSubgroup.nsmul_mem Λ hbu kΦ) (half_nsmul (half_of_idem hb u) kΦ)]
  · obtain ⟨h1, h2⟩ := hne t ht
    have hC : (kΦ * kΨ) • t = kΨ • (kΦ • (t - b • t)) + kΦ • (kΨ • (b • t)) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [hC]
    exact Λ.add_mem (AddSubgroup.nsmul_mem Λ (fΦ _ h1) kΨ) (AddSubgroup.nsmul_mem Λ (fΨ _ h2) kΦ)


open GlobalTheory.LocMod.TensorModel in
theorem isPlaceModel_tensR : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → (∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) → IsSBHalf a Λ Φ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ' 1 (Tm (GlobalTheory.FinPl.PutIn.tens b Φ (halfInd b Λ))) (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensR b Φ) := by
  intro D ψ S T a b Λ Λ' Φ f₀ Tm hab hb hbΛ hΛ hΦ hP
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
  · have hΨ' := isSBHalf_of_half_eq hΛ hΨ
    have key : tens b Φ (fun t => Ψ (t + x)) = fun t => tens b Φ Ψ (t + x) := by
      funext t
      simp only [tens_apply]
      rw [smul_add, half_smul_self hx, add_sub_add_right_eq_sub]
    simp only [LinearMap.comp_apply, tensR_apply]
    rw [key]
    exact hP.trans _ (isSBHalf_tens hab hb hbΛ hΦ hΨ') x (half_sum hab hx)
  · have hΨ' := isSBHalf_of_half_eq hΛ hΨ
    have key : tens b Φ (fun t => ψ (symplO S T t y) * Ψ t) = fun t => ψ (symplO S T t y) * tens b Φ Ψ t := by
      funext t
      simp only [tens_apply]
      by_cases h0 : Φ (t - b • t) = 0
      · rw [h0]; ring
      · have e1 : symplO S T t y = symplO S T (t - b • t) y + symplO S T (b • t) y := by
          rw [← symplO_add_left', sub_add_cancel]
        rw [e1, symplO_half_zero hab (hΦ.1 _ h0) hy, zero_add]
        ring
    simp only [LinearMap.comp_apply, tensR_apply]
    rw [key]
    exact hP.modul _ (isSBHalf_tens hab hb hbΛ hΦ hΨ') y (half_sum_cA hab hy)
  · have hind : halfInd b Λ' = halfInd b Λ := by
      funext t
      unfold halfInd
      have hiff : (t ∈ Λ' ∧ IsHalf b t) ↔ (t ∈ Λ ∧ IsHalf b t) :=
        ⟨fun h => ⟨(hΛ t h.2).1 h.1, h.2⟩, fun h => ⟨(hΛ t h.2).2 h.1, h.2⟩⟩
      by_cases h : t ∈ Λ ∧ IsHalf b t
      · rw [if_pos (hiff.2 h), if_pos h]
      · rw [if_neg (mt hiff.1 h), if_neg h]
    rw [one_smul, hind]
    rfl

end GlobalTheory.FinPl.PutIn.Factor
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourierInversion_inverseRowTransform_negOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψk : AddChar k Circle) (ν : Measure k), Continuous ψk → ψk ≠ 1 → ν.IsAddHaarMeasure → ∃ C : ℂ, ∀ c : Matrix n Unit k → ℂ, c ∈ SB (Matrix n Unit k) → ∀ Φ : Matrix Unit n k → ℂ, (∀ η, Φ η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c (Matrix.of fun r _ => y r)) (η ())) → GlobalTheory.KappaModel.finv ψk ν C Φ = c := by
  first | exact @GlobalTheory.KappaModel.finv_hat_neg_one | exact GlobalTheory.KappaModel.finv_hat_neg_one | (intros; apply GlobalTheory.KappaModel.finv_hat_neg_one <;> assumption)
end
