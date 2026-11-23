module

public import GroundTheory.LocalFields.SeparableClosure
public import GroundTheory.LocalFields.HerbrandFunction
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.KrullTopology
public import GroundTheory.PAdicHodge.BCrisNewtonNorm
public import GroundTheory.PAdicHodge.BCrisNewtonApprox
public import GroundTheory.PAdicHodge.Bundle007
public import GroundTheory.PAdicHodge.BdRGalois
public import Mathlib.RingTheory.Etale.Basic
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
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel IntermediateField

section AbsUpper

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

def absUpper (u : ℝ) : Subgroup Gal(Ω/K) where
  carrier := {σ | ∀ M : FiniteGaloisIntermediateField K Ω,
    AlgEquiv.restrictNormalHom (M : IntermediateField K Ω) σ ∈
      upperRamificationGroup K (M : IntermediateField K Ω) u}
  one_mem' M := by rw [map_one]; exact one_mem _
  mul_mem' hσ hτ M := by rw [map_mul]; exact mul_mem (hσ M) (hτ M)
  inv_mem' hσ M := by rw [map_inv]; exact inv_mem (hσ M)

variable {K Ω}



variable [IsGalois K Ω]

end AbsUpper

section APF

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  (L : IntermediateField K Ω)

def upperSupFixing (u : ℝ) : Subgroup Gal(Ω/K) :=
  absUpper K Ω u ⊔ L.fixingSubgroup

def IsAPF : Prop :=
  ∀ u : ℝ, IsOpen (upperSupFixing K Ω L u : Set Gal(Ω/K))

def apfIndex (u : ℝ) : ℕ :=
  (upperSupFixing K Ω L u).relIndex (absUpper K Ω 0)

def apfPsi (u : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..u, (apfIndex K Ω L w : ℝ)

def IsStrictlyAPF : Prop :=
  IsAPF K Ω L ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ u in Filter.atTop, c * apfIndex K Ω L u ≤ apfPsi K Ω L u

variable {K Ω L}

variable [IsGalois K Ω]

end APF

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector Laurent ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝔸" => Localization.Away (p : AInf K p)

variable {ρ : ℝ}

theorem gn_sum_lt (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ι : Type*} (s : Finset ι) (f : ι → 𝔸) {M : ℝ}
    (hM : 0 < M) (h : ∀ i ∈ s, gn K p ρ (f i) < M) : gn K p ρ (∑ i ∈ s, f i) < M := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, gn_zero]; exact hM
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (gn_add_le hρ0 hρ1 _ _).trans_lt (max_lt (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem sum_sub_sum_mem {R : Type*} [CommRing R] (I : Ideal R) (d : ℕ) (C : ℕ → R) {a a' b b' : R}
    (ha : a - a' ∈ I) (hb : b - b' ∈ I) :
    ∑ i ∈ Finset.range (d + 1), C i * a ^ i * b ^ (d - i) -
      ∑ i ∈ Finset.range (d + 1), C i * a' ^ i * b' ^ (d - i) ∈ I := by
  rw [← Ideal.Quotient.eq]

  simp only [map_sum, map_mul, map_pow, Ideal.Quotient.eq.2 ha, Ideal.Quotient.eq.2 hb]

theorem algebraMap_acrisZero_algebraMap (w : AInf K p) :
    algebraMap (ACrisZero K p) (ACris K p) (algebraMap (AInf K p) (ACrisZero K p) w) =
      algebraMap (AInf K p) (ACris K p) w :=
  rfl


set_option maxHeartbeats 4000000 in
theorem false_of_dominant (hp0 : ‖(p : K)‖ ≤ ρ) (hρ1 : ρ < 1) {a b : ACris K p} {Na Nb : ℕ}
    {Fa Fb : ℝ}
    (hsa : ∀ N ≥ Na, ∀ c : ACrisZero K p,
      a - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} → gn K p ρ (c : 𝔸) = Fa)
    (hsb : ∀ N ≥ Nb, ∀ c : ACrisZero K p,
      b - algebraMap _ (ACris K p) c ∈ Ideal.span {(p : ACris K p) ^ N} → gn K p ρ (c : 𝔸) = Fb)
    (d : ℕ) (x : ℕ → AInf K p)
    (hsum : ∑ i ∈ Finset.range (d + 1),
      algebraMap (AInf K p) (ACris K p) (x i) * a ^ i * b ^ (d - i) = 0)
    {j : ℕ} (hj : j ∈ Finset.range (d + 1))
    (hpos : 0 < gn K p ρ (algebraMap (AInf K p) 𝔸 (x j)) * Fa ^ j * Fb ^ (d - j))
    (hdom : ∀ i ∈ Finset.range (d + 1), i ≠ j →
      gn K p ρ (algebraMap (AInf K p) 𝔸 (x i)) * Fa ^ i * Fb ^ (d - i) <
        gn K p ρ (algebraMap (AInf K p) 𝔸 (x j)) * Fa ^ j * Fb ^ (d - j)) : False := by
  have hρ0 : 0 < ρ := norm_p_pos.trans_le hp0
  set g := fun i => gn K p ρ (algebraMap (AInf K p) 𝔸 (x i)) * Fa ^ i * Fb ^ (d - i) with hg
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hρ1
  set N := max n (max Na Nb)
  have hN : ρ ^ N < g j := (pow_le_pow_of_le_one hρ0.le hρ1.le (le_max_left _ _)).trans_lt hn
  obtain ⟨ca, hca⟩ := exists_approx a N
  obtain ⟨cb, hcb⟩ := exists_approx b N
  have hFa := hsa N ((le_max_left _ _).trans (le_max_right _ _)) ca hca
  have hFb := hsb N ((le_max_right _ _).trans (le_max_right _ _)) cb hcb
  set T : ℕ → ACrisZero K p := fun i => algebraMap (AInf K p) (ACrisZero K p) (x i) * ca ^ i * cb ^ (d - i)
  set S : ACrisZero K p := ∑ i ∈ Finset.range (d + 1), T i

  have hS : algebraMap _ (ACris K p) (0 : ACrisZero K p) - algebraMap _ (ACris K p) S ∈
      Ideal.span {(p : ACris K p) ^ N} := by
    have eS : algebraMap (ACrisZero K p) (ACris K p) S = ∑ i ∈ Finset.range (d + 1),
        algebraMap (AInf K p) (ACris K p) (x i) * algebraMap (ACrisZero K p) (ACris K p) ca ^ i *
          algebraMap (ACrisZero K p) (ACris K p) cb ^ (d - i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [S, T, map_sum, map_mul, map_pow, algebraMap_acrisZero_algebraMap]
    have key := sum_sub_sum_mem (Ideal.span {(p : ACris K p) ^ N}) d
      (fun i => algebraMap (AInf K p) (ACris K p) (x i)) hca hcb
    rw [hsum, zero_sub, ← eS] at key
    rw [map_zero, zero_sub]
    exact key
  have hle := gn_sub_le_of_mem hp0 hρ1 hS
  rw [ZeroMemClass.coe_zero, zero_sub, gn_neg hρ0 hρ1] at hle

  have hT : ∀ i, gn K p ρ ((T i : ACrisZero K p) : 𝔸) = g i := by
    intro i
    simp only [T, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    rw [gn_mul hρ0 hρ1, gn_mul hρ0 hρ1, gn_pow hρ0 hρ1, gn_pow hρ0 hρ1, hFa, hFb]
    rfl
  have hSsum : ((S : ACrisZero K p) : 𝔸) = ∑ i ∈ Finset.range (d + 1), ((T i : ACrisZero K p) : 𝔸) := by
    simp only [S]
    push_cast
    rfl
  have hrest : gn K p ρ (∑ i ∈ (Finset.range (d + 1)).erase j, ((T i : ACrisZero K p) : 𝔸)) < g j :=
    gn_sum_lt hρ0 hρ1 _ _ hpos fun i hi => by
      rw [hT]
      exact hdom i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  have hsplit : ((S : ACrisZero K p) : 𝔸) = ((T j : ACrisZero K p) : 𝔸) +
      ∑ i ∈ (Finset.range (d + 1)).erase j, ((T i : ACrisZero K p) : 𝔸) := by
    rw [hSsum, Finset.add_sum_erase _ (fun i => ((T i : ACrisZero K p) : 𝔸)) hj]
  have hSj : gn K p ρ ((S : ACrisZero K p) : 𝔸) = g j := by
    rw [← hT j]
    refine gn_eq_of_gn_sub_lt hρ0 hρ1 ?_
    rw [hsplit, sub_add_cancel_left, gn_neg hρ0 hρ1, hT j]
    exact hrest
  linarith

end WittTilt

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

open IsLocalRing

namespace GroundTheory.PAdicHodge

section AlgCl

variable (p : ℕ) [Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔪" => maximalIdeal 𝔹

instance isAdicComplete_maximalIdeal_bDeRhamPlus_padicComplex :
    IsAdicComplete (maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p))
      (BDeRhamPlus (normInteger ℂ_[p]) p) :=
  IsPerfectoidField.isAdicComplete_maximalIdeal_bDeRhamPlus (K := ℂ_[p]) (p := p)

instance : Algebra.FormallyEtale ℚ_[p] (PadicAlgCl p) :=
  Algebra.FormallyEtale.of_isSeparable _ _

theorem thetaAlgHom_eq_zero_of_mem_pow {n : ℕ} {a : 𝔹} (ha : a ∈ 𝔪 ^ (n + 1)) :
    thetaAlgHom p a = 0 := by
  have h : a ∈ 𝔪 := Ideal.pow_le_self (Nat.succ_ne_zero n) ha
  rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker] at h
  exact h

def thetaQuot (n : ℕ) : 𝔹 ⧸ 𝔪 ^ (n + 1) →ₐ[ℚ_[p]] ℂ_[p] :=
  Ideal.Quotient.liftₐ _ (thetaAlgHom p) fun _ ha => thetaAlgHom_eq_zero_of_mem_pow p ha

theorem thetaQuot_mk (n : ℕ) (x : 𝔹) :
    thetaQuot p n (Ideal.Quotient.mk _ x) = thetaAlgHom p x := rfl

theorem surjective_thetaQuot (n : ℕ) : Function.Surjective (thetaQuot p n) := by
  intro y
  obtain ⟨x, hx⟩ := IsPerfectoidField.surjective_thetaBDeRhamPlusField (K := ℂ_[p]) p y
  exact ⟨Ideal.Quotient.mk _ x, hx⟩

theorem isNilpotent_ker_thetaQuot (n : ℕ) :
    IsNilpotent (RingHom.ker (thetaQuot p n : 𝔹 ⧸ 𝔪 ^ (n + 1) →+* ℂ_[p])) := by
  have hle : RingHom.ker (thetaQuot p n : 𝔹 ⧸ 𝔪 ^ (n + 1) →+* ℂ_[p]) ≤
      Ideal.map (Ideal.Quotient.mk (𝔪 ^ (n + 1))) 𝔪 := by
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine Ideal.mem_map_of_mem _ ?_
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker]
    exact hy
  refine ⟨n + 1, le_bot_iff.1 ((Ideal.pow_right_mono hle (n + 1)).trans ?_)⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

def algClToQuot (n : ℕ) : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹 ⧸ 𝔪 ^ (n + 1) :=
  Algebra.FormallySmooth.liftOfSurjective (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p])
    (thetaQuot p n) (surjective_thetaQuot p n) (isNilpotent_ker_thetaQuot p n)

theorem thetaQuot_algClToQuot (n : ℕ) (x : PadicAlgCl p) :
    thetaQuot p n (algClToQuot p n x) = (x : ℂ_[p]) :=
  Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ x

theorem eq_algClToQuot (n : ℕ) (g : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹 ⧸ 𝔪 ^ (n + 1))
    (hg : ∀ x, thetaQuot p n (g x) = (x : ℂ_[p])) : g = algClToQuot p n :=
  Algebra.FormallyUnramified.lift_unique' (thetaQuot p n) (isNilpotent_ker_thetaQuot p n) g _
    (AlgHom.ext fun x => by
      simp only [AlgHom.comp_apply]
      rw [hg, thetaQuot_algClToQuot])

theorem thetaQuot_factorₐ {k n : ℕ} (hle : k ≤ n) (y : 𝔹 ⧸ 𝔪 ^ (n + 1)) :
    thetaQuot p k (Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right (Nat.succ_le_succ hle)) y) =
      thetaQuot p n y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

theorem factorₐ_comp_algClToQuot {k n : ℕ} (hle : k ≤ n) :
    (Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right (Nat.succ_le_succ hle))).comp
      (algClToQuot p n) = algClToQuot p k :=
  eq_algClToQuot p k _ fun x => by
    rw [AlgHom.comp_apply, thetaQuot_factorₐ p hle, thetaQuot_algClToQuot]

def algClToQuot' (n : ℕ) : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹 ⧸ 𝔪 ^ n :=
  (Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (algClToQuot p n)

theorem factorₐ_comp_algClToQuot' {k n : ℕ} (hle : k ≤ n) :
    (Ideal.Quotient.factorₐ ℚ_[p] (Ideal.pow_le_pow_right hle)).comp (algClToQuot' p n) =
      algClToQuot' p k := by
  ext x
  simp only [algClToQuot', AlgHom.comp_apply]
  rw [← factorₐ_comp_algClToQuot p hle, AlgHom.comp_apply]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (algClToQuot p n x)
  rw [← hy]
  rfl

def algClToBdR : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹 :=
  IsAdicComplete.liftAlgHom 𝔪 (algClToQuot' p) fun hle => factorₐ_comp_algClToQuot' p hle

theorem mk_algClToBdR (n : ℕ) (x : PadicAlgCl p) :
    Ideal.Quotient.mk (𝔪 ^ n) (algClToBdR p x) = algClToQuot' p n x :=
  IsAdicComplete.mk_liftAlgHom _ _ _ n x

theorem mk_succ_algClToBdR (n : ℕ) (x : PadicAlgCl p) :
    Ideal.Quotient.mk (𝔪 ^ (n + 1)) (algClToBdR p x) = algClToQuot p n x := by
  rw [mk_algClToBdR, algClToQuot', ← factorₐ_comp_algClToQuot p (Nat.le_succ n)]

theorem thetaAlgHom_algClToBdR (x : PadicAlgCl p) : thetaAlgHom p (algClToBdR p x) = (x : ℂ_[p]) := by
  rw [← thetaQuot_mk p 0, mk_succ_algClToBdR, thetaQuot_algClToQuot]

theorem eq_algClToBdR (g : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹) (hg : ∀ x, thetaAlgHom p (g x) = (x : ℂ_[p])) :
    g = algClToBdR p := by
  have h1 : ∀ n, (Ideal.Quotient.mkₐ ℚ_[p] (𝔪 ^ (n + 1))).comp g = algClToQuot p n := fun n =>
    eq_algClToQuot p n _ fun x => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, thetaQuot_mk, hg]
  refine IsAdicComplete.algHom_ext 𝔪 fun n => AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [mk_algClToBdR, algClToQuot', ← h1 n]
  rfl

theorem injective_algClToBdR : Function.Injective (algClToBdR p) :=
  (algClToBdR p).toRingHom.injective

end AlgCl

section Galois

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p

theorem gal_smul_padicIntToWitt (σ : Gal(PadicAlgCl p/K)) (x : ℤ_[p]) :
    σ • IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p x =
      IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p x := by
  ext n
  rw [AInf.gal_smul_coeff]
  simp only [IsPerfectoidField.padicIntToWitt, RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod
    ((preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)).comp
      (ZMod.castHom (dvd_refl p) _)) (ZMod.castHom (dvd_refl p) _)) _

theorem gal_smul_algebraMap_bdR (σ : Gal(PadicAlgCl p/K)) (q : ℚ_[p]) :
    σ • algebraMap ℚ_[p] 𝔹 q = algebraMap ℚ_[p] 𝔹 q := by
  have h : (galBdR σ : 𝔹 →+* 𝔹).comp (algebraMap ℚ_[p] 𝔹) = algebraMap ℚ_[p] 𝔹 := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe, galBdR_apply]
    have hx : algebraMap ℤ_[p] ℚ_[p] x = (x : ℚ_[p]) := rfl
    rw [hx, IsPerfectoidField.algebraMap_padic_coe, gal_smul_wittToBDeRhamPlus,
      gal_smul_padicIntToWitt]
  have := RingHom.congr_fun h q
  simpa only [RingHom.comp_apply, RingHom.coe_coe, galBdR_apply] using this

theorem gal_smul_algClToBdR (σ : Gal(PadicAlgCl p/K)) (x : PadicAlgCl p) :
    σ • algClToBdR p x = algClToBdR p (σ x) := by
  let g : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹 :=
    { toRingHom := ((galBdR σ⁻¹ : 𝔹 ≃+* 𝔹) : 𝔹 →+* 𝔹).comp
        (((algClToBdR p : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹) : PadicAlgCl p →+* 𝔹).comp
          (σ : PadicAlgCl p →+* PadicAlgCl p))
      commutes' := fun q => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_ofClass, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, galBdR_apply]
        rw [IsScalarTower.algebraMap_apply ℚ_[p] K (PadicAlgCl p), AlgEquiv.commutes,
          ← IsScalarTower.algebraMap_apply, AlgHom.commutes, gal_smul_algebraMap_bdR] }
  have hg : g = algClToBdR p := eq_algClToBdR p g fun y => by
    change thetaAlgHom p (σ⁻¹ • algClToBdR p (σ y)) = (y : ℂ_[p])
    rw [thetaAlgHom_apply, thetaBDeRhamPlusField_gal_smul, ← thetaAlgHom_apply,
      thetaAlgHom_algClToBdR, gal_smul_coe]
    congr 1
    change (σ⁻¹ * σ) y = y
    rw [inv_mul_cancel]
    rfl
  have h2 : σ⁻¹ • algClToBdR p (σ x) = algClToBdR p x := AlgHom.congr_fun hg x
  rw [← h2, smul_inv_smul]

end Galois

end GroundTheory.PAdicHodge
end
end
