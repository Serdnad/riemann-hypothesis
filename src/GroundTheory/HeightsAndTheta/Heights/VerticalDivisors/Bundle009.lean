module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
public import Mathlib.RingTheory.RingHom.Flat
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain IsLocalRing

noncomputable section

theorem ParDVRIsDVR.proof : ParDVRIsDVR.Statement := by
  intro K _ _ e n v
  let A := MvPolynomial (Par e n) (𝓞 K)
  let R := ParDVR e n v
  let Rv := Localization.AtPrime v.asIdeal
  have : IsDiscreteValuationRing Rv :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) v.ne_bot Rv
  have : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing (parPrime e n v).primeCompl R inferInstance

  have hC : ∀ s : 𝓞 K, s ∉ v.asIdeal → (C s : A) ∉ parPrime e n v := by
    intro s hs h
    rw [parPrime, MvPolynomial.mem_map_C_iff] at h
    exact hs (by simpa using h 0)
  have hOR : algebraMap (𝓞 K) R = (algebraMap A R).comp C := by
    rw [IsScalarTower.algebraMap_eq (𝓞 K) A R, MvPolynomial.algebraMap_eq]
  let φ : Rv →+* R := IsLocalization.lift (M := v.asIdeal.primeCompl) (g := algebraMap (𝓞 K) R)
    fun s => by
      rw [hOR, RingHom.comp_apply]
      exact IsLocalization.map_units R (⟨C (s : 𝓞 K), hC s s.2⟩ : (parPrime e n v).primeCompl)
  have hφ : φ.comp (algebraMap (𝓞 K) Rv) = algebraMap (𝓞 K) R := IsLocalization.lift_comp _
  have hmax : maximalIdeal R = (maximalIdeal Rv).map φ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal Rv, Ideal.map_map, hφ, hOR, ← Ideal.map_map]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rv
  have hspan : maximalIdeal R = Ideal.span {φ ϖ} := by
    rw [hmax, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]

  have hne : maximalIdeal R ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hbot
    have hmem : algebraMap (𝓞 K) R x ∈ maximalIdeal R := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R, hOR, RingHom.comp_apply]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem C hx)
    rw [hbot, Ideal.mem_bot, hOR, RingHom.comp_apply] at hmem
    have hinj : Function.Injective (algebraMap A R) :=
      IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (parPrime e n v))
    exact hx0 (MvPolynomial.C_injective _ _ (hinj (by rw [hmem, map_zero, map_zero])))
  have hnf : ¬IsField R := fun h => hne (isField_iff_maximalIdeal_eq.mp h)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 5 1).mp
    (show (maximalIdeal R).IsPrincipal from ⟨⟨φ ϖ, hspan⟩⟩)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section Objects

variable {K : Type*} [Field K] [NumberField K]

theorem comap_maximalIdeal_parDVR (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (IsLocalRing.maximalIdeal (ParDVR e n v)).comap (algebraMap (𝓞 K) (ParDVR e n v)) = v.asIdeal := by
  have h1 : algebraMap (𝓞 K) (ParDVR e n v) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)).comp C :=
    IsScalarTower.algebraMap_eq _ _ _
  have h2 : (IsLocalRing.maximalIdeal (ParDVR e n v)).comap
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)) = parPrime e n v :=
    Localization.AtPrime.under_maximalIdeal
  rw [h1, ← Ideal.comap_comap, h2]
  ext x
  simp only [Ideal.mem_comap, parPrime]
  constructor
  · intro hx
    rw [MvPolynomial.mem_map_C_iff] at hx
    simpa using hx 0
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

def resToKappa (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.ResidueField →+* (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField :=
  Ideal.ResidueField.map v.asIdeal (IsLocalRing.maximalIdeal (ParDVR e n v))
    (algebraMap (𝓞 K) (ParDVR e n v)) (comap_maximalIdeal_parDVR e n v).symm

def parYκ (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    Par e n → (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField :=
  fun p => algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField (parY e n v p)

end Objects

def SpecCompDim.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      IsProjPrime (reduceMod v W) ∧
        ringKrullDim (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸ reduceMod v W) = ((e + 1 : ℕ) : WithBot ℕ∞)

def ChartDomain.Statement : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n),
    Q.IsPrime → (∀ c : D, C c ∈ Q → c = 0) → X j ∉ Q →
      IsDomain (Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X j)) ∧
        Function.Injective (algebraMap D
          (Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X j)))

def SecAlgField.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      IsField (SecAlg (Q.map (MvPolynomial.map (algebraMap k (FractionRing (MvPolynomial (Par e n) k)))))
        (fun p => algebraMap (MvPolynomial (Par e n) k) (FractionRing (MvPolynomial (Par e n) k)) (X p)))

def ParFracIsFractionRing.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    letI := (parToFrac e n v).toAlgebra
    IsFractionRing (ParDVR e n v) (ParFrac K e n)

def ResidueAlgIndep.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    letI := (resToKappa e n v).toAlgebra
    AlgebraicIndependent v.asIdeal.ResidueField (parYκ e n v)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain WithZero

noncomputable section

section Dedekind

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)

theorem exists_C_mul_eq_C_pow_mul {a : A} (ha : v.intValuation a = exp (-1 : ℤ)) {σ : Type*}
    (j : ℕ) {p : MvPolynomial σ A} (hp : p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j)) :
    ∃ t ∉ v.asIdeal, ∃ h : MvPolynomial σ A, C t * p = C a ^ j * h := by
  have hlt : v.intValuation a < 1 := by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := (v.intValuation_lt_one_iff_dvd a).mp hlt
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle
    obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.mpr hle
    have h2 : v.asIdeal ^ 2 ∣ Ideal.span {a} := ⟨J', by rw [hJ, hJ', sq, mul_assoc]⟩
    have h3 := (v.intValuation_le_pow_iff_dvd a 2).mpr h2
    rw [ha, exp_le_exp] at h3
    norm_num at h3
  have hJj : ¬ J ^ j ≤ v.asIdeal := fun h => hJv (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨t, htJ, htv⟩ := SetLike.not_le_iff_exists.mp hJj
  have hid : J ^ j * v.asIdeal ^ j = Ideal.span {a ^ j} := by
    rw [← mul_pow, mul_comm, ← hJ, Ideal.span_singleton_pow]
  have hmem : C t * p ∈ Ideal.span {(C a ^ j : MvPolynomial σ A)} := by
    have h1 : C t * p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (J ^ j) *
        Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j) :=
      Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ htJ) hp
    rw [← Ideal.map_mul, hid, Ideal.map_span, Set.image_singleton, map_pow] at h1
    exact h1
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨t, htv, h, by rw [← hh, mul_comm]⟩

end Dedekind

section NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem gaussNorm_map_of_coeff_notMem (v : HeightOneSpectrum (𝓞 K)) {σ : Type*}
    (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v)
      (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding,
      (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1

theorem adicAbv_of_intValuation_eq (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : v.intValuation a = exp (-1 : ℤ)) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K a) =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.valuation_of_algebraMap, ha,
    WithZeroMulInt.toNNReal_neg_apply _ exp_ne_zero]
  rw [WithZero.log_exp, zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]

theorem irreducible_algebraMap_C (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    [IsDiscreteValuationRing (ParDVR e n v)] {a : 𝓞 K} (ha : v.intValuation a = exp (-1 : ℤ)) :
    Irreducible (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by
  set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ
  have hav : a ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem a).mp (by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num)
  have hnu : ¬ IsUnit (φ (C a)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    exact fun h => h (Ideal.mem_map_of_mem _ hav)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ParDVR e n v)
  obtain ⟨x, s, rfl⟩ : ∃ (x : MvPolynomial (Par e n) (𝓞 K)) (s : (parPrime e n v).primeCompl),
      IsLocalization.mk' (ParDVR e n v) x s = ϖ := by
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective (parPrime e n v).primeCompl ϖ
    exact ⟨x, s, hxs⟩
  have hx : x ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ 1) := by
    rw [pow_one]
    by_contra hx
    exact hϖ.not_isUnit
      ((IsLocalization.AtPrime.isUnit_mk'_iff (ParDVR e n v) (parPrime e n v) x s).mpr hx)
  obtain ⟨t, ht, h, hth⟩ := exists_C_mul_eq_C_pow_mul v ha 1 hx
  have htu : IsUnit (φ (C t)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro htP
    exact ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)
  have hx2 : φ x = φ (C a) * (↑htu.unit⁻¹ * φ h) := by
    have h2 := congrArg φ hth
    rw [map_mul, map_mul, pow_one] at h2
    calc φ x = ↑htu.unit⁻¹ * (φ (C t) * φ x) := by
          rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = φ (C a) * (↑htu.unit⁻¹ * φ h) := by rw [h2]; ring
  have hϖ' : IsLocalization.mk' (ParDVR e n v) x s =
      φ (C a) * (↑htu.unit⁻¹ * φ h * IsLocalization.mk' (ParDVR e n v) 1 s) := by
    rw [IsLocalization.mk'_eq_mul_mk'_one, hx2]
    ring
  rw [hϖ'] at hϖ
  rcases hϖ.isUnit_or_isUnit rfl with hu | hu
  · exact (hnu hu).elim
  · exact (irreducible_mul_isUnit hu).mp hϖ

end NumberField

theorem GaussDVR.proof (h1 : ParDVRIsDVR.Statement) : GaussDVR.Statement := by
  intro K _ _ e n v g hg
  have := h1 K e n v
  classical
  obtain ⟨a, ha⟩ := v.intValuation_exists_uniformizer
  set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ
  have hav : a ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem a).mp (by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num)
  let μ : 𝓞 K → ℕ := fun b => multiplicity v.asIdeal (Ideal.span {b})
  have hval : ∀ b : 𝓞 K, b ≠ 0 → ∀ k : ℕ, b ∈ v.asIdeal ^ k ↔ k ≤ μ b := by
    intro b hb k
    rw [← v.intValuation_le_pow_iff_mem, v.intValuation_eq_exp_neg_multiplicity hb, exp_le_exp]
    simp only [μ]
    omega
  have hne : g.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hg)
  obtain ⟨d0, hd0, hmin⟩ := g.support.exists_mem_eq_inf' hne (fun d => μ (g.coeff d))
  set m := g.support.inf' hne (fun d => μ (g.coeff d)) with hm
  have hgm : g ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ m) := by
    rw [MvPolynomial.mem_map_C_iff]
    intro d
    by_cases hd : g.coeff d = 0
    · rw [hd]
      exact Ideal.zero_mem _
    · exact (hval _ hd m).mpr (Finset.inf'_le _ (mem_support_iff.mpr hd))
  obtain ⟨t, ht, h, hth⟩ := exists_C_mul_eq_C_pow_mul v ha m hgm
  have hb0 : g.coeff d0 ≠ 0 := mem_support_iff.mp hd0
  have hh : h.coeff d0 ∉ v.asIdeal := by
    intro hmem
    have hc := congrArg (AddMonoidAlgebra.coeff · d0) hth
    rw [coeff_C_mul, ← C_pow, coeff_C_mul] at hc
    have h3 : t * g.coeff d0 ∈ v.asIdeal ^ (m + 1) := by
      rw [hc, pow_succ]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hav m) hmem
    have h4 := (v.intValuation_le_pow_iff_mem _ _).mpr h3
    rw [map_mul, HeightOneSpectrum.intValuation_eq_one_iff.mpr ht, one_mul, v.intValuation_le_pow_iff_mem,
      hval _ hb0] at h4
    omega
  have htu : IsUnit (φ (C t)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro htP
    exact ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)
  have hhu : IsUnit (φ h) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro hP
    exact hh ((MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp hP d0)
  have hord : Ring.ord (ParDVR e n v) (φ g) = m := by
    rw [Ring.ord_eq_addVal]
    have h0 := congrArg φ hth
    rw [map_mul φ, map_mul φ, map_pow φ] at h0
    have h2 := congrArg (IsDiscreteValuationRing.addVal (ParDVR e n v)) h0
    rw [IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer (irreducible_algebraMap_C e n v ha),
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr htu,
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hhu] at h2
    simpa using h2
  have hK0 := congrArg (MvPolynomial.map (algebraMap (𝓞 K) K)) hth
  rw [map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)), map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)),
    map_pow (MvPolynomial.map (algebraMap (𝓞 K) K)), MvPolynomial.map_C, MvPolynomial.map_C] at hK0
  have hK := congrArg (gaussNorm v) hK0
  rw [← C_pow, gaussNorm_C_mul, gaussNorm_C_mul, map_pow,
    adicAbv_of_intValuation_eq v ha, gaussNorm_map_of_coeff_notMem v h ⟨d0, hh⟩, ← FinitePlace.norm_embedding,
    (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr ht, one_mul, mul_one] at hK
  have hN : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
  rw [hord, ENat.toNat_natCast, hK, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hN)]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem isChowForm_C_mul {F : Type*} [Field F] {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) {c : F} (hc : c ≠ 0) :
    IsChowForm I k (C c * f) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr hc) hf.1, fun g => ?_⟩
  have hu : IsUnit (C c : MvPolynomial (Fin k × Fin n) F) := hc.isUnit.map C
  rw [hf.2 g, IsUnit.mul_left_dvd hu]

theorem specFirst_C_mul {R : Type*} [CommSemiring R] {n k : ℕ} (c : R)
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (C c * f) u = C c * specFirst f u := by
  simp [specFirst]

theorem Main.proof (h1 : GaussEq.Statement) (h2 : PrimitiveScale.Statement)
    (h3 : VertTermEq.Statement) : ChowFormSectionVertical.Statement := by
  intro K _ _ n e I f u hI hf hu v
  obtain ⟨c, g, hc, hg, hprim⟩ := h2 K v _ f hf.1
  have hcf : IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) := by
    rw [hg]
    exact isChowForm_C_mul hf hc
  obtain ⟨h1a, h1b⟩ := h1 K n e I g u v hI hcf hu hprim
  rw [hg, specFirst_C_mul, gaussNorm_C_mul] at h1a
  rw [hg, gaussNorm_C_mul] at h1b
  rw [h3]
  set a := NumberField.HeightOneSpectrum.adicAbv K v c
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  set D := vertDeg e I u v
  have hN : 0 < N := by
    have h := Ideal.absNorm_ne_zero_of_nonZeroDivisors
      (⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ : nonZeroDivisors (Ideal (𝓞 K)))
    have h' : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero h
    exact Nat.cast_pos.mpr h'
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1b
    exact zero_ne_one h1b
  have hfu : 0 < gaussNorm v (specFirst f fun j => (u j : K)) := by
    refine lt_of_le_of_ne (gaussNorm_nonneg v _) fun h0 => ?_
    rw [← h0, mul_zero, zero_mul] at h1a
    exact zero_ne_one h1a
  have hff : gaussNorm v f = gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D := by
    have e1 : a * gaussNorm v f = a * (gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D) := by
      rw [h1b, ← mul_assoc, h1a]
    exact mul_left_cancel₀ ha e1
  rw [hff, Real.log_mul hfu.ne' (pow_ne_zero _ hN.ne'), Real.log_pow]
  ring

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

def SpecChart.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∀ (𝔫 : MaximalSpectrum (SecB e I v)) (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) [W.IsPrime],
        W ∈ specComps I v → secIdealOf e I v W = 𝔫.asIdeal →
          ∃ ψ : Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)) →+*
              Localization.AtPrime 𝔫.asIdeal,
            (∀ g : MvPolynomial (Fin n) (𝓞 K),
              ψ (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime W) g)) =
                algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
                  (Ideal.Quotient.mk _ (g.map (algebraMap (𝓞 K) (ParDVR e n v))))) ∧
            IsLocalHom (ψ.comp (Ideal.Quotient.mk _)) ∧
            @RingHom.Flat (Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
              (Localization.AtPrime 𝔫.asIdeal) _ _ ψ ∧
            (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map (ψ.comp (Ideal.Quotient.mk _)) =
              IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫.asIdeal)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def GenSecKer.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      RingHom.ker ((Ideal.Quotient.mk
          (secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))).comp
        (MvPolynomial.map (algebraMap k (GenParField k e n)))) = Q

end

end GroundTheory.Heights₂.Heights.Vertical
end
