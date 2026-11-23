module

public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.Basic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] {n : ℕ}

theorem resRPf_tpow_add (t : Fin (n + 1) → Rˣ) (m m' : Fin (n + 1) → ℤ) :
    tpow t (m + m') = tpow t m * tpow t m' := by
  simp only [tpow, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]

theorem resRPf_tpow_negOne (t : Fin (n + 1) → Rˣ) :
    tpow t (fun _ => -1) = (((∏ k, t k)⁻¹ : Rˣ) : R) := by
  unfold tpow
  congr 1
  simp only [zpow_neg_one, Finset.prod_inv_distrib]

theorem resRPf_tpow_single (t : Fin (n + 1) → Rˣ) (k : Fin (n + 1)) :
    tpow t (-Pi.single k (1 : ℤ)) = (((t k)⁻¹ : Rˣ) : R) := by
  unfold tpow
  congr 1
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem resRPf_linInd (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R)) :
    LinearIndependent K (tpow t) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg m0 hm0
  set N : ℤ := ∑ m ∈ s, ∑ j, |m j| with hN
  have hbound : ∀ m ∈ s, ∀ j, 0 ≤ m j + N := by
    intro m hm j
    have h1 : |m j| ≤ ∑ j, |m j| :=
      Finset.single_le_sum (f := fun j => |m j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j, |m j| ≤ N :=
      Finset.single_le_sum (f := fun m : Fin (n + 1) → ℤ => ∑ j, |m j|)
        (fun m _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) hm
    have h3 := neg_abs_le (m j)
    linarith
  let e : (Fin (n + 1) → ℤ) → (Fin (n + 1) →₀ ℕ) :=
    fun m => Finsupp.equivFunOnFinite.symm (fun j => (m j + N).toNat)
  have he : ∀ m ∈ s, tpow t (m + fun _ => N) =
      MvPolynomial.aeval (fun k => (t k : R)) (MvPolynomial.monomial (e m) (1 : K)) := by
    intro m hm
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    unfold tpow
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [e, Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply]
    conv_lhs => rw [← Int.toNat_of_nonneg (hbound m hm j)]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  have hmul : ∑ m ∈ s, g m • tpow t (m + fun _ => N) = 0 := by
    simp_rw [resRPf_tpow_add, ← smul_mul_assoc]
    rw [← Finset.sum_mul, hg, zero_mul]
  have hpoly : ∑ m ∈ s, MvPolynomial.monomial (e m) (g m) = 0 := by
    apply algebraicIndependent_iff_injective_aeval.1 ht

    rw [map_sum, map_zero, ← hmul]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [he m hm]
    simp only [MvPolynomial.aeval_monomial, map_one, one_mul, Algebra.smul_def]
  have hinj : ∀ m ∈ s, ∀ m' ∈ s, e m = e m' → m = m' := by
    intro m hm m' hm' h
    funext j
    have h0 := DFunLike.congr_fun h j
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h0
    have h1 := hbound m hm j
    have h2 := hbound m' hm' j
    omega
  have hc := congrArg (AddMonoidAlgebra.coeff · (e m0)) hpoly
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single m0] at hc
  · simpa [MvPolynomial.coeff_monomial] using hc
  · intro m hm hne
    rw [MvPolynomial.coeff_monomial, if_neg (fun h => hne (hinj m hm m0 hm0 h))]
  · intro h
    exact absurd hm0 h

def resRPfLogD (D : Derivation K R R) : Rˣ →* Multiplicative R where
  toFun u := Multiplicative.ofAdd ((((u⁻¹ : Rˣ)) : R) * D (u : R))
  map_one' := by simp
  map_mul' u v := by
    rw [← ofAdd_add]
    congr 1
    have hu : (((u⁻¹ : Rˣ)) : R) * u = 1 := Units.inv_mul u
    have hv : (((v⁻¹ : Rˣ)) : R) * v = 1 := Units.inv_mul v
    simp only [mul_inv_rev, Units.val_mul, Derivation.leibniz, smul_eq_mul]
    linear_combination ((((v⁻¹ : Rˣ)) : R) * D (v : R)) * hu + ((((u⁻¹ : Rˣ)) : R) * D (u : R)) * hv

theorem resRPfLogD_apply (D : Derivation K R R) (u : Rˣ) :
    Multiplicative.toAdd (resRPfLogD D u) = (((u⁻¹ : Rˣ)) : R) * D (u : R) := rfl

theorem resRPf_logD (t : Fin (n + 1) → Rˣ) (D : Derivation K R R) (m : Fin (n + 1) → ℤ) :
    (((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) * D (tpow t m) =
      ∑ j, m j • ((((t j)⁻¹ : Rˣ) : R) * D (t j : R)) := by
  have h := congrArg Multiplicative.toAdd (map_prod (resRPfLogD D) (fun j => t j ^ m j) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow, resRPfLogD_apply] at h
  exact h

theorem resRPf_Dk (t : Fin (n + 1) → Rˣ) (D : Fin (n + 1) → Derivation K R R)
    (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) (k : Fin (n + 1)) (m : Fin (n + 1) → ℤ) :
    D k (tpow t m) = m k • tpow t (m - Pi.single k (1 : ℤ)) := by
  have h := resRPf_logD t (D k) m
  simp only [hD, mul_ite, mul_one, mul_zero, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] at h
  have hU : tpow t m * (((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) = 1 := Units.mul_inv _
  calc D k (tpow t m) = tpow t m * ((((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) * D k (tpow t m)) := by
        rw [← mul_assoc, hU, one_mul]
    _ = tpow t m * (m k • (((t k)⁻¹ : Rˣ) : R)) := by rw [h]
    _ = m k • tpow t (m - Pi.single k (1 : ℤ)) := by
        rw [mul_smul_comm, sub_eq_add_neg, resRPf_tpow_add, resRPf_tpow_single]

theorem res_R_pf (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R))
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    ∃ res : R →ₗ[K] K, res (((∏ k, t k)⁻¹ : Rˣ) : R) = 1 ∧
      (∀ x ∈ Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}), res x = 0) ∧
      ∀ k, ∀ x ∈ torusS K t Finset.univ, res (D k x) = 0 := by
  classical
  have hli := resRPf_linInd (K := K) t ht
  obtain ⟨res, hres⟩ := LinearMap.exists_extend ((Module.Basis.span hli).coord (fun _ => -1))
  have hval : ∀ m, res (tpow t m) = if m = (fun _ => -1) then 1 else 0 := by
    intro m
    have h1 : tpow t m = ((Module.Basis.span hli m : Submodule.span K (Set.range (tpow t))) : R) :=
      congrArg Subtype.val (Module.Basis.span_apply hli m).symm
    have h2 := LinearMap.congr_fun hres (Module.Basis.span hli m)
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h1, h2, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  refine ⟨res, ?_, ?_, ?_⟩
  · rw [← resRPf_tpow_negOne, hval, if_pos rfl]
  · intro x hx
    have hle : Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}) ≤ LinearMap.ker res := by
      rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hval, if_neg hm]
    exact hle hx
  · intro k x hx
    have hx' : x ∈ Submodule.span K (Set.range (tpow t)) := by
      have h1 : x ∈ Subalgebra.toSubmodule (torusS K t Finset.univ) := hx
      rw [torusS, Algebra.adjoin_eq_span] at h1
      refine Submodule.span_mono ?_ h1
      intro y hy
      let M : Submonoid R :=
        { carrier := Set.range (tpow t)
          mul_mem' := by
            rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
            exact ⟨a + b, resRPf_tpow_add t a b⟩
          one_mem' := ⟨0, by simp [tpow]⟩ }
      exact (Submonoid.closure_le (S := M)).2 (Set.image_subset_range _ _) hy
    have hker : Submodule.span K (Set.range (tpow t)) ≤ LinearMap.ker (res ∘ₗ (D k : R →ₗ[K] R)) := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe,
        resRPf_Dk t D hD k m, map_zsmul, hval]
      by_cases h : m - Pi.single k (1 : ℤ) = fun _ => -1
      · have h' := congr_fun h k
        simp only [Pi.sub_apply, Pi.single_eq_same] at h'
        have h0 : m k = 0 := by omega
        rw [h0, zero_smul]
      · rw [if_neg h, smul_zero]
    have h2 := hker hx'
    rwa [LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe] at h2

end CrystallineSemistableComparison.Pb
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R]

theorem chart_ext (A T B0 Bu : Subalgebra K R) (hAT : A ≤ T) (hAB0 : A ≤ B0) (hB0 : B0 ≤ Bu) (hTBu : T ≤ Bu)
    (hB0FG : B0.FG) (hB0Int : ∀ b ∈ B0, IsIntegral A b) (hBuFG : Bu.FG) (hBuInt : ∀ b ∈ Bu, IsIntegral T b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b)
    (w : R) (hwA : w ∈ A) (hw0 : w ≠ 0) (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) :
    ∃ B' : Subalgebra K R, B0 ≤ B' ∧ B'.FG ∧ (∀ b ∈ B', IsIntegral A b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b :=
  chart_ext_pf A T B0 Bu hAT hAB0 hB0 hTBu hB0FG hB0Int hBuFG hBuInt hFrac w hwA hw0 hscale

end CrystallineSemistableComparison.Pb
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_etale_away_pf {K A : Type} [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] {d : ℕ} (s : Fin d → A) (hs : AlgebraicIndependent K s)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range s)) A) :
    ∃ g : A, g ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale := by
  classical
  letI : Algebra (MvPolynomial (Fin d) K) A := (MvPolynomial.aeval s).toRingHom.toAlgebra
  have hRA : algebraMap (MvPolynomial (Fin d) K) A = (MvPolynomial.aeval s).toRingHom := rfl
  have : IsScalarTower K (MvPolynomial (Fin d) K) A := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hRA, MvPolynomial.algebraMap_eq]
    simp
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) K) A) := by
    intro a b h
    exact hs h
  have : FaithfulSMul (MvPolynomial (Fin d) K) A :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin d) K) A).2 hinj
  have : Algebra.FiniteType (MvPolynomial (Fin d) K) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (MvPolynomial (Fin d) K) A
  have : Algebra.FinitePresentation (MvPolynomial (Fin d) K) A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) A := by
    refine Algebra.IsAlgebraic.of_ringHom_of_comp_eq hs.aevalEquiv (RingHom.id A)
      hs.aevalEquiv.surjective Function.injective_id ?_
    ext p
    · simp [hRA]
    · simp [hRA]
  have hL : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := IsFractionRing.toField A
  have : FaithfulSMul (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq (MvPolynomial (Fin d) K) A (Localization.AtPrime ⊥)]
    exact (IsFractionRing.injective A _).comp hinj
  letI := FractionRing.liftAlgebra (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A))
  have : Algebra.IsAlgebraic A (Localization.AtPrime (⊥ : Ideal A)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.IsAlgebraic.trans (MvPolynomial (Fin d) K) A _
  have : Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin d) K)) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (MvPolynomial (Fin d) K) _)
  have : CharZero (FractionRing (MvPolynomial (Fin d) K)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Fin d) K) _)
  have : Algebra.FormallyEtale (FractionRing (MvPolynomial (Fin d) K)) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FormallyEtale (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial (Fin d) K))
  have hE : Algebra.IsEtaleAt (MvPolynomial (Fin d) K) (⊥ : Ideal A) :=
    Algebra.FormallyEtale.comp (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) _
  obtain ⟨g, hg, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := MvPolynomial (Fin d) K) (⊥ : Ideal A)
  refine ⟨g, by simpa using hg, ?_⟩
  have heq : (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g) =
      algebraMap (MvPolynomial (Fin d) K) (Localization.Away g) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K) A (Localization.Away g)]
      simp [hRA, IsScalarTower.algebraMap_apply K A (Localization.Away g)]
    · intro i
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K) A (Localization.Away g)]
      simp [hRA]
  rw [heq]
  exact RingHom.etale_algebraMap.2 he

end CrystallineSemistableComparison.Pb
end
end

section

set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

theorem exists_away_isDomain_of_smooth {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime] :
    ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  obtain ⟨ι, σ, _, _, ⟨Pr⟩⟩ := hstd.out
  haveI : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension K (Localization.Away g) :=
    ⟨⟨ι, σ, ‹_›, ‹_›, Pr, rfl⟩⟩
  obtain ⟨φ, hφ⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    (n := Pr.dimension) (R := K) (S := Localization.Away g)
  letI : Algebra (MvPolynomial (Fin Pr.dimension) K) (Localization.Away g) := φ.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin Pr.dimension) K) (Localization.Away g) := hφ
  haveI hq : (p.map (algebraMap A (Localization.Away g))).IsPrime := by
    apply IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ _ ‹_›
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  obtain ⟨g', hg', hdom⟩ := exists_away_isDomain_of_etale
    (P := MvPolynomial (Fin Pr.dimension) K) (A := Localization.Away g)
    (p.map (algebraMap A (Localization.Away g)))
  refine ⟨g * (IsLocalization.Away.sec g g').1, ?_, ?_⟩
  · refine Ideal.IsPrime.mul_notMem ‹_› hg fun hmem => hg' ?_
    rw [Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst g g').symm]
    exact Ideal.mem_map_of_mem (algebraMap A (Localization.Away g)) hmem
  · intro S _ _ _
    haveI : IsLocalization.Away (g * (IsLocalization.Away.sec g g').1) (Localization.Away g') :=
      .mul_of_associated _ _ g' <| IsLocalization.Away.associated_sec_fst g g'
    let e : S ≃ₐ[A] Localization.Away g' :=
      IsLocalization.algEquiv (Submonoid.powers (g * (IsLocalization.Away.sec g g').1)) S
        (Localization.Away g')
    exact e.toRingEquiv.toMulEquiv.isDomain

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
end
end
