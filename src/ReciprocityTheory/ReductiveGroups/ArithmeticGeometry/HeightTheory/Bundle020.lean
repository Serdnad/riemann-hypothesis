module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle015
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormB
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle004
import ReciprocityTheory.SemistableReduction.Bundle019

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

theorem prod_zpow_eq {ι G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hx]

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_at (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) :
    ∃ n t : ℕ, ∃ N : ℤ, (d.htOf hd h).Ila la = n ∧ d.NlaG h d.wF hd.a4.choose la = N ∧
      ∃ u : Op d.D d.N la, IsUnit u ∧ d.De hd h =
        (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ (((2 * n + t : ℕ) : ℤ) - 2 * N) *
          OpToKT d.D d.N la u := by
  classical
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
  letI := algOpKT (K := K) d.D d.N la
  haveI := Op_isDVR (K := K) d.D d.N la
  haveI := isFractionRing_Op (K := K) d.D d.N la
  have hF := fun c => d.comp_facts hd h la c
  haveI : ∀ c, IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    fun c => (hF c).2.1
  haveI : ∀ c, FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (hF c).2.2.1
  haveI : ∀ c, Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (hF c).2.2.2.1
  let n : ∀ c, AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ := fun c w =>
    d.ord c (d.Wres c w) d.wF (hd.a4.choose c)
  choose g hg0 hgw hgiff using fun c => d.comp_g hd h la c (n c)
  have hset : d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la =
      {y | ∀ c, g c * y c ∈ integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)} := by
    ext y
    simp only [AdmissibleOmegaFamiliesAtPrimeOfSection, Set.mem_setOf_eq]
    exact forall_congr' fun c => hgiff c (y c)
  have hb : ∀ k c, g c * d.bvecG hd.sel hd.a4.choose k c ∈
      integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun k c =>
    (hgiff c _).mp (fun w hw => d.b_mem hd h la k c w hw)
  obtain ⟨nn, t, u, hlen, hdisc⟩ := HDiscLat.lattice_main (R := Op d.D d.N la)
    (F := KTf K d.D d.N) (unifOp_irreducible d.D d.N la) g hg0 (d.del_eq hd h)
    (d.bvecG hd.sel hd.a4.choose) hb (d.b_linIndep hd h)
  choose uN huN hN using fun c => d.comp_norm hd h la c (hg0 c) (n c) (hgw c)
  let Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (_ : w ∈ d.PlOver la c), (d.fze h c w : ℤ) * n c w
  have hfin : ∀ c, (d.PlOver la c).Finite := fun c => by
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hF c
    rw [d.plOver_eq h la c]
    exact ValPl.placesOver_finite (O := Op d.D d.N la) (F := KTf K d.D d.N)
      (L := OmS (Ω c) d.D d.N)
  refine ⟨nn, t, ∑ c, Nc c, ?_, ?_, ?_⟩
  · change Module.length (Op d.D d.N la)
      (↥(Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)) ⧸
        (Submodule.span (Op d.D d.N la) (Set.range (d.bvecG hd.sel hd.a4.choose))).comap
          (Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)).subtype) = nn
    rw [hset]
    exact hlen
  · simp only [NlaG, Nc]
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin c), finsum_mem_eq_finite_toFinset_sum _ (hfin c)]
    push_cast
    rfl
  · set X := OpToKT d.D d.N la (unifOp d.D d.N la) with hX
    have hX0 : X ≠ 0 := (map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr
      (unifOp_irreducible d.D d.N la).ne_zero
    let U : (Op d.D d.N la)ˣ := ∏ c, (huN c).unit
    have hprod : ∏ c, Algebra.norm (KTf K d.D d.N) (g c) =
        X ^ (∑ c, Nc c) * OpToKT d.D d.N la (U : Op d.D d.N la) := by
      rw [Finset.prod_congr rfl fun c _ => hN c, Finset.prod_mul_distrib, prod_zpow_eq hX0,
        ← map_prod]
      congr 2
      simp only [U, Units.coe_prod, IsUnit.unit_spec]
    rw [hprod] at hdisc
    refine ⟨↑(u * U⁻¹ * U⁻¹), Units.isUnit _, ?_⟩
    rw [algK_unif, ← hX]
    set V := OpToKT d.D d.N la (U : Op d.D d.N la)
    set V' := OpToKT d.D d.N la ((U⁻¹ : (Op d.D d.N la)ˣ) : Op d.D d.N la)
    have hU : V * V' = 1 := by
      simp only [V, V']
      rw [← map_mul, Units.mul_inv, map_one]
    set Y := X ^ (∑ c, Nc c)
    have hY : Y ≠ 0 := zpow_ne_zero _ hX0
    have h2 : X ^ (2 * ∑ c, Nc c) = Y ^ 2 := by
      rw [mul_comm, zpow_mul]
      norm_cast
    have hone : (Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V') = 1 := by
      calc (Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V') = (Y ^ 2 * (Y ^ 2)⁻¹) * ((V * V') * (V * V')) := by
            ring
        _ = 1 := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hY), hU]; ring
    have hdisc' : d.De hd h * (Y * V) ^ 2 =
        OpToKT d.D d.N la ↑u * X ^ (2 * nn + t) := by
      rw [← map_pow, ← map_mul]
      exact hdisc
    rw [zpow_sub₀ hX0, zpow_natCast, h2, Units.val_mul, Units.val_mul, map_mul, map_mul]
    calc d.De hd h = d.De hd h * ((Y * V) ^ 2 * ((Y ^ 2)⁻¹ * V' * V')) := by rw [hone, mul_one]
      _ = (d.De hd h * (Y * V) ^ 2) * ((Y ^ 2)⁻¹ * V' * V') := by ring
      _ = _ := by rw [hdisc', div_eq_mul_inv]; ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

set_option linter.style.haveILetI false

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscOmL

open IsDedekindDomain IsLocalRing Module

variable {R F : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)]

omit [IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R F] in
theorem prod_zpow {κ G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset κ)
    (f : κ → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hx]

theorem disc_local (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
    (n : ∀ c, AddValuation (L c) (WithTop ℤ) → ℤ)
    {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c) (hli : LinearIndependent F b)
    (hb : ∀ k c, ∀ w ∈ HNm.OverR (R := R) (F := F) (L := L c) p,
      0 ≤ w (b k c) + (n c w : WithTop ℤ)) :
    ∃ a s : R, s ∉ p ∧
      (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
        algebraMap R F g ^ (2 * ∑ c, ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
          (_ : w ∈ HNm.OverR (R := R) (F := F) (L := L c) p), (HNm.fz (F := F) w : ℤ) * n c w) *
        algebraMap R F s =
        algebraMap R F a := by
  classical
  let O := Localization.AtPrime p
  letI : Algebra O F := IsLocalization.localizationAlgebraOfSubmonoidLe O F p.primeCompl
    (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : IsScalarTower R O F := IsLocalization.localization_isScalarTower_of_submonoid_le O F
    p.primeCompl (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : IsFractionRing O F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl O F
  obtain ⟨hdvr, hirr⟩ := ValUFD.loc_dvr p hp g hg
  haveI := hdvr
  letI : ∀ c, Algebra O (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap O F)).toAlgebra
  haveI : ∀ c, IsScalarTower O F (L c) := fun c => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ c, Algebra R (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap R F)).toAlgebra
  haveI : ∀ c, IsScalarTower R O (L c) := fun c => IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap F (L c) (algebraMap R F x) =
      algebraMap F (L c) (algebraMap O F (algebraMap R O x))
    rw [IsScalarTower.algebraMap_apply R O F x])
  have hded : ∀ c, IsDedekindDomain (integralClosure O (L c)) := fun c =>
    (ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F (L c)).1
  have hfr : ∀ c, IsFractionRing (integralClosure O (L c)) (L c) := fun c =>
    integralClosure.isFractionRing_of_finite_extension F (L c)
  have hset : ∀ c, ValPl.PlacesOver O (L c) = HNm.OverR (R := R) (F := F) (L := L c) p := fun c => by
    ext w
    simp only [ValPl.PlacesOver, HNm.OverR, Set.mem_ofPred_eq]
    rw [← ValPl.placesOver_iff_loc (R := R) p w]
    rfl
  have hG : ∀ c, ∃ gc : L c, gc ≠ 0 ∧ (∀ w ∈ ValPl.PlacesOver O (L c), w gc = n c w) ∧
      ∀ y, (∀ w ∈ ValPl.PlacesOver O (L c), 0 ≤ w y + (n c w : WithTop ℤ)) ↔
        gc * y ∈ integralClosure O (L c) := fun c => by
    haveI := hded c
    haveI := hfr c
    obtain ⟨gc, hg0, hgv⟩ := HDiscVal.exists_val_eq O F (n c)
    refine ⟨gc, hg0, hgv, fun y => ?_⟩
    rw [HDiscVal.mem_integralClosure_iff O F]
    refine forall₂_congr fun w hw => ?_
    rw [AddValuation.map_mul, hgv w hw, add_comm]
  choose gc hgc0 hgcv hgciff using hG
  have hbI : ∀ k c, gc c * b k c ∈ integralClosure O (L c) := fun k c =>
    (hgciff c _).mp (fun w hw => hb k c w (hset c ▸ hw))
  obtain ⟨nn, t, u, -, hdisc⟩ := HDiscLat.lattice_main (R := O) (F := F) hirr gc hgc0 hm b hbI hli
  set Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
    (_ : w ∈ HNm.OverR (R := R) (F := F) (L := L c) p), (HNm.fz (F := F) w : ℤ) * n c w with hNc
  have hN : ∀ c, ∃ uc : O, IsUnit uc ∧ Algebra.norm F (gc c) =
      algebraMap R F g ^ Nc c * algebraMap O F uc := fun c => by
    haveI := hded c
    haveI := hfr c
    obtain ⟨uc, huc, hn⟩ := ValPl.norm_eq_places (O := O) (F := F) (gc c) (hgc0 c) hirr
    refine ⟨uc, huc, ?_⟩
    rw [hn, ← IsScalarTower.algebraMap_apply R O F g, hset c]
    congr 2
    refine finsum_congr fun w => finsum_congr fun hw => ?_
    rw [← hset c] at hw
    rw [hgcv c w hw, WithTop.untopD_coe]
    rfl
  choose uc huc hNe using hN
  set X := algebraMap R F g with hX
  have hX0 : X ≠ 0 := by
    rw [hX, map_ne_zero_iff _ (IsFractionRing.injective R F)]
    rintro rfl
    have : p = ⊥ := by rw [hg, Ideal.span_singleton_eq_bot]
    subst this
    simp at hp
  let U : Oˣ := ∏ c, (huc c).unit
  have hprod : ∏ c, Algebra.norm F (gc c) = X ^ (∑ c, Nc c) * algebraMap O F (U : O) := by
    rw [Finset.prod_congr rfl fun c _ => hNe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0,
      ← map_prod]
    congr 2
    simp only [U, Units.coe_prod, IsUnit.unit_spec]
  rw [hprod] at hdisc
  set Dt := (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det with hDt
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl
    ((u : O) * ((algebraMap R O g) ^ (2 * nn + t)) * ((U⁻¹ : Oˣ) : O) * ((U⁻¹ : Oˣ) : O))
  refine ⟨a, s, s.2, ?_⟩
  have hsF : algebraMap O F (IsLocalization.mk' O a s) * algebraMap R F s = algebraMap R F a := by
    rw [IsScalarTower.algebraMap_apply R O F s, IsScalarTower.algebraMap_apply R O F a, ← map_mul,
      IsLocalization.mk'_spec]
  simp only at has
  rw [← hsF, has]
  congr 1
  set V := algebraMap O F (U : O)
  set V' := algebraMap O F ((U⁻¹ : Oˣ) : O)
  have hU : V * V' = 1 := by
    simp only [V, V']
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : X ^ (2 * ∑ c, Nc c) = (X ^ (∑ c, Nc c)) ^ 2 := by
    rw [mul_comm, zpow_mul]
    norm_cast
  have e1 : algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t) * ((U⁻¹ : Oˣ) : O) *
      ((U⁻¹ : Oˣ) : O)) = algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t)) * V' * V' := by
    simp only [V', map_mul]
  rw [h2, e1, ← hdisc]
  calc Dt * (X ^ ∑ c, Nc c) ^ 2 = Dt * (X ^ ∑ c, Nc c) ^ 2 * (V * V') * (V * V') := by
        rw [hU]; ring
    _ = Dt * ((X ^ ∑ c, Nc c) * V) ^ 2 * V' * V' := by ring

end HDiscOmL

end ReciprocityTheory.ChartRestriction.G.T0
end
