module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle065
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameCoupledEx

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_g_lt (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (hA : IsPlaceOver (F := E) A v) {g : ℕ}
    (hg : ((g : ℕ) : 𝓞 E) ∈ v.asIdeal) : A.valuation ((g : ℕ) : Ω) < 1 := by
  have := (hA ((g : ℕ) : 𝓞 E)).2 hg
  simpa using this


omit [NumberField E] in
theorem val_nat_not_lt (A : ValuationSubring Ω) {g m : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    (hm : ¬ g ∣ m) : ¬ A.valuation ((m : ℕ) : Ω) < 1 := by
  intro hm1
  obtain ⟨a, b, hab⟩ : IsCoprime (m : ℤ) (g : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hgp).2 hm))
  have hle : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have e : (a : Ω) * m + (b : Ω) * g = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have : A.valuation ((a : Ω) * m + (b : Ω) * g) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hle a) zero_le hm1
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hle b) zero_le hg
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem fix_rou {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {m : ℕ} (hm : 0 < m) (hgm : ¬ g ∣ m) {μ : Ω} (hμ : μ ^ m = 1) :
    σ μ = μ := by
  refine ReciprocityTheory.Gal.eq_of_pow_eq_one A (val_nat_not_lt A hgp hg hgm) (by rw [← map_pow, hμ, map_one]) hμ ?_
  exact hσ.2 μ ((A.valuation_le_one_iff _).2 (Formalism.L2.NT.mem_of_pow_eq_one A hm hμ))

theorem not_dvd_pow_sub_one {g d : ℕ} (hgp : g.Prime) (hd : 0 < d) : ¬ g ∣ g ^ d - 1 := by
  intro h
  have h1 : g ∣ g ^ d := dvd_pow_self g hd.ne'
  have h2 : 1 < g ^ d := Nat.one_lt_pow hd.ne' hgp.one_lt
  have h3 : g ∣ g ^ d - (g ^ d - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2.le] at h3
  exact hgp.not_dvd_one h3

theorem pow_sub_one_pos {g d : ℕ} (hgp : g.Prime) (hd : 0 < d) : 0 < g ^ d - 1 := by
  have h2 : 1 < g ^ d := Nat.one_lt_pow hd.ne' hgp.one_lt
  omega

variable [CharZero Ω]

omit [NumberField E] in
theorem ne_zero_of_pow_eq {g N : ℕ} (hgp : g.Prime) (hN : 0 < N) {y : Ω} (hy : y ^ N = ((g : ℕ) : Ω)) : y ≠ 0 := by
  rintro rfl
  rw [zero_pow hN.ne'] at hy
  exact (Nat.cast_ne_zero.2 hgp.ne_zero : ((g : ℕ) : Ω) ≠ 0) hy.symm

theorem ratio_indep {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {N : ℕ} (hN : 0 < N) (hgN : ¬ g ∣ N) {y y' : Ω}
    (hy : y ^ N = ((g : ℕ) : Ω)) (hy' : y' ^ N = ((g : ℕ) : Ω)) : σ y' / y' = σ y / y := by
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  have hy0 := ne_zero_of_pow_eq hgp hN hy
  obtain ⟨μ, rfl⟩ : ∃ μ, y' = μ * y := ⟨y' / y, by field_simp⟩
  have hμ : μ ^ N = 1 := by
    rw [mul_pow, hy] at hy'
    exact (mul_eq_right₀ hg0).1 hy'
  have hμ0 : μ ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hμ; exact zero_ne_one hμ
  rw [map_mul, fix_rou hgp hg hσ hN hgN hμ]
  field_simp

theorem ratio_mul {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (τ : G E Ω) {N : ℕ} (hN : 0 < N) (hgN : ¬ g ∣ N) {y : Ω}
    (hy : y ^ N = ((g : ℕ) : Ω)) : (σ * τ) y / y = (σ y / y) * (τ y / y) := by
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  have hy0 := ne_zero_of_pow_eq hgp hN hy
  have hc : (τ y / y) ^ N = 1 := tameQuot_pow τ hg0 hy
  set c := τ y / y with hcdef
  have e : τ y = c * y := by rw [hcdef]; field_simp
  rw [AlgEquiv.mul_apply, e, map_mul, fix_rou hgp hg hσ hN hgN hc]
  field_simp

theorem ratio_pow {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {N : ℕ} (hN : 0 < N) (hgN : ¬ g ∣ N) {y : Ω}
    (hy : y ^ N = ((g : ℕ) : Ω)) (j : ℕ) : (σ ^ j) y / y = (σ y / y) ^ j := by
  have hy0 := ne_zero_of_pow_eq hgp hN hy
  induction j with
  | zero => simp [hy0]
  | succ j ih =>
    rw [pow_succ, ratio_mul hgp hg (pow_mem hσ j) σ hN hgN hy, ih, pow_succ]

theorem root_down {g d D : ℕ} (hdD : d ∣ D) {r : Ω} (hr : r ^ (g ^ D - 1) = ((g : ℕ) : Ω)) :
    (r ^ ((g ^ D - 1) / (g ^ d - 1))) ^ (g ^ d - 1) = ((g : ℕ) : Ω) := by
  rw [← pow_mul, Nat.div_mul_cancel (Nat.pow_sub_one_dvd_pow_sub_one g hdD), hr]

theorem ratio_descent {A : ValuationSubring Ω} {g : ℕ} (hgp : g.Prime) (hg : A.valuation ((g : ℕ) : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {d D : ℕ} (hd : 0 < d) (hdD : d ∣ D) {y r : Ω}
    (hy : y ^ (g ^ d - 1) = ((g : ℕ) : Ω)) (hr : r ^ (g ^ D - 1) = ((g : ℕ) : Ω)) :
    σ y / y = (σ r / r) ^ ((g ^ D - 1) / (g ^ d - 1)) := by
  rw [ratio_indep hgp hg hσ (pow_sub_one_pos hgp hd) (not_dvd_pow_sub_one hgp hd) (root_down hdD hr) hy,
    map_pow, div_pow]

end

theorem val_sub_one_lt_of_red {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {l : ℕ} [Fact l.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar l) {x : Ω} (hx : x ∈ A) (h : redThrough A κ x = 1) :
    A.valuation (x - 1) < 1 := by
  unfold redThrough at h
  rw [dite_eq_left hx] at h
  have h1 : IsLocalRing.residue A ⟨x, hx⟩ = IsLocalRing.residue A 1 := κ.injective (by rw [h, map_one, map_one])
  have h2 : (⟨x, hx⟩ : A) - 1 ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.1 h1
  have h3 := (A.valuation_lt_one_iff _).1 h2
  simpa using h3

end GlobalTheory.TameCoupledEx
end
end

section

open Formalism.MainNotions.DIV.Cons (intO)
open Polynomial

namespace GlobalTheory.IntegralOfPointValues

theorem mem_intO_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {z : C}
    (hz : IsIntegral ↥(intO C) z) : z ∈ intO C := by
  let V : ValuationSubring C :=
    { intO C with
      mem_or_inv_mem' := fun x => by
        change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
        rcases le_total ‖x‖ 1 with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h) }
  have hz' : IsIntegral V z := hz
  obtain ⟨v, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := C)).1 hz'
  exact v.2


open Polynomial in
theorem _root_.GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul_of_closed {O C B₀ B₁ : Type*} [CommRing O] [Field C] [IsAlgClosed C]
    [Algebra O C] (hinj : Function.Injective (algebraMap O C))
    (hcl : ∀ z : C, IsIntegral O z → z ∈ (algebraMap O C).range)
    [CommRing B₀] [Algebra O B₀] [Algebra.IsIntegral O B₀] [CommRing B₁] [Algebra C B₁]
    [Algebra O B₁] [IsScalarTower O C B₁] (j : B₀ →ₐ[O] B₁) (x : B₀) (q : O) (hq : q ≠ 0)
    (h : ∀ χ : B₀ →ₐ[O] O, q ∣ χ x) : IsIntegral O ((algebraMap O C q)⁻¹ • j x) := by
  classical
  set y := j x with hy
  set a := (algebraMap O C q)⁻¹ with ha
  have hjint : ∀ b, IsIntegral C (j b) := fun b =>
    ((Algebra.IsIntegral.isIntegral (R := O) b).map j).tower_top
  have hyint : IsIntegral C y := hjint x
  have hroot : ∀ α ∈ (minpoly C y).roots, ∃ k : O, algebraMap O C k = a * α := by
    intro α hα
    set D := Algebra.adjoin C (Set.range j) with hD
    haveI : Algebra.IsIntegral C D :=
      Algebra.IsIntegral.adjoin (by rintro _ ⟨b, rfl⟩; exact hjint b)
    have hmem : ∀ b, j b ∈ D := fun b => Algebra.subset_adjoin ⟨b, rfl⟩
    let yD : D := ⟨y, hmem x⟩
    have hnu : yD - algebraMap C D α ∈ nonunits D := by
      intro hu
      have hu' : IsUnit (y - algebraMap C B₁ α) := by
        simpa using hu.map D.val
      have hαr : IsRoot (minpoly C y) α := (mem_roots (minpoly.ne_zero hyint)).1 hα
      have hfac := mul_divByMonic_eq_iff_isRoot.2 hαr
      have hmon : ((minpoly C y) /ₘ (X - Polynomial.C α)).Monic :=
        (monic_X_sub_C α).of_mul_monic_left (by rw [hfac]; exact minpoly.monic hyint)
      apply minpoly.aeval_ne_zero_of_dvdNotUnit_minpoly (A := C) (x := y) hyint hmon
      · refine ⟨hmon.ne_zero, X - Polynomial.C α, ?_, by rw [mul_comm, hfac]⟩
        exact not_isUnit_X_sub_C α
      · have h0 := minpoly.aeval C y
        rw [← hfac, map_mul] at h0
        simpa using (hu'.mul_right_eq_zero).1 (by simpa using h0)
    obtain ⟨M, hMmax, hMmem⟩ := exists_max_ideal_of_mem_nonunits hnu
    letI : Field (D ⧸ M) := Ideal.Quotient.field M
    have hbij : Function.Bijective (algebraMap C (D ⧸ M)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : C ≃ₐ[C] D ⧸ M := AlgEquiv.ofBijective (Algebra.ofId C (D ⧸ M)) hbij
    let ψ : D →ₐ[C] C := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C M)
    have hψy : ψ yD = α := by
      have h1 : Ideal.Quotient.mkₐ C M yD = e α := by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        change _ = Ideal.Quotient.mk M (algebraMap C D α)
        rw [Ideal.Quotient.eq]
        exact hMmem
      simp only [ψ, AlgHom.comp_apply, h1]
      exact e.symm_apply_apply α
    have hcomm : ∀ o : O,
        (⟨j (algebraMap O B₀ o), hmem _⟩ : D) = algebraMap C D (algebraMap O C o) :=
      fun o => by ext; simp [IsScalarTower.algebraMap_apply O C B₁]
    let jres : B₀ →+* D := (j : B₀ →+* B₁).codRestrict D hmem
    let χ₀ : B₀ →ₐ[O] C :=
      { ψ.toRingHom.comp jres with
        commutes' := fun o => by
          show ψ ⟨j (algebraMap O B₀ o), hmem _⟩ = _
          rw [hcomm]; exact ψ.commutes _ }
    have hχ₀x : χ₀ x = α := hψy
    have hval : ∀ b, χ₀ b ∈ (⊥ : Subalgebra O C) := fun b => by
      rw [Algebra.mem_bot]
      obtain ⟨t, ht⟩ := hcl _ ((Algebra.IsIntegral.isIntegral (R := O) b).map χ₀)
      exact ⟨t, ht⟩
    let eb := Algebra.botEquivOfInjective hinj
    let χ : B₀ →ₐ[O] O := eb.toAlgHom.comp (χ₀.codRestrict ⊥ hval)
    have hback : ∀ s : (⊥ : Subalgebra O C), algebraMap O C (eb s) = s := fun s => by
      have h2 : eb.symm (eb s) = s := eb.symm_apply_apply s
      rw [← Algebra.algebraMap_self_apply (eb s), eb.symm.commutes] at h2
      exact congrArg Subtype.val h2
    have hχx : algebraMap O C (χ x) = α := by
      rw [← hχ₀x]; exact hback _
    obtain ⟨k, hk⟩ := h χ
    refine ⟨k, ?_⟩
    have hq' : algebraMap O C q ≠ 0 := (map_ne_zero_iff _ hinj).2 hq
    rw [← hχx, hk, map_mul, ha, ← mul_assoc, inv_mul_cancel₀ hq', one_mul]
  set s := (minpoly C y).roots with hs
  let f : C → O := fun α => if hh : ∃ k : O, algebraMap O C k = a * α then hh.choose else 0
  have hf : ∀ α ∈ s, algebraMap O C (f α) = a * α := fun α hα => by
    have hh := hroot α hα
    simp only [f, dif_pos hh]
    exact hh.choose_spec
  have hsplit : minpoly C y = (s.map fun α => X - Polynomial.C α).prod :=
    (IsAlgClosed.splits (minpoly C y)).eq_prod_roots_of_monic (minpoly.monic hyint)
  have hzero : (s.map fun α => y - algebraMap C B₁ α).prod = 0 := by
    have h0 := minpoly.aeval C y
    rw [hsplit, map_multiset_prod, Multiset.map_map] at h0
    simpa [Function.comp_def] using h0
  refine ⟨(s.map fun α => X - Polynomial.C (f α)).prod,
    monic_multiset_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _), ?_⟩
  rw [eval₂_multiset_prod, Multiset.map_map]
  have hfac : ∀ α ∈ s, (eval₂ (algebraMap O B₁) (a • y) ∘ fun α => X - Polynomial.C (f α)) α =
      algebraMap C B₁ a * (y - algebraMap C B₁ α) := fun α hα => by
    simp only [Function.comp_apply, eval₂_sub, eval₂_X, eval₂_C]
    rw [IsScalarTower.algebraMap_apply O C B₁, hf α hα, Algebra.smul_def, map_mul, mul_sub]
  rw [Multiset.map_congr rfl hfac, Multiset.prod_map_mul, hzero, mul_zero]

theorem isIntegral_inv_smul : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] (B₀ B₁ : Type) [CommRing B₀] [Algebra ↥(intO C) B₀] [Module.Finite ↥(intO C) B₀] [CommRing B₁] [Algebra C B₁] [Algebra ↥(intO C) B₁] [IsScalarTower ↥(intO C) C B₁] (j : B₀ →ₐ[↥(intO C)] B₁) (x : B₀) (q : ↥(intO C)), q ≠ 0 → (∀ χ : B₀ →ₐ[↥(intO C)] ↥(intO C), q ∣ χ x) → IsIntegral ↥(intO C) (((q : C)⁻¹) • j x) := by
  intro C _ _ _ B₀ B₁ _ _ _ _ _ _ _ j x q hq h
  exact isIntegral_inv_smul_of_closed (O := ↥(intO C)) (C := C) Subtype.val_injective
    (fun z hz => ⟨⟨z, mem_intO_of_isIntegral hz⟩, rfl⟩) j x q hq h

end GlobalTheory.IntegralOfPointValues
end

section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

namespace GlobalTheory.AbsIrrOfAlgClosed

theorem span_restrict_eq_top_of_isIrrSub_map {k Γ L : Type} [Field k] [Group Γ] [Field L]
    [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W)
    (habs : IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))))) :
    Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  classical
  letI : Algebra k L := f.toAlgebra
  set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ
  let r : Γ → Module.End k W := fun g => (τ g).restrict (hW g)
  have hr1 : r 1 = 1 := by
    ext v; simp [r]
  have hrm : ∀ g h, r (g * h) = r g * r h := by
    intro g h; ext v; simp [r]
  let d := Module.finrank k W
  let e : W ≃ₗ[k] (Fin d → k) := (Module.finBasis k W).equivFun
  let φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k :=
    e.conj.trans LinearMap.toMatrix'
  have hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ
      (e.symm : (Fin d → k) →ₗ[k] W)) := fun _ => rfl
  have hφ1 : φ 1 = 1 := by
    rw [hφa]
    have : (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ
        (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id := LinearMap.ext fun v => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hφm : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    rw [hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun v => by simp
  let S : Γ →* Matrix (Fin d) (Fin d) k :=
    { toFun := fun g => φ (r g)
      map_one' := by rw [hr1, hφ1]
      map_mul' := fun g h => by rw [hrm, hφm] }
  let σ : Γ →* GL (Fin d) k := MonoidHom.toHomUnits S
  have hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g) := fun g => rfl
  let Li : (Fin d → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ e.symm.toLinearMap
  have hLinj : Function.Injective Li := by
    intro x y hxy
    exact e.symm.injective (Subtype.val_injective hxy)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective Li (LinearMap.ker_eq_bot.2 hLinj)
  let B : Matrix (Fin a) (Fin d) k := LinearMap.toMatrix' Li
  let C : Matrix (Fin d) (Fin a) k := LinearMap.toMatrix' L'
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]
  have hBv : ∀ c, B.mulVec c = Li c := fun c => LinearMap.toMatrix'_mulVec Li c
  have hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k) := by
    intro g
    have hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g) := by
      have : τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) :=
        LinearMap.ext fun v => by rw [hτ, GlobalTheory.BurnsideSub.matRep_apply, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix'_toLin']
    rw [hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun c => ?_
    change τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)
    rw [e.symm_apply_apply]
    rfl
  have hspan : Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) =
      LinearMap.range (B.map f).mulVecLin := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨f ∘ e ⟨w, hw⟩, ?_⟩
      funext i
      have h1 : B.mulVec (e ⟨w, hw⟩) = w := by
        rw [hBv]
        change ((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w
        rw [e.symm_apply_apply]
      rw [Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]
      rfl
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [op_smul_eq_smul]
      refine Submodule.smul_mem _ _ ?_
      apply Submodule.subset_span
      refine ⟨Li (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩
      funext i
      simp [← hBv, Matrix.mulVec_single_one]
  rw [hspan] at habs
  have hirr : IsIrrSub (mapRep f σ) ⊤ := by
    refine GlobalTheory.BurnsideSub.isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f)
      (C.map f) ?_ ?_ habs
    · rw [← Matrix.map_mul, hCB]
      exact Matrix.map_one _ f.map_zero f.map_one
    · intro g
      change (ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f =
        B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f
      rw [← Matrix.map_mul, ← Matrix.map_mul, hint g]
  have h2 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) =
      fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map (algebraMap k L) := by
    funext g
    ext p q
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]
  rw [h3] at h2
  have h4 := GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2
  have h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r := by
    rw [← Set.range_comp]; rfl
  have h6 := Submodule.map_span φ.toLinearMap (Set.range r)
  change Submodule.span k (Set.range r) = ⊤
  refine Submodule.map_injective_of_injective φ.injective ?_
  rw [h6, Submodule.map_top, LinearEquiv.range]
  rw [h5] at h4
  exact h4

theorem absIrrSub_of_isIrrSub_map : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L]
    (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)), IsInv ρ W →
    IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) →
    AbsIrrSub ρ W := by
  intro k Γ L _ _ _ _ f a ρ W hinv hirr
  have hW : Stable (matRep ((Units.coeHom _).comp ρ)) W := fun g v hv => by
    have := hinv g v hv
    simpa [GlobalTheory.BurnsideSub.matRep_apply] using this
  have hne : W ≠ ⊥ := by
    intro h0
    apply hirr.1
    rw [h0]
    simp
  have hsp := span_restrict_eq_top_of_isIrrSub_map f ρ W hW hirr
  unfold AbsIrrSub
  exact GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top _ ρ W hW hne hsp

end GlobalTheory.AbsIrrOfAlgClosed
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (s : Sp A ⟶ S) (k : ℕ), IsUnit (k : A) →
    ∀ (x y : Over.mk s ⟶ G), x ^ k = y ^ k →
    ∀ (κ : Type) [Field κ] (c : A →+* κ), IsLocalHom c → spMap c ≫ x.left = spMap c ≫ y.left → x = y := by
  first | exact @GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint | exact GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint | (intros; apply GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint <;> assumption)
end
