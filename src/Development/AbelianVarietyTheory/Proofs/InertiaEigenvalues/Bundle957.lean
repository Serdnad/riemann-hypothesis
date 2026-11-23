module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle954
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle915
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle910
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedThetaGeneratorEqClassSumIntegralForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle894
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle319
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle955
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.LanglandsMultisegmentsOfSeg
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle902
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSStrict

theorem qpow (q : ℕ) (x : ℝ) : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
  simp

theorem pair_val (q : ℕ) (γ : ℂˣ) (x : ℝ) :
    (γ : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom γ : ℂˣ) : ℂ) * (q : ℂ) ^ (-(x : ℂ)) =
      ((‖(γ : ℂ)‖ ^ 2 * (q : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [qpow]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_conjU (γ : ℂˣ) : ‖((Units.map (starRingEnd ℂ).toMonoidHom γ : ℂˣ) : ℂ)‖ = ‖(γ : ℂ)‖ := by
  simp

theorem hasProd_split {ι : Type*} [DecidableEq ι] (f : ι → ℂ) (T : Finset ι) (w : ι) (hw : w ∉ T) {A B : ℂ}
    (h1 : HasProd (fun v : {v : ι // v ∉ T} => f v.1) A)
    (h2 : HasProd (fun v : {v : ι // v ∉ insert w T} => f v.1) B) : A = f w * B := by
  have h1' : HasProd ({v | v ∉ T}.mulIndicator f) A :=
    (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ T})).mp h1
  have h2' : HasProd ({v | v ∉ insert w T}.mulIndicator f) B :=
    (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ insert w T})).mp h2
  have h3 : HasProd (({w} : Set ι).mulIndicator f) (f w) := by
    have := hasProd_single (f := ({w} : Set ι).mulIndicator f) w (fun b hb => by simp [Set.mulIndicator_apply, hb])
    simpa using this
  have h4 := h3.mul h2'
  have heq : (fun v => ({w} : Set ι).mulIndicator f v * {v | v ∉ insert w T}.mulIndicator f v) =
      {v | v ∉ T}.mulIndicator f := by
    funext v
    by_cases hv : v = w
    · subst hv; simp [Set.mulIndicator_apply, hw]
    · by_cases hvT : v ∈ T <;> simp [Set.mulIndicator_apply, hv, hvT]
  rw [heq] at h4
  exact h1'.unique h4

theorem half_pow_le_norm_prod {α : Type*} (g : α → ℂ) (m : Multiset α) (h : ∀ p ∈ m, (1/2 : ℝ) ≤ ‖g p‖) :
    (1/2 : ℝ) ^ Multiset.card m ≤ ‖(m.map g).prod‖ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih (fun p hp => h p (Multiset.mem_cons_of_mem hp))
    calc (1/2 : ℝ) ^ Multiset.card s * (1/2) = (1/2) * (1/2) ^ Multiset.card s := mul_comm _ _
      _ ≤ _ := mul_le_mul ha hs (by positivity) (norm_nonneg _)

theorem half_le_norm_inv_one_sub {z : ℂ} (hz : ‖z‖ < 1) : (1/2 : ℝ) ≤ ‖(1 - z)⁻¹‖ := by
  have hpos : 0 < ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    simp at this; linarith
  have hle : ‖1 - z‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) z
    simp at this; linarith
  rw [norm_inv, one_div]
  exact inv_anti₀ hpos hle

def gfac (q : ℕ) (x : ℝ) (p : ℂˣ × ℂˣ) : ℂ := (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹

theorem locL_eq (q : ℕ) (B B' : Multiset ℂˣ) (x : ℝ) : locL q B B' (x : ℂ) = ((B ×ˢ B').map (gfac q x)).prod := rfl

theorem norm_sq_lt_absNorm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a), 1 ≤ a →
    σ.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → ∀ w ∉ T, ∀ α ∈ sat σ w,
      ‖(α : ℂ)‖ ^ 2 < (Ideal.absNorm w.asIdeal : ℝ) := by
  intro E _ _ _ a σ ha hσ T hT w hw α hα
  classical
  obtain ⟨L1, hL1, -, c1, hc1, hlim1⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ T hT
  have hT' : UnrOutside (insert w T) σ := fun v hv => hT v (fun h => hv (Finset.mem_insert_of_mem h))
  obtain ⟨L2, hL2, -, c2, hc2, hlim2⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ (insert w T) hT'
  have hsplit : ∀ x : ℝ, 1 < x → (L1 x : ℂ) = ((sat σ w ×ˢ (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom)).map
      (gfac (Ideal.absNorm w.asIdeal) x)).prod * (L2 x : ℂ) := by
    intro x hx
    rw [← locL_eq]
    have e := hasProd_split (ι := HeightOneSpectrum (𝓞 E)) (fun v : HeightOneSpectrum (𝓞 E) => locL (Ideal.absNorm v.asIdeal)
      (sat σ v) ((sat σ v).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) T w hw (hL1 x hx).1 (hL2 x hx).1
    exact e
  generalize hB' : (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom) = B' at hsplit
  have hmem : ∀ γ ∈ sat σ w, (γ, Units.map (starRingEnd ℂ).toMonoidHom γ) ∈ (sat σ w) ×ˢ B' := fun γ hγ =>
    Multiset.mem_product.mpr ⟨hγ, hB' ▸ Multiset.mem_map_of_mem _ hγ⟩
  generalize hqd : Ideal.absNorm w.asIdeal = q at hsplit ⊢
  have hq1 : (1 : ℝ) < q := by rw [← hqd]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hq0 : (0 : ℝ) < q := by linarith

  have hle : ∀ γ ∈ sat σ w, ‖(γ : ℂ)‖ ^ 2 ≤ (q : ℝ) := by
    intro γ hγ
    by_contra hlt
    push_neg at hlt
    have hγ0 : (0 : ℝ) < ‖(γ : ℂ)‖ ^ 2 := by
      have : (γ : ℂ) ≠ 0 := γ.ne_zero
      positivity
    have hlogq : 0 < Real.log q := Real.log_pos hq1
    set x0 := Real.log (‖(γ : ℂ)‖ ^ 2) / Real.log q with hx0def
    have hx0 : 1 < x0 := by
      rw [hx0def, lt_div_iff₀ hlogq, one_mul]
      exact Real.log_lt_log hq0 hlt
    have hpow : (q : ℝ) ^ (-x0) = (‖(γ : ℂ)‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hq0.le, Real.rpow_def_of_pos hq0]
      congr 1
      have : Real.log q * x0 = Real.log (‖(γ : ℂ)‖ ^ 2) := by
        rw [hx0def]; field_simp
      rw [this, Real.exp_log hγ0]
    have hF0 : ((sat σ w ×ˢ B').map (gfac q x0)).prod = 0 := by
      apply Multiset.prod_eq_zero
      refine Multiset.mem_map.mpr ⟨(γ, Units.map (starRingEnd ℂ).toMonoidHom γ), hmem γ hγ, ?_⟩
      simp only [gfac]
      rw [pair_val, hpow, mul_inv_cancel₀ hγ0.ne']
      simp
    have h := hsplit x0 hx0
    rw [hF0, zero_mul] at h
    have h1 := (hL1 x0 hx0).2
    have : L1 x0 = 0 := by exact_mod_cast h
    linarith
  by_contra hnot
  push_neg at hnot
  have heq : ‖(α : ℂ)‖ ^ 2 = q := le_antisymm (hle α hα) hnot
  set t : ℝ → ℝ := fun x => (q : ℝ) * (q : ℝ) ^ (-x) with ht
  have ht1 : ∀ x, 1 < x → t x < 1 := by
    intro x hx
    have : (q : ℝ) ^ (1 + -x) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    rwa [Real.rpow_add hq0, Real.rpow_one] at this
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem (hmem α hα)

  have hlow : ∀ x, 1 < x → (1/2 : ℝ) ^ Multiset.card rest ≤
      (1 - t x) * ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ := by
    intro x hx
    have hspec : gfac q x (α, Units.map (starRingEnd ℂ).toMonoidHom α) = (((1 - t x : ℝ) : ℂ))⁻¹ := by
      simp only [gfac]
      rw [pair_val, heq]
      simp only [ht]
      push_cast
      ring
    have hrestb : ∀ p ∈ rest, (1/2 : ℝ) ≤ ‖gfac q x p‖ := by
      intro p hp
      have hp' : p ∈ (sat σ w) ×ˢ B' := by
        rw [hrest]; exact Multiset.mem_cons_of_mem hp
      obtain ⟨hp1, hp2⟩ := Multiset.mem_product.mp hp'
      rw [← hB'] at hp2
      obtain ⟨β, hβ, hβe⟩ := Multiset.mem_map.mp hp2
      have hb1 := hle p.1 hp1
      have hb2 := hle β hβ
      have hn2 : ‖(p.2 : ℂ)‖ = ‖(β : ℂ)‖ := by rw [← hβe]; exact norm_conjU β
      have hprod : ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ ≤ q := by
        rw [hn2]
        nlinarith [sq_nonneg (‖(p.1 : ℂ)‖ - ‖(β : ℂ)‖), norm_nonneg (p.1 : ℂ), norm_nonneg (β : ℂ)]
      apply half_le_norm_inv_one_sub
      rw [qpow, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
      calc ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ * (q : ℝ) ^ (-x) ≤ q * (q : ℝ) ^ (-x) :=
            mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hq0.le _)
        _ < 1 := ht1 x hx
    have hpos : 0 < 1 - t x := by linarith [ht1 x hx]
    rw [hrest, Multiset.map_cons, Multiset.prod_cons, norm_mul, hspec, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    exact half_pow_le_norm_prod (gfac q x) rest hrestb

  have hnorm : ∀ x, 1 < x → ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ = ((x - 1) * L1 x) / ((x - 1) * L2 x) := by
    intro x hx
    have h := hsplit x hx
    have hL2pos : 0 < L2 x := by linarith [(hL2 x hx).2]
    have hL1pos : 0 < L1 x := by linarith [(hL1 x hx).2]
    have hFx : ((sat σ w ×ˢ B').map (gfac q x)).prod = ((L1 x / L2 x : ℝ) : ℂ) := by
      push_cast
      rw [h, mul_div_assoc, div_self (by exact_mod_cast hL2pos.ne'), mul_one]
    rw [hFx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hL1pos hL2pos),
      mul_div_mul_left _ _ (by linarith : (x - 1) ≠ 0)]
  have htlim : Tendsto t (𝓝[>] 1) (𝓝 1) := by
    have hc : Continuous t := continuous_const.mul (continuous_const.rpow continuous_neg (fun _ => Or.inl hq0.ne'))
    have := hc.tendsto 1
    simp only [ht, Real.rpow_neg_one, mul_inv_cancel₀ hq0.ne'] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hlim : Tendsto (fun x => (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x))) (𝓝[>] 1) (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).mul (hlim1.div hlim2 hc2.ne')
    simpa using this
  have hev1 : ∀ᶠ x in 𝓝[>] (1 : ℝ), (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x)) <
      (1/2 : ℝ) ^ Multiset.card rest := hlim (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x := self_mem_nhdsWithin
  obtain ⟨x, hx1, hx2⟩ := (hev1.and hev2).exists
  have := hlow x hx2
  rw [hnorm x hx2] at this
  linarith

end GlobalTheory.RSStrict
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem unit_of_unitOff : ∀ (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (ε : FractionRing O →+* ℂ) (N : ℕ) (t : FractionRing O), IsUnit (N : O) → UnitOff N (ε t) → ∃ u : Oˣ, t = algebraMap O (FractionRing O) u := by
  intro O _ _ _ ε N t hN ⟨ht0, n, h1, h2⟩
  have hε : Function.Injective ε := ε.injective
  have key : ∀ s : FractionRing O, IsIntegral ℤ (ε s) → ∃ a : O, algebraMap O (FractionRing O) a = s := by
    intro s hs
    letI : Algebra ℤ (FractionRing O) := Ring.toIntAlgebra _
    have hs' : IsIntegral ℤ s := (isIntegral_algHom_iff (ε.toIntAlgHom) hε).mp hs
    have hO : IsIntegral O s := by
      have := IsIntegral.map_of_comp_eq (Int.castRingHom O) (RingHom.id (FractionRing O)) (RingHom.ext_int _ _) hs'
      simpa using this
    exact IsIntegrallyClosed.isIntegral_iff.mp hO
  have ht : t ≠ 0 := by rintro rfl; simp at ht0
  obtain ⟨a, ha⟩ := key (((N : FractionRing O)) ^ n * t) (by simpa [map_mul, map_pow, map_natCast] using h1)
  obtain ⟨b, hb⟩ := key (((N : FractionRing O)) ^ n * t⁻¹) (by simpa [map_mul, map_pow, map_natCast, map_inv₀] using h2)
  have hN' : (N : FractionRing O) ≠ 0 := by
    have := (hN.map (algebraMap O (FractionRing O))).ne_zero
    simpa using this
  have hab : a * b = (N : O) ^ (2 * n) := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, ha, hb, map_pow, map_natCast]
    field_simp
    ring
  have hua : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ hN.pow _)
  have hinv : algebraMap O (FractionRing O) ((hN.unit⁻¹ : Oˣ) : O) = (N : FractionRing O)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_natCast (algebraMap O (FractionRing O)) N, ← map_mul, IsUnit.val_inv_mul, map_one]
  refine ⟨hua.unit * hN.unit⁻¹ ^ n, ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_mul, map_pow, hinv, ha]
  rw [mul_comm (_ ^ n) t, mul_assoc, ← mul_pow, mul_inv_cancel₀ hN', one_pow, mul_one]

end GlobalTheory.PlaceRead
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.conj_thetaClassSum_eq_rootOfUnity_conjTuple : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ (hf : Fixes M.c' ta) (k0 : ℂ), IsRoot1 k0 ∧ ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ∃ (u : M.c'.F) (s : (AE D)ˣ), (u : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (xs : M.Cl' a → VsV D i M.c'.F) (xs' : M.Cl' b → VsV D i M.c'.F), (∀ k, (xs' (e k) : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (xs k : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M a xs f → u • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M b xs' (u • galRul hf f) := by
  first | exact @GlobalTheory.GalEqCls.galRul_isSum | exact GlobalTheory.GalEqCls.galRul_isSum | (intros; apply GlobalTheory.GalEqCls.galRul_isSum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.ClassSumRat

variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)

theorem add_mem_range {k : ℕ} {x y : GA D (Wc D j) → ℂ} (hx : x ∈ Set.range (rdK rd hρ k)) (hy : y ∈ Set.range (rdK rd hρ k)) :
    x + y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  exact ⟨x + y, map_add _ _ _⟩

theorem zero_mem_range {k : ℕ} : (0 : GA D (Wc D j) → ℂ) ∈ Set.range (rdK rd hρ k) := ⟨0, map_zero _⟩

theorem e_smul_mem_range {k : ℕ} (c : FractionRing (D.ntw.O i)) {y : GA D (Wc D j) → ℂ} (hy : y ∈ Set.range (rdK rd hρ k)) :
    ρ.e i b c • y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add (f := _), smul_add]; exact add_mem_range hρ rd hx hy
  | tmul a f => exact ⟨a ⊗ₜ (c • f), by rw [rdK_tmul, rdK_tmul, LinearMap.map_smulₛₗ, smul_comm]⟩

theorem ek_smul_mem_range {k : ℕ} (a : FractionRing (D.ntw.Ok i k)) {y : GA D (Wc D j) → ℂ} (hy : y ∈ Set.range (rdK rd hρ k)) :
    ρ.ek i b k a • y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨p, d, hd, e⟩ := D.ntw.Ok_gen i k a
  generalize Polynomial.aeval (D.ntw.zk i k : D.ntw.Ok i k) p = u at e
  have h1 : ρ.ek i b k a * ρ.eO i b d = ρ.eOk i b k u := by
    rw [← hρ.ek_e i b k d]
    exact (map_mul (ρ.ek i b k) _ _).symm.trans (congrArg (ρ.ek i b k) e)
  have hd0 : ρ.eO i b d ≠ 0 := fun h => hd (ρ.eO_injective i b (h.trans (map_zero _).symm))
  have h2 : ρ.ek i b k a = ρ.e i b (algebraMap (D.ntw.O i) _ d)⁻¹ * ρ.eOk i b k u := by
    rw [map_inv₀, ← h1, mul_comm (ρ.ek i b k a)]
    exact (inv_mul_cancel_left₀ hd0 _).symm
  obtain ⟨x, rfl⟩ := hy
  rw [h2, mul_smul]
  exact e_smul_mem_range hρ rd _ ⟨u • x, LinearMap.map_smulₛₗ _ _ _⟩


include hρ in
theorem exists_rep (t : Twist D Circle) (h : GA D (Vc D j)) : ∃ (γ : GQ (Vc D j)) (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j))
    (κ : (ρ.B i j b).levJ t), SplitSet s ∧ (∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) ∧ h' ∈ GfC (Vc D j) ∧
      SuppAt (idem s) (Vc D j) h' ∧
      finPt (Vc D j) h = Bridge.ratF (Vc D j) γ * finPt (Vc D j) h' * (κ : Bridge.Gf (Vc D j)) := by
  obtain ⟨N₀, hN₀, hK⟩ := GlobalTheory.LevFinCong.exists_finCong_lev D (Vc D j) (ρ.B i j b).F.βS ((ρ.B i j b).levS t)
  have hbad : 0 < ρ.bad i := Nat.pos_of_ne_zero (hρ.bad_ne i)
  have hK' : ∀ k ∈ GfC (Vc D j), GlobalTheory.Member.FinCong (Vc D j) N₀ k → FWT.fin (Vc D j) k ∈ (ρ.B i j b).levJ t :=
    fun k hk hc => ((ρ.B i j b).finPt_mem_levJ _ hk).2 (hK k hk hc).1
  obtain ⟨h', ⟨hh', hs⟩, γ, k, e⟩ := GlobalTheory.SplitReps.exists_split_rep (Vc D j) hN₀ hK' hbad (finPt (Vc D j) h)
  obtain ⟨-, e', P, hP, hoff, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit (Vc D j) (ρ.bad i) h' hh' hs
  refine ⟨γ, P, h', k, ⟨e', hP⟩, hoff, hh', ?_, e⟩
  rw [idem_eq hP]
  exact hsupp

theorem series_datum (hR : RatTwist hρ rd) {k Q ψ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q) {s h P}
    (hd : ρ.IsDatum i j b s h P) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b k Q ψ).chi) ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h P ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have h1 := hR k Q ψ hψ hQ s h P hd ⟨1, GlobalTheory.SplitLinear.suppAt_one _ _, rfl⟩
  rw [mul_one, GlobalTheory.TwTraceCx.gen_eq_smul (hρ.base i j b) ht hadm (hρ.weil_base i j b) (hρ.weil i j b _ ht)] at h1
  obtain ⟨u, hu⟩ := hval (detRoot (Vc D j) h)
  have hc : ((detChar (Vc D j) (ρ.tw i b k Q ψ).chi h : Circle) : ℂ) = ρ.ek i b k (algebraMap (D.ntw.Ok i k) _ u) := hu
  have h2 := ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u)⁻¹ h1
  rwa [map_inv₀, ← hc, inv_smul_smul₀ (Circle.coe_ne_zero _)] at h2

theorem term_mem (hR : RatTwist hρ rd) {k Q ψ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q) {F} (hF : F ∈ ρ.mt i j b k Q ψ)
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b k Q ψ).chi) ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h (F (finPt _ h)) ∈
      Set.range (rdK rd hρ k) := by
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have hB := hρ.base i j b
  obtain ⟨hF1, hF2⟩ := ((ρ.B i j b).mem_mtLat _ _ _).1 hF
  obtain ⟨γ, s, h', κ, hs, hoff, hh', hsupp, e⟩ := exists_rep hρ (i := i) (b := b) (ρ.tw i b k Q ψ) h
  have hlaw := ((ρ.B i j b).mem_formsC.1 hF1).2 γ (finPt _ h') κ
  have hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) =
      F (finPt _ h') := by
    rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, one_apply_eq_self]
  rw [e, hlaw, LinearMap.map_smul, GlobalTheory.BaseClassSum.series_move hB (D.sp.V_sig _) ht hadm (hρ.weil i j b _ ht) hh hh' γ κ e, hinv,
    smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have hspan : F (finPt _ h') ∈ Submodule.span (ρ.eOk i b k).range
      (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) :=
    GlobalTheory.SmallSpan.harmLat_le_span (RingHom.id _) (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.eOk i b k).range
      (hρ.isCoefRing_k i b k).int _ _ hB.wt (GlobalTheory.CoefLatConj.pq_le hB) (GlobalTheory.SmallSpan.isLattice_latAt hB.frame _) (hF2 _)
  generalize F (finPt _ h') = P at hspan
  induction hspan using Submodule.span_induction with
  | mem P hP => exact series_datum hρ rd hR hψ hQ ⟨hs, hoff, hh', hsupp, hP⟩
  | zero => rw [map_zero]; exact zero_mem_range hρ rd
  | add x y _ _ hx hy => rw [map_add]; exact add_mem_range hρ rd hx hy
  | smul a x _ hx =>
    obtain ⟨_, u, rfl⟩ := a
    have h2 := ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u) hx
    rw [← map_smul] at h2
    exact h2

theorem sum_mem_range : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (rd : Rd ρ D.nexp i j b) (T : CellTie hρ D.nexp rd), RatTwist hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  ∀ k Q ψ, TwOK i k Q ψ → ClsQ (D := D) Q → ∀ f, ρ.sum i j b k Q ψ (T.rdV k Q ψ f) ∈ Set.range (rdK rd hρ k) := by
  intro D ρ hρ i j b rd T hR _ k Q ψ hψ hQ f
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have hc := hρ.classes i j b _ ht hadm
  have hf : f ∈ Submodule.span (FractionRing (D.ntw.Ok i k)) (D.nexp.MtLat i ((j : ℕ) + 1) b k Q ψ : Set (D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ)) := by
    rw [D.nexp.MtLat_span]; trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    have hF := (T.mtLat_iff k Q ψ hψ _).2 ⟨f, hf, rfl⟩
    rw [Setup.sum, Base.classSum_apply]
    refine Finset.sum_induction _ (· ∈ Set.range (rdK rd hρ k)) (fun _ _ => add_mem_range hρ rd) (zero_mem_range hρ rd) fun c _ => ?_
    rw [← map_natCast (ρ.ek i b k), ← map_inv₀]
    exact ek_smul_mem_range hρ rd _ (term_mem hρ rd hR hψ hQ hF (hc.fin c))
  | zero => rw [map_zero, map_zero]; exact zero_mem_range hρ rd
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact add_mem_range hρ rd hx hy
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul]; exact ek_smul_mem_range hρ rd a hx

end GlobalTheory.ClassSumRat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

theorem _root_.GlobalTheory.T.thetaFunction_levelType_mem_span_translates : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → GlobalTheory.DownLift.GenFinite.Clean R i t f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.Gen R i t) := by
  first | exact @GlobalTheory.DownLift.GenFinite.gen_of_type_clean | exact GlobalTheory.DownLift.GenFinite.gen_of_type_clean | (intros; apply GlobalTheory.DownLift.GenFinite.gen_of_type_clean <;> assumption)
end

section

namespace GlobalTheory

theorem langlandsMultisegments_outright : GlobalTheory.Published.LanglandsMultisegments :=
  CompanionTheory.Exh.langlandsMultisegments_of_seg CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end

section

namespace GlobalTheory

theorem standardCosocleGL_holds : GlobalTheory.Published.StandardCosocleGL :=
  CompanionTheory.Exh.standardCosocleGL_of_seg CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end
