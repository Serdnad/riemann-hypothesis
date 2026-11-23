module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import GroundTheory.AutomorphicForms.ReductionCore
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle003
import GroundTheory.AutomorphicForms.Bundle012
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.borHaar :
    ∀ (F : Type) [Field F] [NumberField F], ∃ μS : Measure (M.Bor F), μS.IsHaarMeasure ∧ ∀ (f : G1 F → ℝ≥0∞), Measurable f → ∫⁻ s, f s ∂μS = ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
  intro F _ _
  obtain ⟨hcl, e, he⟩ := M.borHomeo F
  have hcont : Continuous fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 :=
    (M.continuous_ab.inv₀ fun a => (M.ab_pos a).ne').pow 2
  have hwm : Measurable (M.wt : IdeleGroup F → ℝ≥0∞) := M.measurable_wt
  have hw0 : ∀ a : IdeleGroup F, M.wt a ≠ 0 := fun a => by
    have : 0 < (ab a)⁻¹ ^ 2 := pow_pos (inv_pos.2 (M.ab_pos a)) 2
    exact (ENNReal.ofReal_pos.2 this).ne'
  set ν : Measure (IdeleGroup F) := (ideleMeasure F).withDensity M.wt with hν
  haveI : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hcont
  haveI : ν.IsOpenPosMeasure :=
    (withDensity_absolutelyContinuous' hwm.aemeasurable (ae_of_all _ hw0)).isOpenPosMeasure
  haveI : SFinite ν := by rw [hν]; infer_instance
  set ρ : Measure (IdeleGroup F × A F) := ν.prod (adeleMeasure F) with hρ
  have hint : ∀ f : G1 F → ℝ≥0∞, Measurable f → ∫⁻ s, f s ∂(ρ.map e) =
      ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
    intro f hf
    have hc : Continuous fun p : IdeleGroup F × A F => nU p.2 * mD p.1 :=
      (M.continuous_nU.comp continuous_snd).mul (M.continuous_mD.comp continuous_fst)
    have hfm : Measurable fun p : IdeleGroup F × A F => f (nU p.2 * mD p.1) := hf.comp hc.measurable
    rw [show ∫⁻ s, f s ∂(ρ.map e) = ∫⁻ p, f (e p) ∂ρ from
      lintegral_map (f := fun s : M.Bor F => f s) (hf.comp measurable_subtype_coe) e.continuous.measurable]
    simp only [he]
    rw [hρ, lintegral_prod _ hfm.aemeasurable, hν,
      lintegral_withDensity_eq_lintegral_mul _ hwm hfm.lintegral_prod_right']
    refine lintegral_congr fun a => ?_
    have hne : M.wt a ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [Pi.mul_apply, lintegral_mul_const' _ _ hne, mul_comm]
  refine ⟨ρ.map e, ?_, hint⟩
  haveI : IsFiniteMeasureOnCompacts (ρ.map e) := ⟨fun K hK => by
    rw [e.measurableEmbedding.map_apply]
    exact ((e.isCompact_preimage).2 hK).measure_lt_top⟩
  haveI : (ρ.map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  haveI : (ρ.map e).IsMulLeftInvariant := ⟨fun g => by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs]
    have hS : MeasurableSet (Subtype.val '' s : Set (G1 F)) := hcl.measurableSet.subtype_image hs
    set f : G1 F → ℝ≥0∞ := (Subtype.val '' s : Set (G1 F)).indicator 1 with hfdef
    have hf : Measurable f := measurable_one.indicator hS
    have hval : ∀ x : M.Bor F, f x = s.indicator 1 x := fun x => by
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, hfdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hx)]; rfl
      · rw [Set.indicator_of_notMem hx, hfdef, Set.indicator_of_notMem]
        rintro ⟨y, hy, hyx⟩
        exact hx (Subtype.ext hyx ▸ hy)
    have h1 : (ρ.map e) s = ∫⁻ x, f x ∂(ρ.map e) := by
      simp only [hval]; rw [lintegral_indicator_one hs]
    have h2 : (ρ.map e) ((fun x => g * x) ⁻¹' s) = ∫⁻ x, (fun y => f (g.1 * y)) x ∂(ρ.map e) := by
      have hs' : MeasurableSet ((fun x => g * x) ⁻¹' s) := measurable_const_mul g hs
      rw [← lintegral_indicator_one hs']
      refine lintegral_congr fun x => ?_
      have := hval (g * x)
      simpa [Set.indicator] using this.symm
    obtain ⟨p, rfl⟩ := e.surjective g
    rw [h1, h2, hint (fun y => f ((e p : G1 F) * y)) (hf.comp (measurable_const_mul _)), hint f hf]
    simp only [he]
    exact M.borLeft F f hf p.2 p.1⟩
  exact {}
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.cosetSum :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (σ) (β u : G1 F → ℝ≥0∞), M.RowSec (F := F) σ → M.NWt β → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = ∫⁻ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ := by
  intro F _ _ M₀ σ β u hσ hβ hu hinv
  have hc := (UpperTheory.ConvolutionTheory.R2.M.rowCosets F).2 σ hσ
  haveI := M₀.haar
  let e : ({r : Fin 2 → F // r ≠ 0} × F) → Gam F := fun p =>
    ⟨nU (rt p.2) * ratS F (σ p.1), (Gam F).mul_mem (M.nU_rt_mem _) ⟨_, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro p q h
      obtain ⟨p0, _, hp⟩ := hc (e p)
      exact (hp p rfl).trans (hp q (congrArg Subtype.val h)).symm
    · intro γ
      obtain ⟨p, hp, _⟩ := hc γ
      exact ⟨p, Subtype.ext hp.symm⟩
  have key : ∀ g : G1 F, ∑' γ : Gam F, u (γ • g) * β (γ • g) = ∑' r, u (ratS F (σ r) * g) := by
    intro g
    rw [← (Equiv.ofBijective e he).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun r => ?_
    have h1 : ∀ ξ : F, u ((Equiv.ofBijective e he (r, ξ)) • g) * β ((Equiv.ofBijective e he (r, ξ)) • g)
        = u (ratS F (σ r) * g) * β (nU (rt ξ) * (ratS F (σ r) * g)) := by
      intro ξ
      have h2 : (Equiv.ofBijective e he (r, ξ)) • g = nU (rt ξ) * (ratS F (σ r) * g) := by
        change (nU (rt ξ) * ratS F (σ r)) * g = _
        rw [mul_assoc]
      rw [h2, hinv]
    simp_rw [h1]
    rw [ENNReal.tsum_mul_left, hβ.2, mul_one]
  have hmeas : ∀ γ : Gam F, Measurable fun g : G1 F => u (γ • g) * β (γ • g) := fun γ =>
    (hu.mul hβ.1).comp (measurable_const_smul γ)
  rw [M₀.fund.lintegral_eq_tsum'', ← lintegral_tsum fun γ => (hmeas γ).aemeasurable]
  exact lintegral_congr key
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.lintegral_unipotent_quotient_right_invariant :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (u : G1 F → ℝ≥0∞), Measurable u → (∀ b g, u (nU b * g) = u g) → ∀ g₀, (M.J0 M₀ fun g => u (g * g₀)) = M.J0 M₀ u := by
  intro F _ _ M₀ u hu hinv g₀
  obtain ⟨β, hβ⟩ := UpperTheory.ConvolutionTheory.R2.M.wtEx F
  haveI := M₀.right
  have hone := UpperTheory.ConvolutionTheory.R2.M.wtOne F β hβ
  have hm : ∀ h : G1 F, Measurable fun g : G1 F => g * h := fun h => measurable_mul_const h
  have h1 := UpperTheory.ConvolutionTheory.R2.M.wtA F M₀ β (fun g => u (g * g₀)) 1 hβ.1 hone (hu.comp (hm g₀))
    (fun b g => by rw [mul_assoc, hinv])
  have h2 := UpperTheory.ConvolutionTheory.R2.M.wtA F M₀ (fun g => β (g * g₀⁻¹)) u 1 (hβ.1.comp (hm g₀⁻¹))
    (fun g => by simpa only [mul_assoc] using hone (g * g₀⁻¹)) hu hinv
  have h3 := lintegral_mul_right_eq_self (μ := M₀.μ) (fun g => u g * β (g * g₀⁻¹)) g₀
  simp only [mul_inv_cancel_right] at h3
  rw [one_mul] at h1 h2
  rw [← h1, ← h2, h3]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem UpperTheory.ConvolutionTheory.R2.M.pow_form {F : Type} [Field F] [NumberField F] (b : A F) (a : (A F)ˣ) (n : ℕ) :
    ∃ c : A F, (nU b * mD a) ^ n = nU c * mD (a ^ n) := by
  induction n with
  | zero => exact ⟨0, by simp [M.nU_zero, M.mD_one]⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + ((a ^ n : (A F)ˣ) : A F) ^ 2 * b, ?_⟩
    rw [pow_succ (nU b * mD a), hc, pow_succ a, M.mD_mul, M.nU_add]
    simp only [mul_assoc]
    rw [← mul_assoc (mD (a ^ n)) (nU b), M.mD_mul_nU]
    simp only [mul_assoc]

private theorem UpperTheory.ConvolutionTheory.R2.M.inv_form {F : Type} [Field F] [NumberField F] (b : A F) (a : (A F)ˣ) :
    ∃ c : A F, (nU b * mD a)⁻¹ = nU c * mD a⁻¹ := by
  refine ⟨((a⁻¹ : (A F)ˣ) : A F) ^ 2 * (-b), ?_⟩
  rw [_root_.mul_inv_rev, ← M.mD_inv, ← M.nU_neg, M.mD_mul_nU]

private theorem UpperTheory.ConvolutionTheory.R2.M.ab_pow {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (n : ℕ) :
    ab (a ^ n) = ab a ^ n := by
  induction n with
  | zero => simp [M.ab_one]
  | succ n ih => rw [pow_succ, pow_succ, M.ab_mul, ih]

private theorem UpperTheory.ConvolutionTheory.R2.M.ab_le_one {F : Type} [Field F] [NumberField F] (U : Set (IdeleGroup F)) (hU : IsCompact U)
    (a : (A F)ˣ) (h : ∀ n : ℕ, a ^ n ∈ U) : ab a ≤ 1 := by
  obtain ⟨C, hC⟩ := (hU.image (M.continuous_ab (F := F))).bddAbove
  by_contra hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.mp hlt)
  have := hC (Set.mem_image_of_mem _ (h n))
  rw [M.ab_pow] at this
  exact absurd hn (not_lt.mpr this)

theorem UpperTheory.ConvolutionTheory.R2.M.borK :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ U : Set (IdeleGroup F), IsCompact U ∧ ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → a ∈ U ∧ ab a = 1 := by
  intro F _ _ _
  obtain ⟨hK, hKc⟩ := M.kkCpt F
  obtain ⟨hB, e, he⟩ := M.borHomeo F
  have hemb : IsClosedEmbedding (Subtype.val : M.Bor F → G1 F) := hB.isClosedEmbedding_subtypeVal
  have hK' : IsCompact ((Subtype.val : M.Bor F → G1 F) ⁻¹' KK F) := hemb.isCompact_preimage hKc
  let U : Set (IdeleGroup F) := Prod.fst '' (e.symm '' ((Subtype.val : M.Bor F → G1 F) ⁻¹' KK F))
  have hU : IsCompact U := (hK'.image e.symm.continuous).image continuous_fst
  have mem : ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → a ∈ U := by
    intro b a h
    refine ⟨(a, b), ⟨e (a, b), ?_, e.symm_apply_apply _⟩, rfl⟩
    change ((e (a, b) : M.Bor F) : G1 F) ∈ KK F
    rw [he]; exact h
  have le : ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → ab a ≤ 1 := by
    intro b a h
    refine M.ab_le_one U hU a fun n => ?_
    obtain ⟨c, hc⟩ := M.pow_form b a n
    refine mem c _ ?_
    rw [← hc, hK]
    rw [hK] at h
    exact (M.Ks F).pow_mem h n
  refine ⟨U, hU, fun b a h => ⟨mem b a h, le_antisymm (le b a h) ?_⟩⟩
  obtain ⟨c, hc⟩ := M.inv_form b a
  have h2 : nU c * mD a⁻¹ ∈ KK F := by
    rw [← hc, hK]
    rw [hK] at h
    exact (M.Ks F).inv_mem h
  have h3 := le c _ h2
  rw [M.ab_inv] at h3
  exact (inv_le_one₀ (M.ab_pos a)).mp h3
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.fromGL :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ (g : G1 F), ∀ b ∈ Reduction.adelicBorel (K := F) (n := 2), ∀ k ∈ Reduction.maxCompact (K := F) (n := 2), gl g = b * k → ∃ (x : A F) (a : (A F)ˣ), ∃ k' ∈ KK F, g = nU x * mD a * k' ∧ (a : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 ∧ Reduction.adeleAbs ((b : Matrix (Fin 2) (Fin 2) (A F)) 1 1) = (ab a)⁻¹ := by
  intro F _ _ _ g b hb k hk hg
  obtain ⟨hdk, hab⟩ := M.detK F k hk
  set t := Matrix.GeneralLinearGroup.det k with ht
  have hk' : (dM t)⁻¹ * k ∈ Reduction.maxCompact (K := F) (n := 2) := mul_mem (inv_mem hdk) hk
  have hd : Matrix.GeneralLinearGroup.det (dM t) = t := by
    refine Units.ext ?_
    simp [dM, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hdet : Matrix.GeneralLinearGroup.det ((dM t)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hd, ← ht, inv_mul_cancel]
  let s : G1 F := ⟨((dM t)⁻¹ * k).val, by
    have h1 := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h1⟩
  have hs : gl s = (dM t)⁻¹ * k := Units.ext rfl
  have hsK : s ∈ KK F := by
    rw [(M.kkCpt F).1]
    show gl s ∈ Reduction.maxCompact (K := F) (n := 2)
    rw [hs]
    exact hk'
  have hc : gl (g * s⁻¹) = b * dM t := by
    have hm : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
    have h1 : gl (g * s⁻¹) = gl g * (gl s)⁻¹ := by
      rw [hm, eq_inv_of_mul_eq_one_left (a := gl s⁻¹) (b := gl s) (by rw [← hm, inv_mul_cancel]; exact map_one _)]
    rw [h1, hs, hg]
    group
  have hv : (g * s⁻¹).1 = (b : Matrix (Fin 2) (Fin 2) (A F)) * (dM t).val :=
    congrArg Units.val hc
  have hlow : (b : Matrix (Fin 2) (Fin 2) (A F)) 1 0 = 0 :=
    (Reduction.mem_adelicBorel.1 hb) (show (0 : Fin 2) < 1 by decide)
  have e00 : (g * s⁻¹).1 0 0 = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * s⁻¹).1 0 1 = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * s⁻¹).1 1 0 = 0 := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two, hlow]
  have e11 : (g * s⁻¹).1 1 1 = (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F) := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet2 : (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 * ((b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F)) = 1 := by
    have h1 := (g * s⁻¹).det_coe
    rw [Matrix.det_fin_two, e00, e01, e10, e11, mul_zero, sub_zero] at h1
    exact h1
  let a : (A F)ˣ := (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 0).unit
  have ha : (a : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 := IsUnit.unit_spec _
  have hinv : ((a⁻¹ : (A F)ˣ) : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [ha]; exact hdet2)
  have hh : g * s⁻¹ = nU ((b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) * (a : A F)) * mD a := by
    refine Subtype.ext ?_
    rw [M.val_mul (nU _) (mD a)]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, ha] using e00
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] using e01
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two] using e10
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, hinv] using e11
  refine ⟨(b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) * (a : A F), a, s, hsK, ?_, ha, ?_⟩
  · rw [← hh, inv_mul_cancel_right]
  · have hb11 : (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 = ((a⁻¹ * t⁻¹ : (A F)ˣ) : A F) := by
      rw [Units.val_mul, hinv, mul_assoc, Units.mul_inv, mul_one]
    rw [hb11, Reduction.adeleAbs_units]
    show ab (a⁻¹ * t⁻¹) = _
    rw [M.ab_mul, M.ab_inv, M.ab_inv, hab, inv_one, mul_one]
end
