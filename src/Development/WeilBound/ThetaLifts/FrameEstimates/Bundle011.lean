module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
public import Development.WeilBound.ThetaLifts.FrameEstimates.FourierInjA
import GroundTheory.GlobalFields.Adele.Bundle001
import Mathlib.Algebra.Module.Torsion.Prod
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels BoundedContinuousFunction

namespace FourInj

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


open scoped Classical in
variable (F κ) in
def split : (κ → AF F) ≃ₜ+ ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) :
    InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  left_inv x := funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  right_inv p := Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) rfl
  map_add' x y := Prod.ext (funext fun i => map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 (y i).1) rfl
  continuous_toFun := Continuous.prodMk
    (continuous_pi fun i => (GroundTheory.Global.homeomorphMixedSpace F).continuous.comp
      (continuous_fst.comp (continuous_apply i)))
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i => by
    have h : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm = (GroundTheory.Global.homeomorphMixedSpace F).symm := by
      funext z
      apply (GroundTheory.Global.homeomorphMixedSpace F).injective
      rw [Homeomorph.apply_symm_apply, GroundTheory.Global.homeomorphMixedSpace_apply, RingEquiv.apply_symm_apply]
    refine Continuous.prodMk ?_ ((continuous_apply i).comp continuous_snd)
    rw [h]
    exact (GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply i).comp continuous_fst)


open scoped Classical in
theorem sch_props (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Continuous Φ ∧ (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) ∧ Integrable Φ μ := by
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    have := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
    have := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
    have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
    let _ : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
    have : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
    let _ : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
    have : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
    have e : pureA F f g = (fun p => f p.1 * g p.2) ∘ split F κ := rfl
    have hc : Continuous fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) => f p.1 * g p.2 :=
      (f.continuous.comp continuous_fst).mul (hg.1.continuous.comp continuous_snd)
    obtain ⟨C, hC⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
    refine ⟨e ▸ hc.comp (split F κ).continuous, ⟨SchwartzMap.seminorm ℂ 0 0 f * C, fun x => ?_⟩, ?_⟩
    · rw [e, Function.comp_apply, norm_mul]
      exact mul_le_mul (SchwartzMap.norm_le_seminorm ℂ f _) (hC _) (norm_nonneg _) (apply_nonneg _ _)
    · let ν : Measure ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
        (Measure.addHaar).prod Measure.addHaar
      have hi : Integrable (fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
          f p.1 * g p.2) ν :=
        f.integrable.mul_prod (hg.1.continuous.integrable_of_hasCompactSupport hg.2)
      have : (μ.map (split F κ)).IsAddHaarMeasure := (split F κ).isAddHaarMeasure_map μ
      have : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
      have h2 := Measure.isAddLeftInvariant_eq_smul (μ.map (split F κ)) ν
      rw [e]
      refine Integrable.comp_measurable ?_ (split F κ).continuous.measurable
      rw [h2]
      exact hi.smul_measure_nnreal
  | zero => exact ⟨continuous_const, ⟨0, fun x => by simp⟩, integrable_zero _ _ _⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨a1, ⟨C, hC⟩, a2⟩ := h1
    obtain ⟨b1, ⟨D, hD⟩, b2⟩ := h2
    exact ⟨a1.add b1, ⟨C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩, a2.add b2⟩
  | smul c Φ _ h =>
    obtain ⟨a1, ⟨C, hC⟩, a2⟩ := h
    refine ⟨a1.const_smul c, ⟨‖c‖ * C, fun x => ?_⟩, a2.smul c⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hat : At (evI F) (realAd F (1 / (2 * n))) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · show u.1 * _ = 0
      rw [h1, zero_mul]
    · show u.2 * 0 = 0
      rw [mul_zero]
  have hev : evI F (realAd F (1 / (2 * n))) = algebraMap ℝ _ (1 / (2 * n) : ℝ) := RingEquiv.apply_symm_apply _ _
  refine ⟨realAd F (1 / (2 * n)), ?_⟩
  rw [hψ.2.2 _ hat, hev, Algebra.trace_algebraMap]
  have eR : (n • (1 / (2 * n) : ℝ) : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    field_simp
  rw [eR]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * ((1 / 2 : ℝ) : ℂ) = -(Real.pi * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  obtain ⟨s, hs⟩ := exists_ne_one hψ
  have hne : ψ ≠ 1 := fun h1 => hs (by rw [h1]; rfl)
  exact (GlobalTheory.CompanionTheory.AdeleAnn.unitary_and_annihilator_eq F ψ hψ.1 hne hψ.2.1).1 x

theorem nondeg {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) (h : ∀ y, ψ (x * y) = 1) : x = 0 := by
  obtain ⟨s, hs⟩ := exists_ne_one hψ
  have hne : ψ ≠ 1 := fun h1 => hs (by rw [h1]; rfl)
  obtain ⟨b, rfl⟩ := (GlobalTheory.CompanionTheory.AdeleAnn.unitary_and_annihilator_eq F ψ hψ.1 hne hψ.2.1).2 x fun a => h _
  by_cases hb : b = 0
  · rw [hb, map_zero]
  · refine absurd ?_ hs
    rw [← h (algebraMap F (AF F) b⁻¹ * s), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hb, map_one, one_mul]

theorem eq_zero {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure]
    {H : (κ → AF F) → ℂ} (hc : Continuous H) (hi : Integrable H μ) (h0 : ∀ y, ∫ u, ψ (u ⬝ᵥ y) * H u ∂μ = 0) :
    H = 0 := by
  classical
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : PolishSpace (κ → AF F) := polish_of_lc _
  have hn := norm_psi hψ
  have hne : ∀ t, ψ t ≠ 0 := fun t h => by simpa [h] using hn t
  let e : (κ → AF F) → (κ → AF F) →ᵇ ℂ := fun y =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun u => ψ (u ⬝ᵥ y))
      (hψ.1.comp (continuous_id.dotProduct continuous_const)) 1 fun u => (hn _).le
  have he : ∀ y u, e y u = ψ (u ⬝ᵥ y) := fun _ _ => rfl
  have hae : H =ᵐ[μ] 0 := by
    refine complex_ae_zero μ e ⟨0, ?_⟩ (fun a b => ⟨a + b, ?_⟩) (fun a => ⟨-a, ?_⟩) (fun x x' hxx => ?_) hi h0
    · ext u; simp [he]
    · ext u; simp [he, AddChar.map_add_eq_mul]
    · ext u
      have h1 : ψ (-(u ⬝ᵥ a)) * ψ (u ⬝ᵥ a) = 1 := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      have h2 : (starRingEnd ℂ) (ψ (u ⬝ᵥ a)) * ψ (u ⬝ᵥ a) = 1 := by simp [Complex.conj_mul', hn]
      simpa [he] using mul_right_cancel₀ (hne _) (h1.trans h2.symm)
    · by_contra hcon
      push Not at hcon
      refine hxx (funext fun i => sub_eq_zero.1 (nondeg hψ _ fun t => ?_))
      have h1 := hcon (Pi.single i t)
      rw [he, he, dotProduct_single, dotProduct_single] at h1
      rw [sub_mul, AddChar.map_sub_eq_div, h1, div_self (hne _)]
  exact (hc.ae_eq_iff_eq μ continuous_const).1 hae

end FourInj


open FourInj in
theorem fourierInj_of : FourierInj := by
  intro F _ _ κ _ ψ hψ μ hμ Φ₁ h₁ Φ₂ h₂ Ψ₁ k₁ Ψ₂ k₂ hco x u
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hn := norm_psi hψ
  have hne : ∀ t, ψ t ≠ 0 := fun t h => by simpa [h] using hn t
  have hcont : ∀ {A B : (κ → AF F) → ℂ}, A ∈ schA F κ → B ∈ schA F κ → ∀ w,
      Continuous fun v => A (v + w) * (starRingEnd ℂ) (B v) := fun hA hB w =>
    ((sch_props μ hA).1.comp (continuous_id.add continuous_const)).mul
      (Complex.continuous_conj.comp (sch_props μ hB).1)
  have hint : ∀ {A B : (κ → AF F) → ℂ}, A ∈ schA F κ → B ∈ schA F κ → ∀ w,
      Integrable (fun v => A (v + w) * (starRingEnd ℂ) (B v)) μ := by
    intro A B hA hB w
    obtain ⟨C, hC⟩ := (sch_props μ hA).2.1
    have hic : Integrable (fun v => (starRingEnd ℂ) (B v)) μ :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (sch_props μ hB).2.2
    exact hic.bdd_mul (c := C)
      ((sch_props μ hA).1.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun v => hC _)
  have hint' : ∀ {A B : (κ → AF F) → ℂ}, A ∈ schA F κ → B ∈ schA F κ → ∀ w y,
      Integrable (fun v => ψ (v ⬝ᵥ y) * (A (v + w) * (starRingEnd ℂ) (B v))) μ := fun hA hB w y =>
    (hint hA hB w).bdd_mul (c := 1)
      (hψ.1.comp (continuous_id.dotProduct continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun v => (hn _).le)
  have hcoef : ∀ (A B : (κ → AF F) → ℂ) w y, coef F ψ μ A B (w, y) =
      ψ (⅟(2 : AF F) * (w ⬝ᵥ y)) * ∫ v, ψ (v ⬝ᵥ y) * (A (v + w) * (starRingEnd ℂ) (B v)) ∂μ := by
    intro A B w y
    rw [coef, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [schr, AddChar.map_add_eq_mul]
    ring
  have key := eq_zero hψ μ ((hcont h₁ h₂ (x - u)).sub (hcont k₁ k₂ (x - u)))
    ((hint h₁ h₂ (x - u)).sub (hint k₁ k₂ (x - u))) fun y => by
      have h3 := congrFun hco (x - u, y)
      rw [hcoef, hcoef] at h3
      have h4 := mul_left_cancel₀ (hne _) h3
      simp only [Pi.sub_apply, mul_sub]
      rw [integral_sub (hint' h₁ h₂ _ y) (hint' k₁ k₂ _ y), h4, sub_self]
  have h5 := congrFun key u
  simp only [Pi.sub_apply, add_sub_cancel, Pi.zero_apply] at h5
  exact sub_eq_zero.1 h5

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sum_pos_lam {n d q y : ℕ} {lam : Fin n → (Fin q → ℝ) →ₗ[ℝ] ℝ} {ix iy : Fin q ↪ Fin n} (h1 : ∀ i j, ix i ≠ iy j)
    (h2 : ∀ i t, lam (ix i) t = t i ∧ lam (iy i) t = -t i) (h3 : ∀ k, (∀ i, ix i ≠ k ∧ iy i ≠ k) → lam k = 0)
    {lam' : Fin d → (Fin y → ℝ) →ₗ[ℝ] ℝ} {jx jy : Fin y ↪ Fin d} (h1' : ∀ i j, jx i ≠ jy j)
    (h2' : ∀ i t, lam' (jx i) t = t i ∧ lam' (jy i) t = -t i) (h3' : ∀ k, (∀ i, jx i ≠ k ∧ jy i ≠ k) → lam' k = 0)
    {s : Fin q → ℝ} {t : Fin y → ℝ} (hs : s ∈ Cone q) (ht : t ∈ Cone y) :
    ∑ k, ∑ l, max 0 (lam k s + lam' l t) = posWt n d s t := by
  let G : ℝ → ℝ := fun u => ∑ l, max 0 (u + lam' l t)
  have hG : ∀ u, G u = ∑ j, max 0 (u + t j) + ∑ j, max 0 (u + -t j) + ((d : ℝ) - 2 * y) * max 0 (u + 0) := fun u =>
    sum_lam h1' h2' h3' (fun v => max 0 (u + v)) t
  have h0 : G 0 = ∑ j, t j := by
    rw [hG]
    have a : ∀ j, max 0 (0 + t j) = t j := fun j => by rw [zero_add, max_eq_right (ht.2 j)]
    have b : ∀ j, max 0 (0 + -t j) = 0 := fun j => by rw [zero_add, max_eq_left (by linarith [ht.2 j])]
    simp only [a, b]
    simp
  have hs' : ∀ i, G (s i) + G (-s i) = ∑ j, 2 * max (s i) (t j) + ((d : ℝ) - 2 * y) * s i := by
    intro i
    have a : ∀ j, 2 * max (s i) (t j) =
        max 0 (s i + t j) + max 0 (s i + -t j) + (max 0 (-s i + t j) + max 0 (-s i + -t j)) := by
      intro j
      have := hs.2 i
      have := ht.2 j
      simp only [max_def]
      split_ifs <;> linarith
    rw [hG, hG, add_zero, add_zero, max_eq_right (hs.2 i), max_eq_left (by linarith [hs.2 i] : -s i ≤ 0)]
    simp only [a, Finset.sum_add_distrib]
    ring
  have := sum_lam h1 h2 h3 G s
  rw [← Finset.sum_add_distrib, h0] at this
  simp only [hs', Finset.sum_add_distrib, ← Finset.mul_sum] at this
  refine this.trans ?_
  simp only [posWt, ← Finset.mul_sum]

theorem tsum_fin_prod {α : Type} (q : ℕ) (φ : Fin q → α → ℝ≥0∞) :
    ∑' x : Fin q → α, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← (Fin.consEquiv fun _ : Fin (q + 1) => α).tsum_eq, ENNReal.tsum_prod', Fin.prod_univ_succ, ← ih,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [Fin.prod_univ_succ]
    rfl

theorem tsum_fun_prod {ι α : Type} [Fintype ι] (φ : ι → α → ℝ≥0∞) :
    ∑' x : ι → α, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  let e := (Fintype.equivFin ι).symm
  rw [← e.prod_comp, ← tsum_fin_prod, ← (e.arrowCongr (Equiv.refl α)).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [← e.prod_comp]
  simp

def oneMaj (τ : ∀ w : InfinitePlace F, EmbOver E w) (m N : ℕ) (ν : ℝ) : E → ℝ≥0∞ :=
  Set.indicator {x | IsIntegral ℤ ((m : E) * x)} fun x =>
    ENNReal.ofReal (((1 + Real.exp (-ν) * ∑ w, ‖(τ w).1 x‖) ^ N)⁻¹)

theorem tsum_oneMaj (hO : OneVar) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ≥0, ∀ ν, ∑' x, oneMaj τ m (Module.finrank ℚ E + 1) ν x ≤
      K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * max 0 ν)) := by
  classical
  obtain ⟨K, hK⟩ := hO (mixedEmbedding.mixedSpace E) (mixedEmbedding.integerLattice E) (Module.finrank ℚ E + 1)
    (by rw [mixedEmbedding.finrank]; omega)
  rw [mixedEmbedding.finrank] at hK
  set N := Module.finrank ℚ E + 1
  refine ⟨(m : ℝ≥0) ^ N * K, fun ν => ?_⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let i : {x : E | IsIntegral ℤ ((m : E) * x)} → mixedEmbedding.integerLattice E := fun x =>
    ⟨mixedEmbedding E (m * x.1), ⟨⟨_, x.2⟩, rfl⟩⟩
  have hi : Function.Injective i := fun x y hxy => by
    have := (mixedEmbedding E).injective (congrArg Subtype.val hxy)
    exact Subtype.ext (mul_left_cancel₀ (by exact_mod_cast hm.ne') this)
  have hn : ∀ x : E, ‖mixedEmbedding E x‖ ≤ ∑ w, ‖(τ w).1 x‖ := by
    intro x
    rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun v _ => ?_
    obtain ⟨w, hw⟩ := norm_emb h τ v.embedding
    rw [mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_eq, hw]
    exact Finset.single_le_sum (f := fun w => ‖(τ w).1 x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  rw [oneMaj, ← tsum_subtype]
  calc _ ≤ ∑' x : {x : E | IsIntegral ℤ ((m : E) * x)}, ((m : ℝ≥0) ^ N : ℝ≥0) *
          ENNReal.ofReal (((1 + Real.exp (-ν) * ‖(i x : mixedEmbedding.mixedSpace E)‖) ^ N)⁻¹) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hS : 0 ≤ ∑ w, ‖(τ w).1 x.1‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have h1 : ‖(i x : mixedEmbedding.mixedSpace E)‖ ≤ m * ∑ w, ‖(τ w).1 x.1‖ := by
          refine (hn _).trans (le_of_eq ?_)
          simp [Finset.mul_sum]
        have h2 : 1 + Real.exp (-ν) * ‖(i x : mixedEmbedding.mixedSpace E)‖ ≤
            m * (1 + Real.exp (-ν) * ∑ w, ‖(τ w).1 x.1‖) := by
          have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-ν)).le
          linarith
        have h3 := pow_le_pow_left₀ (by positivity) h2 N
        rw [mul_pow] at h3
        push_cast
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
        exact h3.trans_eq (mul_comm _ _)
    _ ≤ ((m : ℝ≥0) ^ N : ℝ≥0) * (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * max 0 ν))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi _).trans (hK ν)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]

theorem latTor_of : FrameBasis → OneVar → LatTor := by
  intro hB hO F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  classical
  obtain ⟨b, lam, ix, iy, h1, h2, h3, -, hb⟩ := hB F E σ hσ n J hJ fr hfr
  obtain ⟨b', lam', jx, jy, h1', h2', h3', -, hb'⟩ := hB F E σ hσ d J' hJ' fr' hfr'
  set N₀ := Module.finrank ℚ E + 1 with hN₀
  set c := Fintype.card (Fin n × Fin d) with hc
  refine ⟨N₀ * c, fun C hC => ?_⟩
  obtain ⟨m, K, hm, hK, h⟩ := diag_coords τ hfr hfr' hb hb' hC
  obtain ⟨K₁, hK₁⟩ := tsum_oneMaj hO hσ τ hm
  refine ⟨K.toNNReal ^ (N₀ * c) * K₁ ^ c, fun s hs t ht => ?_⟩
  let i : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → (Fin n × Fin d → E) := fun x p =>
    ((b⁻¹).1 * x.1 * (b'⁻¹).1ᵀ) p.1 p.2
  have hi : Function.Injective i := fun x y hxy => by
    have e : (b⁻¹).1 * x.1 * (b'⁻¹).1ᵀ = (b⁻¹).1 * y.1 * (b'⁻¹).1ᵀ := by
      ext k l
      exact congrFun hxy (k, l)
    have e' : ∀ z : Matrix (Fin n) (Fin d) E, b.1 * ((b⁻¹).1 * z * (b'⁻¹).1ᵀ) * b'.1ᵀ = z := by
      intro z
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]
    exact Subtype.ext (by rw [← e' x.1, e, e'])
  let g : (Fin n × Fin d → E) → ℝ≥0∞ := fun ξ => ∏ p, oneMaj τ m N₀ (lam p.1 s + lam' p.2 t) (ξ p)
  calc _ ≤ ∑' x, (K.toNNReal ^ (N₀ * c) : ℝ≥0) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        obtain ⟨ha, hb⟩ := h s t x.1
        unfold maj
        split_ifs with hx
        swap
        · simp
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        set z := sz τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        let A : Fin n × Fin d → ℝ := fun p => Real.exp (-(lam p.1 s + lam' p.2 t)) * ∑ w, ‖(τ w).1 (i x p)‖
        have hA0 : ∀ p, 0 ≤ A p := fun p => by positivity
        have hA : ∀ p, 1 + A p ≤ K * (1 + z) := fun p => by
          have : ∑ p, A p ≤ K * z := by
            refine le_trans (le_of_eq ?_) hb
            rw [Fintype.sum_prod_type, Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace F)))]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace F)))]
            exact Finset.sum_congr rfl fun l _ => Finset.mul_sum _ _ _
          have h4 := Finset.single_le_sum (f := A) (fun p _ => hA0 p) (Finset.mem_univ p)
          linarith
        have hg : g (i x) = ENNReal.ofReal (∏ p, (1 + A p) ^ N₀)⁻¹ := by
          rw [← Finset.prod_inv_distrib, ENNReal.ofReal_prod_of_nonneg fun p _ => by have := hA0 p; positivity]
          exact Finset.prod_congr rfl fun p _ =>
            Set.indicator_of_mem (s := {x | IsIntegral ℤ ((m : E) * x)}) (a := i x p) (ha hx p.1 p.2) _
        have h5 : ∏ p, (1 + A p) ^ N₀ ≤ (K * (1 + z)) ^ (N₀ * c) := by
          rw [pow_mul, hc, ← Finset.card_univ, ← Finset.prod_const]
          exact Finset.prod_le_prod₀ (fun p _ => by have := hA0 p; positivity)
            fun p _ => pow_le_pow_left₀ (by have := hA0 p; positivity) (hA p) _
        have h6 : 0 < ∏ p, (1 + A p) ^ N₀ := Finset.prod_pos fun p _ => by have := hA0 p; positivity
        rw [hg, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        rw [Real.coe_toNNReal _ (by linarith), ← div_eq_mul_inv, le_div_iff₀ h6, inv_mul_le_iff₀ (by positivity),
          ← mul_pow]
        exact h5.trans_eq (by rw [mul_comm K])
    _ ≤ (K.toNNReal ^ (N₀ * c) : ℝ≥0) * ∏ p : Fin n × Fin d, (K₁ * ENNReal.ofReal
          (Real.exp (Module.finrank ℚ E * max 0 (lam p.1 s + lam' p.2 t)))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        refine (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans ?_
        rw [tsum_fun_prod]
        exact Finset.prod_le_prod' fun p _ => hK₁ _
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hc,
          ← ENNReal.ofReal_prod_of_nonneg fun p _ => (Real.exp_pos _).le, ← Real.exp_sum, ← Finset.mul_sum,
          Fintype.sum_prod_type, sum_pos_lam h1 h2 h3 h1' h2' h3' hs ht]
        push_cast
        rw [mul_assoc]

end PositivityTheory.ThKEst

end
end
