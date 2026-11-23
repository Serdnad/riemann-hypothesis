module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle081
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle047
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle007
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.NoMonodromy

variable {a g : ℕ}

theorem map_mulVec_real (M : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    M.map (fun x : ℤ => (x : ℝ)) *ᵥ (fun k => (v k : ℝ)) = fun k => ((M *ᵥ v) k : ℝ) := by
  funext k
  simp [mulVec, dotProduct]

theorem ker_each (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ)
    (hv : (∑ j, B j) *ᵥ v = 0) (j : Fin a) : B j *ᵥ v = 0 := by
  set r : Fin g → ℝ := fun k => (v k : ℝ) with hr
  have hsum : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have h1 : (∑ j, (B j).map (fun x : ℤ => (x : ℝ))) *ᵥ r = 0 := by
    rw [← hsum, hr, map_mulVec_real, hv]
    funext k
    simp
  have h0 : r ⬝ᵥ ((∑ j, (B j).map (fun x : ℤ => (x : ℝ))) *ᵥ r) = 0 := by
    rw [h1]; simp
  rw [Matrix.sum_mulVec, dotProduct_sum] at h0
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ r ⬝ᵥ ((B i).map (fun x : ℤ => (x : ℝ)) *ᵥ r) := by
    intro i _
    simpa using (hB i).dotProduct_mulVec_nonneg r
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
  have h3 : (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ r = 0 :=
    ((hB j).dotProduct_mulVec_zero_iff).1 (by simpa using h2)
  rw [hr, map_mulVec_real] at h3
  funext k
  have := congrFun h3 k
  simpa using this

theorem vec_eq_sum (t : Fin g → ℂ) : t = ∑ i, t i • cst (Pi.single i 1 : Fin g → ℤ) := by
  funext k
  simp [cst, Finset.sum_apply, Pi.single_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.NoMonodromy

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

open NoMonodromy

theorem noMonodromy_lattice : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (k : ℤ), k ≠ 0 → k • x ∈ chartW bas B → x ∈ chartW bas B) ∧ (∀ x ∈ chartW bas B, ContinuousAt (chartS bas A T0 x) 0 ∧ ∀ w ∈ logCover L.a_le, chartS bas A T0 x (expCover a w) = L.P w x) ∧ Function.Injective (chartPer bas A T0 B) ∧ Submodule.span ℂ (Set.range (chartPer bas A T0 B)) = ⊤ := by
  intro n a g Λ _ L bas A T0 B c ρ h
  have hmem : ∀ x, x ∈ chartW bas B ↔ (∑ j, B j) *ᵥ vCo bas x = 0 := fun x => by
    rw [chartW, LinearMap.mem_ker]
    rfl
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hA0 : ContinuousAt A 0 := h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hT0 : ContinuousAt T0 0 := h.T_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hunit : IsUnit ((A 0)ᵀ).det := Ne.isUnit (by rw [det_transpose]; exact h.A_det)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x k hk hx
    rw [hmem] at hx ⊢
    rw [map_zsmul, Matrix.mulVec_smul] at hx
    exact (smul_eq_zero.1 hx).resolve_left hk
  · intro x hx
    have hxv := (hmem x).1 hx
    refine ⟨?_, fun w hw => ?_⟩
    · have hcts : Continuous (fun p : Matrix (Fin g) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ =>
          p.1ᵀ *ᵥ (cst (uCo bas x) + p.2 *ᵥ cst (vCo bas x))) :=
        (continuous_fst.matrix_transpose).matrix_mulVec
          (continuous_const.add (continuous_snd.matrix_mulVec continuous_const))
      exact ContinuousAt.comp (f := fun z => (A z, T0 z)) hcts.continuousAt (hA0.prodMk hT0)
    · rw [h.per w hw x]
      simp only [chartS, tauAt]
      have hz : (∑ j, (w (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
          (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ cst (vCo bas x) = 0 := by
        rw [Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Matrix.smul_mulVec, cst_mulVec, ker_each B h.B_psd _ hxv j, cst_zero, smul_zero]
      rw [Matrix.add_mulVec, hz, add_zero]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hxv := (hmem _).1 x.2
    set u := uCo bas (x : Λ) with hu
    set v := vCo bas (x : Λ) with hv
    have hS : (A 0)ᵀ *ᵥ (cst u + T0 0 *ᵥ cst v) = 0 := hx
    have hy : cst u + T0 0 *ᵥ cst v = 0 := by
      have := congrArg (fun y => ((A 0)ᵀ)⁻¹ *ᵥ y) hS
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit] using this
    set r : Fin g → ℝ := fun k => (v k : ℝ) with hr
    have him : ((T0 0).map Complex.im) *ᵥ r = 0 := by
      funext i
      have h1 := congrArg Complex.im (congrFun hy i)
      simpa [cst, mulVec, dotProduct, hr] using h1
    have hlow := GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
      Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball h.ρ_le)) h.B_psd h.c_pos h.im_lower 0
      (Metric.mem_ball_self h.ρ_pos) 0 (fun j hj => absurd rfl hj) (fun _ _ => rfl) r
      (fun j _ => by
        rw [hr, map_mulVec_real, ker_each B h.B_psd _ hxv j]
        funext k
        simp)
    simp only [Pi.zero_apply, zero_div, zero_smul, Finset.sum_const_zero, add_zero] at hlow
    rw [him, dotProduct_zero] at hlow
    have hrr : r ⬝ᵥ r ≤ 0 := by
      by_contra hcon
      exact absurd hlow (not_le.2 (mul_pos h.c_pos (not_le.1 hcon)))
    have hr0 : r = 0 := by
      refine dotProduct_self_eq_zero.1 (le_antisymm hrr ?_)
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hv0 : v = 0 := by
      funext k
      have := congrFun hr0 k
      simpa [hr] using this
    have hu0 : u = 0 := by
      rw [hv0, cst_zero, mulVec_zero, add_zero] at hy
      funext k
      have := congrFun hy k
      simpa [cst] using this
    refine Subtype.ext (eq_of_coords bas ?_ ?_)
    · rw [← hu, hu0]; simp
    · rw [← hv, hv0]; simp
  · rw [eq_top_iff]
    intro y _
    set t : Fin g → ℂ := ((A 0)ᵀ)⁻¹ *ᵥ y with ht
    have hyt : y = (A 0)ᵀ *ᵥ t := by
      rw [ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    have hper : ∀ i, (A 0)ᵀ *ᵥ cst (Pi.single i 1 : Fin g → ℤ) ∈
        Submodule.span ℂ (Set.range (chartPer bas A T0 B)) := by
      intro i
      refine Submodule.subset_span ⟨⟨mk bas (Pi.single i 1) 0, ?_⟩, ?_⟩
      · rw [hmem, vCo_mk]; simp
      · change chartS bas A T0 (mk bas (Pi.single i 1) 0) 0 = _
        simp only [chartS, uCo_mk, vCo_mk, cst_zero, mulVec_zero, add_zero]
    rw [hyt, vec_eq_sum t, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (hper i)

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.global_regularization_statement_holds : RegGlobalStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def proj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k × ι k) → ℂ :=
  fun q => z ⟨q.1, q.2.1⟩ * starRingEnd ℂ (z ⟨q.1, q.2.2⟩) / ((∑ i, ‖z ⟨q.1, i⟩‖ ^ 2 : ℝ) : ℂ)

def Pts (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Set ((Σ k, ι k × ι k) → ℂ) :=
  proj '' conePts P

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

def rep (x : Pts P) : (Σ k, ι k) → ℂ := x.2.choose

theorem rep_mem (x : Pts P) : rep x ∈ conePts P := x.2.choose_spec.1

theorem proj_rep (x : Pts P) : proj (rep x) = x.1 := x.2.choose_spec.2


variable (P) in
def src (p : (k : K) → ι k) : Set (Pts P) := {x | ∀ k, rep x ⟨k, p k⟩ ≠ 0}


variable (P) in
def coord (p : (k : K) → ι k) (x : Pts P) : Fin (Fintype.card (Σ k, ι k)) → ℂ :=
  renPt (affCoord p (rep x))


variable (P) in
def ideal (p : (k : K) → ι k) : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  (chartIdeal P p).map (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)


open Classical in
def lift (p : (k : K) → ι k) (q : Σ k, ι k) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  if q.2 = p q.1 then 1 else X (Fintype.equivFin (Σ k, ι k) q)


variable (P) in
def bd (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  ((chartIdeal (P ⊔ D) p).map (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)).radical

theorem finite_minimalPrimes (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : I.minimalPrimes.Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing _ I


variable (P) in
def rc (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : ℕ := (finite_minimalPrimes (P ⊔ D)).toFinset.card


variable (P) in
def compIdeal (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  ((finite_minimalPrimes (P ⊔ D)).toFinset.equivFin.symm k).1


variable (P) in
def comp (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) : Set (Pts P) :=
  {x | ∀ f ∈ compIdeal P D k, eval (rep x) f = 0}

def ordAlong (Q P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (f : MvPolynomial (Σ k, ι k) ℂ) : ℕ :=
  sSup {m : ℕ | ∃ s ∉ Q, s * f ∈ Q ^ m ⊔ P}

theorem compIdeal_mem (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) :
    compIdeal P D k ∈ (P ⊔ D).minimalPrimes := by
  exact (Set.Finite.mem_toFinset _).1 ((finite_minimalPrimes (P ⊔ D)).toFinset.equivFin.symm k).2

theorem eval_lift (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) (q : Σ k, ι k) :
    eval (coord P p x) (lift p q) = affCoord p (rep x) q := by
  classical
  unfold lift
  split_ifs with h
  · obtain ⟨k, i⟩ := q
    simp only at h
    subst h
    simp [affCoord, hx k]
  · simp [coord, renPt]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
end
end

section

set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem sum_log_unit_mul_mass_eq_zero : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (θ : (𝓞 F)ˣ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = 0 := by
  intro hSys hInt K _ ι _ Ω _ F _ _ _ y D L θ hP hbir hL hex
  classical
  obtain ⟨II, hII, -⟩ := hSys
  obtain ⟨x, hx⟩ : ∃ x : F, x = ((θ : 𝓞 F) : F) := ⟨_, rfl⟩
  have hmul : ((((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) * x = 1 := by
    rw [hx]
    have h1 : (((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (θ : 𝓞 F)) = 1 := by simp
    exact_mod_cast congrArg (fun u : 𝓞 F => (u : F)) h1
  have hxinv : ((((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) = x⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact zero_ne_one hmul
  have hxI : IsIntegral ℤ x := hx ▸ RingOfIntegers.isIntegral_coe (θ : 𝓞 F)
  have hxI' : IsIntegral ℤ x⁻¹ := hxinv ▸ RingOfIntegers.isIntegral_coe ((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  rw [← hx]
  have ht0 : algebraMap F Ω x ≠ 0 := (map_ne_zero _).mpr hx0
  have htI : IsIntegral ℤ (algebraMap F Ω x) := hxI.map (algebraMap F Ω).toIntAlgHom
  have htI' : IsIntegral ℤ (algebraMap F Ω x)⁻¹ := by
    rw [← map_inv₀]
    exact hxI'.map (algebraMap F Ω).toIntAlgHom
  obtain ⟨d, f, g, hf, hg, hg0, hfg⟩ := hbir (algebraMap F Ω x)
  have hf0 : aeval y f ≠ 0 := by
    rw [hfg]
    exact mul_ne_zero ht0 hg0
  have hgP : g ∉ mCoordIdeal y := fun h => hg0
    ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hg).mp h)
  have hfP : f ∉ mCoordIdeal y := fun h => hf0
    ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).mp h)
  obtain ⟨B, hB0, hBs, hBl⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun sg => ‖sg x‖) (fun sg => norm_pos_iff.mpr ((map_ne_zero sg).mpr hx0)) hex
  obtain ⟨A, hAa, hA⟩ : ∃ A : HermLine ι, (∀ k, A.a k = d k) ∧ IsSmoothHerm A :=
    ⟨HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (d k : ℤ)), fun _ => rfl,
      GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs _⟩
  have hAB : IsSmoothHerm (A.tensor B) := ContDiffOn.mul hA hBs
  have hABa : ∀ k, (A.tensor B).a k = d k := fun k => by
    simp [HermLine.tensor, hB0, hAa k]
  have hRA := (hII K ι).2.2 (mCoordIdeal y) D L A g d hP hL hA hAa hg hgP
  have hRB := (hII K ι).2.2 (mCoordIdeal y) D L (A.tensor B) f d hP hL hAB hABa hf hfP
  have hadd := (hII K ι).2.1 (mCoordIdeal y) D L A B hP hL hA hBs
  obtain ⟨hsupp, hmult⟩ := GlobalTheory.T.unit_ratio_divisor_support_eq K ι Ω y D d f g (algebraMap F Ω x) hP hf hg hg0 ht0 htI htI' hfg
  have hlog : ∀ z ∈ mcPts (mCoordIdeal y), logNorm (A.tensor B) f z = logNorm A g z := by
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    have hval : B.h z = ‖sg x‖ := (hBl z hz sg hsg).self_of_nhds
    have hfz := hsg d f g x hf hg hfg
    have hs0 : ‖sg x‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero sg).mpr hx0)
    have hAz : A.h z ≠ 0 := (A.pos z hz.1).ne'
    unfold logNorm
    congr 1
    show ‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * B.h z) = _
    rw [hfz, hval, norm_mul]
    field_simp
  have hrec : recR (II K ι) (mCoordIdeal y) L (A.tensor B) f = recR (II K ι) (mCoordIdeal y) L A g := by
    unfold recR
    rw [hsupp]
    congr 1
    · exact finsum_mem_congr rfl fun W hW => by rw [hmult W hW]
    · exact GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) hlog
  rw [← intersection_locConst_trivial hInt K ι Ω F y D L B (fun sg => ‖sg x‖) II hII hP hL hB0 hBs hex hBl]
  linarith [hRA, hRB, hadd, hrec]

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Slots
variable {X : Type} [TopologicalSpace X] {e : ℕ}

def positionPot (th Pn : LocPot X) (f : X → ℝ) (i : ℕ) : Fin e → LocPot X :=
  fun j => (if (j : ℕ) < i then th else Pn) + LocPot.ofFun (if (j : ℕ) < i then f else fun _ => 0)

end Slots

section Lines
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W}

def muVert (Hd : HodgeData D) (B : ℕ) : HermLine J :=
  hermOfFun J (muTwDeg Hd B) fun z => (muLine Hd).h z * ∏ p ∈ D.SB B, D.vertFactor p z

def limTop (Hd : HodgeData D) (B : ℕ) (Nb : HermLine J) : ℝ :=
  II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) -
    ∑ i ∈ Finset.range (D.n + 1), ptsIntegral (mCoordIdeal D.y)
      (pot fun j : Fin D.n => if (j : ℕ) < i then muVert Hd B else Nb)
      (fun z => Real.log (Nb.h z) - Real.log ((muVert Hd B).h z))

end Lines
end GlobalTheory.CompanionTheory.Ar.Cusp
end
end
