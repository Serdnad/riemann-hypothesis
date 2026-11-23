module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle714
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle718
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle229
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle740
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle239
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle748
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle708
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle723
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle698
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle702
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle745
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle749
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle721
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle039
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ShFam.Hor.LogCh.exists_periodChart_of_latFam : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ d : ℝ), 0 < ρ ∧ ρ ≤ 1 ∧ 0 < d ∧ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ρ⁻¹ • logExp a s))⁻¹ := by
  intro n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor
  obtain ⟨rk, d, ρ, P, τ, B, Δ, hρ, hρ1, hd, hrk, hP, hPdet, hτd, hτs, hτm, hB, hPH, hΔc, hΔp, hτΔ, hcl⟩ :=
    GlobalTheory.T.exists_periodFrame_of_holomorphicLatticeFamily n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor
  obtain ⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩ := GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef n a g ha ρ τ B hρ hρ1 hτd hτs hτm
  have hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 ρ) := fun j l => (hτ₀d j l).continuousOn
  have hmv : ∀ (k : Fin a) (v : Fin g → ℤ), ((B k).map (Int.cast : ℤ → ℂ)).mulVec (fun j => (v j : ℂ)) =
      fun i => (((B k).mulVec v i : ℤ) : ℂ) := by
    intro k v; ext i; simp [Matrix.mulVec, dotProduct]
  have htoric : (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix
      (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef := by
    by_contra hnot
    obtain ⟨v, hv0, hvs, hBv⟩ := GlobalTheory.T.exists_common_int_kernel_psd_block_not_posDef a g rk B hpsd hB hnot
    refine hcl v hv0 hvs (fun z => (τ₀ z).mulVec (fun j => (v j : ℂ))) ?_ ?_
    · refine continuousOn_pi.2 fun j => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact continuousOn_finsetSum _ fun l _ => (hcont j l).mul continuousOn_const
    · intro s hs hz
      rw [hτ₀e s hs hz, Matrix.add_mulVec]
      have h0 : (∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)).mulVec
          (fun j => (v j : ℂ)) = 0 := by
        rw [Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Matrix.smul_mulVec, hmv, hBv k]
        ext i; simp
      rw [h0, add_zero]
  have hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ →
      (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val = Δ (logExp a s) := by
    intro s hs hz
    rw [← hτΔ s hs hz, hτ₀e s hs hz]
    ext ⟨j, hj⟩ ⟨l, hl⟩
    simp [Matrix.sum_apply, hB _ j l (Or.inl hj)]
  have heq := GlobalTheory.T.eqOn_ball_of_eqOn_punctPolydiscCoveringExp_image n a ρ _
    (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val) Δ hρ1
    (continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1) hΔc hagree
  have habel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix
      (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef := by
    intro z hz
    have h1 := hΔp z hz
    rw [← heq z hz] at h1
    exact h1
  obtain ⟨hPC, hY⟩ := GlobalTheory.T.periodChart_rescale_ball_to_unitPolydisc n a g rk ha ρ τ₀ B hρ hρ1 hrk hτ₀d hτ₀s hpsd hB htoric habel
  refine ⟨rk, _, B, P, ρ, d, hρ, hρ1, hd, hPC, hP, hPdet, ?_⟩
  intro s hs hz Hm hHm
  have hnz : ∀ i : Fin a, logExp a s (Fin.castLE ha i) ≠ 0 := by
    intro i
    simp only [logExp, Fin.coe_castLE, i.isLt, if_true]
    exact Complex.exp_ne_zero _
  rw [hPH s hs hz Hm hHm, hY _ hnz]
  congr 2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram
  congr 1
  rw [← GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period ha τ₀ B (logExp a s) (fun k => s (Fin.castLE ha k)) ?_]
  · rw [hτ₀e s hs hz]; rfl
  · intro i
    simp only [logExp, Fin.coe_castLE, i.isLt, if_true]
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped Matrix ComplexOrder ContDiff

namespace GlobalTheory.GoodMetric

variable {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ}

theorem eventually_regAt_under {y : CxPts X.str σ} {g : X.Fn} (hg : RegAt (under y) g) :
    ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
  exact regAt_fnOf (mem_ptsIn.1 hz) _ a

theorem eventually_mem_frames {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ}
    {A : Mat m X.Fn} (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_regAt_under (mem_O_ratOf.1 ((hP τ).1 i j))).and (eventually_regAt_under (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem CInfAt.contDiffAt_holoChart {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ} (h : CInfAt f y)
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hy : y ∈ e.source) :
    ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  obtain ⟨W, κ, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have ho := isOpen_over e (isOpen_ptsIn (p := X.str) (σ := σ) W)
  have hl := e.left_inv hy
  have hg : ContDiffAt ℝ ∞ (fun w a => ev X.str σ W (g a) (e.symm w)) (e y) :=
    contDiffAt_pi.2 fun a => (contDiffOn_real ho (he W (g a))).contDiffAt (ho.mem_nhds (mem_over e hy h₁))
  have h₆ : ContDiffAt ℝ ∞ G (fun a => ev X.str σ W (g a) (e.symm (e y))) := by
    rw [hl]; exact h₄.contDiffAt (h₂.mem_nhds h₃)
  refine (h₆.comp (e y) hg).congr_of_eventuallyEq ?_
  have := e.continuousAt_symm (e.map_source hy)
  rw [ContinuousAt, hl] at this
  exact this.eventually h₅

theorem IsMetricOn.mContDiffAt_two {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0} {O : X.X.Opens}
    {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ} (hH : IsMetricOn E O H) {y : CxPts X.str σ}
    (hy : y ∈ ptsIn X.str σ O) {A : Mat m X.Fn} (hA : A ∈ E.S (under y))
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hye : y ∈ e.source) (τ : ι) :
    MContDiffAt 2 (fun v => H A (e.symm v) τ) (e y) := fun i j => by
  obtain ⟨hre, him⟩ := hH.smooth y hy A hA τ i j
  have h1 : ContDiffAt ℝ 2 (fun v => (H A (e.symm v) τ i j).re) (e y) :=
    (CInfAt.contDiffAt_holoChart hre he hye).of_le (by norm_cast)
  have h2 : ContDiffAt ℝ 2 (fun v => (H A (e.symm v) τ i j).im) (e y) :=
    (CInfAt.contDiffAt_holoChart him he hye).of_le (by norm_cast)
  have h3 : ContDiffAt ℝ 2 (fun v => ((H A (e.symm v) τ i j).re : ℂ) + ((H A (e.symm v) τ i j).im : ℂ) * Complex.I) (e y) :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp _ h1).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ h2).mul contDiffAt_const)
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  exact (Complex.re_add_im _).symm

theorem curvPoly_polyRep {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {E : Fr (ratOf X) m 0}
    {O : X.X.Opens} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}
    {H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ} (hH : IsMetricOn E O H)
    (hρ : ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y))
    {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O) {A : Mat m X.Fn} (hA : A ∈ E.S (under y))
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) (hye : y ∈ e.source) :
    curvPoly (fun v => H' (fun _ => ρ.ev A) (e.symm v) ()) (e y) =
      ρ.lie (fun τ => curvPoly (fun v => H A (e.symm v) τ) (e y)) := by
  have hG2 : ∀ τ, MContDiffAt 2 (fun v => H A (e.symm v) τ) (e y) := hH.mContDiffAt_two hy hA he hye
  have hdet : ∀ τ, (H A (e.symm (e y)) τ).det ≠ 0 := fun τ => by
    rw [e.left_inv hye]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef y hy A hA τ).isUnit).ne_zero
  obtain ⟨-, hc⟩ := GlobalTheory.T.chernConnection_curvature_polyRep_eval ι m ρ X.dim (fun v => H A (e.symm v)) (e y) hG2 hdet
  rw [← hc]
  have ht : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have := e.continuousAt_symm (e.map_source hye)
    rwa [ContinuousAt, e.left_inv hye] at this
  have heq : (fun v => H' (fun _ => ρ.ev A) (e.symm v) ()) =ᶠ[𝓝 (e y)] fun v => ρ.ev (H A (e.symm v)) := by
    filter_upwards [ht.eventually ((isOpen_ptsIn O).mem_nhds hy), ht.eventually (eventually_mem_frames hA)] with v h1 h2
    exact hρ _ h1 A h2
  simp only [curvPoly, curv_congr heq]

end GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.Bridge

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.GoodMetric.isGood_polyRep : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (ρ : PolyRep m) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf X) (fun _ : Unit => ρ.M) 0) (O : X.X.Opens)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ),
    (∀ z, ∀ A ∈ E.S z, (fun _ : Unit => ρ.ev A) ∈ E'.S z) → IsMetricOn E O H →
      (∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y)) →
        IsGood E O H → IsGood E' O H' := by
  intro F _ σ X ι _ m ρ E E' O H H' hS hH hρ hG y hy
  obtain ⟨e, S, he, hye, hS0, hSO, A, hA, c, N, hev⟩ := hG y hy
  obtain ⟨c', N', hgood⟩ := GlobalTheory.T.mumfordGoodGrowth_polynomialRepresentation ι m ρ c N
  refine ⟨e, S, he, hye, hS0, hSO, fun _ => ρ.ev A, hS _ A hA, c', N', ?_⟩
  obtain ⟨a₀, ha₀S, ha₀⟩ := (hSO y hye).1 hy
  have hcont : ContinuousAt (fun z => e z a₀) y :=
    (EuclideanSpace.proj (𝕜 := ℂ) a₀).continuous.continuousAt.comp (e.continuousAt hye)
  have hsmall : ∀ᶠ z in 𝓝 y, ‖e z a₀‖ < Real.exp (-1) := by
    have h0 : Tendsto (fun z => e z a₀) (𝓝 y) (𝓝 0) := by
      have := hcont.tendsto
      rwa [ha₀] at this
    exact h0.norm.eventually (gt_mem_nhds (by rw [norm_zero]; positivity))
  filter_upwards [hev, self_mem_nhdsWithin, nhdsWithin_le_nhds (e.open_source.mem_nhds hye),
    nhdsWithin_le_nhds (eventually_mem_frames hA), nhdsWithin_le_nhds hsmall] with z hz hzO hzs hzA hzsm
  rintro ⟨⟩
  have hz2 : ∀ τ, MContDiffAt 2 (fun v => H A (e.symm v) τ) (e z) := hH.mContDiffAt_two hzO hzA he hzs
  have hdet : ∀ τ, (H A (e.symm (e z)) τ).det ≠ 0 := fun τ => by
    rw [e.left_inv hzs]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef z hzO A hzA τ).isUnit).ne_zero
  have hne : e z a₀ ≠ 0 := fun h0 => ((hSO z hzs).2 ⟨a₀, ha₀S, h0⟩) hzO
  have hpos : 0 < ‖e z a₀‖ := norm_pos_iff.2 hne
  have hlt : Real.log ‖e z a₀‖ < -1 := by rw [Real.log_lt_iff_lt_exp hpos]; exact hzsm
  have h1 : 1 ≤ |Real.log ‖e z a₀‖| := by rw [abs_of_neg (by linarith)]; linarith
  have hlog : 1 ≤ ∑ a ∈ S, |Real.log ‖e z a‖| :=
    h1.trans (Finset.single_le_sum (f := fun a => |Real.log ‖e z a‖|) (fun a _ => abs_nonneg _) ha₀S)
  have hb := hgood X.dim S (fun v => H A (e.symm v)) (e z) hz2 hdet hlog hz
  refine goodBound_congr_nhds X.dim (Fin ρ.M) S c' N' _ _ (e z) ?_ hb
  have ht : Tendsto e.symm (𝓝 (e z)) (𝓝 z) := by
    have := e.continuousAt_symm (e.map_source hzs)
    rwa [ContinuousAt, e.left_inv hzs] at this
  filter_upwards [ht.eventually ((isOpen_ptsIn O).mem_nhds hzO), ht.eventually (eventually_mem_frames hzA)]
    with v h1 h2
  exact (hρ _ h1 A h2).symm

theorem _root_.GlobalTheory.GoodMetric.goodChernWeil_of_goodTopChernForm :
    GlobalTheory.Published.GoodTopChernForm → GlobalTheory.Published.ChernWeilNumbers → GlobalTheory.Published.FlagPushForward → GlobalTheory.Published.GoodChernWeil := by
  intro hT hCW hP
  refine ⟨?_, hP⟩
  intro F _ σ X Y ι _ m E E' φ f gr hRef hGr O H hH hG R
  obtain ⟨J, _, ρ, a, hAlg⟩ := GlobalTheory.T.topDegreeFormCoeff_chernPoly_eq_sum_representations ι m X.dim R
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.exists_smooth_hermitianMetric_projective_variety F σ X ι m E
  choose Eb hEbS hEbH using fun j => GlobalTheory.T.exists_polyRep_inducedBundle_and_metric F X ι m (ρ j) E
  choose H' hH' hH'eq using fun j => hEbH j σ O H hH
  choose H₀' hH₀' hH₀'eq using fun j => hEbH j σ ⊤ H₀ hH₀
  choose t ht using fun j => GlobalTheory.T.chernForm_integrable_complexPoints_of_chernWeil hCW F σ X Unit (fun _ => (ρ j).M) (Eb j) (H₀' j) (hH₀' j)
    (MvPolynomial.X ((), X.dim))
  have htO : ∀ j, HasChernIntegral (Eb j) O (H' j) (MvPolynomial.X ((), X.dim)) (t j) := fun j =>
    hT F σ X (ρ j).M (Eb j) O (H' j) (H₀' j) (hH' j)
      (isGood_polyRep F σ X ι m (ρ j) E (Eb j) O H (H' j) (hEbS j) hH (hH'eq j) hG) (hH₀' j) (t j) (ht j)

  have hdens : ∀ (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
      (H' : ∀ j, Mat (fun _ : Unit => (ρ j).M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => (ρ j).M) ℂ),
      IsMetricOn E O H →
      (∀ j, ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' j (fun _ => (ρ j).ev A) y () = (ρ j).ev (H A y)) →
      ∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∃ A ∈ E.S (under y),
        ∃ B : ∀ j, Mat (fun _ : Unit => (ρ j).M) X.Fn, (∀ j, B j ∈ (Eb j).S (under y)) ∧
          chernTop R (fun v => H A (c.e.symm v)) (c.e y) =
            ∑ j, a j * chernTop (MvPolynomial.X ((), X.dim)) (fun v => H' j (B j) (c.e.symm v)) (c.e y) := by
    intro O H H' hH hH'eq y hy c hc
    obtain ⟨A, hA⟩ := E.nonempty (under y)
    refine ⟨A, hA, fun j _ => (ρ j).ev A, fun j => hEbS j _ A hA, ?_⟩
    have hcurv : ∀ j, curvPoly (fun v => H' j (fun _ => (ρ j).ev A) (c.e.symm v) ()) (c.e y) =
        (ρ j).lie (fun τ => curvPoly (fun v => H A (c.e.symm v) τ) (c.e y)) := fun j =>
      curvPoly_polyRep (ρ j) hH (hH'eq j) hy hA c.holo hc
    have hhom : ∀ τ i j, ((fun τ => curvPoly (fun v => H A (c.e.symm v) τ) (c.e y)) τ i j).IsHomogeneous 1 :=
      fun τ i j => by
        simp only [curvPoly, Matrix.of_apply]
        exact IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => isHomogeneous_C_mul_X _ _
    have key := hAlg _ hhom
    simp only [chernTop, chernPoly, aeval_X]
    rw [key]
    simp only [hcurv, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlinO := GlobalTheory.T.hasChernIntegral_linear_of_density_eq_sum F σ X ι m E O H R J (fun j => (ρ j).M) Eb H' (MvPolynomial.X ((), X.dim)) a t hH hH'
    (hdens O H H' hH hH'eq) htO
  have hlinT := GlobalTheory.T.hasChernIntegral_linear_of_density_eq_sum F σ X ι m E ⊤ H₀ R J (fun j => (ρ j).M) Eb H₀' (MvPolynomial.X ((), X.dim)) a t hH₀ hH₀'
    (hdens ⊤ H₀ H₀' hH₀ hH₀'eq) ht
  have hs := hCW F σ X Y ι m E E' φ f gr hRef hGr H₀ hH₀ R
  rw [hs.2.symm.trans hlinT.2]
  exact hlinO

end GlobalTheory.GoodMetric.Bridge
end
end

section


theorem _root_.GlobalTheory.T.untwisted_theta_rational_on_good_covers : GlobalTheory.SerStd.UntwRatS := by
  first | exact @GlobalTheory.SerStd.untwRatS | exact GlobalTheory.SerStd.untwRatS | (intros; apply GlobalTheory.SerStd.untwRatS <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.flagSpace_component_unique_point_each_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x ∧ (Φ.C k).Carries p g := by
  first | exact @GlobalTheory.CarryAll.carries_everywhere | exact GlobalTheory.CarryAll.carries_everywhere | (intros; apply GlobalTheory.CarryAll.carries_everywhere <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.LevExt

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove

theorem frat_delAt_heq {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'} (hP : B'.toPre = B.toPre)
    {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) (l : ℕ) :
    HEq ((Top.Fr.at a'.st f').delAt l) ((Top.Fr.at a.st f).delAt l) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).delAt l)) :))



theorem chars_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Chars (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hP : B'.toPre = B.toPre := l.enl.1
  have hC : x.m.z.R.toLevCh.C = Top.Fr.at (w.st x.o.Z) f := x.m.z.lev.C.trans (by rw [w.C_eq])
  have hC' : x'.m.z.R.toLevCh.C = Top.Fr.at (w'.st x'.o.Z) f' := x'.m.z.lev.C.trans (by rw [w'.C_eq])
  have hs := x.m.z.lev.is
  have hs' := x'.m.z.lev.is
  have hm : (Dof x').R.m = (Dof x).R.m := by
    exact congrArg (fun p : Pre => p.R.m) hP
  have hmu0 : ∀ (i : Fin (Dof x).R.m) (i' : Fin (Dof x').R.m), (i : ℕ) = i' →
      HEq (x'.m.z.R.toLevCh.C.mu0 i') (x.m.z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr h
  refine ⟨?_, fun j => ?_, fun j j' h => ?_, fun l0 => ?_⟩
  · have heta : HEq x'.m.z.R.toLevCh.C.eta x.m.z.R.toLevCh.C.eta := by
      rw [hC, hC']
      exact frat_eta_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP heta hs.eta hs'.eta).symm
  · let j' : Fin (Dof x').R.m := ⟨j, lt_of_lt_of_eq j.2 hm.symm⟩
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP (hmu0 j j' rfl) (hs.mu0 j) (hs'.mu0 j')).symm
  · exact (hmu0 j j' h).symm
  · show HEq (x.m.z.R.toLevCh.C.delAt l0) (x'.m.z.R.toLevCh.C.delAt l0)
    rw [hC, hC']
    exact (frat_delAt_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr l0).symm

end GlobalTheory.HeightCounting.SerMove

end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqUnifCoord

theorem associated_of_pow {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {a b : R} {n : ℕ}
    (hn : 0 < n) (h : Associated (a ^ n) (b ^ n)) : Associated a b := by
  by_cases ha : a = 0
  · subst ha
    rw [zero_pow hn.ne'] at h
    rw [(pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h.symm)]
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at h
    exact ha ((pow_eq_zero_iff hn.ne').1 ((associated_zero_iff_eq_zero _).1 h))
  obtain ⟨u, hu⟩ := h
  set K := FractionRing R
  have inj := IsFractionRing.injective R K
  have ha' : algebraMap R K a ≠ 0 := fun h0 => ha (inj (h0.trans (map_zero _).symm))
  have hb' : algebraMap R K b ≠ 0 := fun h0 => hb (inj (h0.trans (map_zero _).symm))
  have hx : (algebraMap R K b / algebraMap R K a) ^ n = algebraMap R K (u : R) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ ha'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm]
  have hy : (algebraMap R K a / algebraMap R K b) ^ n = algebraMap R K ((u⁻¹ : Rˣ) : R) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ hb'), ← map_pow, ← map_pow, ← map_mul, ← hu, mul_comm,
      mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow hn (hx ▸ isIntegral_algebraMap))
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (IsIntegral.of_pow hn (hy ▸ isIntegral_algebraMap))
  have hcd : c * d = 1 := inj (by rw [map_mul, hc, hd, map_one, div_mul_div_comm, mul_comm (algebraMap R K b),
    div_self (mul_ne_zero ha' hb')])
  refine ⟨⟨c, d, hcd, by rw [mul_comm, hcd]⟩, inj ?_⟩
  show algebraMap R K (a * c) = algebraMap R K b
  rw [map_mul, hc, mul_div_cancel₀ _ ha']

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ ε : D'.toPre.X ≃+ D.toPre.X, ∀ y r r', PsiCoord D.toPre (ε y) r → PsiCoord D'.toPre y r' → Associated (r ^ 2) (r' ^ 2) := by
  intro R _ _ _ hR G _ _ hsa D D' A A' U U' hL
  have hA := admissibleBase_of_completeNormalLocalCharZero hR
  haveI : CharZero R := hR.2.2.2
  haveI : IsIntegrallyClosed R := hR.2.1
  obtain ⟨xe, hxe⟩ := unifPre_characterGroup_iso R _ hA D D' A A' G hsa U.toUnifPre U'.toUnifPre
  obtain ⟨Φ, w, wL, hw, hwL, hm, hp⟩ := GlobalTheory.T.polarisedAbelianPart_iso_of_bundleSquare_iso R hR G hsa D D' A A' U U' hL
  have hc := GlobalTheory.T.degenerationCharMap_eq_on_even_characters R hR G hsa D D' A A' U U' hL Φ w hw hm (fun e => (hp e).1) xe hxe
  refine ⟨xe, fun y r r' hr hr' => ?_⟩
  obtain ⟨⟨s, hs, -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R D hR.2.1 (xe (2 • y))
  obtain ⟨⟨s', hs', -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R D' hR.2.1 (2 • y)
  have a1 : Associated s (r ^ 4) := GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D (xe y) r s hr (by rw [← map_nsmul]; exact hs)
  have a2 : Associated s' (r' ^ 4) := GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four R _ D' y r' s' hr' hs'
  have a3 : Associated (s ^ 4) (s' ^ 4) :=
    GlobalTheory.T.psiCoordinates_evenCharacters_fourthPowers_associated R hR G hsa D D' A A' U U' hL Φ w wL hw hwL hm hp xe hxe hc y s s' hs hs'
  refine associated_of_pow (n := 8) (by norm_num) ?_
  have e1 : (r ^ 2) ^ 8 = (r ^ 4) ^ 4 := by ring
  have e2 : (r' ^ 2) ^ 8 = (r' ^ 4) ^ 4 := by ring
  rw [e1, e2]
  exact ((a1.pow_pow (n := 4)).symm.trans a3).trans (a2.pow_pow (n := 4))

end GlobalTheory.SqUnifCoord
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

theorem _root_.GlobalTheory.T.finiteGroupCharacter_eq_product_residualCharacters_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → RSideW z Wt' R' → LevSame z Wt' R' → R'.toRealDat.grp_chiW := by
  first | exact @GlobalTheory.Mem.R3.Rw.ChiWExt.grp_chiW_ext | exact GlobalTheory.Mem.R3.Rw.ChiWExt.grp_chiW_ext | (intros; apply GlobalTheory.Mem.R3.Rw.ChiWExt.grp_chiW_ext <;> assumption)
end
