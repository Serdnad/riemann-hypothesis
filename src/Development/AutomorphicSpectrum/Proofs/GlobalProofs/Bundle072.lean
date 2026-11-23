module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Continuous
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormInfLeOfEntries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle529
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle002
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle069
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
public import Formalism.LocalToGlobal.GlobalTheory.VolumeCarry.VolumeTheoremTwoOfRationalFrames

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg

variable {D : D7}

theorem exists_lie_oneP {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {V V' : HSp D}
    {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h)
    (τ : D.what₂.Tau) {X : Matrix (Fin V'.rank) (Fin V'.rank) ℂ} (hX : X ∈ lieAt V' τ) :
    ∃ Z ∈ lieAt V τ, ∀ t : ℝ, s (oneP θ V' τ X t) = oneP θ V τ Z t := by
  set c := tauE D τ with hc
  set F : Matrix (Fin V.rank) (Fin V'.rank) ℂ := (frameMat V V' ι).map c with hF
  set H := gramAt D V τ with hH
  set H' := gramAt D V' τ with hH'
  have hFH : Fᴴ * H = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram).map c := by
    rw [Matrix.map_mul]
    congr 1
    ext a b
    simp only [F, Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
    exact (Formalism.IndefR.Eqv.tauE_star D τ _).symm
  have hG := Formalism.L2.GlobalTheoryTheory.VolumeCarry.gram_frameMat D V V' ι hι
  rw [← Formalism.IndefR.Mi.frameMat_eq_global] at hG
  have hFHF : Fᴴ * H * F = H' := by
    rw [hFH, hF, ← Matrix.map_mul, ← hG]; rfl
  have hHu : IsUnit H'.det := GlobalTheory.SmoothAutCheck.gramAt_unit V' τ
  have hHh : H'ᴴ = H' := GlobalTheory.SmoothForms.RealPts.gramAt_herm V' τ
  have hHV : Hᴴ = H := GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ
  have hR1 : H'⁻¹ * H' = 1 := Matrix.nonsing_inv_mul _ hHu
  have hR2 : H' * H'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hHu
  have hRh : (H'⁻¹)ᴴ = H'⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hHh]
  have hXl : Xᴴ * H' + H' * X = 0 := hX
  set Z : Matrix (Fin V.rank) (Fin V.rank) ℂ := F * X * H'⁻¹ * (Fᴴ * H) with hZ
  have hZF : Z * F = F * X := by
    rw [hZ, Matrix.mul_assoc, hFHF, Matrix.mul_assoc, hR1, Matrix.mul_one]
  have hZl : Z ∈ lieAt V τ := by
    change Zᴴ * H + H * Z = 0
    have e1 : Zᴴ * H = H * F * (H'⁻¹ * (Xᴴ * H') * H'⁻¹) * (Fᴴ * H) := by
      rw [hZ]
      simp only [Matrix.conjTranspose_mul, hHV, hRh, Matrix.conjTranspose_conjTranspose]
      have : H'⁻¹ * (Xᴴ * H') * H'⁻¹ = H'⁻¹ * Xᴴ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hR2, Matrix.mul_one]
      rw [this]
      simp only [Matrix.mul_assoc]
    have e2 : H * Z = H * F * (H'⁻¹ * (H' * X) * H'⁻¹) * (Fᴴ * H) := by
      have : H'⁻¹ * (H' * X) * H'⁻¹ = X * H'⁻¹ := by
        rw [← Matrix.mul_assoc, hR1, Matrix.one_mul]
      rw [this, hZ]
      simp only [Matrix.mul_assoc]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.add_mul, ← Matrix.mul_add, hXl]
    simp
  refine ⟨Z, hZl, fun t => ?_⟩
  have h1 : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H' := GlobalTheory.SmoothAutCheck.exp_mem_UH hHu hX t
  have h2 : NormedSpace.exp (t • Z) ∈ Formalism.QuantumDeterminants.UH H :=
    GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hZl t
  have hE : GlobalTheory.RealBessel.IsEmb H F (NormedSpace.exp (t • Z)) (NormedSpace.exp (t • X)) := by
    refine ⟨GlobalTheory.matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine _ _ Z F X hZF t, fun x hx => ?_⟩
    have hZx : Z *ᵥ x = 0 := by
      rw [hZ, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    let W : Matrix (Fin V.rank) (Fin 1) ℂ := Matrix.of fun i _ => x i
    have hW : Z * W = W * (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
      rw [Matrix.mul_zero]
      ext i j
      have := congrFun hZx i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
    have h3 := GlobalTheory.matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine _ _ Z W 0 hW t
    rw [smul_zero, NormedSpace.exp_zero, Matrix.mul_one] at h3
    funext i
    have := congrFun (congrFun h3 i) 0
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
  exact GlobalTheory.AutFunCounterexample.embRel_unique V V' ι hι (hs _)
    (GlobalTheory.EmbAtPlace.embRel_atTau D θ hθ V' V ι τ _ _ h1 h2 hE)

theorem foldr_Rder_eq {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {V V' : HSp D}
    {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h)
    {y : GA D V} (hy : ∀ h, s h * y = y * s h) (ψ : GA D V → ℂ)
    (l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V' p.1) :
    ∃ l' : List (ℝ → GA D V), (∀ γ ∈ l', IsRealLine D.sp.cm.sig V.gram γ) ∧
      ∀ h, (l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) h = l'.foldr lineDer ψ (s h * y) := by
  induction l with
  | nil => exact ⟨[], by simp, fun _ => rfl⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨Z, hZ, e⟩ := exists_lie_oneP hθ hι hs p.1 (hl p List.mem_cons_self)
    refine ⟨oneP θ V p.1 Z :: l', List.forall_mem_cons.2 ⟨GlobalTheory.SphSmooth.isRealLine_oneP hθ V hZ, h1⟩, fun h => ?_⟩
    rw [List.foldr_cons, List.foldr_cons]
    simp only [Rder, lineDer]
    congr 1
    funext t
    rw [h2, map_mul, mul_assoc, hy, ← mul_assoc, e t]

theorem normInf_s_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V V' : HSp D}
    {ι : V'.V →ₗ[D.host.E] V.V} (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h)
    (hV : 0 < V'.rank) : ∃ K : ℝ, 0 ≤ K ∧ ∀ g : GA D V', normInf θ V (s g) ≤ K * normInf θ V' g := by
  obtain ⟨C, hC0, hC⟩ := Formalism.IndefR.Mi.s_entry_le θ hι hs
  refine ⟨Fintype.card D.what₂.Tau * (V.rank * (V.rank * (4 * C))), by positivity, fun g => ?_⟩
  have h1 := GlobalTheory.RatCount.one_le_normInf θ hV g
  set b := normInf θ V' g with hb
  have hb0 : 0 ≤ b := by linarith
  have hE : ∀ τ i j, ‖infMat D.sp.cm.sig V'.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ i j‖ ≤ b := fun τ i j =>
    (Formalism.IndefR.Mi.entry_le_sum (fun i j => ‖infMat D.sp.cm.sig V'.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ i j‖)
      (fun _ _ => by positivity) i j).trans
    (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig V'.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ))
  have a1 : ∀ τ k l, ‖θ τ (Formalism.L2.Theta.infPart D (Formalism.L2.Theta.mt V' g k l))‖ ≤ b := fun τ k l => by
    rw [← Formalism.IndefR.Eqv.infMat_eq]
    linarith [hE τ k l, norm_nonneg (infMat D.sp.cm.sig V'.gram (θ τ) g⁻¹ k l)]
  have a2 : ∀ τ k l, ‖θ τ (Formalism.L2.Theta.infPart D (Formalism.L2.Theta.mt V' g⁻¹ k l))‖ ≤ b := fun τ k l => by
    rw [← Formalism.IndefR.Eqv.infMat_eq]
    linarith [hE τ k l, norm_nonneg (infMat D.sp.cm.sig V'.gram (θ τ) g k l)]
  have hh := Formalism.IndefR.Mi.normInf_le_of_entries θ V (s g) (C * (b + 1)) fun τ i j =>
    ⟨hC g τ b hb0 (a1 τ) i j, by rw [← map_inv]; exact hC g⁻¹ τ b hb0 (a2 τ) i j⟩
  refine hh.trans ?_
  have h4 : C * (b + 1) + C * (b + 1) ≤ 4 * C * b := by nlinarith
  calc (Fintype.card D.what₂.Tau : ℝ) * (V.rank * (V.rank * (C * (b + 1) + C * (b + 1))))
      ≤ (Fintype.card D.what₂.Tau : ℝ) * (V.rank * (V.rank * (4 * C * b))) := by gcongr
    _ = _ := by ring

theorem slice_regular : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ (Γ : Set (GA D V)) (ψ : GA D V → ℂ), IsSmModOn D.sp.cm.sig V.gram Γ ψ → ∀ y : GA D V, (∀ h, s h * y = y * s h) → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V'.rank) (Fin V'.rank) ℂ), (∀ i, Xs i ∈ lieAt V' (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (s (g * (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod) * y)) ∧ ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V' p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V', ‖(l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) (x * g)‖ ≤ C * normInf θ V' g ^ N := by
  intro D θ hθ V V' ι hι s hs Γ ψ hψ y hy
  refine ⟨fun k τs Xs hX g => ?_, ?_⟩
  · choose Z hZ e using fun i => exists_lie_oneP hθ hι hs (τs i) (hX i)
    have key := hψ.smooth k (fun i => oneP θ V (τs i) (Z i))
      (fun i => GlobalTheory.SphSmooth.isRealLine_oneP hθ V (hZ i)) (s g * y)
    have e2 : (fun t : Fin k → ℝ => ψ (s (g * (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod) * y)) =
        fun t => ψ (s g * y * (List.ofFn fun i => oneP θ V (τs i) (Z i) (t i)).prod) := by
      funext t
      have e3 : s (List.ofFn fun i => oneP θ V' (τs i) (Xs i) (t i)).prod =
          (List.ofFn fun i => oneP θ V (τs i) (Z i) (t i)).prod := by
        rw [map_list_prod, List.map_ofFn]
        congr 2
        funext i
        exact e i (t i)
      rw [map_mul, mul_assoc, hy, ← mul_assoc, e3]
    rw [e2]
    exact key
  · obtain ⟨N, hN⟩ := hψ.growth
    rcases Nat.eq_zero_or_pos V'.rank with hV | hV
    · refine ⟨0, fun l _ x => ⟨‖(l.foldr (fun p f => Rder θ V' p.1 p.2 f) (fun h => ψ (s h * y))) x‖, fun g _ => ?_⟩⟩
      have hg1 : g = 1 := Subtype.ext (Units.ext (Matrix.ext fun i j => absurd i.2 (by omega)))
      rw [hg1]
      simp
    · obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow (θ := θ) V hθ
      obtain ⟨K, hK0, hK⟩ := normInf_s_le θ hι hs hV
      refine ⟨d * N, fun l hl x => ?_⟩
      obtain ⟨l', h1, h2⟩ := foldr_Rder_eq hθ hι hs hy ψ l hl
      obtain ⟨C, hC⟩ := hN l' h1
      refine ⟨|C| * (GlobalTheory.Grow.height V (s x * y) * K ^ d) ^ N, fun g hg => ?_⟩
      have hn : 1 ≤ normInf θ V' g := GlobalTheory.RatCount.one_le_normInf θ hV g
      have hsg := Formalism.IndefR.Mi.s_mem_GinfC hι hs hg
      have hnn : 0 ≤ normInf θ V (s g) := by unfold Formalism.L2.Theta.normInf; positivity
      have b1 : GlobalTheory.Grow.height V (s g) ≤ (K * normInf θ V' g) ^ d :=
        (hd _ hsg).trans (pow_le_pow_left₀ hnn (hK g) d)
      have b2 : GlobalTheory.Grow.height V (s (x * g) * y) ≤ GlobalTheory.Grow.height V (s x * y) * (K * normInf θ V' g) ^ d := by
        have e : s (x * g) * y = s x * y * s g := by rw [map_mul, mul_assoc, hy, ← mul_assoc]
        rw [e]
        exact (GlobalTheory.Grow.height_mul_le V _ _).trans
          (mul_le_mul_of_nonneg_left b1 (GlobalTheory.Grow.height_pos V _).le)
      have h0 : 0 ≤ GlobalTheory.Grow.height V (s (x * g) * y) := (GlobalTheory.Grow.height_pos V _).le
      rw [h2]
      calc _ ≤ C * GlobalTheory.Grow.height V (s (x * g) * y) ^ N := hC _
        _ ≤ |C| * GlobalTheory.Grow.height V (s (x * g) * y) ^ N :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h0 N)
        _ ≤ |C| * (GlobalTheory.Grow.height V (s x * y) * (K * normInf θ V' g) ^ d) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 b2 N) (abs_nonneg C)
        _ = |C| * (GlobalTheory.Grow.height V (s x * y) * K ^ d) ^ N * normInf θ V' g ^ (d * N) := by
            rw [pow_mul, mul_pow K]
            ring

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.SliceReg
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspFin

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil

theorem le_re_inner_of_isRepOp {G H : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : G →* (H →L[ℂ] H)} {μ : Measure G} {φ : G → ℝ} {T : H →L[ℂ] H}
    (hT : IsRepOp π μ (fun g => (φ g : ℂ)) T) (hφ : Integrable φ μ) (h0 : 0 ≤ φ) {N : Set G}
    (hs : Function.support φ ⊆ N) (u : H) (c : ℝ) (hc : ∀ g ∈ N, c ≤ (⟪u, π g u⟫_ℂ).re) :
    c * ∫ g, φ g ∂μ ≤ (⟪u, T u⟫_ℂ).re := by
  have hi := (hT u).1
  have hin : Integrable (fun g => ⟪u, (φ g : ℂ) • π g u⟫_ℂ) μ := hi.const_inner u
  have e : (⟪u, T u⟫_ℂ).re = ∫ g, (⟪u, (φ g : ℂ) • π g u⟫_ℂ).re ∂μ := by
    rw [(hT u).2, ← integral_inner hi u]
    exact (integral_re hin).symm
  rw [e, ← integral_const_mul]
  refine integral_mono (hφ.const_mul c) hin.re fun g => ?_
  simp only [inner_smul_right, Complex.re_ofReal_mul]
  by_cases hg : φ g = 0
  · simp [hg]
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hc g (hs hg)) (h0 g)

variable {D : D7} {V : HSp D}

theorem exists_bump (μ : Measure (GA D V)) [μ.IsHaarMeasure] {N : Set (GA D V)} (hN : N ∈ 𝓝 (1 : GA D V)) :
    ∃ φ : GA D V → ℝ, (fun g => (φ g : ℂ)) ∈ CcGA V ∧ 0 ≤ φ ∧ Function.support φ ⊆ N ∧ Integrable φ μ ∧
      0 < ∫ g, φ g ∂μ := by
  obtain ⟨φ, hφ, h0, h1, hs⟩ : ∃ φ : GA D V → ℝ, (fun g => (φ g : ℂ)) ∈ CcGA V ∧ 0 ≤ φ ∧ φ 1 = 1 ∧
      Function.support φ ⊆ N := GlobalTheory.CuspSpectrum.exists_bump_ccAd (isCMExt_host D) hN
  have hc := continuous_of_mem_ccAd hφ
  have hφc : Continuous φ := Complex.continuous_re.comp hc.1
  have hφs : HasCompactSupport φ := hc.2.comp_left (g := Complex.re) rfl
  exact ⟨φ, hφ, h0, hs, hφc.integrable_of_hasCompactSupport hφs,
    hφc.integral_pos_of_hasCompactSupport_nonneg_nonzero hφs h0 (x := 1) (by rw [h1]; exact one_ne_zero)⟩

theorem finiteDimensional_of_coercive (hP : GlobalTheory.Published.CuspDecayBound) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (Sb : Submodule ℂ (L2cusp V μ)) {N : Set (GA D V)} (hN : N ∈ 𝓝 (1 : GA D V))
    (h : ∀ g ∈ N, ∀ u ∈ Sb, (1 / 2 : ℝ) * ‖u‖ ^ 2 ≤ (⟪u, Rcusp V μ g u⟫_ℂ).re) : FiniteDimensional ℂ Sb := by
  obtain ⟨φ, hf, h0, hs, hi, hpos⟩ := exists_bump μ hN
  have hrep := GlobalTheory.CuspSpectrum.isRepOp_RcuspOp (μ := μ) hf
  refine GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive (L2cusp V μ) (RcuspOp V μ _)
    (isCompactOperator_of_isHilbertSchmidt (GlobalTheory.CuspHS.isHilbertSchmidt_RcuspOp hP hf)) Sb
    ((1 / 2) * ∫ g, φ g ∂μ) (by positivity) fun u hu => ?_
  have := le_re_inner_of_isRepOp hrep hi h0 hs u ((1 / 2 : ℝ) * ‖u‖ ^ 2) fun g hg => h g hg u hu
  calc _ = (1 / 2 : ℝ) * ‖u‖ ^ 2 * ∫ g, φ g ∂μ := by ring
    _ ≤ _ := this

end GlobalTheory.CompanionTheory.CuspFin
end
end
