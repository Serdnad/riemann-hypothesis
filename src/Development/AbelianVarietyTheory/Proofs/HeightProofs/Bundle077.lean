module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle075
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle051
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef


open CoefLow in
theorem values_eq_coef : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (x : GA D V), ∃ ℓ : H →ₗ[ℂ] ℂ,
      Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ ∧ SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v : H) ∧
      ∀ y ∈ UJset ε, T v (x * atTau θ V τ (P⁻¹ * y * P)) = ℓ (σ y v) := by
  classical
  intro D θ V τ hθ hHC hCW H _ _ σ lam ε P T _ hDS hP h hT v x
  haveI : CompleteSpace H := hDS.1
  have hstd := std_of_isDS hHC hDS
  have hσ := hstd.1
  obtain ⟨N, hN⟩ := GlobalTheory.TypeSum.GKCoef.exists_growth_exponent θ V τ hθ hHC H σ lam ε P T hDS hP h hT x
  let F : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ → Mx V.rank → ℂ := fun w y => T w (x * atTau θ V τ (P⁻¹ * y * P))
  let f : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] Bd (Unit × UJset ε) :=
    { toFun := fun w => mkBd (fun i => F w i.2.1 / wt N i.2.1) (by
        obtain ⟨C, hC⟩ := hN w
        refine ⟨C, fun i => ?_⟩
        rw [norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
        exact hC _ i.2.2)
      map_add' := fun v w => by ext i; simp [mkBd, F, add_div]; rfl
      map_smul' := fun c v => by ext i; simp [mkBd, F, mul_div_assoc] }
  obtain ⟨T₀, hT₀'⟩ := LinearMap.exists_extend f
  have hT₀ : ∀ (w : H) (hw : IsKFin ε σ w) (i : Unit × UJset ε),
      T₀ w i = F ⟨w, mem_kFin_iff.2 hw⟩ i.2.1 / wt N i.2.1 := fun w hw i => by
    have : T₀ w = f ⟨w, mem_kFin_iff.2 hw⟩ := LinearMap.congr_fun hT₀' ⟨w, mem_kFin_iff.2 hw⟩
    rw [this]; rfl
  let wcomp (c : (Unit × UJset ε) → ℂ) (B : ℝ) (hB0 : 0 ≤ B)
      (hB : ∀ i, ‖c i‖ ≤ B) (φ : (Unit × UJset ε) → (Unit × UJset ε)) :
      Bd (Unit × UJset ε) →L[ℂ] Bd (Unit × UJset ε) :=
    LinearMap.mkContinuous
      { toFun := fun F => mkBd (fun i => c i * F (φ i)) ⟨_, wcomp_le hB φ F⟩
        map_add' := fun F G => by ext i; simp [mkBd, mul_add]; rfl
        map_smul' := fun a F => by ext i; simp [mkBd]; ring } B
      fun F => lp.norm_le_of_forall_le (by positivity) (wcomp_le hB φ F)
  let rt (h : Mx V.rank) : Bd (Unit × UJset ε) →L[ℂ] Bd (Unit × UJset ε) :=
    if hh : h ∈ UJset ε then
      wcomp (fun i => (wt N (i.2.1 * h) : ℂ) / wt N i.2.1) (wt N h) (wt_pos N h).le
        (fun i => by
          rw [norm_div, norm_wt, norm_wt, div_le_iff₀' (wt_pos _ _)]
          exact wt_mul_le _ _ _) fun i => (i.1, ⟨i.2.1 * h, mul_mem_UJ i.2.2 hh⟩)
    else 0
  have rt_apply {h : Mx V.rank} (hh : h ∈ UJset ε) (F : Bd (Unit × UJset ε)) (i : Unit × UJset ε) :
      rt h F i = (wt N (i.2.1 * h) : ℂ) / wt N i.2.1 * F (i.1, ⟨i.2.1 * h, mul_mem_UJ i.2.2 hh⟩) := by
    simp only [rt, dif_pos hh]
    rfl
  have modRep_rt : ModRep ε rt := by
    refine ⟨?_, fun a ha b hb => ?_, 1, N, fun g hg => ?_⟩
    · ext F i
      rw [rt_apply (one_mem_UJ ε)]
      simp [div_self (wt_ne _ _)]
    · ext F i
      rw [ContinuousLinearMap.comp_apply, rt_apply (mul_mem_UJ ha hb), rt_apply ha, rt_apply hb]
      simp only [mul_assoc]
      have := wt_ne N (i.2.1 * a)
      field_simp
    · simp only [rt, dif_pos hg, one_mul]
      dsimp only [wcomp]
      exact LinearMap.mkContinuous_norm_le _ (wt_pos N g).le _
  have key : ∀ (w : H) (hw : IsKFin ε σ w), ∀ y ∈ UJset ε, ∀ i : Unit × UJset ε,
      rt y (T₀ w) i = F ⟨w, mem_kFin_iff.2 hw⟩ (i.2.1 * y) / wt N i.2.1 := by
    intro w hw y hy i
    rw [rt_apply hy, hT₀ w hw]
    have := wt_ne N (i.2.1 * y)
    field_simp

  have hder : ∀ (w : H) (hw : IsKFin ε σ w) {X : Mx V.rank} (hX : X ∈ lieSet ε) {g : Mx V.rank} (hg : g ∈ UJset ε)
      (s : ℝ), HasDerivAt (fun t : ℝ => F ⟨w, mem_kFin_iff.2 hw⟩ (g * NormedSpace.exp (t • X)))
        (F ⟨dRep σ X w, mem_kFin_iff.2 (isKFin_dRep _ ε H σ hstd w hw X hX)⟩ (g * NormedSpace.exp (s • X))) s := by
    intro w hw X hX g hg s
    have hs := mul_mem_UJ hg (exp_mem_UJ hX s)
    have h1 := hasDerivAt_map hθ hP h hT ⟨w, mem_kFin_iff.2 hw⟩
      ⟨dRep σ X w, mem_kFin_iff.2 (isKFin_dRep _ ε H σ hstd w hw X hX)⟩ hX (hstd.2.2.1 w hw) rfl x hs
    have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
    refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
    show F _ _ = F _ _
    simp only [F]
    rw [mul_assoc g (NormedSpace.exp (s • X)), ← exp_add_smul, add_sub_cancel]
  obtain ⟨T', hT1, hT2, S, C, hS, hC⟩ := GlobalTheory.TypeSum.casselmanWallach_banach hCW V.rank ε H σ hstd _ _
    modRep_rt T₀
    (fun k hk w hw => by
      ext i
      rw [key w hw k (K_le_UJ hk), hT₀ _ (isKFin_translate hw hk)]
      congr 1
      exact map_K hθ hP h hT hk _ _ rfl x i.2.2)
    (fun X hX w hw => by
      have hw1 := isKFin_dRep _ ε H σ hstd w hw X hX
      have hw2 := isKFin_dRep _ ε H σ hstd _ hw1 X hX
      obtain ⟨C2, hC2⟩ := hN ⟨_, mem_kFin_iff.2 hw2⟩
      obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image
        ((continuous_wt N).comp (continuous_exp_smul X)).continuousOn)
      refine hasDerivAt_of_sq (K := |C2| * |B|) fun t ht => lp.norm_le_of_forall_le (by positivity) fun i => ?_
      have e : (t • T₀ (dRep σ X w)) i = t • T₀ (dRep σ X w) i := rfl
      rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, e, key w hw _ (exp_mem_UJ hX _),
        key w hw _ (exp_mem_UJ hX _), hT₀ _ hw1, zero_smul, NormedSpace.exp_zero, mul_one,
        ← smul_div_assoc, ← sub_div, ← sub_div, norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
      have tb := taylor_two (hder w hw hX i.2.2) (hder _ hw1 hX i.2.2) (K := |C2| * |B| * wt N i.2.1)
        (fun s hs => by
          refine (hC2 _ (mul_mem_UJ i.2.2 (exp_mem_UJ hX s))).trans ?_
          have w1 := wt_mul_le N i.2.1 (NormedSpace.exp (s • X))
          have w2 : wt N (NormedSpace.exp (s • X)) ≤ |B| := (hB ⟨s, abs_le.1 hs, rfl⟩).trans (le_abs_self B)
          have w3 := wt_pos N i.2.1
          have w4 := wt_pos N (i.2.1 * NormedSpace.exp (s • X))
          change C2 * wt N _ ≤ _
          calc C2 * wt N (i.2.1 * NormedSpace.exp (s • X)) ≤ |C2| * (wt N i.2.1 * |B|) :=
                mul_le_mul (le_abs_self _) (w1.trans (mul_le_mul_of_nonneg_left w2 w3.le)) w4.le (abs_nonneg _)
            _ = _ := by ring) ht
      simp only [zero_smul, NormedSpace.exp_zero, mul_one] at tb
      calc _ ≤ |C2| * |B| * wt N i.2.1 * t ^ 2 := tb
        _ = _ := by ring)
  let ℓ : H →ₗ[ℂ] ℂ :=
    { toFun := fun w => wt N (1 : Mx V.rank) * T' w ((), ⟨1, one_mem_UJ ε⟩)
      map_add' := fun a b => by simp [mul_add]
      map_smul' := fun c a => by simp; ring }
  have hvK : IsKFin ε σ (v : H) := mem_kFin_iff.1 v.2
  refine ⟨ℓ, ⟨S, wt N (1 : Mx V.rank) * |C|, hS, fun w hw => ?_⟩, hstd.2.2.1 _ hvK, fun y hy => ?_⟩
  · change ‖(wt N (1 : Mx V.rank) : ℂ) * T' w ((), ⟨1, one_mem_UJ ε⟩)‖ ≤ _
    rw [norm_mul, norm_wt, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((apply_le _ _).trans ((hC w hw).trans ?_)) (wt_pos _ _).le
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
  · change _ = (wt N (1 : Mx V.rank) : ℂ) * T' (σ y v) ((), ⟨1, one_mem_UJ ε⟩)
    rw [hT2 y hy _ (hstd.2.2.1 _ hvK), hT1 _ hvK, key _ hvK y hy]
    have := wt_ne N (1 : Mx V.rank)
    simp only [one_mul, F]
    field_simp

end GlobalTheory.TypeSum.GKCoef

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem _root_.GlobalTheory.T.exists_secNorm_inputsR_of_inputsNet : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsNet large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → ∃ n : SecNorm B, InputsR large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  first | exact @GlobalTheory.FinalJoin.inputsR_of_inputsNet | exact GlobalTheory.FinalJoin.inputsR_of_inputsNet | (intros; apply GlobalTheory.FinalJoin.inputsR_of_inputsNet <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos


theorem _root_.GlobalTheory.T.exists_maps_of_relations_alt : GlobalTheory.Published.HarishChandraModules → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Ltr ε → Module.End ℂ M) (m₀ : M),
    (∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE τ (u i) m₀ = 0) →
    ∃ T : Fin d → (H →ₗ[ℂ] M), (∀ a v, IsKFin ε σ v → ∀ x, T a (ltrV σ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), T a v = ∑ i, c i • wordE τ (u i) m₀ := by
  first | exact @GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations | exact GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations | (intros; apply GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Submodule ℂ (K → GA D V → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × GA D V => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) → (∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, (fun k => Rder θ V τ X (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, Continuous (fun x => ∫ k, F k x ∂μ) ∧ (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ) ∧ ∀ τ j, gelf θ V τ j (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, gelf θ V τ j (F k) x ∂μ := by
  first | exact @GlobalTheory.AvgFam.avg_closed | exact GlobalTheory.AvgFam.avg_closed | (intros; apply GlobalTheory.AvgFam.avg_closed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open MeasureTheory Filter Topology

namespace GlobalTheory.KAvgGrowth

theorem continuousOn_and_umg_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) ∧
    GlobalTheory.TypeSum.UMG ε (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  classical
  intro n ε f hf hU e he
  obtain ⟨N, F, hF0, hFd, hFg⟩ := hU
  refine ⟨GlobalTheory.T.continuousOn_integral_mul_right_translate_toMK n ε f hf e he, ?_⟩
  let B := Module.finBasis ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))
  let b : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n := fun i => (B i : Mx n)
  have hb : ∀ i, b i ∈ lieSet ε := fun i => by rw [lieSet_eq_lie]; exact (B i).2
  let c : Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))) → Mx n → ℝ := fun i Z =>
    if h : Z ∈ lieSet ε then B.repr ⟨Z, by rwa [lieSet_eq_lie] at h⟩ i else 0
  have hsum : ∀ Z ∈ lieSet ε, Z = ∑ i, c i Z • b i := by
    intro Z hZ
    have hZ' : Z ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε) := by rwa [lieSet_eq_lie] at hZ
    have := congrArg Subtype.val (B.sum_repr ⟨Z, hZ'⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    simp only [c, dif_pos hZ]
    exact this.symm
  have hli : LinearIndependent ℝ b :=
    B.linearIndependent.map' (GlobalTheory.LowTypeDetermined.lie (Jm ε)).subtype (Submodule.ker_subtype _)
  have hC : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g := by
    intro l hl Z hZ g hg
    obtain ⟨τ, hτ0, hτ, hev⟩ := GlobalTheory.T.exp_second_kind_coordinates n ε _ b hb hli (fun Z hZ => ⟨fun i => c i Z, hsum Z hZ⟩) (fun i => c i Z)
    have h2 := GlobalTheory.T.hasFDerivAt_derFam_mul_prod_exp_smul_zero n ε N F hFd hFg l hl _ b hb g hg
    rw [← hτ0] at h2
    have h3 := h2.comp_hasDerivAt (0 : ℝ) hτ
    have h4 : HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) (F (Z :: l) g) 0 := hFd l hl Z hZ g hg
    have h5 : (fun t : ℝ => F l (g * NormedSpace.exp (t • Z))) =ᶠ[nhds 0]
        ((fun t : Fin _ → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod)) ∘ τ) := by
      filter_upwards [hev] with t ht
      rw [← hsum Z hZ] at ht
      simp only [Function.comp_apply, ht]
    have h6 := h4.unique (h3.congr_of_eventuallyEq h5)
    rw [h6]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, Complex.real_smul]
  have hD := GlobalTheory.T.derFam_ofFn_eq_sum_prod_coeff_of_expand n ε F hFd _ b c hb hC
  have hK : ∀ k : ↥(KG ε), toMK k ∈ UJset ε := fun k => K_le_UJ (toMK_mem_K k)
  have had : ∀ (k : ↥(KG ε)) (X : Mx n), X ∈ lieSet ε → (toMK k)⁻¹ * X * toMK k ∈ lieSet ε := by
    intro k X hX
    rw [lieSet_eq_lie] at hX ⊢
    exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) (hK k) hX
  have hinvc : Continuous fun k : ↥(KG ε) => (toMK k)⁻¹ := by
    have e1 : (fun k : ↥(KG ε) => (toMK k)⁻¹) = fun k => toMK k⁻¹ := by
      funext k
      exact (Matrix.coe_units_inv _).symm
    rw [e1]
    exact (continuous_toMK ε).comp continuous_inv
  have hcc : ∀ i (X : Mx n), X ∈ lieSet ε → Continuous fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k) := by
    intro i X hX
    have hX' : ∀ k : ↥(KG ε), (toMK k)⁻¹ * X * toMK k ∈ GlobalTheory.LowTypeDetermined.lie (Jm ε) := fun k => by
      have := had k X hX; rwa [lieSet_eq_lie] at this
    have e1 : (fun k : ↥(KG ε) => c i ((toMK k)⁻¹ * X * toMK k)) =
        fun k => B.repr ⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ i := by
      funext k
      simp only [c, dif_pos (had k X hX)]
    rw [e1]
    have hm : Continuous fun k : ↥(KG ε) => (⟨(toMK k)⁻¹ * X * toMK k, hX' k⟩ : GlobalTheory.LowTypeDetermined.lie (Jm ε)) :=
      ((hinvc.matrix_mul continuous_const).matrix_mul (continuous_toMK ε)).subtype_mk _
    exact ((B.coord i).continuous_of_finiteDimensional).comp hm
  have e1 : ∀ (l : List (Mx n)) (k : ↥(KG ε)), (l.map fun X => (toMK k)⁻¹ * X * toMK k) =
      List.ofFn fun j => (toMK k)⁻¹ * l.get j * toMK k := by
    intro l k
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn]; rfl
  have hbw : ∀ {m : ℕ} (J : Fin m → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε)))),
      ∀ Y ∈ List.ofFn (fun j => b (J j)), Y ∈ lieSet ε := by
    intro m J Y hY
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hY
    exact hb _
  have hUb : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (toMK k)⁻¹ * X * toMK k) g‖ ≤ C * (1 + hs g) ^ N := by
    intro l hl
    have hcb : ∀ i (j : Fin l.length), ∃ M : ℝ, ∀ k : ↥(KG ε), |c i ((toMK k)⁻¹ * l.get j * toMK k)| ≤ M := by
      intro i j
      obtain ⟨M, hM⟩ := (isCompact_univ.image (hcc i _ (hl _ (List.get_mem l j)))).isBounded.exists_norm_le
      exact ⟨M, fun k => by simpa [Real.norm_eq_abs] using hM _ ⟨k, Set.mem_univ _, rfl⟩⟩
    choose M hM using hcb
    have hCJ : ∀ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))), ∃ C : ℝ,
        ∀ g ∈ UJset ε, ‖F (List.ofFn fun j => b (J j)) g‖ ≤ C * (1 + hs g) ^ N := fun J => hFg _ (hbw J)
    choose CJ hCJ using hCJ
    refine ⟨∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))),
      (∏ j, |M (J j) j|) * |CJ J|, fun k g hg => ?_⟩
    rw [e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) g hg, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => ?_)
    rw [norm_mul, norm_prod, mul_assoc]
    have hw : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) _
    refine mul_le_mul (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_) ?_ (norm_nonneg _)
      (Finset.prod_nonneg fun j _ => abs_nonneg _)
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hM _ _ k).trans (le_abs_self _)
    · exact (hCJ J g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw)
  have hF0c : ContinuousOn (F []) (UJset ε) := hf.congr fun g hg => hF0 g hg
  have hMs : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      AEStronglyMeasurable (fun k : ↥(KG ε) =>
        F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) (muK ε) := by
    intro l hl z hz
    refine Measurable.aestronglyMeasurable ?_
    have e2 : (fun k : ↥(KG ε) => F (l.map fun X => (toMK k)⁻¹ * X * toMK k) (z * toMK k)) =
        fun k => ∑ J : Fin l.length → Fin (Module.finrank ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))),
          (∏ j, (c (J j) ((toMK k)⁻¹ * l.get j * toMK k) : ℂ)) * F (List.ofFn fun j => b (J j)) (z * toMK k) := by
      funext k
      rw [e1, hD _ _ (fun j => had k _ (hl _ (List.get_mem l j))) _ (mul_mem_UJ hz (hK k))]
    rw [e2]
    refine Finset.measurable_sum _ fun J _ => Measurable.mul ?_ ?_
    · exact Finset.measurable_prod _ fun j _ =>
        Complex.measurable_ofReal.comp (hcc _ _ (hl _ (List.get_mem l j))).measurable
    · exact GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset n ε F hFd hF0c _ (hbw J) (↥(KG ε)) (fun k => z * toMK k)
        (continuous_const.matrix_mul (continuous_toMK ε)) fun k => mul_mem_UJ hz (hK k)
  obtain ⟨hA, hB⟩ := GlobalTheory.T.avg_derFam_growth_alt n ε N F hFd hUb hMs e he
  refine ⟨N, _, fun y hy => ?_, hA, hB⟩
  simp only [List.map_nil]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only
  rw [hF0 _ (mul_mem_UJ hy (hK k))]

end GlobalTheory.KAvgGrowth
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_common_growth_exponent_gK_discreteSeries : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ N : ℕ,
    ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ ∃ (m : List (List (Mx n)) → ℕ) (A : List (List (Mx n)) → ℝ),
    ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) →
    (∀ j, IsKFin ε σ (x j)) → ∀ B : ℕ → ℝ,
    (∀ k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (Dw σ w (x j)))‖ ≤ B k * (1 + hs y) ^ N) →
    ∃ (q : ℕ) (ℓ' : Fin q → (H →ₗ[ℂ] ℂ)) (x' : Fin q → H) (c : Fin q → ℝ),
      (∀ i, Sm ε σ (x' i)) ∧ (∀ i, 0 ≤ c i) ∧ (∀ i w, Sm ε σ w → ‖ℓ' i w‖ ≤ c i * sobNorm σ S w) ∧
      (∀ S', Words (lieSet ε) S' → ∑ i, c i * sobNorm σ S' (x' i) ≤ A S' * B (m S')) ∧
      ∀ y ∈ UJset ε, ∑ j, ℓ j (σ y (x j)) = ∑ i, ℓ' i (σ y (x' i)) := by
  first | exact @GlobalTheory.TypeSum.CoefRep.exists_rewrite | exact GlobalTheory.TypeSum.CoefRep.exists_rewrite | (intros; apply GlobalTheory.TypeSum.CoefRep.exists_rewrite <;> assumption)
end
