module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle328
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteLeOfGKStableDiscreteSeriesModel
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AvgDerFamGrowth
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef

theorem exists_growth_exponent : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T → ∀ x : GA D V, ∃ N : ℕ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ, ∃ C : ℝ,
      ∀ y ∈ UJset ε, ‖T w (x * atTau θ V τ (P⁻¹ * y * P))‖ ≤ C * (1 + Formalism.REAL.hs y) ^ N := by
  intro D θ V τ hθ hHC H _ _ σ lam ε P T hDS hP hPG hT x
  haveI : CompleteSpace H := hDS.1
  have hstd : Std ε σ := std_of_isDS hHC hDS
  obtain ⟨Th, hTh⟩ := LinearMap.exists_extend T
  have eTh : ∀ v (hv : v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ), Th v = T ⟨v, hv⟩ := fun v hv => LinearMap.congr_fun hTh ⟨v, hv⟩
  have hkf : ∀ v, IsKFin ε σ v → v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ := fun v hv => mem_kFin_iff.2 hv
  have hDw : ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v → IsKFin ε σ (Dw σ l v) := by
    intro l hl v hv
    induction l with
    | nil => exact hv
    | cons X l ih =>
      exact isKFin_dRep _ ε H σ hstd _ (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) X (hl X List.mem_cons_self)
  obtain ⟨u, hu, hu0⟩ := hstd.2.2.2.2
  obtain ⟨N, F, hF0, hFd, hFg⟩ := umg_atTau D θ hθ V τ (T ⟨u, hkf u hu⟩) (hT.aut _) ε P hP hPG x
  have hFeq : ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∀ y ∈ UJset ε,
      F l y = Th (Dw σ l u) (x * atTau θ V τ (P⁻¹ * y * P)) := by
    intro l hl
    induction l with
    | nil => intro y hy; rw [hF0 y hy]; exact (congrFun (eTh u (hkf u hu)) _).symm
    | cons X l ih =>
      intro y hy
      have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
      have hX := hl X List.mem_cons_self
      have k1 := hDw l hl' u hu
      have k2 := hDw (X :: l) hl u hu
      have d1 := hFd l hl' X hX y hy
      have d2 := hasDerivAt_map hθ hP hPG hT ⟨Dw σ l u, hkf _ k1⟩ ⟨Dw σ (X :: l) u, hkf _ k2⟩ hX
        (hstd.2.2.1 _ k1) rfl x hy
      have d1' : HasDerivAt (fun t : ℝ => T ⟨Dw σ l u, hkf _ k1⟩
          (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P))) (F (X :: l) y) 0 := by
        refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
        show _ = F l _
        rw [ih hl' _ (mul_mem_UJ hy (exp_mem_UJ hX t)), eTh _ (hkf _ k1)]
      rw [d1'.unique d2, eTh _ (hkf _ k2)]
  obtain ⟨Pr, hPr⟩ : ∃ Pr : H → Prop, ∀ w, Pr w ↔ ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) →
      ∃ C : ℝ, ∀ y ∈ UJset ε, ‖Th (Dw σ l w) (x * atTau θ V τ (P⁻¹ * y * P))‖ ≤ C * (1 + hs y) ^ N :=
    ⟨_, fun _ => Iff.rfl⟩
  have hSm : ∀ w, IsKFin ε σ w → Sm ε σ w := hstd.2.2.1
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ H, ∀ w, w ∈ W ↔ IsKFin ε σ w ∧ Pr w := by
    refine ⟨{ carrier := {w | IsKFin ε σ w ∧ Pr w}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ },
      fun _ => Iff.rfl⟩
    · rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
      refine ⟨mem_kfin.1 ((kfin ε σ).add_mem (mem_kfin.2 ha1) (mem_kfin.2 hb1)), (hPr _).2 fun l hl => ?_⟩
      obtain ⟨C1, h1⟩ := (hPr a).1 ha2 l hl
      obtain ⟨C2, h2⟩ := (hPr b).1 hb2 l hl
      refine ⟨C1 + C2, fun y hy => ?_⟩
      rw [Dw_add hstd.1 hl (hSm _ ha1) (hSm _ hb1), map_add (f := _), Pi.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (h1 y hy) (h2 y hy))
    · have h0 : IsKFin ε σ (0 : H) := mem_kfin.1 (kfin ε σ).zero_mem
      refine ⟨h0, (hPr _).2 fun l hl => ⟨0, fun y hy => ?_⟩⟩
      have e := Dw_smul hstd.1 hl (0 : ℂ) (hSm _ h0)
      rw [zero_smul, zero_smul] at e
      rw [e, map_zero]
      simp
    · rintro c a ⟨ha1, ha2⟩
      refine ⟨mem_kfin.1 ((kfin ε σ).smul_mem c (mem_kfin.2 ha1)), (hPr _).2 fun l hl => ?_⟩
      obtain ⟨C, h1⟩ := (hPr a).1 ha2 l hl
      refine ⟨‖c‖ * C, fun y hy => ?_⟩
      rw [Dw_smul hstd.1 hl c (hSm _ ha1), map_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (h1 y hy) (norm_nonneg c)).trans_eq (by ring)
  have hWk : ∀ w ∈ W, IsKFin ε σ w := fun w hw => ((hW w).1 hw).1
  have hWX : ∀ X, inG ε X → ∀ w ∈ W, dRep σ X w ∈ W := by
    intro X hXg w hw
    obtain ⟨hw1, hw2⟩ := (hW w).1 hw
    have hXl : X ∈ lieSet ε := hXg
    refine (hW _).2 ⟨isKFin_dRep _ ε H σ hstd w hw1 X hXl, (hPr _).2 fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := (hPr w).1 hw2 (l ++ [X]) (by
      intro Y hY
      rcases List.mem_append.1 hY with h | h
      · exact hl Y h
      · rw [List.mem_singleton] at h; rw [h]; exact hXl)
    refine ⟨C, fun y hy => ?_⟩
    have e : Dw σ l (dRep σ X w) = Dw σ (l ++ [X]) w := by rw [Dw_append]; rfl
    rw [e]
    exact hC y hy
  have hWK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W := by
    intro k hk w hw
    obtain ⟨hw1, hw2⟩ := (hW w).1 hw
    have hkU := K_le_UJ hk
    refine (hW _).2 ⟨isKFin_translate hw1 hk, (hPr _).2 fun l hl => ?_⟩
    have hl' : ∀ X ∈ l.map (fun X => k⁻¹ * X * k), X ∈ lieSet ε := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Y hY)
    obtain ⟨C, hC⟩ := (hPr w).1 hw2 _ hl'
    have hv' := hDw _ hl' w hw1
    refine ⟨|C| * (1 + hs k) ^ N, fun y hy => ?_⟩
    rw [Dw_translate hstd.1 hkU (hSm _ hw1) hl, eTh _ (hkf _ (isKFin_translate hv' hk)),
      map_K hθ hP hPG hT hk ⟨_, hkf _ hv'⟩ _ rfl x hy, ← eTh _ (hkf _ hv')]
    refine (hC (y * k) (mul_mem_UJ hy hkU)).trans ?_
    have hp : (1 + hs (y * k)) ^ N ≤ (1 + hs y) ^ N * (1 + hs k) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [hs_nonneg (y * k)]) (one_add_hs_mul_le y k) N
    calc C * (1 + hs (y * k)) ^ N ≤ |C| * (1 + hs (y * k)) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith [hs_nonneg (y * k)]) _)
      _ ≤ |C| * ((1 + hs y) ^ N * (1 + hs k) ^ N) := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
      _ = |C| * (1 + hs k) ^ N * (1 + hs y) ^ N := by ring
  have huW : u ∈ W := (hW u).2 ⟨hu, (hPr u).2 fun l hl => by
    obtain ⟨C, hC⟩ := hFg l hl
    exact ⟨C, fun y hy => by rw [← hFeq l hl y hy]; exact hC y hy⟩⟩
  have hW0 : W ≠ ⊥ := fun hb => hu0 ((Submodule.mem_bot ℂ).1 (hb ▸ huW))
  have hd := GlobalTheory.HCModIrred.dense_of_stable hHC hstd.1 hstd.2.1 hWk hWX hWK hW0
  refine ⟨N, fun w => ?_⟩
  have hmem := GlobalTheory.HCModIrred.mem_of_dense hstd hd hWk hWK (mem_kFin_iff.1 w.2)
  obtain ⟨C, hC⟩ := (hPr _).1 ((hW _).1 hmem).2 [] (by simp)
  refine ⟨C, fun y hy => ?_⟩
  have := hC y hy
  rwa [show Dw σ [] (w : H) = w from rfl, eTh _ w.2] at this

end GlobalTheory.TypeSum.GKCoef

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin




theorem inputsR_of_inputsNet : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsNet large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → ∃ n : SecNorm B, InputsR large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus h
  obtain ⟨hB, G, Gc, PH, Prw, Pet, Pd, hN, hF, hP⟩ := h
  obtain ⟨n, h1, h2, h3⟩ := secNorm_of_netIn D B P j X large₂ K ka Pd hN
  obtain ⟨G', hF', hP'⟩ := GlobalTheory.T.exists_formFamilyHypotheses_changedSecondNorm D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n G Gc PH Prw Pet
    Pd _ hF hP
  exact ⟨n, baseIn_secNorm D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n hB, h1, h2,
    G', Gc, PH, Prw, Pet, Pd, h3, hF', hP'⟩

end GlobalTheory.FinalJoin
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem _root_.GlobalTheory.T.runNumericalConditions_of_indexBound_beyond_threshold : ∀ Z₀ : ℝ → ℝ → ℝ, ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → x₀ H.CA H.CK ≤ large₂.sc.x → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 ∧ Z₀ H.CA H.CK ≤ zBase large₂ := by
  first | exact @GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond | exact GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond | (intros; apply GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos


theorem _root_.GlobalTheory.T.coeffSum_smooth_rightDerivWords : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (d : ℕ) (L : Fin d → (H →ₗ[ℂ] ℂ)), (∀ a, Sobolev₂ (lieSet ε) σ (L a)) →
    ∀ x : Fin d → H, (∀ a, Sm ε σ (x a)) →
    CSm ε (fun y => ∑ a, L a (σ y (x a))) ∧ ∀ (u : List (Ltr ε)), ∀ y ∈ UJset ε,
      wordF u (fun y => ∑ a, L a (σ y (x a))) y = ∑ a, L a (σ y (wordV σ u (x a))) := by
  first | exact @GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF | exact GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF | (intros; apply GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

namespace GlobalTheory.TypeSum.CoefClos

theorem exists_hom_of_ann {R V M : Type} [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R V] {d : ℕ} (w : Fin d → V) (m₀ : M) (h : ∀ α : R, α • w = 0 → α • m₀ = 0) :
    ∃ T : Fin d → (V →ₗ[R] M), ∑ a, T a (w a) = m₀ ∧ ∀ a v, ∃ α : R, T a v = α • m₀ := by
  classical
  let f : R →ₗ[R] (Fin d → V) := LinearMap.toSpanSingleton R _ w
  let g : R →ₗ[R] M := LinearMap.toSpanSingleton R _ m₀
  have hk : LinearMap.ker f ≤ LinearMap.ker g := fun α hα => h α hα
  let φ : LinearMap.range f →ₗ[R] M := (LinearMap.ker f).liftQ g hk ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ α : R, φ ⟨f α, α, rfl⟩ = α • m₀ := by
    intro α
    have : f.quotKerEquivRange.symm ⟨f α, α, rfl⟩ = Submodule.Quotient.mk α := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker f).liftQ g hk (f.quotKerEquivRange.symm ⟨f α, α, rfl⟩) = _
    rw [this]; rfl
  obtain ⟨P, hP⟩ := IsSemisimpleModule.extension_property (LinearMap.range f).subtype
    (LinearMap.range f).injective_subtype LinearMap.id
  refine ⟨fun a => φ ∘ₗ P ∘ₗ LinearMap.single R (fun _ => V) a, ?_, fun a v => ?_⟩
  · have e : ∑ a, Pi.single a (w a) = (LinearMap.range f).subtype ⟨f 1, 1, rfl⟩ := by
      rw [Finset.univ_sum_single]
      exact (one_smul R w).symm
    have e2 := LinearMap.congr_fun hP ⟨f 1, 1, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.coe_single]

    rw [← map_sum, ← map_sum, e]
    rw [LinearMap.comp_apply] at e2
    rw [e2, LinearMap.id_apply, hφ, one_smul]
  · obtain ⟨α, hα⟩ := (P (Pi.single a v)).2
    refine ⟨α, ?_⟩
    rw [← hφ]
    exact congrArg φ (Subtype.ext hα.symm)

theorem exists_words {L : Type} (α : FreeAlgebra ℂ L) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), α = ∑ i, c i • ((u i).map (FreeAlgebra.ι ℂ)).prod := by
  have h1 : α ∈ (Algebra.adjoin ℂ (Set.range (FreeAlgebra.ι ℂ : L → _))).toSubmodule := by
    rw [FreeAlgebra.adjoin_range_ι]; trivial
  rw [Algebra.adjoin_eq_span] at h1
  obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h1
  have : ∀ x ∈ Submonoid.closure (Set.range (FreeAlgebra.ι ℂ : L → _)),
      ∃ u : List L, (u.map (FreeAlgebra.ι ℂ)).prod = x := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx => obtain ⟨y, rfl⟩ := hx; exact ⟨[y], by simp⟩
    | one => exact ⟨[], by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u ++ v, by simp⟩
  choose u hu using fun i => this _ (g i).2
  exact ⟨m, c, u, by rw [← e]; simp only [hu]⟩

theorem lift_words {L M : Type} [AddCommGroup M] [Module ℂ M] (τ : L → Module.End ℂ M) {m : ℕ} (c : Fin m → ℂ)
    (u : Fin m → List L) (x : M) :
    FreeAlgebra.lift ℂ τ (∑ i, c i • ((u i).map (FreeAlgebra.ι ℂ)).prod) x =
      ∑ i, c i • (u i).foldr (fun y => τ y) x := by
  have : ∀ l : List L, FreeAlgebra.lift ℂ τ (l.map (FreeAlgebra.ι ℂ)).prod x = l.foldr (fun y => τ y) x := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih => rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih]; simp

  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, this]

theorem exists_intertwiner {L V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (ρ : L → Module.End ℂ V) (hρ : ∀ W : Submodule ℂ V, (∀ x, ∀ v ∈ W, ρ x v ∈ W) → W ≠ ⊥ → W = ⊤)
    (τ : L → Module.End ℂ M) {d : ℕ} (w : Fin d → V) (m₀ : M)
    (h : ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), (∀ a, ∑ i, c i • (u i).foldr (fun y => ρ y) (w a) = 0) →
      ∑ i, c i • (u i).foldr (fun y => τ y) m₀ = 0) :
    ∃ T : Fin d → (V →ₗ[ℂ] M), (∀ a v x, T a (ρ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List L), T a v = ∑ i, c i • (u i).foldr (fun y => τ y) m₀ := by
  letI : Module (FreeAlgebra ℂ L) V := Module.compHom V (FreeAlgebra.lift ℂ ρ).toRingHom
  letI : Module (FreeAlgebra ℂ L) M := Module.compHom M (FreeAlgebra.lift ℂ τ).toRingHom
  have eV : ∀ (α : FreeAlgebra ℂ L) (v : V), α • v = FreeAlgebra.lift ℂ ρ α v := fun _ _ => rfl
  have eM : ∀ (α : FreeAlgebra ℂ L) (v : M), α • v = FreeAlgebra.lift ℂ τ α v := fun _ _ => rfl
  have cV : ∀ (c : ℂ) (v : V), algebraMap ℂ (FreeAlgebra ℂ L) c • v = c • v := fun c v => by
    rw [eV, AlgHom.commutes]; rfl
  have cM : ∀ (c : ℂ) (v : M), algebraMap ℂ (FreeAlgebra ℂ L) c • v = c • v := fun c v => by
    rw [eM, AlgHom.commutes]; rfl
  have hs : ∀ N : Submodule (FreeAlgebra ℂ L) V, N = ⊥ ∨ N = ⊤ := by
    intro N
    let W : Submodule ℂ V :=
      { carrier := N
        add_mem' := N.add_mem
        zero_mem' := N.zero_mem
        smul_mem' := fun c v hv => by rw [← cV]; exact N.smul_mem _ hv }
    by_cases h0 : W = ⊥
    · left
      rw [eq_bot_iff] at h0 ⊢
      exact fun v hv => h0 (show v ∈ W from hv)
    · right
      have := hρ W (fun x v hv => by
        have := N.smul_mem (FreeAlgebra.ι ℂ x) hv
        rwa [eV, FreeAlgebra.lift_ι_apply] at this) h0
      rw [eq_top_iff] at this ⊢
      exact fun v _ => (show v ∈ W from this trivial)
  haveI : IsSemisimpleModule (FreeAlgebra ℂ L) V := by
    refine (isSemisimpleModule_iff _ _).2 ⟨fun N => ?_⟩
    rcases hs N with rfl | rfl
    exacts [⟨⊤, isCompl_bot_top⟩, ⟨⊥, isCompl_top_bot⟩]
  obtain ⟨T, h1, h2⟩ := exists_hom_of_ann (R := FreeAlgebra ℂ L) w m₀ (by
    intro α hα
    obtain ⟨m, c, u, rfl⟩ := exists_words α
    rw [eM, lift_words]
    refine h m c u fun a => ?_
    rw [← lift_words, ← eV]
    exact congrFun hα a)
  refine ⟨fun a =>
    { toFun := T a
      map_add' := (T a).map_add
      map_smul' := fun c v => by rw [← cV, map_smul, cM]; rfl }, fun a v x => ?_, h1, fun a v => ?_⟩
  · have := (T a).map_smul (FreeAlgebra.ι ℂ x) v
    rwa [eV, eM, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply] at this
  · obtain ⟨α, hα⟩ := h2 a v
    obtain ⟨m, c, u, rfl⟩ := exists_words α
    exact ⟨m, c, u, hα.trans (by rw [eM, lift_words])⟩

theorem exists_maps_of_relations : GlobalTheory.Published.HarishChandraModules → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Ltr ε → Module.End ℂ M) (m₀ : M),
    (∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE τ (u i) m₀ = 0) →
    ∃ T : Fin d → (H →ₗ[ℂ] M), (∀ a v, IsKFin ε σ v → ∀ x, T a (ltrV σ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), T a v = ∑ i, c i • wordE τ (u i) m₀ := by
  intro hHC n ε H _ _ _ σ hσ d w hw M _ _ τ m₀ h
  have hmem : ∀ (x : Ltr ε) v, IsKFin ε σ v → IsKFin ε σ (ltrV σ x v) := by
    rintro (X | k) v hv
    exacts [isKFin_dRep n ε H σ hσ v hv X.1 X.2, isKFin_translate hv k.2]
  let ρ : Ltr ε → Module.End ℂ (kfin ε σ) := fun x =>
    { toFun := fun v => ⟨ltrV σ x v.1, hmem x v.1 v.2⟩
      map_add' := fun a b => Subtype.ext (by
        rcases x with X | k
        · exact Dw_add hσ.1 (l := [X.1]) (by simpa using X.2) (hσ.2.2.1 _ a.2) (hσ.2.2.1 _ b.2)
        · exact map_add (σ k.1) _ _)
      map_smul' := fun c a => Subtype.ext (by
        rcases x with X | k
        · exact Dw_smul hσ.1 (l := [X.1]) (by simpa using X.2) c (hσ.2.2.1 _ a.2)
        · exact map_smul (σ k.1) _ _) }
  have hword : ∀ (u : List (Ltr ε)) (v : kfin ε σ), (u.foldr (fun y => ρ y) v : kfin ε σ).1 = wordV σ u v.1 := by
    intro u v
    induction u with
    | nil => rfl
    | cons x u ih =>
      show ltrV σ x (u.foldr (fun y => ρ y) v : kfin ε σ).1 = ltrV σ x (wordV σ u v.1)
      rw [ih]
  have hρ : ∀ W : Submodule ℂ (kfin ε σ), (∀ x, ∀ v ∈ W, ρ x v ∈ W) → W ≠ ⊥ → W = ⊤ := by
    intro W hW h0
    have k1 : ∀ v ∈ W.map (kfin ε σ).subtype, IsKFin ε σ v := by
      rintro _ ⟨v, -, rfl⟩; exact v.2
    have k2 : ∀ (x : Ltr ε), ∀ v ∈ W.map (kfin ε σ).subtype, ltrV σ x v ∈ W.map (kfin ε σ).subtype := by
      rintro x _ ⟨v, hv, rfl⟩; exact ⟨ρ x v, hW x v hv, rfl⟩
    have k3 : ∀ k ∈ Kset ε, ∀ v ∈ W.map (kfin ε σ).subtype, σ k v ∈ W.map (kfin ε σ).subtype :=
      fun k hk => k2 (Sum.inr ⟨k, hk⟩)
    have hd := GlobalTheory.HCModIrred.dense_of_stable hHC hσ.1 hσ.2.1 k1 (fun X hX => k2 (Sum.inl ⟨X, hX⟩)) k3
      (fun e => h0 (Submodule.map_injective_of_injective (kfin ε σ).injective_subtype
        (e.trans (Submodule.map_bot _).symm)))
    rw [eq_top_iff]
    intro v _
    obtain ⟨y, hy, e⟩ := GlobalTheory.HCModIrred.mem_of_dense hσ hd k1 k3 v.2
    exact (Subtype.ext e : y = v) ▸ hy
  obtain ⟨T, h1, h2, h3⟩ := exists_intertwiner ρ hρ τ (fun a => (⟨w a, hw a⟩ : kfin ε σ)) m₀ (by
    intro m c u hu
    refine h m c u fun a => ?_
    have := congrArg Subtype.val (hu a)
    simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, hword, Submodule.coe_zero] using this)
  choose T' hT' using fun a => LinearMap.exists_extend (T a)
  have e : ∀ a v (hv : IsKFin ε σ v), T' a v = T a ⟨v, hv⟩ := fun a v hv => LinearMap.congr_fun (hT' a) ⟨v, hv⟩
  refine ⟨T', fun a v hv x => ?_, ?_, fun a v hv => ?_⟩
  · rw [e a _ (hmem x v hv), e a v hv]
    exact h1 a ⟨v, hv⟩ x
  · rw [← h2]
    exact Finset.sum_congr rfl fun a _ => e a _ (hw a)
  · rw [e a v hv]
    exact h3 a _

end GlobalTheory.TypeSum.CoefClos
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology


theorem _root_.GlobalTheory.T.avg_derFam_growth_alt : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) g‖ ≤ C * (1 + hs g) ^ N) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      MeasureTheory.AEStronglyMeasurable (fun k : ↥(Formalism.REAL.KG ε) =>
        F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) (z * Formalism.REAL.toMK k)) (Formalism.REAL.muK ε)) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    GlobalTheory.TypeSum.IsDerFam ε (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
    GlobalTheory.TypeSum.FamGrowth ε N (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  first | exact @GlobalTheory.KAvgDeriv.avg_derFam_growth | exact GlobalTheory.KAvgDeriv.avg_derFam_growth | (intros; apply GlobalTheory.KAvgDeriv.avg_derFam_growth <;> assumption)
end
