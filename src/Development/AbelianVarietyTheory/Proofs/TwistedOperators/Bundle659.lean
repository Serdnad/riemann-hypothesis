module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle651
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiLevelOneCosetAtGoodPlace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle573
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle563
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle213
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle379
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle653
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle652
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle413
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle336
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle414
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle654
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_realComponent_frame_hom_unitaryDiag : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ E : GA D V →* Formalism.REAL.UJ (M.ε τ), ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ := by
  first | exact @GlobalTheory.FibreAtTau.cmp_frame_hom | exact GlobalTheory.FibreAtTau.cmp_frame_hom | (intros; apply GlobalTheory.FibreAtTau.cmp_frame_hom <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.poincareSeries_partialSums_bounded_compact : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (v : ∀ τ, M.H τ), KDecay M v → Nonempty D.what₂.Tau → ∀ (c : GA D V) (a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (Kc : Set (GA D V)), IsCompact Kc → ∃ B : ℝ, ∀ x ∈ Kc, ∀ s : Finset (GQ V), ∑ γ ∈ s, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * x)‖ ≤ B := by
  first | exact @GlobalTheory.PoinAut.partialSum_bdd | exact GlobalTheory.PoinAut.partialSum_bdd | (intros; apply GlobalTheory.PoinAut.partialSum_bdd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.PoinDer

variable {D : D7}

theorem termBound (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ) (hv : KDecay M v) (b : ∀ τ, M.H τ)
    (hb : ∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ :=
  GlobalTheory.T.norm_levelIndicatorCoefficientTest_le_decay D θ hθ V S M K v hv b hb

theorem sumBound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ →
    ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) →
    (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) →
    (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V,
    Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A :=
  GlobalTheory.T.coefficientPoincareSeries_summable_majorant

theorem termDeriv (hHC : GlobalTheory.Published.HarishChandraModules) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ)
    (τ : D.what₂.Tau) (hb : b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (x : GA D V) :
    HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s))
      (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 :=
  GlobalTheory.T.hasDerivAt_levelIndicatorCoefficientTest_oneParam D hHC θ hθ V S M K v b τ hb X hX x

theorem onePDecay (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : GA D V) (t : ℝ), |t| < 1 →
      ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤ L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ :=
  GlobalTheory.T.decayWeight_oneParamTranslate_le_const_mul D θ hθ V τ X hX N

theorem finE_mul_oneP (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (x : GA D V) (t : ℝ) :
    Lev.finE V (x * oneP θ V τ X t) = Lev.finE V x := by
  have h : finHom V (oneP θ V τ X t) = 1 := GlobalTheory.PointAtPlaceHom.atTau_mem V τ _
  show (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) (x * oneP θ V τ X t) = (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) x
  rw [map_mul, MonoidHom.comp_apply (Formalism.UG.bc (Lev.swapAE D)) (finHom V) (oneP θ V τ X t), h, map_one, mul_one]

theorem poin_smooth_growth_deriv : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ UnifModGrowth V θ (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (w : M.H τ) = dRep (M.rep τ) X (a τ) → (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ' => Function.update a τ w τ') = Rder θ V τ X (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c a
  obtain ⟨C₀, A, hB⟩ := sumBound D θ hθ V Λ hΛ 𝔪 c
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK

  have hsum : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, ∀ g,
      Summable (fun γ : GQ V => ‖coef θ M K v b (c * (γ : GA D V) * g)‖) ∧
      ∑' γ : GQ V, ‖coef θ M K v b (c * (γ : GA D V) * g)‖ ≤ C * height V g ^ A := by
    intro b hb
    obtain ⟨C, hC0, hC⟩ := termBound θ hθ M K v hv b hb
    refine ⟨C * C₀, fun g => ?_⟩
    refine hB (fun x => ‖coef θ M K v b x‖) C (fun _ => norm_nonneg _) (fun x hx => ?_) hC g
    simp only [coef, if_neg hx, norm_zero]
  have grow : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ModGrowthExp V A (poin θ M K v c b) := by
    intro b hb
    obtain ⟨C, hC⟩ := hsum b hb
    exact ⟨C, fun g => (norm_tsum_le_tsum_norm (hC g).1).trans (hC g).2⟩

  have der : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∀ τ, ∀ X ∈ lieAt V τ, ∀ g,
      HasDerivAt (fun t : ℝ => poin θ M K v c b (g * oneP θ V τ X t))
        (poin θ M K v c (Function.update b τ (dRep (M.rep τ) X (b τ))) g) 0 := by
    intro b hb τ X hX g
    set b' := Function.update b τ (dRep (M.rep τ) X (b τ)) with hb'd
    have hb' : ∀ τ', b' τ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ' := by
      intro τ'
      by_cases h : τ' = τ
      · subst h
        rw [hb'd, Function.update_self]
        exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M τ' hX (hb τ')
      · rw [hb'd, Function.update_of_ne h]
        exact hb τ'
    obtain ⟨C', hC'0, hC'⟩ := termBound θ hθ M K v hv b' hb'
    obtain ⟨L, hL0, hL⟩ := onePDecay θ hθ V τ hX (2 * V.rank ^ 2 + 1)
    set u : GA D V → ℝ := fun x => if Lev.finE V x ∈ K then C' * L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ else 0
      with hu
    have hprod : ∀ x : GA D V, 0 ≤ ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x =>
      Finset.prod_nonneg fun τ' _ => inv_nonneg.2 (pow_nonneg (by unfold hsn; positivity) _)
    have hu0 : ∀ x, 0 ≤ u x := fun x => by
      simp only [hu]; split_ifs
      · exact mul_nonneg (mul_nonneg hC'0 hL0) (hprod x)
      · exact le_rfl
    have huK : ∀ x, Lev.finE V x ∉ K → u x = 0 := fun x hx => by simp only [hu, if_neg hx]
    have huC : ∀ x, u x ≤ (C' * L) * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x => by
      simp only [hu]; split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg hC'0 hL0) (hprod x)
    have hbd : ∀ (x : GA D V) (y : ℝ), y ∈ Set.Ioo (-1 : ℝ) 1 → ‖coef θ M K v b' (x * oneP θ V τ X y)‖ ≤ u x := by
      intro x y hy
      by_cases hx : Lev.finE V x ∈ K
      · have h1 := hC' (x * oneP θ V τ X y)
        have h2 := hL x y (abs_lt.2 ⟨hy.1, hy.2⟩)
        simp only [hu, if_pos hx]
        calc _ ≤ _ := h1
          _ ≤ C' * (L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) := mul_le_mul_of_nonneg_left h2 hC'0
          _ = _ := by ring
      · have : coef θ M K v b' (x * oneP θ V τ X y) = 0 := by
          simp only [coef, finE_mul_oneP, if_neg hx]
        rw [this, norm_zero]
        exact hu0 x
    have hS := (hB u (C' * L) hu0 huK huC g).1
    obtain ⟨Cb, hCb⟩ := hsum b hb
    have key := hasDerivAt_tsum_of_isPreconnected (g := fun (γ : GQ V) (s : ℝ) => coef θ M K v b (c * (γ : GA D V) * g * oneP θ V τ X s))
      (g' := fun (γ : GQ V) (s : ℝ) => coef θ M K v b' (c * (γ : GA D V) * g * oneP θ V τ X s)) (t := Set.Ioo (-1 : ℝ) 1)
      (y₀ := 0) (y := 0) hS isOpen_Ioo isPreconnected_Ioo
      (fun γ y _ => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun x => termDeriv hHC θ hθ M K v b τ (hb τ) hX x) _ y)
      (fun γ y hy => hbd _ y hy) (by norm_num)
      (by simpa [GlobalTheory.Mem.Lift.oneP_zero hθ] using (hCb g).1.of_norm) (by norm_num)
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
    refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [poin, mul_assoc]
  refine ⟨?_, ⟨A, fun l hl => ?_⟩, ?_⟩
  ·
    refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V
      {φ | ∃ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) ∧ φ = poin θ M K v c b} ?_ ?_ _ ⟨_, fun τ => (a τ).2, rfl⟩
    · rintro φ ⟨b, hb, rfl⟩
      exact (((GlobalTheory.T.coefficientPoincareSeries_isAutomorphic D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c).1 fun τ => ⟨b τ, hb τ⟩).1).cont
    · rintro φ ⟨b, hb, rfl⟩ τ X hX
      refine ⟨_, ⟨Function.update b τ (dRep (M.rep τ) X (b τ)), fun τ' => ?_, rfl⟩, der b hb τ X hX⟩
      by_cases h : τ' = τ
      · subst h
        rw [Function.update_self]
        exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M τ' hX (hb τ')
      · rw [Function.update_of_ne h]
        exact hb τ'
  ·
    have claim : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∃ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) ∧
          l.foldr (fun p f => Rder θ V p.1 p.2 f) (poin θ M K v c fun τ => a τ) = poin θ M K v c b := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨fun τ => a τ, fun τ => (a τ).2, rfl⟩
      | cons p l ih =>
        intro hl'
        obtain ⟨b, hb, e⟩ := ih fun q hq => hl' q (List.mem_cons_of_mem _ hq)
        have hX : p.2 ∈ lieAt V p.1 := hl' p List.mem_cons_self
        refine ⟨Function.update b p.1 (dRep (M.rep p.1) p.2 (b p.1)), fun τ' => ?_, ?_⟩
        · by_cases h : τ' = p.1
          · rw [h, Function.update_self]
            exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M p.1 hX (hb p.1)
          · rw [Function.update_of_ne h]
            exact hb τ'
        · rw [List.foldr_cons, e]
          funext g
          exact (der b hb p.1 p.2 hX g).deriv
    obtain ⟨b, hb, e⟩ := claim l hl
    rw [e]
    exact grow b hb
  ·
    intro τ X hX w hw
    funext g
    have e : (fun τ' => (Function.update a τ w τ' : M.H τ')) =
        Function.update (fun τ' => (a τ' : M.H τ')) τ (dRep (M.rep τ) X (a τ)) := by
      funext τ'
      by_cases h : τ' = τ
      · subst h
        simp [hw]
      · simp [Function.update_of_ne h]
    rw [e]
    exact ((der (fun τ' => a τ') (fun τ' => (a τ').2) τ X hX g).deriv).symm

end GlobalTheory.PoinDer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.psi_primitive_standardFrames_besselLevel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, PrimAt W.ψ (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) v := by
  first | exact @GlobalTheory.AscFin.primAt_std_bessel | exact GlobalTheory.AscFin.primAt_std_bessel | (intros; apply GlobalTheory.AscFin.primAt_std_bessel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.fourierJacobiLevel_oneCoset_at_goodPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ A L : HSp D) (σ : ℕ) (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ) (o : OrthDec W₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (p : Pieces V₀ W W₀ (σ + 1) σ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (LA : Lat A) (LL : Lat L) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xLast dW (vecB o ζ)) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → IsSelfDualC A LA → IsSelfDualC L LL → OrthAt o LW₀ LA LL v → ∀ h ∈ grpAt W (· = v), Cond dW p (xLast dW (vecB o ζ)) 0 ψ (· = v) h → CosetAt W (Rgrp W (xLast dW (vecB o ζ))) LW v h := by
  first | exact @GlobalTheory.AscFin.OneCosetFJ.oneCoset_good | exact GlobalTheory.AscFin.OneCosetFJ.oneCoset_good | (intros; apply GlobalTheory.AscFin.OneCosetFJ.oneCoset_good <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)
open scoped ComplexOrder

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

open GlobalTheory.Grid (neg neg_gram sigOK_sgn isCartanInv_sgn)

theorem exists_stdRig (n : ℕ) : ∃ (V : HSp D) (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V), V.rank = n ∧ V.SigOK ∧ r.IsStd ∧ r.Is := by
  let V : HSp D := Formalism.BasicNotions.Examples₂.posSpace Formalism.BasicNotions.Examples₂.star_isIntegral n
  have hg : V.gram = 1 := by
    change (Formalism.BasicNotions.Examples₂.stdSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0).gram = (1 : Matrix (Fin n) (Fin n) D.host.E)
    ext i j
    change Fin n at i j
    change (Formalism.BasicNotions.Examples₂.stdSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0).gram i j = (if i = j then 1 else 0)
    simpa [Formalism.BasicNotions.Examples₂.sgn] using
      (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0 i j)
  let Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)
  have hmem : ∀ y, y ∈ Λ ↔ ∀ i, IsIntegral ℤ (y i) := fun y => by
    simp only [Λ, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨y i, h⟩, rfl⟩⟩
  have hsingle : ∀ i, (Pi.single i 1 : Fin V.rank → D.host.E) ∈ Λ := fun i => (hmem _).2 fun k => by
    by_cases h : k = i
    · subst h; simpa using isIntegral_one
    · simpa [h] using isIntegral_zero
  have hsd : IsSelfDualC V Λ := by
    refine ⟨Submodule.IsLattice.of_fg D.host.E (Submodule.fg_pi fun _ => ?_), fun y => ⟨fun hy x hx => ?_, fun h => (hmem y).2 fun i => ?_⟩⟩
    · rw [Submodule.one_eq_span]
      exact Submodule.fg_span (Set.finite_singleton _)
    · have hs : IsIntegral ℤ (∑ a, ∑ b, star (x a) * V.gram a b * y b) := by
        rw [hg]
        refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_
        by_cases hab : a = b
        · subst hab
          simpa using (Formalism.BasicNotions.Examples₂.star_isIntegral _ ((hmem x).1 hx a)).mul ((hmem y).1 hy a)
        · simpa [Matrix.one_apply, hab] using isIntegral_zero
      exact ⟨⟨_, hs⟩, rfl⟩
    · obtain ⟨b, hb⟩ := h _ (hsingle i)
      have e : ∑ a, ∑ c, star ((Pi.single i 1 : Fin V.rank → D.host.E) a) * V.gram a c * y c = y i := by
        rw [hg, Finset.sum_eq_single i]
        · simp [Matrix.one_apply]
        · intro a _ ha
          simp [ha]
        · simp
      rw [e] at hb
      exact hb ▸ b.isIntegral_coe
  obtain ⟨r, hr, hri⟩ := GlobalTheory.T.self_dual_lattice_has_rigidification D V Λ (Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n) hsd
  have hgt : ∀ τ, gramAt D V τ = 1 := fun τ => by rw [gramAt, hg]; simp
  refine ⟨V, ⟨Λ, r.β, fun _ => 1, fun _ => 1⟩, rfl, Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n,
    ⟨hg, fun y => (hmem y).trans (forall_congr' fun i => ⟨fun h => ⟨⟨y i, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩),
      fun _ => ⟨rfl, rfl⟩⟩, hsd, hr ▸ hri.2.1, fun τ => ⟨?_, V.rank, ?_⟩⟩
  · rw [hgt]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  · rw [hgt]
    refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩ <;> simp

theorem bottom_chars {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i j : Fin D.R.m) (t : T) :
    IsHeckeChar D (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) ∧
      IsHeckeChar D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) ∧
      ResEta D (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) (SqNum.botSmall D i j) ∧
      ResEta D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (SqNum.botBig D i j) := by
  have hmul : ∀ {χ η : (AE D)ˣ →* Circle}, IsHeckeChar D χ → IsHeckeChar D η → IsHeckeChar D (χ * η) := fun h1 h2 =>
    ⟨h1.1.mul h2.1, fun x => by rw [MonoidHom.mul_apply, h1.2, h2.2, mul_one]⟩
  have heta : IsHeckeChar D L.eta := hL.eta.1
  have hpow : ∀ n, IsHeckeChar D (L.eta ^ n) := fun n =>
    ⟨heta.1.pow n, fun x => by rw [MonoidHom.pow_apply, heta.2, one_pow]⟩
  have hi := i.2
  have hchiE := G.ch.chi_eq (D.R.m - i) (by omega) (by omega)
  have rpow : ∀ n, ResEta D (L.eta ^ n) n := fun n => by
    induction n with
    | zero => exact ⟨(GlobalTheory.HeckeCharacterRestriction.resEta_eta hL).1, fun η _ a => by simp⟩
    | succ n ih => rw [pow_succ]; exact resEta_mul ih (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL)
  have rchi : ResEta D (G.ch.chi (D.R.m - i)) 0 := ⟨(GlobalTheory.HeckeCharacterRestriction.resEta_eta hL).1, fun η _ a => by
    rw [pow_zero]; exact GlobalTheory.GridWeil.triv_base hchiE (G.ch.triv _ (by omega) (by omega)) a⟩
  obtain ⟨h1, h2, h3⟩ := SqNum.ranks_exact D i j
  refine ⟨hmul (GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j) (hpow _), hmul hchiE.1 (hpow _),
    resEta_parity (resEta_mul (GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j) (rpow _)) ?_,
    resEta_parity (resEta_mul rchi (rpow _)) ?_⟩ <;> omega

theorem isSelfDualC_neg' {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (h : IsSelfDualC A Λ) :
    IsSelfDualC (neg A) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [neg_gram, hc]
  · simp [neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

theorem exists_bottomTri {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (W : G.Weil) (i j : Fin D.R.m) :
    ∃ (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X := by
  obtain ⟨A, rA, hA1, hA2, hA3, hA4⟩ := exists_stdRig (D := D) (SqNum.botBig D i j)
  obtain ⟨A', rA', hB1, hB2, hB3, hB4⟩ := exists_stdRig (D := D) (SqNum.botSmall D i j)
  obtain ⟨WW, rW, hW1, hW2, hW3, hW4⟩ := exists_stdRig (D := D) (SqNum.botBig D i j + SqNum.botSmall D i j)
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hc := fun t => bottom_chars hL G i j t
  have hd : ∀ {χ η : (AE D)ˣ →* Circle}, IsHeckeChar D χ → IsHeckeChar D η → IsHeckeChar D (χ / η) := fun h1 h2 =>
    ⟨h1.1.div' h2.1, fun x => by rw [MonoidHom.div_apply, h1.2, h2.2, div_one]⟩
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true A WW (hc t).2.1 (hd (hc t).2.1 (hc t).1)
    (hA1 ▸ (hc t).2.2.2) (by rw [hW1, div_eq_mul_inv]; exact resEta_mul (hc t).2.2.2 (resEta_inv (hc t).2.2.1))
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false A' WW (hc t).1 (hd (hc t).1 (hc t).2.1)
    (hB1 ▸ (hc t).2.2.1) (by rw [hW1, div_eq_mul_inv, Nat.add_comm (SqNum.botBig D i j)]; exact resEta_mul (hc t).2.2.1 (resEta_inv (hc t).2.2.2))
  have s1 : (neg A).SigOK := sigOK_sgn true hA2
  obtain ⟨vac, hv⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (neg A) WW (fun τ => -rA.s τ) rW.s
    s1 hW2 (fun τ => isCartanInv_sgn true _ τ (hA4.2.2 τ).1) (fun τ => (hW4.2.2 τ).1) rA.Λ rW.Λ (isSelfDualC_neg' hA4.1) hW4.1
  obtain ⟨vac', hv'⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ A' WW rA'.s rW.s
    hB2 hW2 (fun τ => (hB4.2.2 τ).1) (fun τ => (hW4.2.2 τ).1) rA'.Λ rW.Λ hB4.1 hW4.1
  choose e he using GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G
  choose c hc' using fun t w => GlobalTheory.ConstRatio.exists_expAt (SqNum.nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D W.ψ W.θ A WW rA rW _ _ _ _ _ hA4 hW4 (hd (hc t).1 (hc t).2.1) (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    GlobalTheory.T.exists_thetaFunction_standardPairSecond D W.ψ W.θ A' WW rA' rW _ _ _ _ A.rank _ hB4 hW4 (hd (hc t).1 (hc t).2.1) (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas A
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas A'
  exact ⟨A, A', WW, ⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩, hA1, hB1, hA3, hB3, hW3,
    ⟨by rw [hA1, hB1, hW1], hA4, hB4, hW4, hω, hω', hv, hv', he, fun t w _ => hc' t w, hf, hf', hm, hm'⟩⟩

theorem IsBottomTri.integrable {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) :
    (∀ P g, IntegrableOn (X.ker W.ψ W.θ t P g) X.fd X.m) ∧ ∀ P g, IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m' := by
  have h := hX.is
  have hA := GlobalTheory.ConstRatio.posDef_of_std hX.std
  have hA' := GlobalTheory.ConstRatio.posDef_of_std hX.std'
  refine ⟨fun P g => ?_, fun P g => ?_⟩
  · exact (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ true A WW _ _ (X.ω t) X.m X.fd _ (h.weil t) hA h.meas.1 h.meas.2
      (GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f h t).1 P)).1 g
  · exact (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (h.weil' t) hA' h.meas'.1 h.meas'.2
      (GlobalTheory.Chain.InnerSteps.theta_pureTensorO h.isVac'.1 h.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f h t).2 P)).1 g

end GlobalTheory.RowTest

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.commutantPart_chosenPlaces_mem_completedLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ w ∈ Ann ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → e • w ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True := by
  first | exact @GlobalTheory.AnnPart.part_mem_latO | exact GlobalTheory.AnnPart.part_mem_latO | (intros; apply GlobalTheory.AnnPart.part_mem_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_nonzero_real_intertwiner_grid_arrow : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V) (f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f → ∃ It : GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j) →ₗ[ℂ] SmT (G.V i j).M →ₗ[ℂ] SmT (G.V (i + 1) j).M, IsItW R.θ (G.V (i + 1) j).M (G.V i j).M ω (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) It := by
  first | exact @GlobalTheory.GridJoin.ArrX.exists_intertwiner | exact GlobalTheory.GridJoin.ArrX.exists_intertwiner | (intros; apply GlobalTheory.GridJoin.ArrX.exists_intertwiner <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_downArrow_realIntertwiner_with_adjoint : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V) (f : WO (G.P (i + 1)).V (G.P i).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f → ∃ (It : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ[ℂ] SmT (G.P (i + 1)).M →ₗ[ℂ] SmT (G.P i).M) (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), GlobalTheory.Grid.IsIntw R.θ (G.P i).M (G.P (i + 1)).M ω.swap (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f) It ∧ (⟨ω, f, It⟩ : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i)).IsAdj U := by
  first | exact @GlobalTheory.DownArrow.down_intertwiner_adj | exact GlobalTheory.DownArrow.down_intertwiner_adj | (intros; apply GlobalTheory.DownArrow.down_intertwiner_adj <;> assumption)
end
