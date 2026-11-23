module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle208
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.exists_one_parameter_subgroup_maxCompact_skewHermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb := by
  first | exact @GlobalTheory.CompactLine.exists_line_in_kInf_skew | exact GlobalTheory.CompactLine.exists_line_in_kInf_skew | (intros; apply GlobalTheory.CompactLine.exists_line_in_kInf_skew <;> assumption)
end

section

open Formalism.BasicNotions

namespace GlobalTheory

theorem modelsAreCoverSeries_of_hypotheses :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adelicUnitary_closure_local_components_open : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → (∀ g : GA D V, {p : Place D | ¬ (gAt V p g ∈ U ∧ gAt V p g ∈ GfC V)}.Finite) ∧ Submonoid.closure ({g : GA D V | ∃ p, gAt V p g = g} ∪ {k : GA D V | k ∈ U ∧ k ∈ GfC V ∧ ∀ p, gAt V p k ∈ U ∧ gAt V p k ∈ GfC V}) = ⊤ := by
  first | exact @GlobalTheory.PlaceGen.gen_by_local | exact GlobalTheory.PlaceGen.gen_by_local | (intros; apply GlobalTheory.PlaceGen.gen_by_local <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_max_valuation_ideal_splitPlace_and_conjugate : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) ∧ (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) := by
  first | exact @GlobalTheory.SplitIdealMax.exists_max_both | exact GlobalTheory.SplitIdealMax.exists_max_both | (intros; apply GlobalTheory.SplitIdealMax.exists_max_both <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adelicUnitaryComponentAtPlace_laws : ∀ (D : D7), (∀ (V : HSp D) (p : Place D) (g : GA D V), Formalism.L2.Theta.mt V (gAt V p g) = idem D p • Formalism.L2.Theta.mt V g + (1 - idem D p) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ gAt V p (gAt V p g) = gAt V p g ∧ ∀ q, q ≠ p → gAt V q (gAt V p g) = 1) ∧ ∀ (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (w : WO S T), actO S T (gAt S p g) (gAt T p h) w = idem D p • actO S T g h w + (1 - idem D p) • w ∧ wAt p (actO S T g h w) = actO S T (gAt S p g) (gAt T p h) (wAt p w) := by
  first | exact @GlobalTheory.PlaceComponent.gAt_laws | exact GlobalTheory.PlaceComponent.gAt_laws | (intros; apply GlobalTheory.PlaceComponent.gAt_laws <;> assumption)
end

section


theorem _root_.GlobalTheory.T.typeIdempotent_constantTerm_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish := by
  first | exact @GlobalTheory.TypeConstTerm.typeConstTermVanish | exact GlobalTheory.TypeConstTerm.typeConstTermVanish | (intros; apply GlobalTheory.TypeConstTerm.typeConstTermVanish <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Grid

theorem heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (Z : GlobalTheory.Grid.PlaceDat D), Z.S0 R.Pg = G'.pl.S0 → (∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D) → (∀ w ∈ Z.Wd, Formalism.L2.Host.OverP D.host D.host.pde w ∨ Formalism.L2.Host.OverP D.host D.host.pde' w) → Z.w0 = G'.pl.w G'.pl.v0 → ∀ i, 1 ≤ i → i ≤ D.R.m → Z.IsGridPlaceAuxiliaryHeckeCharacter R.Pg (fun τ => GlobalTheory.Grid.cen D τ i) (G'.ch.chiH i) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hgap hc G' Z hS0 hS1 hwd hw0 i hi1 hi2
  have hcen : ∀ τ, GlobalTheory.Grid.cen D τ i = GlobalTheory.ChiGrid.cen D sc.cGap τ i := by
    intro τ
    rw [hc]
    unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
    rw [hgap]
    rfl
  have hunit : (G'.ch.chiH i).IsUnitary := GlobalTheory.T.heckeChar_isUnitary_of_unitary_infinityType _ _ _ _ (G'.ch.inf i hi1 hi2)
  refine ⟨hunit, G'.ch.triv i hi1 hi2, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun τ => 2 * GlobalTheory.ChiGrid.cen D sc.cGap τ i, fun τ => ?_, G'.ch.inf i hi1 hi2⟩
    show ((2 * GlobalTheory.ChiGrid.cen D sc.cGap τ i : ℤ) : ℚ) = 2 * ((GlobalTheory.Grid.cen D τ i : ℤ) : ℚ)
    rw [hcen τ]; push_cast; ring
  · intro w hw
    rw [hS0] at hw
    exact G'.ch.unr i hi1 hi2 w hw
  · intro w hw
    exact G'.ch.lev1 i hi1 hi2 w (hS1 w hw)
  · intro w hw x hx
    exact G'.ch.wild i hi1 hi2 w (hwd w hw) x hx
  · have hu : Z.w0.under (𝓞 D.host.F) = G'.pl.v0 := by
      rw [hw0]; exact G'.pl.under_w (G'.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
    exact G'.ch.lev0 i hi1 hi2 Z.w0 hu

end GlobalTheory.Grid

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem hT_eq_coords (S : HSp D) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * S.gram i j * S.frame.repr y j := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Formalism.BasicNotions.HSpace.gram]
  ring

theorem hT_cols (S : HSp D) {k l : ℕ} (a : Matrix (Fin S.rank) (Fin k) D.host.E) (b : Matrix (Fin S.rank) (Fin l) D.host.E)
    (q : Fin k) (p : Fin l) :
    S.hT (S.frame.equivFun.symm (fun i => a i q)) (S.frame.equivFun.symm (fun i => b i p)) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) a * S.gram * b) q p := by
  rw [hT_eq_coords]
  have e1 : ∀ v : Fin S.rank → D.host.E, S.frame.repr (S.frame.equivFun.symm v) = v := fun v => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [e1, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem exists_orthogonalSum_testGrid_of_levelChoiceGrid {D : D7} (A B : GlobalTheory.Grid.Node D) {c : ℕ} {ε : D.host.E}
    (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A.V B.V c ε) (𝔟 : Fin c → GlobalTheory.Grid.FrId D) (_hε : ε = 1 ∨ ε = -1)
    (hΛ : B.Λ = d.lat A.Λ 𝔟) :
    ∃ d' : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c, d'.ι = d.ι ∧ d'.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c ε p q) 𝔟 := by
  refine ⟨⟨d.ι, fun p => B.V.frame.equivFun.symm (fun k => d.a k p)⟩, rfl, ?_⟩
  have e1 : ∀ v : Fin B.V.rank → D.host.E, B.V.frame.repr (B.V.frame.equivFun.symm v) = v := fun v => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨d.isom, ?_, ?_, d.rank, ?_⟩
  ·
    intro x p
    show B.V.hT _ (d.ι x) = 0
    conv_lhs => rw [← A.V.frame.sum_repr x]

    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h1 := B.V.herm.eq (d.ι (A.V.frame k)) (B.V.frame.equivFun.symm (fun i => d.a i p))
    have h2 : d.ι (A.V.frame k) = B.V.frame.equivFun.symm (fun i => frameMat B.V A.V d.ι i k) := by
      apply B.V.frame.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      ext i
      simp [frameMat, LinearMap.toMatrix_apply]
    have h3 : B.V.hT (d.ι (A.V.frame k)) (B.V.frame.equivFun.symm (fun i => d.a i p)) = 0 := by
      rw [h2, hT_cols, d.perp]; rfl
    rw [← h1, h3]
    simp
  ·
    intro p q
    show B.V.hT _ _ = _
    rw [hT_cols, d.gram]
    simp only [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix]
    split_ifs <;> first | rfl | (exfalso; omega) | (simp_all [Fin.ext_iff]; omega) | simp_all
  ·
    have key : ∀ (x : A.V.V) (t : Fin c → D.host.E),
        B.V.frame.equivFun (d.ι x + ∑ p, t p • B.V.frame.equivFun.symm (fun k => d.a k p)) =
          frameMat B.V A.V d.ι *ᵥ A.V.frame.equivFun x + d.a *ᵥ t := by
      intro x t

      rw [map_add (f := _), map_sum]
      congr 1
      · simp only [Module.Basis.equivFun_apply, frameMat]
        exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm
      · simp only [map_smul, LinearEquiv.apply_symm_apply]
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    intro y
    show B.V.frame.equivFun y ∈ B.Λ ↔ _
    rw [hΛ]
    constructor
    · rintro ⟨z, hz, u, hu, hy⟩
      refine ⟨A.V.frame.equivFun.symm z, ?_, u, hu, ?_⟩
      · show A.V.frame.equivFun (A.V.frame.equivFun.symm z) ∈ A.Λ
        rwa [LinearEquiv.apply_symm_apply]
      · apply B.V.frame.equivFun.injective
        rw [key, LinearEquiv.apply_symm_apply]
        exact hy
    · rintro ⟨x, hx, t, ht, rfl⟩
      exact ⟨A.V.frame.equivFun x, hx, t, ht, key x t⟩

end GlobalTheory.GridJoin

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

theorem sqrt_intCast_eq_sqrt_toNat (x : ℤ) : Real.sqrt (x : ℝ) = Real.sqrt ((x.toNat : ℕ) : ℝ) := by
  rcases le_or_gt 0 x with h | h
  · rw [show ((x.toNat : ℕ) : ℝ) = (x : ℝ) by exact_mod_cast Int.toNat_of_nonneg h]
  · rw [Real.sqrt_eq_zero'.2 (by exact_mod_cast h.le), Int.toNat_eq_zero.2 h.le]; simp

theorem gap_eq_chiGap : ∀ D : D7, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 := by
  intro D
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hv : ∀ τ : D.what₂.Tau, (GlobalTheory.Grid.gridOf D 0 0 τ).v = (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v := fun _ => rfl
  have hk : ∀ τ : D.what₂.Tau, (GlobalTheory.Grid.gridOf D 0 0 τ).v 2 - (GlobalTheory.Grid.gridOf D 0 0 τ).v D.R.k =
      (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k := fun τ => by rw [hv]
  have hN : (GlobalTheory.Grid.bigN D : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := rfl
  have hN' : GlobalTheory.Grid.bigN D = GlobalTheory.ChiGrid.bigN D := rfl
  have hs : GlobalTheory.Grid.sLen D = GlobalTheory.ChiGrid.sLen D := rfl
  have hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = (D.R.r : ℝ) + 1 := by simp [GlobalTheory.ChiGrid.nRk]
  set f : D.what₂.Tau → ℤ := fun τ => (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k with hf
  have hc : GlobalTheory.ChiGrid.cloudLen D = Finset.univ.sup fun τ => (f τ).toNat := rfl
  have key : ∀ γ : ℕ, GlobalTheory.Grid.GapCond D γ ↔ GlobalTheory.ChiGrid.GapBound D 1 γ := by
    intro γ
    unfold GlobalTheory.Grid.GapCond GlobalTheory.ChiGrid.GapBound
    simp only [one_mul, hk, hn, hN, hN', hs, hc]
    refine and_congr ?_ Iff.rfl
    have hB : (0 : ℝ) ≤ ((D.R.r : ℝ) + 1) ^ 3 := by positivity
    constructor
    · intro h
      obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun τ => (f τ).toNat
      have := h τ
      rw [sqrt_intCast_eq_sqrt_toNat] at this
      rw [hτ]; exact this
    · intro h τ
      rw [sqrt_intCast_eq_sqrt_toNat]
      refine le_trans ?_ h
      have h1 : (f τ).toNat ≤ Finset.univ.sup fun τ => (f τ).toNat := Finset.le_sup (f := fun τ => (f τ).toNat) (Finset.mem_univ τ)
      have h2 : Real.sqrt (((f τ).toNat : ℕ) : ℝ) ≤ Real.sqrt (((Finset.univ.sup fun τ => (f τ).toNat : ℕ)) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast h1)
      nlinarith
  have e : {γ | GlobalTheory.Grid.GapCond D γ} = {g | GlobalTheory.ChiGrid.GapBound D 1 g} := Set.ext fun γ => key γ
  have h1 := GlobalTheory.Grid.isLeast_gap D
  rw [e] at h1
  exact h1.unique (GlobalTheory.ChiGrid.isLeast_gap D 1)

end GlobalTheory.GridJoin
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConvLevel

theorem ccGA_leftInv {D : D7} {V : HSp D} {f : GA D V → ℂ} (hf : f ∈ GlobalTheory.Orb.CcGA V) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ y, f (k * y) = f y := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, -, b, hb, rfl⟩ := hf
    obtain ⟨K, hK, hb'⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨K.comap (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram),
      hK.preimage (GlobalTheory.AdelicU.continuous_projFin _ _), fun k hk hk' y => ?_⟩
    have h1 : GlobalTheory.AdelicU.projInf D.sp.cm.sig V.gram k = 1 := GlobalTheory.AdelicU.mem_finPts.1 hk'
    simp only [GlobalTheory.Orb.infFin, map_mul, h1, one_mul]
    rw [(hb' _ hk _).1]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add f f' _ _ h h' =>
    obtain ⟨U, hU, e⟩ := h
    obtain ⟨U', hU', e'⟩ := h'
    exact ⟨U ⊓ U', hU.inter hU', fun k hk hk' y => by
      simp only [Pi.add_apply, e k hk.1 hk' y, e' k hk.2 hk' y]⟩
  | smul c f _ h =>
    obtain ⟨U, hU, e⟩ := h
    exact ⟨U, hU, fun k hk hk' y => by simp only [Pi.smul_apply, e k hk hk' y]⟩

theorem convR_level : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, ∀ k ∈ U, k ∈ GfC V → ∀ g, GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * k) = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g := by
  intro D V μ _ _ f hf
  obtain ⟨U, hU, e⟩ := ccGA_leftInv hf
  refine ⟨U, hU, fun F k hk hk' g => ?_⟩
  rw [GlobalTheory.AutomorphicL2Unitary.convR_eq, GlobalTheory.AutomorphicL2Unitary.convR_eq]
  congr 1
  funext y
  rw [mul_inv_rev, mul_assoc, e _ (U.inv_mem hk) ((GfC V).inv_mem hk')]

end GlobalTheory.ConvLevel
end

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

theorem _root_.GlobalTheory.T.eventually_exists_doubleCoset_antiInvolution_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L → ∀ᶠ v in cofinite, ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧ ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  first | exact @GlobalTheory.AntiInvLoc.eventually_exists_antiInv | exact GlobalTheory.AntiInvLoc.eventually_exists_antiInv | (intros; apply GlobalTheory.AntiInvLoc.eventually_exists_antiInv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AvgCol

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def frRel (W : G.Weil) {U : Set T} (N : Std G U) (X : Node) (τ : D.what₂.Tau) :
    Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ :=
  (W.onb X τ)⁻¹ * N.frC X τ

def frCh (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => frRel W N (.top (j + 1)) τ) (fun τ => ((frRel W N (.top j) τ)⁻¹)ᵀ)

def frChInv (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => (frRel W N (.top (j + 1)) τ)⁻¹) (fun τ => (frRel W N (.top j) τ)ᵀ)

end GlobalTheory.AvgCol

end
end
