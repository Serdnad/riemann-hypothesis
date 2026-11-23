module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle274
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle275
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle276
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle015
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140

@[expose] public section

section

open GlobalTheory.FunObj

namespace GlobalTheory.ChainSmul

theorem chainTo_update_of_le {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (B : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, n ≤ j₀ → chainTo (Function.update k j₀ B) n = chainTo k n
  | 0, _ => rfl
  | n + 1, h => by
    have hne : n ≠ j₀ := by omega
    show Function.update k j₀ B n ∘ₗ chainTo (Function.update k j₀ B) n = k n ∘ₗ chainTo k n
    rw [Function.update_of_ne hne, chainTo_update_of_le k j₀ B n (by omega)]

theorem chainTo_update_smul {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (c : ℂ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, j₀ < n → chainTo (Function.update k j₀ (c • A)) n = c • chainTo (Function.update k j₀ A) n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    show Function.update k j₀ (c • A) n ∘ₗ chainTo (Function.update k j₀ (c • A)) n =
      c • (Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · have hne : n ≠ j₀ := by omega
      rw [Function.update_of_ne hne, Function.update_of_ne hne, chainTo_update_smul k j₀ c A n h',
        LinearMap.comp_smul]
    · rw [Function.update_self, Function.update_self, chainTo_update_of_le k j₀ _ j₀ le_rfl,
        chainTo_update_of_le k j₀ _ j₀ le_rfl, LinearMap.smul_comp]

end GlobalTheory.ChainSmul
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def pairPts (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  τ.sum fun d a => a • (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
    (S.colMap d x) (S.rowMap d y)

end GlobalTheory.ExpansionInvariance
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConvRDeriv

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem oneP_add' (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (s t : ℝ) :
    oneP θ V τ X (s + t) = oneP θ V τ X s * oneP θ V τ X t := by
  have e : ∀ r : ℝ, NormedSpace.exp (r • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun r =>
    GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX r
  unfold oneP
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (e s) (e t), add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]

theorem leftDeriv (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    starFn (Rder θ V τ X (starFn f)) ∈ CcGA V ∧ ∀ z t, HasDerivAt (fun s => f ((oneP θ V τ X s)⁻¹ * z))
      (starFn (Rder θ V τ X (starFn f)) ((oneP θ V τ X t)⁻¹ * z)) t := by
  have hh : starFn f ∈ CcGA V := starFn_mem_ccAd hf
  have hsm := ccGA_smooth_and_Rder_mem D V θ hθ _ hh
  have hd0 : ∀ w, HasDerivAt (fun t : ℝ => starFn f (w * oneP θ V τ X t)) (Rder θ V τ X (starFn f) w) 0 := fun w =>
    (((isSmoothRealFam_oneP hθ hX).1.contDiff hh w).differentiable (by simp) 0).hasDerivAt
  refine ⟨starFn_mem_ccAd (hsm.2 τ X hX), fun z t => ?_⟩
  have h1 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd0 (z⁻¹ * oneP θ V τ X t))
  have h2 : HasDerivAt (fun s : ℝ => starFn f (z⁻¹ * oneP θ V τ X s)) (Rder θ V τ X (starFn f) (z⁻¹ * oneP θ V τ X t)) t :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
      simp only [mul_assoc, ← oneP_add' hθ hX, add_sub_cancel])
  have h3 := h2.star
  have ef : (fun s => f ((oneP θ V τ X s)⁻¹ * z)) = fun s => star (starFn f (z⁻¹ * oneP θ V τ X s)) := by
    funext s; simp [starFn, mul_inv_rev, Complex.star_def]
  have ev : starFn (Rder θ V τ X (starFn f)) ((oneP θ V τ X t)⁻¹ * z) =
      star (Rder θ V τ X (starFn f) (z⁻¹ * oneP θ V τ X t)) := by
    simp [starFn, mul_inv_rev, Complex.star_def]
  rw [ef, ev]; exact h3

theorem Rder_convR : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}, X ∈ lieAt V τ → ∃ f' ∈ GlobalTheory.Orb.CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, Rder θ V τ X (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) = GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) := by
  intro D V μ _ _ θ hθ f hf τ X hX
  obtain ⟨hf', hD⟩ := leftDeriv hθ hX hf
  set f' := starFn (Rder θ V τ X (starFn f)) with hf'_def
  set u := oneP θ V τ X with hu_def
  have hu := isSmoothRealFam_oneP hθ hX
  have huc : Continuous u := hu.2.1
  have hu0 : u 0 = 1 := hu.2.2
  obtain ⟨hfc, hfs⟩ := continuous_of_mem_ccAd hf
  obtain ⟨hf'c, hf's⟩ := continuous_of_mem_ccAd hf'
  refine ⟨f', hf', ?_, fun F => ?_⟩
  · refine closure_minimal (fun y hy => ?_) (isClosed_tsupport f)
    by_contra hy'
    apply hy
    have ht : Tendsto (fun s : ℝ => (u s)⁻¹ * y) (𝓝 0) (𝓝 y) := by
      simpa [hu0] using ((huc.inv.mul continuous_const).tendsto (f := fun s : ℝ => (u s)⁻¹ * y) 0)
    have hev : (fun s : ℝ => f ((u s)⁻¹ * y)) =ᶠ[𝓝 0] fun _ => 0 :=
      ht.eventually (notMem_tsupport_iff_eventuallyEq.1 hy')
    have h1 := (hD y 0).deriv
    rw [hu0, inv_one, one_mul, hev.deriv_eq, deriv_const] at h1
    exact h1.symm
  · set φ := lift (GQ V) F
    have hφ : LocallyIntegrable φ μ :=
      locallyIntegrable_iff.2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
    funext g
    obtain ⟨M, hM⟩ := hf'c.bounded_above_of_compact_support hf's
    have hK : IsCompact ((fun p : ℝ × GA D V => g * u p.1 * p.2) '' (Metric.closedBall 0 1 ×ˢ tsupport f')) :=
      ((isCompact_closedBall 0 1).prod hf's.isCompact).image (by fun_prop)
    set K := (fun p : ℝ × GA D V => g * u p.1 * p.2) '' (Metric.closedBall 0 1 ×ˢ tsupport f')
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
      (F := fun t y => f ((u t)⁻¹ * (g⁻¹ * y)) * φ y) (F' := fun t y => f' ((u t)⁻¹ * (g⁻¹ * y)) * φ y)
      (bound := K.indicator fun y => M * ‖φ y‖) (s := Metric.closedBall 0 1) (Metric.closedBall_mem_nhds 0 zero_lt_one)
      (.of_forall fun t => (hfc.comp (by fun_prop)).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
      (by simpa [hu0] using (GlobalTheory.AutomorphicL2Local.continuous_integral_inv_mul_of_locallyIntegrable hfc hfs hφ).1 g)
      ((hf'c.comp (by fun_prop)).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
      (.of_forall fun y t ht => ?_)
      ((integrable_indicator_iff hK.measurableSet).2 ((hφ.integrableOn_isCompact hK).norm.const_mul M))
      (.of_forall fun y t _ => (hD (g⁻¹ * y) t).mul_const (φ y))
    · have e1 : (fun t : ℝ => convR μ f φ (g * u t)) = fun t => ∫ y, f ((u t)⁻¹ * (g⁻¹ * y)) * φ y ∂μ := by
        funext t; rw [convR_eq]; simp only [mul_inv_rev, mul_assoc]
      have e2 : convR μ f' φ g = ∫ y, f' ((u 0)⁻¹ * (g⁻¹ * y)) * φ y ∂μ := by
        rw [convR_eq, hu0]; simp
      show deriv (fun t : ℝ => convR μ f φ (g * u t)) 0 = _
      rw [e1, e2]
      exact key.2.deriv
    · by_cases hy : y ∈ K
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport (f := f') fun h => hy ⟨(t, _), ⟨?_, h⟩, ?_⟩]
        · simp
        · exact ht
        · simp [mul_assoc]

end GlobalTheory.ConvRDeriv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → (∀ h ∈ Hecke ℂ (KGL w (n := n)), ∃ c : ℂ, heckeVec ρ (KGL w (n := n)) h x = c • x) → ∃ B, IsSatVecGL w ρ x B ∧ ∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.FinZeta.ParGL.exists_isSatVecGL_bound | exact GlobalTheory.FinZeta.ParGL.exists_isSatVecGL_bound | (intros; apply GlobalTheory.FinZeta.ParGL.exists_isSatVecGL_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaLiftAdjoint_preserves_heckeEigenvectors_matchedPair : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (cX c0 : List ℤ →₀ ℂ), GlobalTheory.Hk3.MatchE R t P cX c0 → ∀ (x : R.HE.H) (l : ℂ), h P c0 x = l • x → h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
  first | exact @GlobalTheory.Hk3.SysE.matched_keeps_eigen | exact GlobalTheory.Hk3.SysE.matched_keeps_eigen | (intros; apply GlobalTheory.Hk3.SysE.matched_keeps_eigen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.discreteSeries_testData_large_gaps_integrable : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D), HostHyp D → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  first | exact @GlobalTheory.DSGapData.dsData_gap_integrable | exact GlobalTheory.DSGapData.dsData_gap_integrable | (intros; apply GlobalTheory.DSGapData.dsData_gap_integrable <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugateModel_unitFrames_eq_movedOrthonormalFrames : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → (∀ a, GlobalTheory.HolRead.IsUnitFr C.X (C.xB (C.mvB a B))) ∧ (∀ y, GlobalTheory.HolRead.IsUnitFr C.X y → ∃ a ∈ GinfC T, C.xB (C.mvB a B) = y) ∧ (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, C.xB (C.mvB a B) = C.xB (C.mvB a' B) → a = a') := by
  first | exact @GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved | exact GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved | (intros; apply GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eq_of_rational_level_invariant_agree_chosen : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (M : ℕ), 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ φ ψ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g) → (∀ k, C.LevK Lv k 1 → ∀ g, φ (g * k) = φ g) → (∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a)) → φ = ψ := by
  first | exact @GlobalTheory.Ker.ExtInv.eq_of_invariant | exact GlobalTheory.Ker.ExtInv.eq_of_invariant | (intros; apply GlobalTheory.Ker.ExtInv.eq_of_invariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.congruenceModPrime_of_polarisationIdealTimesLattice : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (P : Ideal (𝓞 D.host.E)), P.IsPrime → IsAA Λ ΛT → ∀ m : Matrix (Fin k) (Fin k) (AfE D), (∀ u ∈ hatV Λ, m *ᵥ u - u ∈ hatV (P • Λ)) → ∃ b : 𝓞 D.host.E, b ∉ P ∧ ∀ u ∈ hatV ΛT, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (m *ᵥ u - u) ∈ hatV (P • ΛT) := by
  first | exact @GlobalTheory.LevkLoc.congr_of_isAA | exact GlobalTheory.LevkLoc.congr_of_isAA | (intros; apply GlobalTheory.LevkLoc.congr_of_isAA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.latticeTransport_of_polarisationIdealTimesLattice : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)), IsAA Λ ΛT → IsMov m Λ Λ → IsMov m ΛT ΛT := by
  first | exact @GlobalTheory.LevMoveAA.isMov_of_isAA | exact GlobalTheory.LevMoveAA.isMov_of_isAA | (intros; apply GlobalTheory.LevMoveAA.isMov_of_isAA <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitConst

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem isMatch_symm {X X' : Data E r} {a : GL (Fin r) E} (h : IsMatch X X' a) : IsMatch X' X a⁻¹ := by
  have e : ∀ v : Fin r → E, (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact ⟨h.psi.symm, h.p0.symm, h.xi.symm, fun u v => by rw [← h.iso, e, e], fun v => by rw [h.lat, e]⟩

theorem isMatch_trans {X X' X'' : Data E r} {a b : GL (Fin r) E} (h : IsMatch X X' a) (h' : IsMatch X' X'' b) :
    IsMatch X X'' (b * a) :=
  ⟨h.psi.trans h'.psi, h.p0.trans h'.p0, h.xi.trans h'.xi,
    fun u v => by rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h'.iso, h.iso],
    fun v => by rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h'.lat, h.lat]⟩

omit [NumberField E] [IsCMField E] in
theorem lact_cast_lact {Ψ Ψ' Ψ'' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (h' : Ψ' = Ψ'') (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact b (castFr h' (lact a (castFr h x))) = lact (b * a) (castFr (h.trans h') x) := by
  subst h h'
  funext τ
  show (b : Matrix (Fin r) (Fin r) E).map τ.1 * ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((b * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one_cast {Ψ : Finset (E →+* ℂ)} (h : Ψ = Ψ) (x : Frame Ψ r) : lact 1 (castFr h x) = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

variable {U : Formalism.L2.PjFree.Unf Xo c σ r} {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ}

def ExactAt (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) : Prop :=
  ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ),
    ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom,
        Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x))

theorem rdU_eq_of_comp_eq (hE : ∀ k, ExactAt U k) (hs : ρ ≫ Xo.s = Xo.s) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f f' : Rul Xo c} (hf : f ∈ sec Xo c w n) (hf' : f' ∈ sec Xo c w n)
    (hv : ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y')
    {k k' : U.Comp} {δ : GL (Fin r) E} {h : IsMatch (U.X k) (U.X k') δ} (hk : k' = k) (m : MoveMatch U U k k' h ρ ν)
    {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k' (lact δ (castFr h.psi x)) := by
  subst hk
  exact hE _ δ h ρ ν hs m w n hD f hf f' hf' hv x hx

end Free

section Lifts

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts
open GlobalTheory.Member (FinCong)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

section

variable {Dw : Datum H} {l : Level H} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}
  {g g' : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l} {k k' : GA D V}

end


end Lifts

section Main

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts GlobalTheory.GeoLevel GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

theorem one_le_rank (h : LawsJ T) (hj : InR D j) : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
  have hp := h.pins
  rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
  have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
  simp only [Ranks.sigW]; omega


section

set_option synthInstance.maxHeartbeats 400000 in
variable {g : LevGrp T j} {k : GA D (T.V j σ)} {hr : (T.V j σ).rank = D.R.r} {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
  {ρ : LevGrp T j →* (T.cuspA j a n →ₗ[T.Q.c.F] T.cuspA j a n)}


end

end Main

end GlobalTheory.UnitConst
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_fixed_denominator_finiteCoords_integral : ∀ (D : D7), ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x → ∀ k, (d : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  first | exact @GlobalTheory.DenInt.exists_den | exact GlobalTheory.DenInt.exists_den | (intros; apply GlobalTheory.DenInt.exists_den <;> assumption)
end
