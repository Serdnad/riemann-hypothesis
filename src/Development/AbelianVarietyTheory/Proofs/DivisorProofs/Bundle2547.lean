module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle359
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2541
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem good_of_isAbelianScheme : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R]
    [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Good A.hom := by
  intro HC HH R _ _ A _ g hA hg
  have hs : Smooth A.hom := hA.smooth
  have hp : IsProper A.hom := hA.proper
  have hsep : IsSeparated A.hom := inferInstance
  have hqc : QuasiCompact A.hom := inferInstance
  have bij := HC.bijective_cechDeRhamComparison_degreeOne A.hom hs hsep hqc
  obtain ⟨-, -, ⟨-, hproj, -⟩, -, ⟨hcl, hinj, -⟩, -⟩ := HH R A g hA hg
  have key : ∀ f : Form A.hom, cmp1 A.hom (Form.cl A.hom f) = clForm A.hom (cmpForm A.hom f) :=
    comparison_formClass A.hom
  refine ⟨GlobalTheory.T.globalFunctionsAreConstant_abelianScheme_noetherian R A hA, GlobalTheory.T.abelianScheme_differentials_from_globalForms HC HH R A g hA hg, hproj, fun w ↦ ?_, fun f ↦ ?_⟩
  · have hw : w ∈ ClosedForm A.hom := hcl ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := bij.2 (clForm A.hom ⟨w, hw⟩)
    have h1 : clForm A.hom ⟨w, hw⟩ ∈ CechHodgeFiltration A.hom := (cechHodgeFiltration_eq_range A.hom).symm ▸ ⟨_, rfl⟩
    have h2 : c ∈ F1 A.hom := by
      change toH1O A.hom c = 0
      apply cmpO_injective R A.left A.hom
      rw [← structureSheaf_comparison_comm, hc, map_zero]
      exact h1
    rw [hodgeFiltration_eq_range] at h2
    obtain ⟨f, rfl⟩ := h2
    refine ⟨f, ?_⟩
    have := hinj ((key f).symm.trans hc)
    exact congrArg Subtype.val this
  · constructor
    · intro h
      apply hinj
      rw [← key, h, map_zero, map_zero]
    · intro h
      apply bij.1
      rw [key, h, map_zero, map_zero]

end GlobalTheory.LiftSys
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  first | exact @GlobalTheory.BotFrames.move_fst | exact GlobalTheory.BotFrames.move_fst | (intros; apply GlobalTheory.BotFrames.move_fst <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteBottomTriple_constants_eq_of_same_lattices : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    X.rA = Y.rA → X.rA' = Y.rA' → X.rW = Y.rW → ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  first | exact @GlobalTheory.BotSameRig.const_of_sameRig | exact GlobalTheory.BotSameRig.const_of_sameRig | (intros; apply GlobalTheory.BotSameRig.const_of_sameRig <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.continuous_transport_weil_datum_cm_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsContOn (adeleClass F) om := by
  first | exact @GlobalTheory.WeilContF.continuous_transportF | exact GlobalTheory.WeilContF.continuous_transportF | (intros; apply GlobalTheory.WeilContF.continuous_transportF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigRoute

theorem modGrowth_integral_norm_kerBig {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) :
    GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := by
  obtain ⟨ε, ω, χ, χ', Φ, C₀, hω, hΦ, hb⟩ := GlobalTheory.T.bigRoute_kernel_norm_le_const_mul_thetaKernel (G := G) hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  obtain ⟨p, hsig, hrk⟩ := GlobalTheory.T.squareThetaTriple_exists_signature_rank_sum_lt W t i j hT M hM
  have hHF : GlobalTheory.SquareComm.IsHaarFD _ (M.ν (.grid (i + 1) (j + 1))) (M.fd (.grid (i + 1) (j + 1))) :=
    (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨N, Cw, hMI⟩ := hWC D W.ψ W.θ W.θ_is ε _ _ χ χ' ω hω p hsig hrk _ _ hHF Φ hΦ
  obtain ⟨Cc, hCc, hcmp⟩ := GlobalTheory.Grow.height_comparison (G.V (.grid i (j + 1))) W.θ_is
  set h₁ : ℝ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ g₁ : ℝ)
  refine ⟨max C₀ 0 * (max Cw 0 * (Cc * h₁) ^ N), N, fun g => ?_⟩
  have hI := (hMI (GlobalTheory.SquareComm.blk _ _ (g, g₁))).1
  have hle := (hMI (GlobalTheory.SquareComm.blk _ _ (g, g₁))).2
  have hpos : 0 ≤ ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_of_nonneg hpos]
  have h1 : ∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) ≤
      ∫ u in M.fd (.grid (i + 1) (j + 1)), max C₀ 0 * ‖thetaKO ω u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) Φ‖ ∂M.ν (.grid (i + 1) (j + 1)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hI.norm.const_mul _)
      (Filter.Eventually.of_forall fun u => (hb g u).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  rw [integral_const_mul] at h1
  have hX := GlobalTheory.T.unitaryAdelicHeight_orthogonalSum_embedding_le_mul D W.θ _ _ g g₁
  have hXg : ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ≤
      Cc * GlobalTheory.Grow.height _ g * h₁ := by
    have := (hcmp g).1
    calc _ ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ g : ℝ) * h₁ := by exact_mod_cast hX
      _ ≤ _ := mul_le_mul_of_nonneg_right this (NNReal.coe_nonneg _)
  have h0 : (0 : ℝ) ≤ ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) := NNReal.coe_nonneg _
  have h2 : ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ^ N ≤
      (Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 (hXg.trans_eq (by ring)) N
  have h3 : Cw * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height W.θ _ (GlobalTheory.SquareComm.blk _ _ (g, g₁)) : NNReal) : ℝ) ^ N ≤
      max Cw 0 * ((Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 _)).trans
      (mul_le_mul_of_nonneg_left h2 (le_max_right _ _))
  calc _ ≤ _ := h1
    _ ≤ max C₀ 0 * (max Cw 0 * ((Cc * h₁) ^ N * GlobalTheory.Grow.height _ g ^ N)) :=
      mul_le_mul_of_nonneg_left (hle.trans h3) (le_max_right _ _)
    _ = _ := by ring

end GlobalTheory.BigRoute
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

theorem _root_.GlobalTheory.T.exists_satakeParameters_const_one_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∃ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par := by
  first | exact @GlobalTheory.BottomIPData.isParamFun_one_bottom | exact GlobalTheory.BottomIPData.isParamFun_one_bottom | (intros; apply GlobalTheory.BottomIPData.isParamFun_one_bottom <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitsCompletely_typePrime (D : D7) (k : Fin 2) : SplitsCompletely D.host.E (D.host.g k) := by
  refine ⟨D.host.g_prime k, ?_⟩
  have hg0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  have h := D.nd.g_split k
  rw [← h]
  have : {P : Ideal (𝓞 D.host.E) | P.IsPrime ∧ ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P} =
      (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.asIdeal) '' {v : HeightOneSpectrum (𝓞 D.host.E) | ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal} := by
    ext P
    constructor
    · rintro ⟨hP, hg⟩
      have hne : P ≠ ⊥ := fun h0 => hg0 (by rw [h0] at hg; simpa using hg)
      exact ⟨⟨P, hP, hne⟩, hg, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, hv⟩
  rw [this, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem half_le_plGw (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (k : Fin 2) (v : D.nd.PlG k) :
    p.T.Q.l.Mb ≤ (D.naut.plGw k v).asIdeal := by
  rw [h.half]
  obtain ⟨plg, -, hplg, -, -, -⟩ := p.grpRecPin
  have hmem : D.naut.plGw k v ∈ (R2 p).Pg := by
    rw [← hplg ⟨k, v⟩]
    exact (plg ⟨k, v⟩).2
  exact (Ideal.prod_le_inf).trans (Finset.inf_le hmem)

theorem levelCondition_restrict_of_halfUnipotent (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type} [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r) (hg : ∀ k : Fin 2, 3 * D.R.r < D.host.g k)
    (hM : RunModel p r h i M ka) : ∀ H : Subgroup p.P.Gp, HalfUnip p H → LevelHyp (sub M H) := by
  intro H hH
  obtain ⟨k, hk⟩ := hH
  obtain ⟨v0, e, -, -, -, hd1, φ, hd2⟩ := hM
  refine ⟨D.host.g k, splitsCompletely_typePrime D k, hg k, ?_⟩
  intro c β hβ P hP hgP
  obtain ⟨u, huc, γ, hγ, rfl⟩ := hβ
  have huc' : (u : p.P.Gp) • c = c := huc
  have hγL : ∀ w, w ∈ (M.comp c).L' ↔ Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L' :=
    M.Γ_L' c γ hγ
  have htL : ∀ w, w ∈ (M.comp c).L' ↔
      Matrix.mulVec (M.tr u c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L' := by
    intro w
    have := M.tr_L' u c w
    rwa [huc'] at this
  have half : ∀ v : D.nd.PlG k, ∀ w ∈ (M.comp c).L',
      Matrix.mulVec ((((γ * M.tr u c : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) - 1) ^ D.R.r) w ∈
        (D.naut.plGw k v).asIdeal • (M.comp c).L' := by
    intro v w hw
    obtain ⟨n, hn⟩ := hd2 c u huc'
    rw [Units.val_mul]
    exact GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half _ _ _ (half_le_plGw p r h k v) (φ c) (r.lev i u) n (GlobalTheory.T.levelChange_unitriangular_unipotent_modPlace p r h i u k v (hk u u.2 v)) _ _ (fun w hw => (hγL w).1 hw)
      (hd1 c γ hγ) hn w hw
  obtain ⟨v, rfl | rfl⟩ := GlobalTheory.T.prime_over_typePrime_fixedPlace_or_conj D k P hP hgP
  · exact half v
  · refine GlobalTheory.T.unitary_unipotent_mod_ideal_mod_conjIdeal (M.comp c) (γ * M.tr u c) ?_ ?_ _ (half v)
    · intro a b
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ((M.comp c).Γ_stab γ hγ).1, M.comp_Gm c, M.tr_herm]
    · intro a
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (htL a).trans (hγL _)

end GlobalTheory.ShareOn

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.central_uniformiser_acts_by_dilation_tame_kernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∃ κ : ℂ, UnitOff N κ ∧ ∀ Tm, IsModel R i eQ fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (lattice₂ R i) Ψ → ω (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (dil i (ϖ : D.host.E)⁻¹ x)) := by
  first | exact @GlobalTheory.BaseCmp.dilKer_of_ne_zero | exact GlobalTheory.BaseCmp.dilKer_of_ne_zero | (intros; apply GlobalTheory.BaseCmp.dilKer_of_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



theorem _root_.GlobalTheory.T.lift_datum_conjugate_half_finite_fourier_sum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → (∀ PP ∈ Q, ξR PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∃ (Y : Finset (WO (Vc D i) (Wc D i))) (a : WO (Vc D i) (Wc D i) → ℂ) (Gc : ℂ), UnitOff N Gc ∧ (∀ y ∈ Y, IsHalf eQ y) ∧
      (∀ t, (if IsHalf (cA D eQ) t ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t)) else 0) =
        halfInd (cA D eQ) (lattice₂ R i) t * ∑ y ∈ Y, a y * R.ψ (symplO (Vc D i) (Wc D i) t y)) ∧
      ∀ t, ∑ y ∈ Y, a y * halfInd eQ (lattice₂ R i) (t + y) = Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) t) := by
  first | exact @GlobalTheory.LiftFour.datum_conj_half_fourier | exact GlobalTheory.LiftFour.datum_conj_half_fourier | (intros; apply GlobalTheory.LiftFour.datum_conj_half_fourier <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.transportedWeilDatum_doubledTarget_restrict_boxTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ωd omp →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ))),
            gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              omp (gd, 1) (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  first | exact @GlobalTheory.WeilSchrodinger.DblRestrict.omp_diag_boxFun | exact GlobalTheory.WeilSchrodinger.DblRestrict.omp_diag_boxFun | (intros; apply GlobalTheory.WeilSchrodinger.DblRestrict.omp_diag_boxFun <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isUnitarySplitting_transportedDoubledWeilDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (GlobalTheory.DblSchr.dblD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co)
            (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) (GlobalTheory.DblSchr.omdOf omd₀) := by
  first | exact @GlobalTheory.DblSchr.isUSplitting_omdOf | exact GlobalTheory.DblSchr.isUSplitting_omdOf | (intros; apply GlobalTheory.DblSchr.isUSplitting_omdOf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.coeffPlace_valuation_residueFieldCard_eq_zero_of_not_mem : ∀ {D : D7} (P : Pl D.host.E) (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
  first | exact @GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero | exact GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero | (intros; apply GlobalTheory.UnfoldLoss.ResCardAway.vw_resCard_eq_zero <;> assumption)
end
