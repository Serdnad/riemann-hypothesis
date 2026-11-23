module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle053
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle568
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle379
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle268
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle605
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle249
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNilpotentSubOneOfFullBlockUnipotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle251
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle094
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle096
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaNormEqProdLocalFactors
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle092
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.NonVanBottom
theorem bottom_theta_lift_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe →
    GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
      IsBottomTri W i j X → ∀ t : T, (∃ P h, X.I W.ψ W.θ t P h ≠ 0) ∧ ∃ P' h, X.I' W.ψ W.θ t P' h ≠ 0 := by
  intro hP hK hM hL
  obtain ⟨a1, h1⟩ := _root_.GlobalTheory.T.rallis_inner_product_big_theta_lift hP
  obtain ⟨a2, h2⟩ := _root_.GlobalTheory.T.bottom_theta_norm_eq_prod_local_factors hP.howeDualityReal hP hK hM hL
  obtain ⟨a3, h3⟩ := hL
  refine ⟨max (max a1 a2) a3, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCF)
  obtain ⟨C3, x3, k3⟩ := h3 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max (max C1 C2) C3, max (max x1 x2) x3, fun C hC D large₂ he hx hr T Lc μ₀ hμ G W i j A A' WW X hX t => ?_⟩
  have n1 := k1 C (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) hr T Lc μ₀ hμ G W i j A A' WW X hX t
  have n2 := k2 C (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx) hr T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Λ, hΛ, hne⟩ := ((k3 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hr T Lc μ₀ hμ G) i j).1 t
  have hh : ((h0 D i j : ℕ) : ℤ) ≤ (halfRank D i j : ℤ) := by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j
  obtain ⟨P, ν, 𝓕, c, hc, -, -, hf⟩ := n1
  obtain ⟨Pi, p, p', J, -, ⟨P', hP'⟩, hJ, hI, hI'⟩ := n2
  obtain ⟨y, hy⟩ := exists_ne_zero_of_norm_formula hc (fun s hs hs' => hne s hs (hs'.trans hh)) (hf Λ hΛ)
  refine ⟨⟨P, y, hy⟩, P', ?_⟩
  obtain ⟨lam, hlam⟩ := hI t
  have hinj : Function.Injective (J t) := by
    refine (hJ t).resolve_left fun h0 => hy ?_
    rw [hlam P, h0]
    simp
  by_contra hc'
  push_neg at hc'
  apply hP'
  apply hinj
  rw [← hI' t P', map_zero]
  exact funext hc'
end GlobalTheory.NonVanBottom
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.first_occurrence_theta_lift_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ t : T, (∃ P h, X.I W.ψ W.θ t P h ≠ 0) ∧ ∃ P' h, X.I' W.ψ W.θ t P' h ≠ 0 := by
  first | exact @_root_.GlobalTheory.NonVanBottom.bottom_theta_lift_ne_zero | exact _root_.GlobalTheory.NonVanBottom.bottom_theta_lift_ne_zero | (intros; apply _root_.GlobalTheory.NonVanBottom.bottom_theta_lift_ne_zero <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn GlobalTheory.LiftRows
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.LiftsOnly
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
section Real
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Real

theorem holdsL_of_ties_alt (P : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems) (hHL : GlobalTheory.Published.HeckeLPartialContinuation)
    (eps : ℝ) (heps : 0 < eps) : ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
      {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
      (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
      (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec)
      (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x →
      Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat →
      R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Rw.HoldsL R F := by
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.LiftRows.goodForms_definite_exist (GlobalTheory.DefFree.goodVectorsDefinite P.q12) eps heps
  refine ⟨x₀, ?_⟩
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O L hLe hLx hSz ⟨pV⟩ hT hG hM hInt
  obtain ⟨hGiven, hGS, hCD, -, hTR, hUp, -⟩ := _root_.GlobalTheory.T.lift_data_of_multiplicity_one P R F hT hM
  obtain ⟨hOk, hGU, hGE, hBlk, hA, hB⟩ := _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq P R F hT hM
  obtain ⟨hLT, hLTB, hML⟩ := GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility T R F κ v₀ O hT hG
  have hU : R.toRealDat.LUnif := hG.unif
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hcore := GlobalTheory.CoreOfWeak.core_of_weak R F hT.char hT.ex
  have hSch : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay P.q2 R.toRealDat
  have hRows : RowsNe R.toRealDat F.lv2 := GlobalTheory.RowsNeProof.rowsNe R.toRealDat F.lv2 1 hT.ok.ok2 hcore.1 hSch R.SF hcore.2.1 hTR
    (hx₀ D L pV hLe hLx hSz R.toRealDat F.lv2 hGiven)
  have hCar := carries_of_upInj P.q2 P.q1 R F hT.ok hT.char hT.ex hT.junk hGE hUp
  obtain ⟨hScal, hMatch, -, -⟩ := GlobalTheory.T.thetaLift_scalarIdentity_matching_adjointInjective P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8
    (_root_.ResidueKilled.sec_of_dm P.q9) P.q10 P.q11 R.toRealDat F.lv2 hGiven hT.ccK hT.char.allPl
    (GlobalTheory.FixAllGood.fixAll_of_good R F hT.char hT.ex) R.SF hcore.2.1 hTR
  have hK := GlobalTheory.PosAtBase.pos_at_base R F hT.ok hT.char hT.ex hScal hMatch
    (GlobalTheory.CarriesOne.parts_eq_of_carries P.q1 P.q2 R F hT.ok hT.char hT.ex hJ hUp)
    (exists_rowPart_ne_bot_positiveDimension P.q2 R F hT.char hT.ex hCar hRows)
  have hLev := levW_of_span P.q2 R F hT.ok hT.char hT.ex hGS hCD hM hBlk hCar hK hA hLT hU
  have hW := partsW_of_carried P.q2 R F hT.ok hT.char hT.ex hGS hCD hM hOk.1 hCar hK hB hU
  obtain ⟨-, hH, hTS, -⟩ := GlobalTheory.Hk3.HeckeClose.heckeClose P.q1 P.q3 P.q2 R F 1 hT.ok hT.char hT.ex hT.junk hT.ser hT.trSem hU
    hGU hGE hLev hA hB hK hW
  have hOnto := _root_.GlobalTheory.T.partial_L_function_of_hypotheses_alt P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hHL R F hT.ok hT.char hT.ex hT.host hT.params
    hT.ccK hT.guard hT.types hOk.2 hGE hU
  obtain ⟨fw, hbar⟩ := hG.fw
  have hConj : R.toRealDat.PConj := GlobalTheory.ConjNorm.pConj T R.toRealDat F.lv2 κ v₀ hcore.1 hSch fw hbar hU
  have hLW : R.toRealDat.LLevelW F.lv2 :=
    GlobalTheory.LevelForms.levelW_of_irr _ _ hT.ok.ok2.irr hU hT.char.base.models.HW
  exact ⟨hOk.1, hOk.2, hH, hGU, hGE, hBlk, hLT, hLTB, hOnto, hU, hML, hLev, hA, hW, ⟨hT.ex, hConj, hLW, hInt⟩, hT.ok, hTS⟩
end GlobalTheory.LiftsOnly
end
end
end
