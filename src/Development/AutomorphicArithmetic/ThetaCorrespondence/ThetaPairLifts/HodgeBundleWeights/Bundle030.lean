module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsWeightHodgeBundleGenerated
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HermitianGeometricHypothesisHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure

@[expose] public section

section

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
namespace GlobalTheory.HSShortRun
open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}
theorem hilbertSamuel_estimate_at_level (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : Quoted)
    (hN : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hPr : GlobalTheory.Published.Principalisation)
    (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hC : GlobalTheory.Published.ToroidalChartsForFan)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (hE : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) {P : WtPar (T.Q.Dw j)} (hW : WtBig P)
    (hA : ∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) {PP κ : ℝ} (hPP : 0 ≤ PP) (hκ : 0 ≤ κ)
    (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂)
    (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) {Λ β : ℝ} (hΛ : 1 ≤ Λ) (hβ : 1 ≤ β)
    (hfr : ∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ)
    (hberg : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ β)
    (hBir : BirOn Y.U Z (wtOf _ P.u₁ 0) ∧ BirOn Y.U Z (wtOf _ P.u₂ 0))
    (h0 : ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U (P.wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧
      Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z
        (wtOf _ (P.wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)))
    (hsh : ∀ i ≤ P.T, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U (P.wt i)), (∀ q, v q ∈ latOn Y.U Z _) ∧
      Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z
        (wtOf _ (P.wt i) 0) σ (v q).1 ≤ Real.exp (PP * κ)) :
    1 ≤ (f₁.n : ℝ) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 P.T (CompHt.dimFlag (T.Q.Dw j)) f₁.n 1 Λ β (Real.exp (PP * κ))
      (Real.exp (PP * κ)) (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)) (Y.dg P.u₁ Z) (Y.ht P.u₁ Z)
      (Y.rkC (P.wt P.T) Z) (Y.degC (P.wt P.T) Z) := by
  obtain ⟨TF, R, ω, h⟩ := _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated hP hG hQ hN hPr hS hC hL D T j Y e o hY hE Z P hW hA
  have hPk : 0 ≤ PP * κ := mul_nonneg hPP hκ
  let k : Consts := ⟨Λ, β, Real.exp (PP * κ), Real.exp (PP * κ), 0, hβ, Real.one_le_exp hPk, Real.one_le_exp hPk⟩
  let th : R.L.Sec := 0
  have r₁ := GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hBir.1
  have r₂ := GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₂ ⟨R.toModif⟩ hBir.2
  have hΛ₀ : 1 ≤ Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)) := Real.one_le_exp (by positivity)
  have sh : ∀ i ≤ P.T, (h.data f₁ f₂ th k).ShortFamily i (Real.exp (PP * κ)) := fun i hi => by
    obtain ⟨m, v, l, s, n⟩ := hsh i hi
    exact GlobalTheory.HSApp.shortFamily_of_spanning _ _ _ _ _ _ TF Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k i hi _ m v l s n
  have s0 : (h.data f₁ f₂ th k).ShortFamily 0 (Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1))) := by
    obtain ⟨m, v, l, s, n⟩ := h0
    exact GlobalTheory.HSApp.shortFamily_of_spanning _ _ _ _ _ _ TF Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k 0 P.T.zero_le _ m v l s n
  have hDT : FlagTan.dimFlag (T.Q.Dw j) ≤ P.T := (Nat.le_succ _).trans h.le_T
  have hyp := _root_.GlobalTheory.T.hermitian_geometric_hypothesis_holds hP hG hQ hN hPr hS hC hL D T j Y e o hY hE Z TF P R ω h f₁ f₂ th k _ hW r₁ r₂ hberg hΛ hfr hΛ₀ s0
    (sh _ hDT) (sh _ le_rfl)
  have hC := GlobalTheory.T.hilbertSamuel_component_short_basis_bound hQ _ _ _ _ _ _ _ TF.X Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k _ hyp
  have hrk : Y.rkC (P.wt P.T) Z = Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
    show ((Formalism.HN.rkK _ : ℕ) : ℝ) = _
    rw [Formalism.HN.rkK, (h.good _ le_rfl).2.2, finrank_top]
  rw [Real.log_exp] at hC
  refine ⟨by exact_mod_cast (h.geo f₁ f₂ th k).one_le_n, ?_⟩
  rw [hrk]
  exact hC
end GlobalTheory.HSShortRun
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
end
end

section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.CovHt.GeomBound
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem geometric_height_bound_at_place (hX : GlobalTheory.CovTop.HypothesesX) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hS1 : GlobalTheory.Published.SiegelToroidalIntegral) (hS2 : GlobalTheory.Published.ToroidalForFanKS)
    (hS3 : GlobalTheory.Published.SemiAbelianLieSeminegative)
    {PP C A M : ℝ} (hsz : SizeAt p i PP C) (hN : HostNum D L PP A M) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (Y : Cov p i) (hY : GoodCov p i Y) (u1 : AllWt.Weight (dat p i)) (hu : Quo p i PP u1) : GeomAt p i Y u1 := by
  obtain ⟨hsig1, hsig2, -⟩ := hw.sig
  have hk := D.R.m_add_three_le_k
  have hp1 : 1 ≤ (dat p i).p := by rw [hsig1]; simp only [Ranks.sigW]; omega
  have hq1 : 1 ≤ (dat p i).q := by rw [hsig2]; simp only [Ranks.sigW]; omega
  have hf : 2 < Module.finrank ℚ D.host.E / 2 := by rw [hN.deg]; have := hN.f8; omega
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hL : LawsJ p.T := p.fw.laws
  have hYg := hY.1
  obtain ⟨-, -, -, -, -, -, hq⟩ := hsz
  obtain ⟨-, hq⟩ := hq hi
  obtain ⟨-, -, hρ1, -⟩ := hq u1 hu
  have hgap := quo_gaps p i hN hw hi u1 hu
  have hsa : ∀ τ, StrictAnti (u1 τ) := fun τ => strictAnti_of_step fun a b hb => by
    have := hgap τ a b hb
    have : (0 : ℤ) ≤ (((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℤ) := by positivity
    omega
  have hg1 : ∀ τ, 1 ≤ GlobalTheory.CompHS.gap (u1 τ) ((dat p i).p - 1) := fun τ => by
    have e := GlobalTheory.CompHS.gap_eq (u1 τ) (i := ⟨(dat p i).p - 1, by omega⟩) (j := ⟨(dat p i).p, by omega⟩)
      (by simp only; omega)
    simp only at e
    rw [e]
    have := hgap τ ⟨(dat p i).p - 1, by omega⟩ ⟨(dat p i).p, by omega⟩ (by simp only; omega)
    have : (0 : ℤ) ≤ ((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) := by positivity
    push_cast at *
    nlinarith
  have hgood := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg u1 (fun τ => (hsa τ).antitone) hg1
  have hbir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hS1 (_root_.GlobalTheory.T.covering_topology_refinement hP) hP.q15 hP.q16 _ p.T hL _ hp1 hq1 Y _ _ hYg u1 hgap
  have hprop := (_root_.GlobalTheory.T.proportionality_principle_compactification hP hS1 hS2 hS3 _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg).1
  intro Z
  refine ⟨hgood.2 Z, hbir Z, ?_⟩
  have hv : vdm u1 ≠ 0 := (GlobalTheory.CompHt.vdm_pos hsa).ne'
  rw [delPrime_eq Y.U Z hv]
  exact mul_le_mul_of_nonneg_left (GlobalTheory.DegTop.compDeg_le hprop Z hsa) (by linarith)
end Point
end GlobalTheory.CovHt.GeomBound
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
end
end
