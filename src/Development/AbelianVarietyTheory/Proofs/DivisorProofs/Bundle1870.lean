module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_add_le_of_mul_le (a b c d e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ≤ c * d) (hce : c ≤ e) :
    Real.log a + Real.log b ≤ Real.log e + Real.log d := by
  apply _root_.GlobalTheory.HSNef.log_add_log_le_of_mul_le_mul <;> assumption

theorem lc_add_A_le : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField),
    P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
    P.lc (n * m : ℕ) m 1 ≤ P.lc (n * m : ℕ) 0 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  intro hHS hAC k _ X _ p D hD P b s t hG ε hε
  have hfin : ∀ (a c : ℤ) (R : ℝ), (P.Bl a c R).Finite := fun a c R =>
    GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hD P b s t hG a c R hAC
  have hball : ∀ a c : ℤ, IsBallFam (P.H a c) (P.Bl a c) := GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P
  have hpos : ∀ (a c : ℤ) (R : ℝ), 0 ≤ R → 1 ≤ (P.Bl a c R).ncard := fun a c R hR =>
    Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (hfin a c R)).mpr ⟨0, (hball a c).zero_mem R hR⟩).ne'
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.smallSectionCount_le_pow_goodPair hHS hAC k X p D hD P b s t hG
  obtain ⟨δ, hδ, hrad⟩ := GlobalTheory.T.exists_log_ncard_seminormBall_exp_small_le X.functionField (fun N => P.H (N : ℤ) 0) (fun N => P.Bl (N : ℤ) 0) (D + 1)
    (Nat.succ_pos D) (fun N => hball N 0) (fun N R => hfin N 0 R) C0 hC0 (ε / 3) (by positivity)
  obtain ⟨C, hC, hdiv⟩ := GlobalTheory.T.mem_smallSectionBall_of_mul_pow_section k X p D hD P s hG.s_mem.1 hG.s_ne (δ / 2) (by positivity)
  have hdA := GlobalTheory.T.smallSectionCount_nearPowers_le hHS hAC k X p D hD P b s t hG (ε / 3) (by positivity)
  have hn : ∀ᶠ n : ℕ in atTop, (2 * C + 2) / δ ≤ (n : ℝ) ∧ 1 ≤ n :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and (eventually_ge_atTop 1)
  filter_upwards [hdA, hn] with n hdAn hnn
  obtain ⟨hnC, hn1⟩ := hnn
  have htend : Tendsto (fun m : ℕ => n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hn1) tendsto_id
  filter_upwards [hdAn, htend.eventually hrad, eventually_ge_atTop 1] with m hdm hradm hm1
  have hnδ : 2 * C + 2 ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnC
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1

  have hrad_le : 2 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m) ≤ Real.exp (δ * ((n * m : ℕ) : ℝ)) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    calc 2 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m)
        ≤ Real.exp 1 * Real.exp (δ / 2 * ((n * m : ℕ) : ℝ) + C * m) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (1 + (δ / 2 * ((n * m : ℕ) : ℝ) + C * m)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (δ * ((n * m : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right hnδ (by linarith : (0 : ℝ) ≤ m)]
  have hSsub : {f | f ∈ P.H (n * m : ℕ) 0 ∧ f * s ^ m ∈ P.Bl (n * m : ℕ) m 2} ⊆
      P.Bl (n * m : ℕ) 0 (Real.exp (δ * ((n * m : ℕ) : ℝ))) := by
    rintro f ⟨hf1, hf2⟩
    have hf := hdiv (n * m) m f hf1 hf2
    exact ⟨hf.1, fun σ y => (hf.2 σ y).trans hrad_le⟩
  have hEfin := hfin (n * m : ℕ) 0 (Real.exp (δ * ((n * m : ℕ) : ℝ)))
  have hSfin := hEfin.subset hSsub
  have hlev := GlobalTheory.T.arith_small_sections_encard_mul_le_finite_level k X p D hD P b s t hG (n * m) m (hfin _ _ _)
  rw [← (hfin _ _ _).cast_ncard_eq, ← (hfin _ _ _).cast_ncard_eq, ← hSfin.cast_ncard_eq,
    ← (hfin _ _ _).cast_ncard_eq] at hlev
  norm_cast at hlev
  have hkey := log_add_le_of_mul_le _ _ _ _ _ (hpos _ _ _ zero_le_one) (hpos _ _ _ zero_le_one) hlev
    (Set.ncard_le_ncard hSsub hEfin)
  have hX : (0 : ℝ) ≤ ((n : ℝ) * m) ^ (D + 1) := by positivity
  have hX3 := mul_nonneg (by positivity : (0 : ℝ) ≤ ε / 3) hX
  simp only [Pair.lc] at hdm ⊢
  push_cast at hradm hkey hdm ⊢
  linarith

end GlobalTheory.VolBr
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (root)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsKTypeOf IsDS)
open CompanionTheory.D.LK (IsKMod)

theorem _root_.GlobalTheory.T.kType_weight_mem_cone_over_lowest_kType : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  exact @GlobalTheory.kType_weight_in_cone_over_lowK
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColRows

theorem hostTie_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.HostTie (ofRecord (I.rec7 l Z) L Del h0) t.seam t.Pr := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS
  obtain ⟨hX, hseam, hPr, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hseam
  exact GlobalTheory.CoreHt.host_tie_trueCols I hOk l Z L

end GlobalTheory.ColRows

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.characterCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.CharTie (ofRecord (I.rec7 l Z) L Del h0) t.seam W t.Ch t.glob t.sel := by
  first | exact @GlobalTheory.ColRows.charTie_stdKer | exact GlobalTheory.ColRows.charTie_stdKer | (intros; apply GlobalTheory.ColRows.charTie_stdKer <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weightCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (I.rec7 l Z).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (I.rec7 l Z) L Del h0) W pl (t.word u) (letterOf (I.rec7 l Z) L Del h0 u) := by
  first | exact @GlobalTheory.ColRows.weightTie_of_stdKer | exact GlobalTheory.ColRows.weightTie_of_stdKer | (intros; apply GlobalTheory.ColRows.weightTie_of_stdKer <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ConjVacuumPower

theorem even_rank (R : Ranks) (l : ℕ) : Even (R.N l) := by
  unfold Ranks.N
  exact R.k_even.add ((R.t_odd.add_one).mul_left l)

theorem logThAt_eq_mul : ∀ (D : D7) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (K : Type) [Field K] (σ₀ : K →+* ℂ) (R : Ranks) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D D.host.ccK → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK dl → TaylorLogMetric.IsChi D χ → B.VecP χ → ThetaFieldData B cD σ₀ R M → ∀ ρ : M →ₐ[ℚ] ℂ, ∃ lt : ℝ, ∀ i < R.m, logThAt B M ρ (R.N i) (R.N (i + 1)) = (R.N i : ℝ) * (R.N (i + 1) : ℝ) * lt := by
  intro D dl B χ cD K _ σ₀ R M _ hadm hpsi hcur hdel hχ hV hH ρ
  have hc : StandardLatticesGL3.Crv D D.host.ccK dl := ⟨hcur, hdel⟩
  have hY := GlobalTheory.ExponentsFinite.yFinite D B.γ₀ B.kc
  have hT := GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum D _ dl B χ hadm hpsi hcur hdel hχ hY
  have hD : TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK dl) M := hH.2.1
  obtain ⟨t', ht'⟩ := (GlobalTheory.TwoTorsionPt.exists_point D _ dl hc).2 M ρ hD.2.1 hD.2.2
  refine ⟨(TaylorLogMetric.fF D : ℝ) * Real.log (StandardLatticesGL3.nrm1Sq (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK dl))
    (GL3Theta.th0 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK dl)) t')), fun i hi => ?_⟩
  obtain ⟨hAdm, hbase⟩ := GlobalTheory.NatAtStd.eNat_std D _ dl B χ hχ hV _ _ (even_rank R i) (even_rank R (i + 1))
  have hE := hT _ B.t0 _ _ _ _ hAdm
  rw [hbase] at hE
  have hs : ∀ n, StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) := fun n => by
    letI := D.host.cmStar
    exact GlobalTheory.NatAtStd.isSD_pi _ n
  have h := (GlobalTheory.ConjNorm.useNorm_all D _ dl hc _ B.t0 _ _ _ _ (hs _) (hs _) ((even_rank R i).mul_right _) _ hE M ρ hD
    (hH.2.2.2 i hi) t' ht').1
  unfold logThAt
  erw [h]
  rw [Real.log_pow]
  push_cast
  ring

end GlobalTheory.ConjVacuumPower
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.HaarConj

variable {D : D7}

theorem isFundamentalDomain_image {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
    (φ : G ≃* H) (hc : Measurable φ) (hc' : Measurable φ.symm) (Γ : Subgroup G) (Γ' : Subgroup H)
    (hQ : ∀ g, g ∈ Γ ↔ φ g ∈ Γ') (μ : Measure G) (𝓕 : Set G) (h : IsFundamentalDomain Γ 𝓕 μ) :
    IsFundamentalDomain Γ' (φ '' 𝓕) (μ.map φ) := by
  let ψ : G ≃ᵐ H := ⟨φ.toEquiv, hc, hc'⟩
  have hψ : MeasurePreserving ψ μ (μ.map φ) := ⟨ψ.measurable, rfl⟩
  have e : φ '' 𝓕 = φ.symm ⁻¹' 𝓕 := φ.toEquiv.image_eq_preimage_symm 𝓕
  rw [e]
  exact h.preimage_of_equiv (f := φ.symm) (MeasurePreserving.symm ψ hψ).quasiMeasurePreserving
    (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
    ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
      fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
    fun γ y => by
      show φ.symm (φ γ * y) = γ * φ.symm y
      rw [map_mul, φ.symm_apply_apply]

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (D.sp.cm.sig e) := by
  simp [cA, sigR, incA, inclR, Algebra.TensorProduct.map_tmul]

theorem incA_inj : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 D.host.F) (K := D.host.F))

def conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : GA D V :=
  ⟨GeneralLinearGroup.map (cA D) u.1, by
    have hu : u.1.1ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * u.1.1.map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := u.2
    have e : (u.1.1.map (cA D)).map (cA D) = u.1.1 := Matrix.ext fun _ _ => cA_cA _
    show Formalism.UG.cT (cA D) (u.1.1.map (cA D)) * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram * u.1.1.map (cA D)
      = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram
    rw [Formalism.UG.cT, e]
    generalize u.1.1 = M at hu ⊢
    rw [h, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hu
    have k : incA D c⁻¹ * incA D c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    have := congrArg (incA D c⁻¹ • ·) hu
    simpa only [smul_smul, k, one_smul] using this⟩

def conjE (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GA D V ≃* GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J where
  toFun := conjU V c h
  invFun := conjInv V c hc h
  left_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => cA_cA _))
  right_inv u := Subtype.ext (Units.ext (Matrix.ext fun _ _ => cA_cA _))
  map_mul' a b := Subtype.ext (by
    show GeneralLinearGroup.map (cA D) (matHom V (a * b)) = GeneralLinearGroup.map (cA D) (matHom V a) *
      GeneralLinearGroup.map (cA D) (matHom V b)
    rw [map_mul, map_mul])

theorem continuous_conjInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : Continuous (conjInv V c hc h) := by
  have h1 : Continuous (fun u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J => u.1) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
  · exact (Units.continuous_coe_inv.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)

theorem mem_ratU_iff (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (g : GA D V) :
    g ∈ GQ V ↔ conjE V c hc h g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J := by
  have hg : Formalism.UG.cT (cA D) g.1.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram * g.1.1 = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram := g.2
  constructor
  · intro hq
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hq)
    refine Subgroup.mem_subgroupOf.2 ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) x, ?_⟩
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun y : GL (Fin V.rank) (AE D) => y.1 i j) hx
    show incA D (D.sp.cm.sig (x.1 i j)) = cA D (g.1.1 i j)
    rw [← this, ← cA_incA]
    rfl
  · intro hq
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.1 hq
    have hw' : ∀ i j, incA D (w.1 i j) = cA D (g.1.1 i j) := fun i j =>
      congrArg (fun y : GL (Fin V.rank) (AE D) => y.1 i j) hw
    have hx : ∀ i j, incA D (D.sp.cm.sig (w.1 i j)) = g.1.1 i j := fun i j => by
      rw [← cA_incA, hw', cA_cA]
    let x := GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) w
    have hxm : x.1.map (incA D) = g.1.1 := Matrix.ext fun i j => hx i j
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, Units.ext (Matrix.ext fun i j => hx i j)⟩)
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1 = V.gram
    have key : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1 * V.gram * x.1).map (incA D) =
        V.gram.map (incA D) := by
      rw [Matrix.map_mul, Matrix.map_mul, hxm]
      have e1 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x.1).map (incA D) = Formalism.UG.cT (cA D) g.1.1 := by
        rw [← hxm]
        ext i j
        simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply]
        exact (cA_incA _).symm
      rw [e1]
      exact hg
    exact Matrix.ext fun i j => incA_inj (congrFun (congrFun key i) j)

theorem haarConj : ∀ {D : D7} (V : HSp D) (c : D.host.E), c ≠ 0 → ∀ {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hJ : J = c • V.gram)
    (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∃ dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J), (ν.map (conjU V c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) dom (ν.map (conjU V c hJ)) := by
  intro D V c hc J hJ ν fd hν hfd
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  have c1 : Continuous (conjE V c hc hJ) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V c hJ
  have c2 : Continuous (conjE V c hc hJ).symm := continuous_conjInv V c hc hJ
  exact ⟨conjE V c hc hJ '' fd, MulEquiv.isHaarMeasure_map ν (conjE V c hc hJ) c1 c2,
    isFundamentalDomain_image (conjE V c hc hJ) c1.measurable c2.measurable (GQ V) _ (mem_ratU_iff V c hc hJ) ν fd hfd⟩

end GlobalTheory.HaarConj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjUTransport

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (UB incM incM_smul mt_gram continuous_conj continuous_conjU)

variable {D : D7}

theorem mem_inv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) :
    (GeneralLinearGroup.map (cA D) (show GL (Fin V.rank) (AE D) from x.1) : GL (Fin V.rank) (AE D)) ∈
      HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have e : ((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)).map (cA D) =
      (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
  have hx : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))ᵀ * incM J *
      (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = incM J := x.2
  show (((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)).map (cA D))ᵀ * incM V.gram *
    (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = incM V.gram
  rw [e]
  generalize (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = X at hx ⊢
  rw [h, incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hx
  have hx' := congrArg (fun y => incA D c⁻¹ • y) hx
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul] at hx'
  exact hx'

def conjUInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) : GA D V :=
  show HR (AF D.host.F) D.sp.cm.sig V.gram from ⟨_, mem_inv V c hc h x⟩

def conjEquiv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GA D V ≃* UB J where
  toFun := conjU V c h
  invFun := conjUInv V c hc h
  left_inv g := by
    apply Subtype.ext; apply Units.ext; ext i j; exact Formalism.L2.Theta.cA_cA _
  right_inv x := by
    apply Subtype.ext; apply Units.ext; ext i j; exact Formalism.L2.Theta.cA_cA _
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    show (mt V (a * b)).map (cA D) = (mt V a).map (cA D) * (mt V b).map (cA D)
    rw [← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt, map_mul]

theorem continuous_conjUInv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : Continuous (conjUInv V c hc h) := by
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map (continuous_conj D)
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (continuous_conj D)

theorem cA_inclR (a : D.host.E) :
    cA D (inclR (F := D.host.F) (AF D.host.F) a) = inclR (F := D.host.F) (AF D.host.F) (D.sp.cm.sig a) := rfl

theorem rat_fwd (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (h : J = c • V.gram)
    (γ : GA D V) (hγ : γ ∈ GQ V) : conjU V c h γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J := by
  obtain ⟨y, -, e⟩ := hγ
  refine ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) y, Units.ext ?_⟩
  have e' : mt V γ = (y : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) :=
    (congrArg Units.val e).symm
  show _ = (mt V γ).map (cA D)
  rw [e']
  ext i j
  exact (cA_inclR _).symm

theorem inclR_injective : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem rat_inv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) (x : UB J) (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) : conjUInv V c hc h x ∈ GQ V := by
  obtain ⟨z, hz⟩ := hx
  have hz' : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) =
      (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) :=
    (congrArg Units.val hz).symm
  set Z := (z : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (D.sp.cm.sig : D.host.E →+* D.host.E) with hZ
  have hY : (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) =
      Z.map (inclR (F := D.host.F) (AF D.host.F)) := by
    rw [hz']; ext i j; exact cA_inclR _
  refine ⟨GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) z, ?_, Units.ext ?_⟩
  · have hm := mem_inv V c hc h x
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)) *
      JR (AF D.host.F) V.gram * (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D) = JR (AF D.host.F) V.gram at hm
    rw [hY] at hm
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Z.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; exact cA_inclR _
    rw [hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * V.gram * Z = V.gram
    apply Matrix.map_injective inclR_injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · show Z.map (inclR (F := D.host.F) (AF D.host.F)) = (x.1.1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (cA D)
    exact hY.symm

def ratEquiv (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hc : c ≠ 0)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J ≃ GQ V where
  toFun γ := ⟨conjUInv V c hc h γ.1, rat_inv V c hc h γ.1 γ.2⟩
  invFun γ := ⟨conjU V c h γ.1, rat_fwd V c h γ.1 γ.2⟩
  left_inv γ := Subtype.ext ((conjEquiv V c hc h).right_inv γ.1)
  right_inv γ := Subtype.ext ((conjEquiv V c hc h).left_inv γ.1)

theorem map_isHaar_isFundamentalDomain : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure →
    IsFundamentalDomain (GQ V) fd ν →
    (ν.map (conjU V c h)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (conjU V c h '' fd) (ν.map (conjU V c h)) := by
  intro D V J c hc h ν fd hν hfd
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have : BorelSpace (UB J) := ⟨rfl⟩
  let φ := conjEquiv V c hc h
  have c1 : Continuous φ := continuous_conjU V c h
  have c2 : Continuous φ.symm := continuous_conjUInv V c hc h
  have hH : (ν.map φ).IsHaarMeasure := MulEquiv.isHaarMeasure_map ν φ c1 c2
  refine ⟨hH, ?_⟩
  let H : GA D V ≃ₜ UB J := ⟨φ.toEquiv, c1, c2⟩
  let M := H.toMeasurableEquiv
  have hq : Measure.QuasiMeasurePreserving M.symm (ν.map M) ν :=
    (M.measurePreserving_symm ν).quasiMeasurePreserving
  refine hfd.image_of_equiv M.toEquiv hq (ratEquiv V c hc h) fun γ x => ?_
  show φ (φ.symm γ.1 * x) = γ.1 * φ x
  rw [map_mul, MulEquiv.apply_symm_apply]

end GlobalTheory.ConjUTransport
end
end
