module

public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle264
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle825
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle508
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle509
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle510
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
import Mathlib.RingTheory.TotallySplit
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowRepR

private theorem lamS_eq_lamAt (R : Ranks) (P : HCParam R) (i : Fin R.r) :
    Formalism.MainNotions.S.lamS R P i = ((Formalism.L2.NTheta.lamAt P i.val : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.S.lamS Formalism.L2.NTheta.lamAt
  by_cases h1 : i.val < R.k - 1
  · simp [h1]
  · by_cases h2 : i.val - (R.k - 1) < R.m
    · simp [h1, h2]
    · simp [h1, h2]

private theorem lamAt_gap_of_lt {D : D7} (hH : HostHyp D) (τ : D.what₂.Tau)
    {i j : ℕ} (hij : i < j) (hj : j < D.R.r) :
    100 * (D.R.r : ℚ) ^ 4 ≤
      Formalism.L2.NTheta.lamAt (D.hc τ) i - Formalism.L2.NTheta.lamAt (D.hc τ) j := by
  induction j, hij using Nat.le_induction with
  | base => exact hH.gapR τ i hj
  | succ j _ ih =>
    exact (ih (Nat.lt_of_succ_lt hj)).trans
      (sub_le_sub_left (Formalism.L2.NTheta.lamAt_lt (D.hc τ) j hj).le _)

private theorem gapGe_hundred_mul_r_pow_four {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hH : HostHyp D) :
    GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  intro v
  unfold Formalism.QuantumDeterminants.GapAtLeast
  intro a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq, lamS_eq_lamAt, lamS_eq_lamAt]
  have key : ∀ i j : Fin D.R.r, i.val < j.val →
      100 * (D.R.r : ℝ) ^ 4 ≤ |((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) i.val : ℚ) : ℝ) -
        ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) j.val : ℚ) : ℝ)| := by
    intro i j hij
    have hq := lamAt_gap_of_lt hH (X.pl v) hij j.isLt
    have hr : 100 * (D.R.r : ℝ) ^ 4 ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) i.val : ℚ) : ℝ) -
        ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) j.val : ℚ) : ℝ) := by exact_mod_cast hq
    exact hr.trans (le_abs_self _)
  have hne : (Fin.cast X.n_eq a).val ≠ (Fin.cast X.n_eq b).val := fun hv => hab (congrArg _ (Fin.ext hv))
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact key _ _ hlt
  · rw [abs_sub_comm]
    exact key _ _ hgt

theorem exists_contRep_rows : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM hH hE t c ht hconj hc Φ hΦ u
  exact GlobalTheory.ConjRowRep.exists_contRep hDS D X h R.θ _ (MP R) _ _ t c rfl hM.inf (gapGe_hundred_mul_r_pow_four X hH) hE
    ⟨ht, hconj⟩ hc Φ hΦ u

end GlobalTheory.ConjRowRepR

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.HeckeLevelFree

theorem ne_under_of_offS {D : D7} {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q : HeightOneSpectrum (𝓞 D.host.E)}
    (hQ : OffS D SF Q) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ SF) :
    v ≠ HeightOneSpectrum.under (𝓞 D.host.F) Q := by
  intro hvq
  obtain ⟨x, hx, hy⟩ := hQ v hv
  have hx' : x ∈ (HeightOneSpectrum.under (𝓞 D.host.F) Q).asIdeal := hvq ▸ hx
  have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ Q.asIdeal := hx'
  refine hy (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ?_ hmem
  rfl

theorem rTup_eq_one {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hQ : OffS D SF Q) {e f : AE D} (hef : IsPrimeIdem Q e f)
    {g : GA D V} (hg : SuppF V f g) (hS : finE V g ∈ St β) : rTup β L (finE V g) = 1 := by
  have hproj : ∀ v ∈ SF, GlobalTheory.FinZeta.projV V v g = 1 := fun v hv =>
    (GlobalTheory.SuppLocal.suppF_local D V Q e f g hef hg).2 v (ne_under_of_offS hQ hv)
  funext PP
  obtain ⟨v, hv, hPv⟩ := hPg PP.1 PP.2
  have hu : HeightOneSpectrum.under (𝓞 D.host.F) PP.1 ∈ SF := by
    have : HeightOneSpectrum.under (𝓞 D.host.F) PP.1 = v := HeightOneSpectrum.ext hPv
    rw [this]; exact hv
  have hr := GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β SF hS hproj hu
  show upperLeftBlock L.hr (redFn β PP.1 (finE V g)) = 1
  rw [hr]; exact blockDiagonalExtendByOnePrimeField_one _ _

theorem mem_and_chi {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (P P' : LevelP L.Pg L.r ℂ) {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hQ : OffS D SF Q) {e f : AE D} (hef : IsPrimeIdem Q e f)
    {g : GA D V} (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P)) :
    g ∈ levS V β (withP L P') ∧ levChi V β (withP L P) g = levChi V β (withP L P') g := by
  obtain ⟨hG, hl⟩ := hJ
  have hpar : finE V g ∈ parLev D.sp.cm V.gram β (withP L P) := (mem_lev.1 hl).1
  have hS : finE V g ∈ St β := parLev_St hpar
  have h1 : rTup β L (finE V g) = 1 := rTup_eq_one β L hPg hQ hef hg hS
  refine ⟨⟨hG, mem_lev.2 ⟨hpar, ?_⟩⟩, ?_⟩
  · show rTup β L (finE V g) ∈ P'.H
    rw [h1]; exact Subgroup.one_mem _
  · unfold levChi
    rw [levFn_withP, levFn_withP, h1, blockDiagonalExtendByOnePrimeField_one, blockDiagonalExtendByOnePrimeField_one]

theorem isHeckeOpFull_imp {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (P P' : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)) :
    Hecke₂ V (levS V β (withP L P)) (levChi V β (withP L P)) SF Q d Rp →
      Hecke₂ V (levS V β (withP L P')) (levChi V β (withP L P')) SF Q d Rp := by
  rintro ⟨e, f, ϖ, α, hQ, hef, h1, h2, h3, hK, hχ, h4, h5, h6, hR⟩
  have key := fun g (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P)) => mem_and_chi β L P P' hPg hQ hef hg hJ
  have key' := fun g (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P')) => mem_and_chi β L P' P hPg hQ hef hg hJ
  have hset : {k | k ∈ levS V β (withP L P) ∧ SuppF V f k} = {k | k ∈ levS V β (withP L P') ∧ SuppF V f k} := by
    ext k
    exact ⟨fun ⟨a, b⟩ => ⟨(key k b a).1, b⟩, fun ⟨a, b⟩ => ⟨(key' k b a).1, b⟩⟩
  refine ⟨e, f, ϖ, α, hQ, hef, h1, h2, h3, fun g hg => ?_, fun g hJ hg => ?_, h4, h5, h6, hset ▸ hR⟩
  · exact ⟨fun h => (hK g hg).1 ((key' g hg h).1), fun h => (key g hg ((hK g hg).2 h)).1⟩
  · have hJ0 := (key' g hg hJ).1
    rw [← (key g hg hJ0).2]
    exact hχ g hJ0 hg

theorem isHeckeOpFull_withP_iff : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P P' : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))), (∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) → ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)), Hecke₂ V (levS V β (withP L P)) (levChi V β (withP L P)) SF Q d Rp ↔ Hecke₂ V (levS V β (withP L P')) (levChi V β (withP L P')) SF Q d Rp := by
  intro D V β L P P' SF hPg Q d Rp
  exact ⟨isHeckeOpFull_imp β L P P' SF hPg Q d Rp, isHeckeOpFull_imp β L P' P SF hPg Q d Rp⟩

end GlobalTheory.HeckeLevelFree
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open Matrix


theorem _root_.GlobalTheory.T.weilActionO_mem_latticeO_of_integralCombinations : ∀ {D : D7} (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    (∀ s ∈ AS, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin S.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BS) ∧
      ∀ i, finPart D ((mt S g *ᵥ fun k => incA D (s k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    (∀ t ∈ AT, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin T.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BT) ∧
      ∀ i, finPart D ((mt T h *ᵥ fun k => incA D (t k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    ∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  first | exact @GlobalTheory.LatMoveGen.actO_mem_latO | exact GlobalTheory.LatMoveGen.actO_mem_latO | (intros; apply GlobalTheory.LatMoveGen.actO_mem_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.isTypeAt_dualPar_iff_star_isTypeAt : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (P : SPar) (φ : GA D V → ℂ), IsTypeAt θ V τ (Formalism.IndefR.Mult.dualPar P) φ ↔ IsTypeAt θ V τ P fun g => star (φ g) := by
  first | exact @GlobalTheory.TypeConj.isTypeAt_dualPar_iff | exact GlobalTheory.TypeConj.isTypeAt_dualPar_iff | (intros; apply GlobalTheory.TypeConj.isTypeAt_dualPar_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

theorem _root_.GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      LinearMap.adjoint (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) = (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) := by
  first | exact @GlobalTheory.RepAdj.rep_adjoint_eq_inv | exact GlobalTheory.RepAdj.rep_adjoint_eq_inv | (intros; apply GlobalTheory.RepAdj.rep_adjoint_eq_inv <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem exists_finite_factor {F R K L : Type} [Field F] [CommRing R] [Field K] [Field L] [Algebra F R]
    [Algebra F K] [Algebra F L] [Algebra.FiniteType F R] (φ : K →ₐ[F] L) (hφ : φ.toRingHom.IsIntegral)
    (ψ : R →ₐ[F] L) :
    ∃ (M : Type) (_ : Field M) (_ : Algebra F M) (i : K →ₐ[F] M) (j : M →ₐ[F] L) (χ : R →ₐ[F] M),
      j.comp i = φ ∧ i.toRingHom.Finite ∧ j.comp χ = ψ := by
  classical
  letI : Algebra K L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F R).out
  let M : IntermediateField K L := IntermediateField.adjoin K ((s.image ψ : Finset L) : Set L)
  haveI hM : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => hφ x
  have hmem : ∀ r : R, ψ r ∈ M.toSubalgebra.restrictScalars F := by
    intro r
    have hr : r ∈ Algebra.adjoin F (s : Set R) := hs ▸ Algebra.mem_top
    have : Algebra.adjoin F (s : Set R) ≤ (M.toSubalgebra.restrictScalars F).comap ψ := by
      refine Algebra.adjoin_le fun x hx => ?_
      exact IntermediateField.subset_adjoin K _ (by simpa using ⟨x, hx, rfl⟩)
    exact this hr
  refine ⟨M, inferInstance, inferInstance, IsScalarTower.toAlgHom F K M, M.val.restrictScalars F,
    ψ.codRestrict (M.toSubalgebra.restrictScalars F) hmem, ?_, ?_, ?_⟩
  · ext a; rfl
  · exact RingHom.finite_algebraMap.2 hM
  · ext a; rfl

theorem frPt_descends_finite :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (z : FrPt Xo c L), φ.toRingHom.IsIntegral → ∃ (M : Type) (_ : Field M) (_ : Algebra c.F M) (i : K →ₐ[c.F] M) (j : M →ₐ[c.F] L) (z₁ : FrPt Xo c M), j.comp i = φ ∧ i.toRingHom.Finite ∧ FrMap j z₁ z := by
  intro E _ _ _ H Dw l Xo c K L _ _ _ _ φ z hφ
  obtain ⟨p, ψ, u, hu⟩ := GlobalTheory.FlagTan.fromTest_of_isLocalRing z
  haveI : Algebra.FiniteType c.F p.R := inferInstance
  obtain ⟨M, _, _, i, j, χ, h1, h2, h3⟩ := exists_finite_factor φ hφ ψ
  obtain ⟨z₁, hz⟩ := GlobalTheory.FlagTan.exists_frMap χ u
  exact ⟨M, inferInstance, inferInstance, i, j, z₁, h1, h2,
    GlobalTheory.FlagTan.frMap_of_comp hz hu fun a => DFunLike.congr_fun h3 a⟩

end GlobalTheory.HkIntegral
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeKerLat

theorem ex_nsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (n : ℕ) (w : Fin g → ℂ) :
    F.ex i P (n • w) = F.ex i P w ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have := (F.ex_ker i P hP 0).2 (zero_mem _)
    exact this
  | succ n ih => rw [succ_nsmul, F.ex_add i P hP, ih, pow_succ]

theorem exists_lift_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → Formalism.L2.Pj.IsHkIsog p (F.u i P) (F.u j P') C ψ ψp →
  ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
    (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
    (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ (∀ z, F.ex j P' (h z) = ψp (F.ex i P z)) ∧
    (∀ a, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) ∈ C ↔ ∃ b, gam a = (p ^ 2) • b) ∧
    ∀ c ∈ C, ∃ a, c = F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) := by
  intro E _ _ _ H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := GlobalTheory.T.heckeIsogeny_lifts_to_lattice_map_scaling_forms E H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  have hker : ψp.ker = C := hI.2.2.2.2.2.1
  have hp0 : ((p : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨gam, h, h1, h2, h3, h4, fun a => ?_, fun c hc => ?_⟩
  · rw [← hker, MonoidHom.mem_ker, ← h4, map_smul, ← h2, F.ex_ker j P' hP']
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hP'.2.1 ?_⟩
      rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      push_cast
      rw [mul_inv_cancel₀ hp0, one_smul]
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [hb, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      push_cast
      rw [inv_mul_cancel₀ hp0, one_smul]
  · obtain ⟨w, rfl⟩ := F.ex_onto i P hP c
    have e1 : F.ex i P ((p ^ 2) • w) = 1 := by rw [ex_nsmul F i P hP, hC _ hc]
    obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 e1
    refine ⟨a, congrArg _ ?_⟩
    rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hp0, one_smul]

end GlobalTheory.HeckeKerLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


theorem _root_.GlobalTheory.T.entire_eq_of_monomial_derivations_at_zero_eq : ∀ {D : D7} {N N' : ℕ} (Φ Ψ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ), Differentiable ℂ Φ → Differentiable ℂ Ψ → (∀ k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ, Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ = Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Ψ) → Φ = Ψ := by
  first | exact @GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq | exact GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq | (intros; apply GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.exists_orthogonalProjection_posDef_sesquilinear_finiteDim : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (F : Submodule ℂ M), FiniteDimensional ℂ F →
    (∀ x ∈ F, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ F, ∀ y ∈ F, star (b x y) = b y x) →
    ∃ e : M →ₗ[ℂ] M, (∀ x, e x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (e x) f = b x f := by
  first | exact @GlobalTheory.exists_proj_sesq_posDef_finiteDim | exact GlobalTheory.exists_proj_sesq_posDef_finiteDim | (intros; apply GlobalTheory.exists_proj_sesq_posDef_finiteDim <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.exists_jointEigenDecomposition_commuting_symmetricOps : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (Z : Submodule ℂ E), FiniteDimensional ℂ Z →
    (∀ i, ∀ x ∈ Z, F i x ∈ Z) → (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ Z, F i (a • x) = a • F i x) → (∀ i j, ∀ x ∈ Z, F i (F j x) = F j (F i x)) →
    ∀ b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ, (∀ x ∈ Z, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ Z, ∀ y ∈ Z, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, b x (F i y) = b (F i x) y) →
    ∃ C : Finset (ι → ℂ), ∀ x ∈ Z, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h} := by
  first | exact @GlobalTheory.JointSpectral.exists_finset_joint_eigen | exact GlobalTheory.JointSpectral.exists_finset_joint_eigen | (intros; apply GlobalTheory.JointSpectral.exists_finset_joint_eigen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.mem_iSup_jointEigenspaces_inf_of_stableSubmodule : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (G P : Submodule ℂ E) (C : Finset (ι → ℂ)),
    (∀ i, ∀ x ∈ G, F i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x) → P ≤ G → (∀ i, ∀ x ∈ P, F i x ∈ P) →
    (∀ x ∈ G, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h}) →
    ∀ x ∈ P, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
  first | exact @GlobalTheory.mem_iSup_jointEigen_inf_of_stable | exact GlobalTheory.mem_iSup_jointEigen_inf_of_stable | (intros; apply GlobalTheory.mem_iSup_jointEigen_inf_of_stable <;> assumption)
end
