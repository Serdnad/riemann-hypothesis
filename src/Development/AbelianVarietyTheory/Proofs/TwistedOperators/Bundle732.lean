module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle582
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle699
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle706
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle730
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignFlatDictionaryAtOnePlaceLargeDepth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle731
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUnfoldingIntegratedOverFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfDepthValuations
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle565
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle729
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle557
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle031

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.RowAnn

theorem annRow_isCompact : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → IsCompact {u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) | MxAt (fun _ => True) u' ∧ ∀ u ∈ latRow G i, W.ψ (symplO _ _ u u') = 1} := by
  intro D _ T L μ0 hL sc G W M _ i hi

  have hsd : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.grid k 0)) (G.Λ (.grid k 0)) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    ·
      obtain ⟨c, hc⟩ := hL.βY 0 (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
      have hY := Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
      show IsSelfDualC (G.node (.grid 0 0)).sp (G.node (.grid 0 0)).lat
      rw [G.node_zero_zero]
      exact hY
    ·
      refine (G.isV (X := .grid k 0) ⟨hk, Nat.zero_le _⟩ ?_).sd
      intro j hj
      injection hj with h1 h2
      omega

  have hfin : FinLat (latRow G i) :=
    GlobalTheory.AscFin.DepLat.finLat_depLat G (.chi i 0) (isSelfDualC_neg (hsd (i + 1) hi)) (hsd i hi.le)
  obtain ⟨U, hU, h0, hUΓ⟩ := hfin.opn
  exact GlobalTheory.AnnNbhdCpt.isCompact_annSet W.ψ W.ψ_std _ _ (latRow G i) U hU h0 hUΓ

end GlobalTheory.AscFin.RowAnn

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

theorem _root_.GlobalTheory.T.depthLatticeGridRow_local_eq_completed_homLattice : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0, ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (· = v) u → (u ∈ latRow G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  first | exact @GlobalTheory.RowLoc.latRow_at | exact GlobalTheory.RowLoc.latRow_at | (intros; apply GlobalTheory.RowLoc.latRow_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v, ∀ e ∈ intAt D (· = v), ∀ u ∈ latRow G i, e • u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) := by
  first | exact @GlobalTheory.RowInt.smul_mem_latO_at | exact GlobalTheory.RowInt.smul_mem_latO_at | (intros; apply GlobalTheory.RowInt.smul_mem_latO_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

theorem comb_smul_heis {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  have h : ∀ u, heisO ψ S T u (a • f) = a • heisO ψ S T u f := fun u => by
    funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  unfold comb
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [h, smul_comm]

theorem movedAt_big : Big fun ch => MovedAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs _ => ?_⟩⟩
  obtain ⟨v, hv, κ, z, hz, hcol⟩ := GlobalTheory.T.exists_columnUnitVacuaFamily_moved large₂ F hS ch hIs
  choose κ' hκ' using fun i : Fin D.R.m => GlobalTheory.T.lastRow_moved_vacuum_eq_unit_mul_chosen large₂ F hS ch hIs i i.2
  refine ⟨v, hv, κ, fun i => if h : i < D.R.m then κ' ⟨i, h⟩ else 1, z, hz,
    fun t a β τ c hSum hExp hC d hd => ⟨fun j => ?_, fun i => ?_⟩⟩
  · have hvec := ((hSum.vec β τ hExp d hd).1 j)
    obtain ⟨e, -, hd1, -⟩ := hExp
    have hz1 := ((hd1 d hd).1 j).2.2
    rw [GlobalTheory.T.movedFiniteDatum_eq_heisenbergCombination_vacuum large₂ F hS ch hIs t (.top t j) (show DefPair D.R.m (Pair.top t (j : ℕ) : Pair T) from j.2) (d.1 j) ((c d).1 j) hz1 hvec ((hC d hd).1 j),
      hcol t j j.2, comb_smul_heis]
  · have hvec := ((hSum.vec β τ hExp d hd).2 i)
    obtain ⟨e, -, hd1, -⟩ := hExp
    have hz1 := ((hd1 d hd).2 i).2.2
    rw [GlobalTheory.T.movedFiniteDatum_eq_heisenbergCombination_vacuum large₂ F hS ch hIs t (.chi i D.R.m) (show DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) from ⟨i.2, rfl⟩) (d.2 i) ((c d).2 i) hz1 hvec ((hC d hd).2 i),
      hκ' i, comb_smul_heis]
    simp only [dif_pos i.2, combR]

end GlobalTheory.RowVal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastRow_unfolding_basicHypotheses : Big fun ch => BasicAt ch := by
  first | exact @GlobalTheory.RowBasic.basicAt | exact GlobalTheory.RowBasic.basicAt | (intros; apply GlobalTheory.RowBasic.basicAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flippedFiniteTensorLatticeFixed_largeDepth : Big fun ch => KFix ch := by
  first | exact @GlobalTheory.RowKFix.kfix | exact GlobalTheory.RowKFix.kfix | (intros; apply GlobalTheory.RowKFix.kfix <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unfoldedVacuaAreRealDatum_largeDepth : Big fun ch => VacReal ch := by
  first | exact @GlobalTheory.VacRealPf.vacReal | exact GlobalTheory.VacRealPf.vacReal | (intros; apply GlobalTheory.VacRealPf.vacReal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem _root_.GlobalTheory.T.exists_periodGroup_point_lifting_rowGroup_localElements : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ) t, ∀ j ∈ idx D, ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m)
    (δ : GA D (ch.G.V (.grid D.R.m j))), IsTilt ch.G j δ →
    ∀ l : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1),
      (∀ w, l w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
      ∃ y, HasLoc t ch.S.B hj y (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) ∧
        δ * y * δ⁻¹ ∈ rowGrp ch.G j := by
  first | exact @GlobalTheory.RowLift.lift_rowR | exact GlobalTheory.RowLift.lift_rowR | (intros; apply GlobalTheory.RowLift.lift_rowR <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_sign_flatDictionaryAtOnePlace_largeDepth : Big fun ch => ∃ s, PlaceAt ch s := by
  first | exact @GlobalTheory.FlatPlace.big_placeAt | exact GlobalTheory.FlatPlace.big_placeAt | (intros; apply GlobalTheory.FlatPlace.big_placeAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.corePair_integralPoint_pairs_trivially_half : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)), ∀ a ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True), IsHalf (cA D e) a → W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) a) = 1 := by
  first | exact @GlobalTheory.CoreOnto.IntDatum.psi_int | exact GlobalTheory.CoreOnto.IntDatum.psi_int | (intros; apply GlobalTheory.CoreOnto.IntDatum.psi_int <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.thetaLift_unfolding_integrated_over_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → Integrable (a.tot G Φ) (a.totMeas 𝓑) ∧ IntegrableOn (a.ker G Φ) 𝓑 a.vW.μ ∧ a.lhs G Φ = ∫ p, a.tot G Φ p ∂(a.totMeas 𝓑) ∧ ∀ S : Set (GA D W), MeasurableSet S → ∫ h in 𝓑 ∩ S, a.ker G Φ h ∂a.vW.μ = ∫ p in {p | p.1.1 ∈ S}, a.tot G Φ p ∂(a.totMeas 𝓑) := by
  first | exact @GlobalTheory.Asc.unfold_family | exact GlobalTheory.Asc.unfold_family | (intros; apply GlobalTheory.Asc.unfold_family <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeckeTermIdent

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare GlobalTheory.HeckeCount

theorem nonempty_hkKer_equiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (P : Ideal (𝓞 E)) (q i : ℕ) (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P q)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (z : FrPt Xo c Ω) :
    Nonempty (hkKer (Xo := Xo) P q i Ω z ≃ LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i)) := by
  have hs : IsSplitPrimeOff l q P := (splitPrime_iff l q P).2 (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.1 hP)
  have : CharZero Ω := charZero_of_injective_ringHom (Spec.preimage (z.x ≫ Xo.s)).hom.injective
  obtain ⟨o, ⟨m⟩⟩ := exists_fibre_obj Xo z.x z.x rfl
  obtain ⟨eT⟩ := nonempty_transfer_equiv Xo.univ m P q i
  obtain ⟨eL⟩ := nonempty_datum_equiv GlobalTheory.firstFiveLaws.1 o hs i
  exact ⟨eT.symm.trans ((heckeKerEquivDatum GlobalTheory.firstFiveLaws.1 o hs i).trans eL)⟩

end GlobalTheory.HeckeTermIdent

namespace GlobalTheory.HeckeTermIdent

open NumberField

theorem isHeckePrime_of_setting {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {i : Fin D.R.m} {P : Formalism.L2.DIV.Pl D.host.E} {p k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T.Q.l P.asIdeal p := by
  obtain ⟨hOff, hp, hpP, hM, -⟩ := hS
  refine GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, ?_, hp, hpP, hM⟩
  let b : 𝓞 D.host.E ≃+* 𝓞 D.host.E := Formalism.L2.Pj.barE D
  have hb : ∀ a : 𝓞 D.host.E, T.Q.H.bar a = b a := fun a => GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations.bar_eq_barE T.Q a
  have hmap : P.asIdeal.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    congr 1; exact RingHom.ext hb
  have hconj : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    apply le_antisymm
    · rw [Formalism.HermitianLatticesTheory.conjIdeal, Ideal.span_le]
      rintro r ⟨s, hs, e⟩
      have : r = b s := by
        apply RingOfIntegers.coe_injective
        exact e.trans rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ hs
    · rw [Ideal.map_le_iff_le_comap]
      intro s hs
      exact Ideal.subset_span ⟨s, hs, rfl⟩
  have hmax : (P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal := Ideal.map_isMaximal_of_equiv b
  have hne : P.asIdeal ≠ P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    intro e; exact hOff.1 (hconj.trans e.symm)
  rw [hmap]
  exact P.isMaximal.coprime_of_ne hmax hne

end GlobalTheory.HeckeTermIdent

namespace GlobalTheory.HeckeTermIdent

open NumberField

theorem heckeKernelCoset : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2, hx'⟩) z := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hFP P p k α Rc hS h hx
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hP := GlobalTheory.HeckeTermIdent.isHeckePrime_of_setting hS
  have hE := GlobalTheory.T.exists_heckeKernel_coset_framedPoint D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hFP P p k α Rc hS h hx
  choose f hfR hfZ using hE
  have hTot := hHk.2.1 _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hP (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)
  have hU : IsUnf (T.U ((i : ℕ) + 1) σ) := hTie.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ σ (hσ ▸ T.toCore.good_σ₀)
  let g : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) → Rc := fun C => ⟨f C, hfR C⟩
  have hinj : Function.Injective g := by
    intro C C' hCC
    have e : f C = f C' := congrArg Subtype.val hCC
    obtain ⟨z, hz⟩ := hTot C
    obtain ⟨z', hz'⟩ := hTot C'
    obtain ⟨hx1, t, ht, hb⟩ := hfZ C z hz
    have key : ∀ a, f C' = a → ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈
        ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
        (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z' := by
      rintro a rfl; exact hfZ C' z' hz'
    obtain ⟨hx2, t', ht', hb'⟩ := key (f C) e.symm
    exact GlobalTheory.T.heckeKernel_eq_of_unipotent_frameChange (T.Q.Xo ((i : ℕ) + 1)) T.Q.c σ D.R.r (T.U ((i : ℕ) + 1) σ) hU P.asIdeal p k hP _ _ C C' z z' _ t t'
      hz hz' ht ht' hb hb'
  have hfin : Finite (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) := Finite.of_injective g hinj
  obtain ⟨eK⟩ := GlobalTheory.HeckeTermIdent.nonempty_hkKer_equiv (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hP (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)
  have hcard : Nat.card Rc ≤ Nat.card (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) := by
    rw [Nat.card_congr eK, ← GlobalTheory.T.card_hecke_cosets_eq_card_submodules_split_place D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hFP P p k α Rc hS,
      Nat.card_eq_fintype_card, Fintype.card_coe]
  refine ⟨Equiv.ofBijective g (hinj.bijective_of_nat_card_le hcard), fun C z hz => hfZ C z hz⟩

end GlobalTheory.HeckeTermIdent
end
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedVectorsAreCombinationsOfVacua_of_large_depth : Big fun ch => MovedAt ch := by
  first | exact @GlobalTheory.RowVal.movedAt_big | exact GlobalTheory.RowVal.movedAt_big | (intros; apply GlobalTheory.RowVal.movedAt_big <;> assumption)

end
end
