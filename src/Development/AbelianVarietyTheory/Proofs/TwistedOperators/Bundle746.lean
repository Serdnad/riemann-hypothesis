module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle741
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle742
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle743
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle744
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiStepCoreComponentMemCoreDepthLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesMutualAnnihilators
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.bessel_depth_lattice_core_splits_along_target_witt : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)), (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) → (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ w)) ∈ latRow G (2 * ρ + 1) := by
  first | exact @GlobalTheory.AscFin.latRow_bessel_core_split | exact GlobalTheory.AscFin.latRow_bessel_core_split | (intros; apply GlobalTheory.AscFin.latRow_bessel_core_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.biduality_depth_lattice_piece_bessel_step : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ a, MxAt (fun _ => True) a → (∀ a' ∈ (pcBF W F ρ h).A₂, W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1) → a ∈ (pcBF W F ρ h).A₁ := by
  first | exact @GlobalTheory.AscFin.BidualLattice.bidual_pcBF | exact GlobalTheory.AscFin.BidualLattice.bidual_pcBF | (intros; apply GlobalTheory.AscFin.BidualLattice.bidual_pcBF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.last_seesaw_lattices_nonzero_line_vacua : OnStd fun {D} _ _ _ {G} W F => (∀ ρ, 2 * ρ + 2 ≤ D.R.m → ∃ Φ₀, VacG W.ψ _ _ (lineLat F ρ) Φ₀ ∧ Φ₀ ≠ 0) ∧ ∀ (v : CoreVol G) h, LastLat W.ψ (F.jac v 0 h) F.oz (latRow G 0) (lineLat F 0) (latCore G 0) := by
  first | exact @GlobalTheory.LastSeeSaw.lastLat_std | exact GlobalTheory.LastSeeSaw.lastLat_std | (intros; apply GlobalTheory.LastSeeSaw.lastLat_std <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcBF W F ρ h).B₁ ↔ ∀ η ∈ (pcBF W F ρ h).B₂, W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1)) ∧ ∀ η, MxAt (fun _ => True) η → (η ∈ (pcBF W F ρ h).B₂ ↔ ∀ ξ ∈ (pcBF W F ρ h).B₁, W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1) := by
  first | exact @GlobalTheory.PcBFDual.dualB | exact GlobalTheory.PcBFDual.dualB | (intros; apply GlobalTheory.PcBFDual.dualB <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.jacobi_depth_lattice_keeps_isotropic_hom_part : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), (F.dJ (σ + 1) h).extX _ (u ⬝ (F.dJ (σ + 1) h).jX) ∈ latRow G (2 * σ + 2) := by
  first | exact @GlobalTheory.AscFin.SplitX.latRow_extX | exact GlobalTheory.AscFin.SplitX.latRow_extX | (intros; apply GlobalTheory.AscFin.SplitX.latRow_extX <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (∀ u ∈ (pcBF W F ρ h).Γ₀, MxAt (fun _ => True) (show Mx D (G.V (.core (2 * ρ + 1))).rank (F.V₀ ρ).rank from u)) ∧ ∃ f, VacG W.ψ (F.V₀ ρ) (G.V (.core (2 * ρ + 1))) (pcBF W F ρ h).Γ₀ f ∧ f ≠ 0 := by
  first | exact @GlobalTheory.AscFin.CorePiece.core_fin_vac | exact GlobalTheory.AscFin.CorePiece.core_fin_vac | (intros; apply GlobalTheory.AscFin.CorePiece.core_fin_vac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.bessel_step_line_component_mem_hom_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 ∈ latO (negSp F.Lz) (G.V (.core (2 * ρ + 1))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _) (G.Λ (.core (2 * ρ + 1)) : Set _) fun _ => True := by
  first | exact @GlobalTheory.AscFin.BoxBF.lineComp_mem_latO | exact GlobalTheory.AscFin.BoxBF.lineComp_mem_latO | (intros; apply GlobalTheory.AscFin.BoxBF.lineComp_mem_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.jacobi_to_bessel_core_piece_nonzero_vacuum : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∃ f, VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ f ∧ f ≠ 0 := by
  first | exact @GlobalTheory.AscFin.PcFBVac.pcFB_vac | exact GlobalTheory.AscFin.PcFBVac.pcFB_vac | (intros; apply GlobalTheory.AscFin.PcFBVac.pcFB_vac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.bessel_depth_lattice_splits_along_source_witt : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) ∈ latRow G (2 * ρ + 1) ∧ (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) ∈ latRow G (2 * ρ + 1) ∧ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) ∈ latRow G (2 * ρ + 1) := by
  first | exact @GlobalTheory.AscFin.srcSplit_pcBF | exact GlobalTheory.AscFin.srcSplit_pcBF | (intros; apply GlobalTheory.AscFin.srcSplit_pcBF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.depth_lattice_core_parts_mem_selfDual_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)), (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) → (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ w)) ∈ latBig G (2 * ρ + 1) ∧ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ w)) ∈ latBig G (2 * ρ + 1) := by
  first | exact @GlobalTheory.AscFin.pcBF_big_core | exact GlobalTheory.AscFin.pcBF_big_core | (intros; apply GlobalTheory.AscFin.pcBF_big_core <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.jacobi_step_core_component_mem_core_depth_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := by
  first | exact @GlobalTheory.CoreComp.core_mem_latCore | exact GlobalTheory.CoreComp.core_mem_latCore | (intros; apply GlobalTheory.CoreComp.core_mem_latCore <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.jacobi_to_bessel_pieces_mutual_annihilators : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcFB W F σ h h').B₁ ↔ ∀ η ∈ (pcFB W F σ h h').B₂, W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) ∧ (∀ η, MxAt (fun _ => True) η → (η ∈ (pcFB W F σ h h').B₂ ↔ ∀ ξ ∈ (pcFB W F σ h h').B₁, W.ψ (symplO _ _ ((F.dB σ h').incX _ ξ) ((F.dB σ h').incY _ η)) = 1)) := by
  first | exact @GlobalTheory.AscFin.DualParts.pcFB_dual | exact GlobalTheory.AscFin.DualParts.pcFB_dual | (intros; apply GlobalTheory.AscFin.DualParts.pcFB_dual <;> assumption)
end
