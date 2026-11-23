module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle736
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle748
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiAnnihilatorPieceCompactOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialFourierJacobiStep
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle749
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodGivesFourierJacobiPeriodOfLift
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.core_chain_composites_exist_lift_combinations : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → DepFixed → CoreModels → ChainEx := by
  first | exact @GlobalTheory.ChainLifts.chainEx | exact GlobalTheory.ChainLifts.chainEx | (intros; apply GlobalTheory.ChainLifts.chainEx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.SplitsFB

theorem inv_neg_mat {D : D7} {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem symplO_negSp {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have e : hO (negSp S) T x y = -hO S T x y := by
    unfold hO
    rw [negSp_gram, inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplO
  rw [e, mul_neg, map_neg]

theorem symplO_zero_left' {D : D7} (S T : HSp D) (y : WO S T) : symplO S T 0 y = 0 := by
  unfold symplO hO
  simp

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem sd_grid (i : ℕ) (h1 : 1 ≤ i) (h : i ≤ D.R.m) : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) :=
  (G.isV (X := .grid i 0) (by show _ ∧ _; constructor <;> omega) (by intro j hj; injection hj with h2; omega)).sd

theorem latRow_mxAt (i : ℕ) (h1 : 1 ≤ i) (h : i + 1 ≤ D.R.m) {u} (hu : u ∈ latRow G i) : MxAt (fun _ => True) u :=
  ((GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D _ _ _ _ (isSelfDualC_neg (sd_grid G (i + 1) (by omega) h)) (sd_grid G i h1 (by omega)) (fun _ => True) u).1
    hu.1).1

theorem latRow_pair (W : G.Weil) (i : ℕ) (h1 : 1 ≤ i) (h : i + 1 ≤ D.R.m) {u u'} (hu : u ∈ latRow G i) (hu' : u' ∈ latRow G i) :
    W.ψ (symplO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) u u') = 1 := by
  have := (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D W.ψ W.ψ_std _ _ _ _ (isSelfDualC_neg (sd_grid G (i + 1) (by omega) h)) (sd_grid G i h1 (by omega))
    (fun _ => True) u (latRow_mxAt G i h1 h hu)).1 hu.1 u' hu'.1
  rwa [symplO_negSp, AddChar.map_neg_eq_inv, inv_eq_one] at this

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {x : Mx D m n} (hx : MxAt P x) (y : Mx D n k) : MxAt P (x ⬝ y) :=
  fun i j => by
    show (x * y) i j ∈ _
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

end



theorem splits_FB : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hS := GlobalTheory.T.depthLatticeGridRow_stable_witt_projections D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hT := GlobalTheory.T.depthLatticeGridRow_stable_wittTargetProjections D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hC := GlobalTheory.T.fourierJacobi_basePoint_character_trivial_depthLattice D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hB := GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) (by omega)
  refine ⟨fun u hu => ?_⟩
  set dV := F.dJ (σ + 1) h with hdV
  set dW := F.dB σ h' with hdW
  obtain ⟨hX, hY⟩ := hS u hu
  have e1 := dV.sum_eq_one
  have e2 := dW.sum_eq_one
  have h0 : u ⬝ (dV.j0 ⬝ dV.p0) ∈ latRow G (2 * σ + 2) := by
    have s : u ⬝ (dV.jX ⬝ dV.pX) + u ⬝ (dV.j0 ⬝ dV.p0) + u ⬝ (dV.jY ⬝ dV.pY) = u := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, e1, Matrix.mul_one]
    have e : u ⬝ (dV.j0 ⬝ dV.p0) = u - u ⬝ (dV.jX ⬝ dV.pX) - u ⬝ (dV.jY ⬝ dV.pY) := by
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
      conv_rhs => rw [← s]
      abel
    rw [e]
    exact sub_mem (sub_mem hu hX) hY
  set w := u ⬝ (dV.j0 ⬝ dV.p0) with hw
  obtain ⟨gX, gY⟩ := hT w h0
  have g0 : (dW.j0 ⬝ dW.p0) ⬝ w ∈ latRow G (2 * σ + 2) := by
    have s : (dW.jX ⬝ dW.pX) ⬝ w + (dW.j0 ⬝ dW.p0) ⬝ w + (dW.jY ⬝ dW.pY) ⬝ w = w := by
      rw [← Matrix.add_mul, ← Matrix.add_mul, e2, Matrix.one_mul]
    have e : (dW.j0 ⬝ dW.p0) ⬝ w = w - (dW.jX ⬝ dW.pX) ⬝ w - (dW.jY ⬝ dW.pY) ⬝ w := by
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
      conv_rhs => rw [← s]
      abel
    rw [e]
    exact sub_mem (sub_mem h0 gX) gY
  have hA1 : dV.extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jX) ∈ latRow G (2 * σ + 2) := by
    rw [HypDec.extX_apply, Matrix.mul_assoc]; exact hX
  have hA2 : dV.extY (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jY) ∈ latRow G (2 * σ + 2) := by
    rw [HypDec.extY_apply, Matrix.mul_assoc]; exact hY
  have hB1 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0))) = (dW.jX ⬝ dW.pX) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, hw]; simp only [Matrix.mul_assoc]
  have hB2 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0))) = (dW.jY ⬝ dW.pY) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, hw]; simp only [Matrix.mul_assoc]
  have hG0 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) = (dW.j0 ⬝ dW.p0) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, hw]; simp only [Matrix.mul_assoc]
  have heq : u = dV.extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jX) + dV.extY (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jY) +
      dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0)) + dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0)) +
        dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) := by
    rw [map_add (f := _), map_add (f := _), hB1, hB2, hG0, HypDec.extX_apply, HypDec.extY_apply, ← Matrix.add_mul, ← Matrix.add_mul,
      show dW.jX ⬝ dW.pX + dW.jY ⬝ dW.pY + dW.j0 ⬝ dW.p0 = 1 from (add_right_comm _ _ _).trans e2, Matrix.one_mul, hw,
      Matrix.mul_assoc, Matrix.mul_assoc]
    have s : u ⬝ (dV.jX ⬝ dV.pX) + u ⬝ (dV.j0 ⬝ dV.p0) + u ⬝ (dV.jY ⬝ dV.pY) = u := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, e1, Matrix.mul_one]
    conv_lhs => rw [← s]
    abel
  refine ⟨u ⬝ dV.jX, hA1, u ⬝ dV.jY, AddSubgroup.subset_closure
      ⟨mxAt_mul (latRow_mxAt G (2 * σ + 2) (by omega) (by omega) hu) _,
        fun a ha => latRow_pair G W (2 * σ + 2) (by omega) (by omega) ha hA2⟩,
    dW.pX ⬝ (u ⬝ dV.j0), ?_, dW.pY ⬝ (u ⬝ dV.j0), ?_, dW.p0 ⬝ (u ⬝ dV.j0), ?_, heq, hC _ hA2, ?_⟩
  · show dV.ext0 _ (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0))) ∈ latBig G (2 * σ + 2)
    rw [hB1]; exact hB gX
  · show dV.ext0 _ (dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0))) ∈ latBig G (2 * σ + 2)
    rw [hB2]; exact hB gY
  · show dV.ext0 _ (dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) ∈ latRow G (2 * σ + 2)
    rw [hG0]; exact g0
  · rw [map_zero, symplO_zero_left', AddChar.map_zero_eq_one]

end GlobalTheory.AscFin.SplitsFB
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

theorem _root_.GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), IsCompact ((pcBF W F ρ h).A₂ : Set (Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ)) ∧ ∃ U : Set (Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ), IsOpen U ∧ (0 : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ) ∈ U ∧ ∀ a ∈ U, MxAt (fun _ => True) a → a ∈ (pcBF W F ρ h).A₂ := by
  first | exact @GlobalTheory.AnnPiece.pcBF_A₂_compact_open | exact GlobalTheory.AnnPiece.pcBF_A₂_compact_open | (intros; apply GlobalTheory.AnnPiece.pcBF_A₂_compact_open <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.fourierJacobiToBessel_pieces_mutual_annihilators : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₂ ∧ (∀ a, MxAt (fun _ => True) a → (a ∈ (pcFB W F σ h h').A₁ ↔ ∀ a' ∈ (pcFB W F σ h h').A₂, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) ∧ (∀ a', MxAt (fun _ => True) a' → (a' ∈ (pcFB W F σ h h').A₂ ↔ ∀ a ∈ (pcFB W F σ h h').A₁, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) := by
  first | exact @GlobalTheory.AscFin.AnnPieces.pcFB_dualA | exact GlobalTheory.AscFin.AnnPieces.pcFB_dualA | (intros; apply GlobalTheory.AscFin.AnnPieces.pcFB_dualA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.lattice_membership_adjoint_iff : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, 0 < ρ → ∀ a ∈ idAt D (· = v), (F.dJ ρ h).incAdj (F.V₀ ρ) (a • yBF F ρ h) ∈ latO (F.V₀ ρ) _ (lat0 F ρ h : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.AscFin.incAdj_yBF_mem_latO_iff | exact GlobalTheory.AscFin.incAdj_yBF_mem_latO_iff | (intros; apply GlobalTheory.AscFin.incAdj_yBF_mem_latO_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.star_adjoint_mem_hat_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2)) ∈ hatMx (G.modul • homLat (G.Λ (.core (2 * 0 + 1))) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  first | exact @GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep | exact GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep | (intros; apply GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.additive_character_superdiag_trivial : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∈ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  first | exact @GlobalTheory.AscFin.psiE_superdiag_S0 | exact GlobalTheory.AscFin.psiE_superdiag_S0 | (intros; apply GlobalTheory.AscFin.psiE_superdiag_S0 <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselToFourierJacobi_depthLattice_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  first | exact @GlobalTheory.AscFin.pcBF_splits | exact GlobalTheory.AscFin.pcBF_splits | (intros; apply GlobalTheory.AscFin.pcBF_splits <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.fourierJacobi_depthDatum_mul_lineVacuum_isVacuum : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ Ξ₁ Φ₀, VacG W.ψ _ _ (latCore G (2 * σ + 2)) Ξ₁ → VacG W.ψ _ _ (lineLat F (σ + 1)) Φ₀ → VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ ((F.oB σ h').boxT _ Ξ₁ Φ₀) := by
  first | exact @GlobalTheory.BoxFB.vacG_boxT_fb | exact GlobalTheory.BoxFB.vacG_boxT_fb | (intros; apply GlobalTheory.BoxFB.vacG_boxT_fb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.genericCharacter_trivial_fourierJacobi_step : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u : UX D (σ + 1), MxAt (fun _ => True) (u.1.1 - 1) → xFB F σ h' ⬝ u.1.1 - xFB F σ h' ∈ (pcFB W F σ h h').A₁ → psiUni W.ψ u.1 = 1 := by
  first | exact @GlobalTheory.UniStepFB.psiUni_pcFB | exact GlobalTheory.UniStepFB.psiUni_pcFB | (intros; apply GlobalTheory.UniStepFB.psiUni_pcFB <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.bessel_period_gives_fourierJacobi_period_of_lift : ∀ D : D7, UpFB D := by
  first | exact @GlobalTheory.UpFromBessel.upFB | exact GlobalTheory.UpFromBessel.upFB | (intros; apply GlobalTheory.UpFromBessel.upFB <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.fourierJacobi_period_gives_bessel_period_of_lift : ∀ D : D7, UpBF D := by
  first | exact @GlobalTheory.UpBessel.upBF | exact GlobalTheory.UpBessel.upBF | (intros; apply GlobalTheory.UpBessel.upBF <;> assumption)
end
