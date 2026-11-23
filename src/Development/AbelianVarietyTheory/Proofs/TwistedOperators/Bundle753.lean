module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle746
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle745
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle750
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle710
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle752
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle451
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle747
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle748
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PcBF

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem symplO_neg_right' (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = - symplO S T x y := by
  have := symplO_add_right' S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right'] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem ann_of_mem {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (Γ Γ' : AddSubgroup (WO V W)) {a' : Mx D W.rank ρ}
    (ha' : a' ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₂) :
    ∀ a ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₁, ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1 := by
  intro a ha
  induction ha' using AddSubgroup.closure_induction with
  | mem b hb => exact hb.2 a ha
  | zero => rw [map_zero, symplO_zero_right', AddChar.map_zero_eq_one]
  | add b c _ _ hb hc => rw [map_add (f := _), symplO_add_right', AddChar.map_add_eq_mul, hb, hc, one_mul]
  | neg b _ hb => rw [map_neg, symplO_neg_right', AddChar.map_neg_eq_inv, hb, inv_one]

end GlobalTheory.PcBF

namespace GlobalTheory.PcBF

theorem pieces_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (pcBF W F ρ h).Is (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ ∧ Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  set_option maxHeartbeats 0 in
    intro D hD T L μ0 hL sc G W M hM F hF ρ h
    refine ⟨⟨GlobalTheory.T.finite_lattice_standard_parabolic D hD T L μ0 hL sc G W M hM F hF ρ h, ⟨?_, (GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
      (GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices D hD T L μ0 hL sc G W M hM F hF ρ h).2, ?_, ?_,
      (GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators D hD T L μ0 hL sc G W M hM F hF ρ h).2,
      GlobalTheory.T.genericCharacter_trivial_besselStep_unitriangular D hD T L μ0 hL sc G W M hM F hF ρ h, (GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
      GlobalTheory.T.besselToFourierJacobi_depthLattice_splits D hD T L μ0 hL sc G W M hM F hF ρ h⟩
    · intro a' ha'
      induction ha' using AddSubgroup.closure_induction with
      | mem b hb => exact hb.1
      | zero => intro i j; simp only [Matrix.zero_apply]; exact zero_mem _
      | add b c _ _ hb hc => intro i j; simp only [Matrix.add_apply]; exact add_mem (hb i j) (hc i j)
      | neg b _ hb => intro i j; simp only [Matrix.neg_apply]; exact neg_mem (hb i j)
    · intro a ha
      exact ⟨fun h1 a' h2 => ann_of_mem _ _ _ _ _ h2 a h1, GlobalTheory.T.biduality_depth_lattice_piece_bessel_step D hD T L μ0 hL sc G W M hM F hF ρ h a ha⟩
    · intro a' ha'
      exact ⟨fun h2 a h1 => ann_of_mem _ _ _ _ _ h2 a h1, fun H => AddSubgroup.subset_closure ⟨ha', fun a h1 => H a h1⟩⟩

end GlobalTheory.PcBF
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

namespace GlobalTheory.LineComp

theorem star_smul_mem_span : ∀ (D : D7) (n : ℕ) (I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), D.host.AAbar * I ≤ D.host.AA * J → ∀ a ∈ D.host.AA, ∀ s ∈ idLat I Λ, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat J Λ, y = a' • s'} := by
  intro D n I J Λ hIJ a ha s hs
  have hsa : star a ∈ D.host.AAbar := by
    have e : star a = D.host.conj a := by
      first
      | exact GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.bridge_star_holds D.R D.host a
      | exact Formalism.BasicNotions.Examples₂.star_eq_conj D.host a
      | (apply D.host.φ₀.injective
         have h1 : D.host.φ₀ (D.host.conj a) = starRingEnd ℂ (D.host.φ₀ a) := Formalism.HC.HostAx.conjE_apply _ _ _
         rw [h1]
         haveI := D.host.isCMField_hostE
         exact IsCMField.complexEmbedding_complexConj _ _ _)
    rw [e]; exact Formalism.L2.Pj.conj_mem_AAbar D ha
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, y, hy, rfl⟩ := hx
    have hm : star a * c ∈ (D.host.AA * J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      hIJ (FractionalIdeal.mul_mem_mul hsa hc)
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hm
    rw [smul_smul]
    have key : ∀ z ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) * (J : Submodule (𝓞 D.host.E) D.host.E)),
        z • y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat J Λ, y = a' • s'} := by
      intro z hz
      induction hz using Submodule.mul_induction_on' with
      | mem_mul_mem a' ha' j hj =>
        exact Submodule.subset_span ⟨a', ha', j • y, Submodule.subset_span ⟨j, hj, y, hy, rfl⟩, by rw [smul_smul]⟩
      | add x x' _ _ ihx ihy => rw [add_smul]; exact Submodule.add_mem _ ihx ihy
    exact key _ hm
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem stairRatio_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (σ : ℕ), D.host.AAbar * (G.pl.stA sc ^ (σ + 2) * (G.pl.stAbar sc ^ (σ + 2))⁻¹) ≤ D.host.AA * (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹ * shiftId G) := by
  intro D T L sc G σ
  have hA : (D.host.AAbar : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h] at h1
    simp at h1
  refine le_of_eq ?_
  simp only [shiftId, Places.stA, Places.stAbar, GridData.modul]
  generalize D.host.AA = a at *
  generalize D.host.AAbar = b at *
  generalize ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = n
  generalize ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = m
  rw [pow_succ (a * n⁻¹) (σ + 1), pow_succ (b * m⁻¹) (σ + 1), mul_inv (_ ^ (σ + 1)), mul_inv b, inv_inv]
  calc b * ((a * n⁻¹) ^ (σ + 1) * (a * n⁻¹) * (((b * m⁻¹) ^ (σ + 1))⁻¹ * (b⁻¹ * m)))
      = (b * b⁻¹) * (a * ((a * n⁻¹) ^ (σ + 1) * ((b * m⁻¹) ^ (σ + 1))⁻¹ * (m * n⁻¹))) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA, one_mul]

theorem main : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀,
    ∃ w ∈ lineLat F ρ, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 = (F.lnk ρ).κ _ w := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  refine ⟨_, ?_, (GlobalTheory.T.standardFrameLink_map_inverts_hermitianSkewAdjoint D hq T L μ0 hL sc G W M hM F hF ρ _).symm⟩
  cases ρ with
  | zero => exact GlobalTheory.T.besselStepZero_lineComponent_adjoint_mem_lattice D hq T L μ0 hL sc G W M hM F hF h u hu
  | succ σ =>
    exact GlobalTheory.T.hermitianSkewAdjoint_mem_adjoint_homLattice D _ _ _ _ _ _ (star_smul_mem_span D _ _ _ _ (stairRatio_le G σ)) _
      (GlobalTheory.T.bessel_step_line_component_mem_hom_lattice D hq T L μ0 hL sc G W M hM F hF (σ + 1) h u hu)

end GlobalTheory.LineComp

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

theorem _root_.GlobalTheory.T.fourierJacobi_step_pieces_admissible_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (pcFB W F σ h h').Is (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ ∧ Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  first | exact @GlobalTheory.AscFin.piecesFB_is_and_splits | exact GlobalTheory.AscFin.piecesFB_is_and_splits | (intros; apply GlobalTheory.AscFin.piecesFB_is_and_splits <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem levels_invariant (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T}
    (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (ht : t ∈ U)
    (hβ : β ∈ S.supp t Φ) (hτ : S.IsExpansion t Φ β τ)
    (hv : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) :
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    ((∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
      x D.R.m = finEmb G.sp.topDec (y D.R.m) → finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
      pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0))) :=
  ⟨GlobalTheory.T.expansionPairing_invariant_inner_vertex_level S hL hde hc ht hβ hτ hv Ψ F, GlobalTheory.T.expansionPairing_invariant_parabolic_basePoint S hL hde hc ht hβ hτ hv Ψ F,
    GlobalTheory.T.expansionPairing_invariant_innerVertex_level S hL hde hc ht hβ hτ hv Ψ F, GlobalTheory.T.expansion_pairing_invariant_last_vertex_level S hL hde hc ht hβ hτ hv Ψ F⟩

end GlobalTheory.ExpansionInvariance

end
end
