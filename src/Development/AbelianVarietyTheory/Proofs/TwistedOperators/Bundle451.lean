module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle417
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle418
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjections
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle064
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.standardFrameLink_map_inverts_hermitianSkewAdjoint : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (x : WO (negSp F.Lz) (G.V (.core (2 * ρ + 1)))), (F.lnk ρ).κ _ (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ x) = x := by
  first | exact @GlobalTheory.KapAdjLine.kap_starAdj | exact GlobalTheory.KapAdjLine.kap_starAdj | (intros; apply GlobalTheory.KapAdjLine.kap_starAdj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.depthLatticeGridRow_dualPart_finite_pairs_trivially : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), MxAt (fun _ => True) (u ⬝ (F.dB ρ h).jY) ∧ ∀ a, (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a ∈ latRow G (2 * ρ + 1) → W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  first | exact @GlobalTheory.AscFin.BesIso.splits_iso | exact GlobalTheory.AscFin.BesIso.splits_iso | (intros; apply GlobalTheory.AscFin.BesIso.splits_iso <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.star_smul_mem_span_modulusDivConjugate_lattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {n : ℕ} (Λ₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), ∀ a ∈ D.host.AA, ∀ s ∈ idLat (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) Λ₀, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
  first | exact @GlobalTheory.AdjSrcZero.star_smul_mem_span | exact GlobalTheory.AdjSrcZero.star_smul_mem_span | (intros; apply GlobalTheory.AdjSrcZero.star_smul_mem_span <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.depthLatticeGridRow_stable_wittTargetProjections : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (_ : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), ((F.dB σ h').jX * (F.dB σ h').pX) * u ∈ latRow G (2 * σ + 2) ∧ ((F.dB σ h').jY * (F.dB σ h').pY) * u ∈ latRow G (2 * σ + 2) := by
  first | exact @GlobalTheory.AscFin.latRow_proj_tgt | exact GlobalTheory.AscFin.latRow_proj_tgt | (intros; apply GlobalTheory.AscFin.latRow_proj_tgt <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMix

theorem finite_rat_mem_of_isCompact {D : D7} {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, -, -, ht2, hdisc, -⟩ := lattice_Mx D m n
  haveI : IsTopologicalAddGroup (Mx D m n) := hg
  haveI : T2Space (Mx D m n) := ht2
  haveI : T1Space (Mx D m n) := @T2Space.t1Space _ _ ht2
  haveI : DiscreteTopology (ratMx D m n) := hdisc
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, rat_mem γ⟩, hγ, rfl⟩

theorem poinX_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → Continuous (poinX ψ d T β) := by
  intro D ψ hψ S S₀ T ρ d β hβ
  obtain ⟨hg, hlc, -, -, -, -⟩ := lattice_Mx D T.rank S.rank
  haveI : IsTopologicalAddGroup (WO S T) := hg
  haveI : LocallyCompactSpace (WO S T) := hlc
  obtain ⟨hg', -, -, -, -, -⟩ := lattice_Mx D T.rank ρ
  haveI : IsTopologicalAddGroup (Mx D T.rank ρ) := hg'
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg'
  have hjX : Continuous fun u : WO S T => u ⬝ d.jX := Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const
  have hjY : Continuous fun u : WO S T => u ⬝ d.jY := Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const
  have hterm : ∀ γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, Continuous fun u : WO S T =>
      ψ (trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) * β (u ⬝ d.jX + rat γ) := by
    intro γ
    have e : (fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) =
        fun u : WO S T => symplOH S T (d.extX T (u ⬝ d.jX + 2 • rat γ)) (d.extY T (u ⬝ d.jY)) :=
      funext fun u => (d.symplOH_extX_extY T _ _).symm
    have hc : Continuous fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY)) := by
      rw [e]
      refine GlobalTheory.OrientedHeis.continuous_symplOH ?_ ?_
      · simp only [HypDec.extX_apply]
        exact (hjX.add continuous_const).matrix_mul continuous_const
      · simp only [HypDec.extY_apply]
        exact hjY.matrix_mul continuous_const
    exact (hψ.1.1.comp hc).mul (hβ.cont.comp (hjX.add continuous_const))
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds u₀
  have hK : IsCompact ((fun p : Mx D T.rank ρ × WO S T => p.1 - p.2 ⬝ d.jX) '' (tsupport β ×ˢ U)) :=
    (hβ.supp.isCompact.prod hU).image (continuous_fst.sub (Continuous.matrix_mul (A := fun p : Mx D T.rank ρ × WO S T => p.2) continuous_snd continuous_const))
  have hF := finite_rat_mem_of_isCompact _ hK
  have vanish : ∀ u ∈ U, ∀ γ, γ ∉ hF.toFinset → β (u ⬝ d.jX + rat γ) = 0 := by
    intro u hu γ hγ
    by_contra hne
    exact hγ (hF.mem_toFinset.2 ⟨(u ⬝ d.jX + rat γ, u), ⟨subset_tsupport β hne, hu⟩, add_sub_cancel_left _ _⟩)
  refine (continuous_finsetSum hF.toFinset fun γ _ => hterm γ).continuousAt.congr
    (Filter.eventually_of_mem hUn fun u hu => ?_)
  show _ = poinX ψ d T β u
  unfold poinX
  refine (tsum_eq_sum fun γ hγ => ?_).symm
  rw [vanish u hu γ hγ, mul_zero]

end GlobalTheory.BumpMix

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixSmooth

variable {D : D7}

theorem finite_rat_mem (m n : ℕ) (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, hlc, -, ht2, hdisc, -⟩ := lattice_Mx D m n
  letI : IsTopologicalAddGroup (Mx D m n) := hg
  letI : T2Space (Mx D m n) := ht2
  letI : T1Space (Mx D m n) := T2Space.t1Space
  letI : DiscreteTopology (ratMx D m n) := hdisc
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, γ, rfl⟩, hγ, rfl⟩

theorem contDiff_of_additive {k : ℕ} (f : (Fin k → ℝ) → ℂ) (h0 : f 0 = 0) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hc : Continuous f) : ContDiff ℝ ∞ f :=
  GlobalTheory.WeilVacMove.contDiff_additive (⟨⟨f, h0⟩, hadd⟩ : (Fin k → ℝ) →+ ℂ) hc

def rmul {m n p : ℕ} (Q : Mx D n p) : Mx D m n →+ Mx D m p where
  toFun x := x ⬝ Q
  map_zero' := Matrix.zero_mul _
  map_add' x y := Matrix.add_mul _ _ _

theorem continuous_rmul {m n p : ℕ} (Q : Mx D n p) : Continuous (rmul (m := m) Q) :=
  continuous_id.matrix_mul continuous_const

theorem contDiff_psi_symplOH {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {k : ℕ}
    (A B : (Fin k → ℝ) →+ WO S T) (hA : Continuous A) (hB : Continuous B)
    (hA0 : ∀ t, (A t).map (finPart D) = 0) (hB0 : ∀ t, (B t).map (finPart D) = 0) (c c' : WO S T) :
    ContDiff ℝ ∞ fun t => ψ (symplOH S T (c + A t) (c' + B t)) := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  have hadd1 := GlobalTheory.WeilVacMove.symplOH_add_left S T
  have hadd2 := GlobalTheory.WeilVacMove.symplOH_add_right S T
  have hz1 := GlobalTheory.WeilVacMove.symplOH_zero_left S T
  have hz2 := GlobalTheory.WeilVacMove.symplOH_zero_right S T
  have h1 : ContDiff ℝ ∞ fun t => lam (symplOH S T c (B t)) :=
    contDiff_of_additive _ (by rw [map_zero, hz2, map_zero]) (fun x y => by rw [map_add (f := _), hadd2, map_add (f := _)])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_const hB))
  have h2 : ContDiff ℝ ∞ fun t => lam (symplOH S T (A t) c') :=
    contDiff_of_additive _ (by rw [map_zero, hz1, map_zero]) (fun x y => by rw [map_add (f := _), hadd1, map_add (f := _)])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hA continuous_const))
  have hQ : ContDiff ℝ ∞ fun t => lam (symplOH S T (A t) (B t)) := by
    let φ : (Fin k → ℝ) → ((Fin k → ℝ) →+ ℂ) := fun t =>
      { toFun := fun s => lam (symplOH S T (A s) (B t))
        map_zero' := by rw [map_zero, hz1, map_zero]
        map_add' := fun x y => by rw [map_add (f := _), hadd1, map_add (f := _)] }
    have hφ : ∀ t, Continuous (φ t) := fun t =>
      hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hA continuous_const)
    have e : (fun t => lam (symplOH S T (A t) (B t))) =
        fun t => ∑ i, t i • lam (symplOH S T (A fun j => if i = j then 1 else 0) (B t)) := by
      funext t
      exact LinearMap.pi_apply_eq_sum_univ ((φ t).toRealLinearMap (hφ t) : (Fin k → ℝ) →ₗ[ℝ] ℂ) t
    rw [e]
    refine ContDiff.sum fun i _ => (contDiff_apply ℝ (fun _ => ℝ) i).smul ?_
    exact contDiff_of_additive _ (by rw [map_zero, hz2, map_zero]) (fun x y => by rw [map_add (f := _), hadd2, map_add (f := _)])
      (hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_const hB))
  have e : ∀ t, ψ (symplOH S T (c + A t) (c' + B t)) = ψ (symplOH S T c c') *
      Complex.exp (lam (symplOH S T c (B t)) + lam (symplOH S T (A t) c') + lam (symplOH S T (A t) (B t))) := by
    intro t
    have hs : sndA D.host.F (symplOH S T c (B t) + symplOH S T (A t) c' + symplOH S T (A t) (B t)) = 0 := by
      rw [map_add (f := _), map_add (f := _), GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inr (hB0 t)),
        GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inl (hA0 t)), GlobalTheory.WeilVacMove.snd_symplOH S T _ _ (Or.inl (hA0 t)),
        add_zero, add_zero]
    rw [hadd1, hadd2, hadd2, show ∀ a b c d : AF D.host.F, a + b + (c + d) = a + (b + c + d) from fun _ _ _ _ => by abel,
      AddChar.map_add_eq_mul, hlam _ hs, map_add, map_add]
  rw [show (fun t => ψ (symplOH S T (c + A t) (c' + B t))) = _ from funext e]
  exact contDiff_const.mul ((h1.add h2).add hQ).cexp

end GlobalTheory.BumpMixSmooth

namespace GlobalTheory.BumpMixSmooth

theorem poinX_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ)
    (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L →
    (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => poinX ψ d T β (w + L t) := by
  intro D ψ hψ S S₀ T ρ d β hβ k L hL hL0 w
  obtain ⟨hg, hlc, -, -, -, -⟩ := lattice_Mx D T.rank ρ
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg
  have hx : Continuous fun t => (w + L t) ⬝ d.jX := (continuous_const.add hL).matrix_mul continuous_const
  let lX := (rmul (m := T.rank) d.jX).comp L
  let lY := (rmul (m := T.rank) d.jY).comp L
  have hlX : Continuous lX := (continuous_rmul _).comp hL
  have hlY : Continuous lY := (continuous_rmul _).comp hL
  have hlX0 : ∀ t, (lX t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hL0 t) _
  have hlY0 : ∀ t, (lY t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hL0 t) _
  let A := (d.extX T).comp lX
  let B := (d.extY T).comp lY
  have hA : Continuous A := show Continuous fun t => lX t ⬝ d.pX from hlX.matrix_mul continuous_const
  have hB : Continuous B := show Continuous fun t => lY t ⬝ d.pY from hlY.matrix_mul continuous_const
  have hA0 : ∀ t, (A t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hlX0 t) d.pX
  have hB0 : ∀ t, (B t).map (finPart D) = 0 := fun t => map_mul_eq_zero_left (finPart D) (hlY0 t) d.pY
  have hterm : ∀ γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ContDiff ℝ ∞ fun t =>
      ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) * β ((w + L t) ⬝ d.jX + rat γ) := by
    intro γ
    have e : ∀ t, ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) *
        β ((w + L t) ⬝ d.jX + rat γ) = ψ (symplOH S T (d.extX T (w ⬝ d.jX + 2 • rat γ) + A t)
          (d.extY T (w ⬝ d.jY) + B t)) * β ((w ⬝ d.jX + rat γ) + lX t) := by
      intro t
      have hx' : (w + L t) ⬝ d.jX = w ⬝ d.jX + lX t := Matrix.add_mul _ _ _
      have hy' : (w + L t) ⬝ d.jY = w ⬝ d.jY + lY t := Matrix.add_mul _ _ _
      have e1 : d.extX T (w ⬝ d.jX + lX t + 2 • rat γ) = d.extX T (w ⬝ d.jX + 2 • rat γ) + A t := by
        rw [add_right_comm, map_add (f := _)]; rfl
      have e2 : d.extY T (w ⬝ d.jY + lY t) = d.extY T (w ⬝ d.jY) + B t := map_add _ _ _
      rw [hx', hy', ← d.symplOH_extX_extY T, e1, e2, add_right_comm (w ⬝ d.jX)]
    rw [show (fun t => ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) *
        β ((w + L t) ⬝ d.jX + rat γ)) = _ from funext e]
    exact (contDiff_psi_symplOH hψ A B hA hB hA0 hB0 _ _).mul (hβ.smooth k lX hlX hlX0 _)
  rw [contDiff_iff_contDiffAt]
  intro t₀
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds t₀
  have hC : IsCompact ((fun p : Mx D T.rank ρ × Mx D T.rank ρ => p.1 - p.2) ''
      (tsupport β ×ˢ ((fun t => (w + L t) ⬝ d.jX) '' K))) :=
    (hβ.supp.isCompact.prod (hK.image hx)).image (continuous_fst.sub continuous_snd)
  have hF := finite_rat_mem T.rank ρ _ hC
  have hsum : ContDiff ℝ ∞ fun t => ∑ γ ∈ hF.toFinset,
      ψ (trHalf D (pairS T ((w + L t) ⬝ d.jX + 2 • rat γ) ((w + L t) ⬝ d.jY))) * β ((w + L t) ⬝ d.jX + rat γ) :=
    ContDiff.sum fun γ _ => hterm γ
  refine hsum.contDiffAt.congr_of_eventuallyEq (Filter.eventually_of_mem hKn fun t ht => ?_)
  show poinX ψ d T β (w + L t) = _
  rw [poinX]
  refine tsum_eq_sum fun γ hγ => ?_
  have h0 : β ((w + L t) ⬝ d.jX + rat γ) = 0 := by
    by_contra hne
    exact hγ (hF.mem_toFinset.2 ⟨((w + L t) ⬝ d.jX + rat γ, (w + L t) ⬝ d.jX),
      ⟨subset_tsupport β hne, t, ht, rfl⟩, add_sub_cancel_left _ _⟩)
  rw [h0, mul_zero]

end GlobalTheory.BumpMixSmooth

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaNZ

theorem exists_ratPt_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {s : LB.Sec (PPx x₁)}, IsThGen x₁ s → ∃ w : Sp Ω ⟶ Gx x₁, w ≫ (fst (Over.mk x₁) Xo.univ.t.G).left = 𝟙 _ ∧ ∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s w z J ≠ 0 := by
  intro E _ _ _ H Dw l Xo Ω _ _ x₁ s hs
  have hnz := GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo Ω x₁ s hs
  obtain ⟨q, i, -, hqi⟩ := hnz (IsLocalRing.closedPoint Ω)
  have := Xo.univ.t.semi.smooth
  have : Smooth (fst (Over.mk x₁) Xo.univ.t.G).left := by
    show Smooth (pullback.fst x₁ Xo.univ.t.G.hom)
    infer_instance
  have : JacobsonSpace ↥(Over.mk x₁).left := inferInstanceAs (JacobsonSpace (PrimeSpectrum Ω))
  have : JacobsonSpace ↥(Gx x₁) := LocallyOfFiniteType.jacobsonSpace (fst (Over.mk x₁) Xo.univ.t.G).left
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints ⟨q, hqi⟩
    ((Gx x₁).basicOpen (s.f i)).isOpen.isLocallyClosed
  have hyc' : IsClosed ({y} : Set (Gx x₁)) := hyc
  refine ⟨pointOfClosedPoint (fst (Over.mk x₁) Xo.univ.t.G).left y hyc',
    pointOfClosedPoint_comp _ y hyc', fun z J hJ => ?_⟩
  set w := pointOfClosedPoint (fst (Over.mk x₁) Xo.univ.t.G).left y hyc'
  have hwz : w z = y := pointOfClosedPoint_apply _ y hyc' z
  let φ : Fin 1 → (Gx x₁ ⟶ Xo.univ.t.G.left) := fun _ => (snd (Over.mk x₁) Xo.univ.t.G).left
  have hi : w z ∈ LB.wchart Xo.univ.t.PP.L φ i := by
    rw [hwz]; exact Scheme.basicOpen_le _ _ hy
  have hj := hJ.mem φ w
  show sval s w z J ≠ 0
  rw [sval_of s w z J (fun k => J (w ≫ φ k)) (fun k => rfl), sec_trans s w z hj hi]
  have hU : IsUnit (gs w z (LB.wchart Xo.univ.t.PP.L φ i) (s.f i)) := by
    have hb : z ∈ (Sp Ω).basicOpen ((w.app _).hom (s.f i)) := by
      rw [← Scheme.preimage_basicOpen]
      show w z ∈ (Gx x₁).basicOpen (s.f i)
      rw [hwz]; exact hy
    convert ((Sp Ω).mem_basicOpen _ z hi).1 hb using 1
    exact gs_eq w z _ hi _
  exact ((Units.isUnit _).mul hU).ne_zero

end GlobalTheory.ThetaNZ
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx

theorem gs_appLE_top {X Y : Scheme.{0}} (w : Y ⟶ X) (U : X.Opens) (hi : ⊤ ≤ w ⁻¹ᵁ U) (z : Y) (a : Γ(X, U)) :
    gs (𝟙 Y) z ⊤ ((w.appLE U ⊤ hi).hom a) = gs w z U a := by
  rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, gs_res (𝟙 Y) z hi trivial,
    gs_pull (𝟙 Y) w z U (hi trivial), Category.id_comp]

theorem appLE_eq_mul_of_sv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (α : Ω), (∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t w z J = gs (𝟙 (Sp Ω)) z ⊤ (toΓ Ω α) * sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J) → ∀ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t.f i) = toΓ Ω α * (w.appLE _ ⊤ hi).hom (t₀.f i) := by
  intro E _ _ _ H Dw l Xo T Ω _ _ x k w t t₀ α h i hi
  apply fn_ext
  intro z _
  have hw : w z ∈ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i := hi trivial
  have hc : ∀ a b, (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) a =
      (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) b → i a = i b := fun a b _ =>
    congrArg i (Subsingleton.elim a b)
  obtain ⟨J, hJ, hJi⟩ := exists_good Xo.univ.t.PP.L Xo.univ.t.PP.isLB z
    (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) i hc (fun q => Set.mem_iInter.1 hw q)
  have e := h z J hJ
  unfold sv at e
  rw [sval_of t w z J i hJi, sval_of t₀ w z J i hJi] at e
  rw [gs_appLE_top, gs_mul (𝟙 (Sp Ω)) z (⊤ : (Sp Ω).Opens) (show (𝟙 (Sp Ω) : Sp Ω ⟶ Sp Ω) z ∈ (⊤ : (Sp Ω).Opens) from trivial),
    gs_appLE_top]
  exact e

end GlobalTheory.HeckeEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx.SvPull

theorem sv_pull_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x₁ : Sp T ⟶ Xo.X} (pm : Gx x₁ ⟶ Gx x) {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)}, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₁) Xo.univ.t.G).left → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (hi : (PPx x₁).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ hi).hom (s.f i) = s'.f i) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo S T _ _ x x₁ pm s s' hsnd hf Z r z J hJ
  have hi0 : (PPx x₁).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) ≤
      pm ⁻¹ᵁ (PPx x).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) := by
    intro y hy
    have h1 := Set.mem_iInter.1 hy 0
    change pm.base y ∈ (⋂ k : Fin 1, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹'
      (Xo.univ.t.PP.L.U (J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) : Set _))
    refine Set.mem_iInter.2 fun _ => ?_
    simp only [Set.mem_preimage] at h1 ⊢
    rw [← Scheme.Hom.comp_apply, hsnd]
    exact h1
  have hz : r z ∈ (PPx x₁).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) :=
    hJ.mem (fun _ : Fin 1 => (snd (Over.mk x₁) Xo.univ.t.G).left) r
  dsimp only [sv]
  rw [sval_of s (r ≫ pm) z J (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left))
    (fun _ => by rw [Category.assoc, hsnd])]
  show gs r z ((PPx x₁).U _) (s'.f _) = _
  rw [← hf _ hi0, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, gs_res r z hi0 hz,
    gs_pull r pm z _ (hi0 hz)]
  rfl

end GlobalTheory.HeckeEx.SvPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx

theorem exists_appLE_ne_zero_of_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [Field Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J ≠ 0 → ∃ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t₀.f i) ≠ 0 := by
  intro E _ _ _ H Dw l Xo T Ω _ _ x k w t₀ z J hJ hne
  refine ⟨fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left), ?_, ?_⟩
  · intro y _
    have hy : y = z := Subsingleton.elim _ _
    subst hy
    exact hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) w
  · intro hi
    have hz : w z ∈ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
        (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) :=
      hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) w
    apply hne
    rw [sv, sval_of t₀ w z J (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) (fun _ => rfl)]
    erw [gs_eq w z _ hz]
    have hle : (⊤ : (Sp Ω).Opens) ≤ w ⁻¹ᵁ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
        (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) := by
      intro y _
      have hy : y = z := Subsingleton.elim _ _
      subst hy
      exact hz
    rw [← TopCat.Presheaf.germ_res_apply (Sp Ω).presheaf (homOfLE hle) z trivial]
    refine (congrArg ((Sp Ω).presheaf.germ ⊤ z trivial).hom ?_).trans (map_zero _)
    exact hi

end GlobalTheory.HeckeEx
end

end

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix


theorem _root_.GlobalTheory.T.contDiff_poincareSumOverRationalHom_realDirections : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => poinX ψ d T β (w + L t) := by
  first | exact @GlobalTheory.BumpMixSmooth.poinX_smooth | exact GlobalTheory.BumpMixSmooth.poinX_smooth | (intros; apply GlobalTheory.BumpMixSmooth.poinX_smooth <;> assumption)

end
end
end

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix


theorem _root_.GlobalTheory.T.continuous_poincareSumOverRationalHom_bump : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → Continuous (poinX ψ d T β) := by
  first | exact @GlobalTheory.BumpMix.poinX_continuous | exact GlobalTheory.BumpMix.poinX_continuous | (intros; apply GlobalTheory.BumpMix.poinX_continuous <;> assumption)

end
end
end
