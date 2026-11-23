module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle736
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle729
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle536
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle647
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle737
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle672
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle449
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle619
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle483
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle626
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle628
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle738
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem _root_.GlobalTheory.T.heckeReading_kernels_match_cosets_through_frame : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
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
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
          ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C, (∃ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z) ∧
          ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (κ i).n,
            (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
              σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f z) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k * GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) := by
  first | exact @GlobalTheory.HeckeTerm.heckeTerm | exact GlobalTheory.HeckeTerm.heckeTerm | (intros; apply GlobalTheory.HeckeTerm.heckeTerm <;> assumption)
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

noncomputable section
namespace GlobalTheory.AscFin.LatticeBidual

theorem latRow_bidual : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u → (∀ u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u' → (∀ v ∈ latRow G i, W.ψ (symplO _ _ v u') = 1) → W.ψ (symplO _ _ u u') = 1) → u ∈ latRow G i := by
  intro D hq T L μ0 hL sc G W M hM i hi u hu H
  have sdG : ∀ j, j ≤ D.R.m → IsSelfDualC (G.V (.grid j 0)) (G.Λ (.grid j 0)) := by
    intro j hj
    cases j with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ j => exact (G.sp.V_is (j + 1) 0 (by omega) hj (by omega)).sd
  have sdS := sdG (i + 1) hi
  have sdT := sdG i hi.le
  have sdB : IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    obtain ⟨I', h1, h2⟩ := GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal G.pl sc 0 1
    simp only [pow_zero, pow_one, inv_one, one_mul] at h1 h2
    exact GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one _ _ _ I' sdT h1 h2
  have hO : ∀ v ∈ latRow G i, v ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := fun v hv => GlobalTheory.RowLoc.mem_latO_negSp.1 hv.1
  have hB : ∀ v ∈ latRow G i, v ∈ latBig G i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · exact fun v hv => GlobalTheory.T.depthLatticeGridRow_zero_le_selfDualHomLattice D hq T L μ0 hL sc G W M hM hi hv
    · exact fun v hv => GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hq T L μ0 hL sc G W M hM i hi1 hi hv
  have hdep := GlobalTheory.T.idempotent_smul_mem_hat_lattice D hq T L μ0 hL sc G W M hM i hi
  have finO := (GlobalTheory.AscFinWit.finLat_latO
    (S := G.V (.grid (i + 1) 0)) (T := G.V (.grid i 0))
    (LS := G.Λ (.grid (i + 1) 0)) (LT := G.Λ (.grid i 0))
    (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdS | exact (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdS).toIsLattice)
    (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdT | exact (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdT).toIsLattice)).fin
  have finB := (GlobalTheory.AscFinWit.finLat_latO
    (S := G.V (.grid (i + 1) 0)) (T := G.V (.grid i 0))
    (LS := G.Λ (.grid (i + 1) 0)) (LT := idLat (shiftId G) (G.Λ (.grid i 0)))
    (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdS | exact (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdS).toIsLattice)
    (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdB | exact (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdB).toIsLattice)).fin
  have uO : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := by
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdT (fun _ => True) u hu).2 fun u' hu' => ?_
    refine H u' (finO u' hu') fun v hv => ?_
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdT (fun _ => True) v (finO v (hO v hv))).1 (hO v hv) u' hu'
  have uB : u ∈ latBig G i := by
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdB (fun _ => True) u hu).2 fun u' hu' => ?_
    refine H u' (finB u' hu') fun v hv => ?_
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdB (fun _ => True) v (finB v (hB v hv))).1 (hB v hv) u' hu'
  exact ⟨GlobalTheory.RowLoc.mem_latO_negSp.2 uO, hdep u uO uB⟩

end GlobalTheory.AscFin.LatticeBidual
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate

namespace GlobalTheory.CoreOnto.PreSteps

theorem preOK (hDF : DepFixed) : PreOK := by
  intro D hQ hS T L μ0 hL sc hc G W Mv hM i hi r r' hr hr' v M M'
  obtain ⟨hth, -, -, hbij, hmeas, hweil⟩ := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D W.ψ (G.V (.core i)) (G.V (.core (i + 1))) W.ψ_std
  have hom := W.om_is (.core i) (show i + 1 ≤ D.R.m by omega)
  obtain ⟨hcS, hcT⟩ := G.chr_core (i := i) (by omega)
  rw [hcS, hcT] at hom
  obtain ⟨ω, hω, hωx⟩ := hweil _ _ _ hom
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_latticeHom_onto_modulo_depthIdeal D hQ T L μ0 hL sc G W Mv hM i hi
  obtain ⟨f, hvac, hsph, hcos⟩ := GlobalTheory.T.exists_cosetFockVacuumDatum D hQ T L μ0 hL sc G W Mv hM i hi r r' hr hr' _ _ (r.mod M) (r'.mod M') x₀ hx₀.1
  have hRL := (GlobalTheory.T.selfDualLattice_changeOfLattice_laws D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r'
  have hinj : Function.Injective (exch (G.V (.core i)) (G.V (.core (i + 1)))) := by
    intro F₁ F₂ h
    funext w
    obtain ⟨x, rfl⟩ := hbij.2 w
    exact congrFun h x
  refine ⟨ω, f, ⟨(hRL.2 _ _ ω).2 hω, fun τ => ?_, hvac, hsph, ?_, ?_⟩, hωx, fun φ => (hcos φ).1⟩
  · show GlobalTheory.EvenOnto.UpPair (sLen D - 1) (Node.par D sc.cGap (.core i) τ) (Node.par D sc.cGap (.core (i + 1)) τ)
      (-(cen D sc.cGap τ (D.R.m - i) : ℚ)) (-(cen D sc.cGap τ (D.R.m - i) : ℚ))
    rw [hc]
    exact GlobalTheory.T.coreChain_realParameters_correspond D hS i hi τ
  · intro φ κ hκ κ' hκ'
    have hD := (hcos φ).1
    have hthF := (hth _).2 hD.1
    exact hinj ((hωx _ hthF κ κ').symm.trans (hDF D hQ T L μ0 hL sc G W Mv hM i hi (.core i) (Or.inr rfl) _ hD κ hκ κ' hκ'))
  · intro m X hX φ g hg hgb
    by_contra hne
    apply hgb
    have hD := (hcos φ).1
    have hthF := (hth _).2 hD.1
    obtain ⟨m', X', hX', heq⟩ := hmeas m X hX
    have hne' : (∫ w in X', W.om (.core i) (1, g) (exch (G.V (.core i)) (G.V (.core (i + 1)))
        (GlobalTheory.Chain.ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ)) w *
        conj (exch (G.V (.core i)) (G.V (.core (i + 1)))
          (GlobalTheory.Chain.ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ) w) ∂m') ≠ 0 := by
      have h1 := hωx _ hthF g 1
      rw [map_one] at h1
      rw [h1, ← heq]
      exact hne
    have hsd := (G.sp.P_is i (by omega)).sd
    have hstab : ∀ w ∉ G.pl.S0, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram w g ∈
        GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (G.Λ (.core i)) w := by
      intro w hw
      have h0 := hg w hw
      have h1 : GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram w g ∈
          GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (GlobalTheory.AdelicU.frameLat r.sp) w := h0
      have hΛ : GlobalTheory.AdelicU.frameLat r.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) (G.Λ (.core i)) := hr
      rw [hΛ, (GlobalTheory.T.polarisationTwist_lattice_selfDual_same_stabilisers D (G.V (.core i)) (G.Λ (.core i)) hsd i).2.1 w] at h1
      exact h1
    have hfin := GlobalTheory.T.cosetSupported_coefficient_congruenceSubgroup D hQ T L μ0 hL sc G W Mv hM i hi x₀ hx₀ _ (hcos φ) m' X' hX' g hstab hne'
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (G.V (.core i))).1 g
    refine ⟨⟨a, ha⟩, k, Subgroup.mem_inf.2 ⟨hk, ?_⟩, rfl⟩
    have ha' : Lev.finE (G.V (.core i)) a = 1 := by
      have h : finHom (G.V (.core i)) a = 1 := ha
      show Formalism.UG.bc (Lev.swapAE D) (finHom (G.V (.core i)) a) = 1
      rw [h, map_one]
    show Lev.finE (G.V (.core i)) k ∈ G.levCong (.core i)
    rw [map_mul, ha', one_mul] at hfin
    exact hfin

end GlobalTheory.CoreOnto.PreSteps
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem biInv_eq_of_cells {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)]
    {R K : ∀ i, Subgroup (H i)} {q : (∀ i, H i) → ℂ} :
    ∀ (l : List ι), BiInv R K l q → ∀ h h' : (∀ i, H i), (∀ i, i ∉ l → h i = h' i) →
      (∀ i ∈ l, ∃ r ∈ R i, ∃ k ∈ K i, h i = r * h' i * k) → q h = q h'
  | [], _, h, h', h1, _ => by
      have : h = h' := funext fun i => h1 i List.not_mem_nil
      rw [this]
  | i :: l, hq, h, h', h1, h2 => by
      have hi : i ∈ i :: l := List.mem_cons_self
      rcases h2 i hi with ⟨r, hr, k, hk, e⟩
      have hq' : BiInv R K l q := fun j hj => hq j (List.mem_cons_of_mem _ hj)
      set h₁ := Function.update h i (h' i) with hh₁
      have hi₁ : h₁ i = h' i := by simp [hh₁]
      have step1 : q h = q h₁ := by
        have a1 := (hq i List.mem_cons_self (Function.update h₁ i (h' i * k))).1 r hr
        have a2 := (hq i List.mem_cons_self h₁).2 k hk
        simp only [Function.update_self, Function.update_idem] at a1
        rw [hi₁] at a2
        have hh : h = Function.update h₁ i (r * (h' i * k)) := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [e, mul_assoc]
          · simp [hh₁, Function.update_of_ne hj]
        rw [hh, a1, a2]
      rw [step1]
      refine biInv_eq_of_cells l hq' h₁ h' (fun j hj => ?_) (fun j hj => ?_)
      · by_cases hji : j = i
        · subst hji; exact hi₁
        · rw [hh₁, Function.update_of_ne hji]
          exact h1 j (by simp [hji, hj])
      · by_cases hji : j = i
        · subst hji; exact ⟨1, one_mem _, 1, one_mem _, by simp [hi₁]⟩
        · rw [hh₁, Function.update_of_ne hji]
          exact h2 j (List.mem_cons_of_mem _ hj)

theorem zero_not_mem_idx (D : D7) : 0 ∉ idx D := by simp [idx, List.mem_range']; intro x _; omega

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R)

theorem evT_eq_zero_of (C : BiFam ch.G) (j : ℕ) (hj : Even j) (hjm : j < D.R.m) (hC : C j = 0) (f : SchRow ch.G)
    (u : ColPt ch.G) (y : RowPt ch.G) : evT C f u y = 0 := by
  obtain ⟨k, rfl⟩ := hj
  obtain ⟨c, hc⟩ := D.R.m_even
  unfold evT
  rw [Finset.prod_eq_zero (i := k) (by simp [Finset.mem_range]; omega) (by rw [two_mul, hC]; rfl), zero_mul]

end
end GlobalTheory.RowVal

namespace GlobalTheory.RowVal
section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R)

theorem suppOn_of_cover (s : ℤˣ) (hC : CoverAt ch s) (hF : FlatAt ch s) (hO : OffAt ch) (hI : InvAt ch) (hT : TensAt ch)
    (hB : BasicAt ch) : SuppOn ch s := by
  intro t a τ hτ M hM P y b hb h h1 hne
  obtain ⟨hφ, hFt, hHaar, -, hGood, -, -⟩ := hB
  have hsum : ∀ h' : Pts ch.G, tot ch.W hM P τ (colFn ch a) (formTop ch t y) h' = ∑ d ∈ τ.support,
      τ d * per ch.W M t (conAt ch.W hM (fockD ch.W t d.2 P.2) h') d.1 P.1 (colFn ch a) (formTop ch t y) := fun _ => rfl
  have hne' := hne
  rw [hsum] at hne'
  obtain ⟨d, hd, hdne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  have hper := right_ne_zero_of_mul hdne
  have hnz : ∀ j, Even j → j < D.R.m → conAt ch.W hM (fockD ch.W t d.2 P.2) h j ≠ 0 := by
    intro j hj hjm h0
    apply hper
    have := hT t M (hHaar t M hM) _ _ (hφ a) (hFt t y) Unit {()} (fun _ => 1)
      (fun _ => conAt ch.W hM (fockD ch.W t d.2 P.2) h) (fun _ => d.1)
      (fun _ _ => hGood t _ τ hτ M hM d hd P.2 h)
      (fun u y' => by simp [evT_eq_zero_of ch _ j hj hjm h0]) P.1
    simpa using this
  have h0 : h 0 = 1 := h1 0 (zero_not_mem_idx D)
  obtain ⟨β, hβ⟩ := hC t b hb h (hO t _ τ hτ M hM d hd P.2 h h0 hnz)
  refine ⟨β, ?_, hβ⟩
  by_contra hns
  apply hne
  classical

  choose! r hr a' ha' k hk e using hβ
  let p : Pts ch.G := fun j => if j ∈ idx D then a' j else 1
  have hp : IsRealPt p := by
    refine ⟨fun j => ?_, fun j hj => by simp [p, hj]⟩
    by_cases hj : j ∈ idx D
    · simp only [p, if_pos hj]; exact ha' j hj
    · simp only [p, if_neg hj]; exact one_mem _
  have hmove : tot ch.W hM P τ (colFn ch a) (formTop ch t y) h = tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b β) := by
    refine biInv_eq_of_cells (idx D) (hI t a τ hτ M hM P y) h (p * b β) (fun j hj => ?_) (fun j hj => ?_)
    · simp [p, hj, h1 j hj, (hb β).1 j hj]
    · refine ⟨r j, hr j hj, k j, hk j hj, ?_⟩
      simp only [Pi.mul_apply, p, if_pos hj, e j hj, mul_assoc]
  rw [hmove]

  have hexp : ch.S.IsExpansion t (ch.Phi a) β 0 := by
    obtain ⟨e₀, he₀, -⟩ := hτ
    refine ⟨e₀, he₀, by simp, fun x y' _ _ => ?_⟩
    rw [Finsupp.sum_zero_index]
    simp only [GridChoice.supp, Set.mem_setOf_eq, not_forall] at hns
    obtain ⟨w, hw⟩ := hns
    have hz : (ch.S.term t (ch.Phi a) β w).datum = 0 := by
      simpa [unfSupport, GridChoice.term] using hw
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hz]; rfl)
  obtain ⟨z, -, hFl⟩ := hF
  obtain ⟨Cr, -, hCr⟩ := hFl P.2 p hp
  obtain ⟨ζ, -, hz⟩ := hCr t (ch.Phi a) τ hτ M hM β (b β) (hb β) 0 (fun _ => 0) hexp (by intro d hd; simp at hd)
  rw [hsum]
  exact hT t M (hHaar t M hM) _ _ (hφ a) (hFt t y) _ τ.support (fun d => τ d)
    (fun d => conAt ch.W hM (fockD ch.W t d.2 P.2) (p * b β)) (fun d => d.1)
    (fun d hd => hGood t _ τ hτ M hM d hd P.2 _)
    (fun u y' => by simpa [Finsupp.sum] using hz u y') P.1

end

theorem big_suppOn_of_flat :
    GlobalTheory.RowClaim.Big fun ch => ∀ s, FlatAt ch s → OffAt ch → InvAt ch → TensAt ch → BasicAt ch → SuppOn ch s :=
  big_mono (fun ch hC s hF hO hI hT hB => suppOn_of_cover ch s (hC s) hF hO hI hT hB) GlobalTheory.T.tiltedPoints_covered_by_representativeCells

end GlobalTheory.RowVal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.periodReductionToFockVectors_large_depth : Big fun ch => FockAt ch := by
  first | exact @GlobalTheory.FockRed.fockAt_big | exact GlobalTheory.FockRed.fockAt_big | (intros; apply GlobalTheory.FockRed.fockAt_big <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.isSeesawHermitianTriple_gridSquare_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m),
    SquareStanding G t → ∀ M : Vol G, M.Is t →
      GlobalTheory.SquareComm.IsTriple (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) := by
  first | exact @GlobalTheory.SquareTripleForm.isTriple_of_standing | exact GlobalTheory.SquareTripleForm.isTriple_of_standing | (intros; apply GlobalTheory.SquareTripleForm.isTriple_of_standing <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

open GlobalTheory.ExpansionInvariance in
theorem pairPts_last_invariant (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T}
    (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (ht : t ∈ U) (hβ : β ∈ S.supp t Φ) (hτ : S.IsExpansion t Φ β τ)
    (hv : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m)))
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m))
    (hx : x D.R.m = finEmb G.sp.topDec (y D.R.m)) (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) :
    pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  have hm := D.R.two_le_m
  have h0x : Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0 = x 0 :=
    Function.update_of_ne (by omega) _ _
  have h0y : Function.update y D.R.m (y D.R.m * k) 0 = y 0 := Function.update_of_ne (by omega) _ _
  rw [h0x, h0y, GlobalTheory.FunObj.SumModel.finEmb_mul, ← hx]
  have hth : ∀ d ∈ τ.support, (∀ j, IsThetaFunO W.ψ _ _ (S.Z.vec (d.1 j))) ∧ ∀ i, IsThetaFunO W.ψ _ _ (S.Z.vec (d.2 i)) :=
    fun d hd => ⟨fun j => vec_theta S (defPair_top t j) (inRange_top t j) _ ((hv d hd).1 j),
      fun i => vec_theta S (defPair_chi i) (inRange_chi i) _ ((hv d hd).2 i)⟩
  obtain ⟨M, hM⟩ := GlobalTheory.ArrowMultilinear.pairing_multilinear S t x y (Ψ (x 0)) (F (y 0))
  set uc : PureDat G t → ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ := fun d =>
    Function.update (fun j => S.Z.vec (d.1 j)) (lastIx D) (colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D))))
    with huc
  set ur : PureDat G t → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ := fun d =>
    Function.update (fun i => S.Z.vec (d.2 i)) (lastIx D) (rowShift S k (S.Z.vec (d.2 (lastIx D)))) with hur
  have thc : ∀ d ∈ τ.support, ∀ j, IsThetaFunO W.ψ _ _ (uc d j) := by
    intro d hd j
    by_cases hj : j = lastIx D
    · subst hj
      simp only [huc, Function.update_self]
      exact colShift_theta S t _ ((hth d hd).1 _)
    · simp only [huc, Function.update_of_ne hj]
      exact (hth d hd).1 j
  have thr : ∀ d ∈ τ.support, ∀ i, IsThetaFunO W.ψ _ _ (ur d i) := by
    intro d hd i
    by_cases hi : i = lastIx D
    · subst hi
      simp only [hur, Function.update_self]
      exact rowShift_theta S k ((hth d hd).2 _)
    · simp only [hur, Function.update_of_ne hi]
      exact (hth d hd).2 i
  have lhs : pairPts S τ (Function.update x D.R.m (x D.R.m * finEmb G.sp.topDec k)) (Function.update y D.R.m (y D.R.m * k))
      (Ψ (x 0)) (F (y 0)) = τ.sum fun d a => a * M (fun j => toTh W _ (uc d j)) (fun i => toTh W _ (ur d i)) := by
    simp only [pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq, GlobalTheory.LastColumnMove.colMapV_update_last S _ x _ ((hth d hd).1 _), GlobalTheory.LastRowMove.rowMapV_update_last S _ y _ ((hth d hd).2 _)]
    have e1 : (fun j : Fin D.R.m => (toTh W _ (uc d j) : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) = uc d :=
      funext fun j => coe_toTh W _ (thc d hd j)
    have e2 : (fun i : Fin D.R.m => (toTh W _ (ur d i) : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) = ur d :=
      funext fun i => coe_toTh W _ (thr d hd i)
    rw [e1, e2]
  have rhs : pairPts S τ x y (Ψ (x 0)) (F (y 0)) =
      τ.sum fun d a => a * M (fun j => toTh W _ (S.Z.vec (d.1 j))) (fun i => toTh W _ (S.Z.vec (d.2 i))) := by
    simp only [pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq]
    have e1 : (fun j : Fin D.R.m => (toTh W _ (S.Z.vec (d.1 j)) : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) = fun j : Fin D.R.m => S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh W _ (S.Z.vec (d.2 i)) : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        fun i : Fin D.R.m => S.Z.vec (d.2 i) :=
      funext fun i => coe_toTh W _ ((hth d hd).2 i)
    rw [e1, e2]
  rw [lhs, rhs]
  refine GlobalTheory.funProd_multilinear_sum_eq M τ _ _ _ _ fun w v => ?_
  have key := GlobalTheory.T.productFunction_totalTensor_invariant_lastArrows S hL hde hc ht hβ hτ hv k hk w v
  simp only [Finsupp.sum] at key ⊢
  refine (Finset.sum_congr rfl fun d hd => ?_).trans (key.trans (Finset.sum_congr rfl fun d hd => ?_))
  · simp only [coe_toTh W _ (thc d hd _), coe_toTh W _ (thr d hd _)]
    rfl
  · simp only [coe_toTh W _ ((hth d hd).1 _), coe_toTh W _ ((hth d hd).2 _)]

end GlobalTheory.LastVertexInv
end
end
