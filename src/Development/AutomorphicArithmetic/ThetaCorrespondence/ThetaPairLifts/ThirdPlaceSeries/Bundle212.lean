module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle149
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle139
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle166
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliarySquarefreeLevelTwistPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle905
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle844
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle118
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034

@[expose] public section

section



section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt


noncomputable section
namespace GlobalTheory.ThinTwist
theorem twist_thin_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → ∀ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), ∃ g ∈ cuspOn Y.U Z (wtOf (dat p i) u1 0), ∃ K : ℝ, 0 < K ∧ ∀ z : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r, z ∈ framesOn (Y.U σ) Z → ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) z = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) z := by
  intro hP _ _ hS hFD
  have R := _root_.GlobalTheory.T.weight_conditions_at_index'
  have F := _root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le hFD
  have Q := _root_.GlobalTheory.RefSum.QuoShape.quo_shape_dom_lastPos_weight_eq hS
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (R.and (F.and Q)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, -, -, -, hj, -⟩ := hA i hi
  have hFl := (hB i hi Y hY).2.2.1
  intro u1 hq Z σ hσ _ _ f hf
  obtain ⟨-, -, -, -, -, -, -, -, hG⟩ := hC i hi u1 hq
  rw [hG] at hf ⊢
  exact _root_.GlobalTheory.ThinTwist.exists_constant_twist_of_thin_divisor hP p.T _ Y _ _ hL hj hY.1 hFl u1 _ _ Z σ hσ hf
end GlobalTheory.ThinTwist
theorem _root_.GlobalTheory.T.cusp_form_bounded_on_frames_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → ∀ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), ∃ g ∈ cuspOn Y.U Z (wtOf (dat p i) u1 0), ∃ K : ℝ, 0 < K ∧ ∀ z : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r, z ∈ framesOn (Y.U σ) Z → ptN (modelWt (Y.U σ) (wtOf (dat p i) u1 0)) (rdU (Y.U σ) g) z = K * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) z := _root_.GlobalTheory.ThinTwist.twist_thin_alt_alt
end
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BigOn.Exp.SerBase
open Formalism.L2.Host (embLL0)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
section BaseChange
variable {E K₀ K ι : Type} [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Fintype ι]
  {n : ℕ}
end BaseChange
end GlobalTheory.BigOn.Exp.SerBase
namespace GlobalTheory.BigOn.Exp.SerBase
theorem latIoAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.LatticeInclusionAt := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hR hM w hw j => ?_
  intro ρ hρ hpin c hc hs
  obtain ⟨gramR, c0R, c0L, hft, u, hu, hsc⟩ := hs
  refine ⟨u, hu, fun h hh P hP => ?_⟩
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hio : IoExt (R2 p) := hR.ioExt
  have hB := hρ.base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have hlam := hBo.lam
  have hMlat := GlobalTheory.LatFull.latAt_isFullLattice _ ρ hρ ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h
  obtain ⟨hPh, hPF⟩ := (mem_harmLat _ _ _).1 hP
  rw [hlam] at hPF
  have key : ∀ φ ∈ coefLatFn (embLL0 (Fm.D x i)) (labLL0 (Fm.D x i)) (smallInt (Fm.D x i)) (lamV (Fm.D x i) j)
      ((ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h)),
      ∃ F : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j), F ∈ nabAtr (labLL (Fm.D x i)) (lamV (Fm.D x i) j)
        ((ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h)) ∧
        φ = coefFn (Fm.D x i).what₂.embLL (lamV (Fm.D x i) j) (F : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨F₀, hF₀, rfl⟩ := hφ
      refine ⟨⟨MvPolynomial.map (Fm.D x i).LL0.val.toRingHom F₀.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ F₀.2⟩,
        map_mem_nabAtr_comp (Fm.D x i).LL0.val.toRingHom (labLL0 (Fm.D x i)) _ _ hMlat hF₀, ?_⟩
      funext y
      rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]
      rfl
    | zero => exact ⟨0, zero_mem _, funext fun y => by simp [coefFn]⟩
    | add φ ψ _ _ h1 h2 =>
      obtain ⟨F1, m1, rfl⟩ := h1
      obtain ⟨F2, m2, rfl⟩ := h2
      exact ⟨F1 + F2, add_mem m1 m2, funext fun y => by simp [coefFn, mul_add]⟩
    | smul a φ _ h1 =>
      obtain ⟨F1, m1, rfl⟩ := h1
      obtain ⟨t, ht⟩ := a.2
      refine ⟨RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t • F1, Submodule.smul_mem _ _ m1, funext fun y => ?_⟩
      have e1 : ((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t • F1 : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j)) :
          Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) =
          MvPolynomial.C (((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t : 𝓞 (Fm.D x i).what₂.LL)) :
            (Fm.D x i).what₂.LL) * (F1 : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) := by
        rw [← MvPolynomial.smul_eq_C_mul]
        rfl
      have e2 : (Fm.D x i).what₂.embLL (((RingOfIntegers.mapRingHom (Fm.D x i).LL0.val.toRingHom t : 𝓞 (Fm.D x i).what₂.LL)) :
          (Fm.D x i).what₂.LL) = (a : ℂ) := by
        rw [← ht]
        rfl
      show (a : ℂ) * coefFn _ _ (F1 : Pol (Fm.D x i).what₂.LL (Fm.D x i).what₂.Tau (Vc (Fm.D x i) j).rank) y = _
      rw [e1, coefFn, coefFn, map_mul, MvPolynomial.eval₂Hom_C, e2]
      ring
  obtain ⟨F, hF, hFe⟩ := key _ hPF
  have hM' : (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).latAt (finPt (Vc (Fm.D x i) j) h) =
      Bridge.hLat (Vc (Fm.D x i) j) (fin (Vc (Fm.D x i) j) h) :=
    GlobalTheory.LatAtHLat.latAt_eq_hLat _ _ _ _ (GlobalTheory.LatFull.baseFrame_one_eq _ _ _ (hρ.latS _ j _)) _
  refine ⟨c0L j F, ⟨gramR, c0R, c0L, hft, F, by rw [← hM']; exact hF, rfl⟩, ?_⟩
  obtain ⟨u', w₀, hu', -, hw₀⟩ := IsChosenExtremalVector.io _ ((fw2 p).hv₀ j _) hio
  have huu : u' = (u : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ) :=
    funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  rw [huu] at hw₀
  have hm : ∀ τ, (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).w.p τ +
      (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).w.q τ ≤ (Wc (Fm.D x i) j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE (Fm.D x i) τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function _ _ _ _ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).F.BS hB.wt hm
  exact IsScaleAt.ioP_eq (Rl := p.R) hsc hinj hPh
    (GlobalTheory.SeriesTie.UnivRat.ioP_mem_harmonic hC.lev hC.thP (hC.models.cV j) hB (hpin.psi _ j _) (hpin.inf _ j _)
      (hpin.cartT _ j _) (hpin.onbS _ j _) (hpin.onbT _ j _) (hpin.mu0 _ j _) (hpin.eta _ j _) (hpin.ap _ j _) (hpin.am _ j _)
      _ w₀ hw₀ _) hFe
end GlobalTheory.BigOn.Exp.SerBase
end
end
end
