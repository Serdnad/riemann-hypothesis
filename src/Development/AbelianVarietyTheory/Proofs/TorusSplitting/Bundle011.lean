module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantFamilyNorms
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem relab_isTypeFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, Dw.mult (relab c σ τ) = Dw.mult τ) ∧ ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  intro E _ _ _ H Dw l _ c σ hσ
  obtain ⟨hbij, hrt, -, hty⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  refine ⟨hbij, fun τ => ?_, fun g e => hty Dw g e⟩
  unfold Datum.mult
  exact if_congr (hrt τ) rfl rfl

end GlobalTheory.EtaAn
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoundedCusp

theorem mem_SS_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : FD.Wt X.Ψ r) (τ0 : X.Ψ) (h : X.p0 = 0 ∨ X.p0 = r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) :
    P ∈ X.SS la := by
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  exfalso
  have hiso : X.IsIsoV (X.embV ξ) := fun τ =>
    ⟨by rw [show X.embV ξ τ = Data.emb τ.1 ξ from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  have hmpos := PositiveMinorUnits.mN_pos (MajorantFamilyNorms.hG_of X τ0) X.p0 X.p0_le (mat x τ0) (hx τ0).1
    (MajorantFamilyNorms.hsg_of X hx τ0) (X.embV ξ τ0) (hiso τ0).1 (hiso τ0).2
  have htop := PositiveMinorUnits.mN_top (MajorantFamilyNorms.hG_of X τ0) X.p0 (mat x τ0) (hx τ0).1
    (MajorantFamilyNorms.hsg_of X hx τ0) (X.embV ξ τ0) (hiso τ0).1
  rcases h with h | h
  · rw [h, PositiveMinorUnits.mN_zero] at hmpos
    exact lt_irrefl _ hmpos
  · rw [h, htop] at hmpos
    exact lt_irrefl _ hmpos

end GlobalTheory.BoundedCusp

namespace GlobalTheory

theorem cusp_and_supC_le_of_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (n : ℕ) (f : Rul Xo c) (C : ℝ), 2 ≤ n → Even n → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → f ∈ sec Xo c 0 n → (∀ σ, GoodEmb c σ → ∀ k, ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm (laU (U σ) 0 n k) (rdU (U σ) f k) x ≤ C) → 0 ≤ C → f ∈ cusp Xo c U 0 n ∧ ∀ σ (xi : ℝ), GoodEmb c σ → supC Xo c U xi σ 0 n f ≤ C := by
  intro E _ _ _ H Dw l Xo c r U n f C hn hev hU hf hb hC
  refine ⟨?_, fun σ xi hσ => ?_⟩
  · rw [mem_cusp]
    refine ⟨hf, fun σ hσ => holCusp_mem_holSub _ _ fun j => ?_⟩
    obtain ⟨-, -, -, -, hsec, -⟩ := hU σ hσ
    have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun τ i i' _ => le_rfl, hev⟩
    obtain ⟨τ0⟩ : Nonempty ((U σ).X j).Ψ := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases h : τ ∈ ((U σ).X j).Ψ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, not_not.mp (fun h' => h ((((U σ).X j).cmType τ).mpr h'))⟩⟩
    have hbd : ((U σ).X j).IsBddSec (laU (U σ) 0 n j) (rdU (U σ) f j) :=
      ⟨hsec _ _ hD f hf j, C, hb σ hσ j⟩
    have hle := ((U σ).X j).p0_le
    by_cases h0 : ((U σ).X j).p0 = 0 ∨ ((U σ).X j).p0 = r
    · exact BoundedCusp.mem_SS_of_definite _ _ τ0 h0 _ hbd
    · refine AR.Up.cuspStatement_holds r _ _ τ0 (by omega) (by omega) ?_ ?_ _ hbd
      · intro i i' h1 h2
        unfold laU
        by_cases h3 : ((U σ).X j).p0 ≤ (i : ℕ)
        · rw [if_pos h3, if_pos (by omega)]
          simp
        · rw [if_neg h3, if_neg (by omega)]
          simp
      · intro i i' h1 h2
        unfold laU
        rw [if_neg (by omega), if_pos (by omega)]
        omega
  · have h1 : lieFac Dw xi (0 : (E →+* ℂ) × ℕ → ℕ) = 1 := by simp [lieFac]
    unfold supC supN
    rw [h1, _root_.one_mul]
    refine ENNReal.toReal_le_of_le_ofReal hC ?_
    exact iSup_le fun p => ENNReal.ofReal_le_ofReal (hb σ hσ p.1 p.2 p.2.2)

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem exists_unit_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ (∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1) ∧ X.la1 (rmul x b) = X.la1 x ∧ (∀ th, I2.phiFD X th (rmul x b) = I2.phiFD X th x) ∧ ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P → X.pnorm la P x = ‖P (rmul x b)‖ := by
  intro E _ _ _ r X x hx
  have hb := FrameDegreeData.bOf_mem X hx
  have ho := FrameDegreeData.ortho_bOf X hx
  have hd : ∀ τ i, ‖dmin X.Gm (rmul x (FrameDegreeData.bOf X x)) τ i‖ = 1 := by
    intro τ i
    unfold dmin
    rw [ho τ, FrameDegreeData.lminor_diagonal, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Complex.norm_real]
    rcases FrameDegreeData.sgn_sq X.p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) j : Fin r) with h | h <;>
      rw [h] <;> simp
  have hl : X.la1 (rmul x (FrameDegreeData.bOf X x)) = X.la1 x := by
    unfold Data.la1
    rw [ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimumSq_rightBorel X hx hb]
  refine ⟨_, hb, OrthogonalFrameDomain.rmul_mem_dom X hx hb, hd, hl, fun th => ?_, fun la P hP => ?_⟩
  · unfold I2.phiFD
    rw [hl]
  · rw [← FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx _ hb]
    unfold Data.pnorm
    simp only [norm_div, hd, div_one, Real.one_rpow, Finset.prod_const_one, _root_.mul_one]

end GlobalTheory.EtaAn
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_borel_orthonormal_flag_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ (∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1) ∧ X.la1 (rmul x b) = X.la1 x ∧ (∀ th, I2.phiFD X th (rmul x b) = I2.phiFD X th x) ∧ ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P → X.pnorm la P x = ‖P (rmul x b)‖ := by
  first | exact @GlobalTheory.EtaAn.exists_unit_frame | exact GlobalTheory.EtaAn.exists_unit_frame | (intros; apply GlobalTheory.EtaAn.exists_unit_frame <;> assumption)

end
end
