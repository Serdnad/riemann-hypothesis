module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.DensOne

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * (G.map τ * x.map (starRingEnd ℂ)) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem det_ne_zero_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    (mat x τ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (hx τ)
  rw [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
  exact_mod_cast sgn_ne X.p0 (a : ℕ)

theorem densF_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    densF X x = fun w => ∏ τ, ∏ i : Fin r, ‖lminor (Gw X w τ) i.castSucc‖ ^ (-2 : ℤ) := by
  funext w
  unfold densF
  simp only [dmin_cpt_orth X hx]

theorem dens_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r), IsOrth X x → ContinuousAt (densF X x) 0 ∧ densF X x 0 = 1 ∧
      ∀ τ, (mat x τ).det ≠ 0 := by
  intro E _ _ _ r X x hx
  refine ⟨?_, ?_, det_ne_zero_of_orth X hx⟩
  · rw [densF_orth X hx]
    refine tendsto_finsetProd _ fun τ _ => tendsto_finsetProd _ fun i _ => ?_
    refine ((cont_lminor X τ i.castSucc).norm.continuousAt).zpow₀ _ (Or.inl ?_)
    simp [norm_lminor_zero]
  · rw [densF_orth X hx]
    simp only [norm_lminor_zero, _root_.one_zpow, Finset.prod_const_one]

end GlobalTheory.DensOne
end

section

noncomputable section

namespace GlobalTheory.SUChartSection

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def gsU (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  FrameDegreeData.uMat (PoinPf.Gw X w τ)

def gsS (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (k : Fin r) : ℝ :=
  (Real.sqrt |(((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re|)⁻¹

def gsB (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  gsU X w τ * Matrix.diagonal fun k => ((gsS X w τ k : ℝ) : ℂ)

def yM (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  mat (nmat X w) τ * gsB X w τ

def yF (X : Data E r) (w : V (nd X)) : X.Ψ → Fin r → Fin r → ℂ := fun τ a b => yM X w τ a b

def dY (X : Data E r) : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ) := fderiv ℝ (yF X) 0

def secM (X : Data E r) (x : Frame X.Ψ r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  mat x τ * yM X w τ * (mat x τ)⁻¹

theorem gram_cpt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (cpt X x w) τ) = PoinPf.Gw X w τ := by
  show gram τ.1 X.Gm (mat x τ * mat (nmat X w) τ) = _
  rw [FrameDegreeData.gram_mul, hx τ]
  rfl

theorem bOf_cpt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) :
    FrameDegreeData.bOf X (cpt X x w) = fun τ => gsB X w τ := by
  funext τ
  simp only [FrameDegreeData.bOf, FrameDegreeData.uOf, gram_cpt X hx, gsB, gsU]
  refine congrArg (fun d => FrameDegreeData.uMat (PoinPf.Gw X w τ) * Matrix.diagonal d) ?_
  funext k
  simp only [FrameDegreeData.sOf, FrameDegreeData.dOf, FrameDegreeData.uOf, FrameDegreeData.gram_mul, gram_cpt X hx, gsS, gsU]

theorem det_ne_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det (hx τ)
  rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
  exact_mod_cast PoinPf.sgn_ne _ _

theorem mem_dom_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) : x ∈ X.dom := by
  intro τ
  refine ⟨det_ne_of_orth X hx τ, fun i => ?_⟩
  have h := PoinPf.dmin_cpt_orth X hx 0 τ i
  rw [PoinPf.cpt_zero, PoinPf.Gw_zero, PoinPf.lminor_Jd] at h
  rw [h, Complex.ofReal_re]
  exact mul_self_pos.2 (PoinPf.psgn_ne _ _)

theorem exists_ball (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    ∃ R > 0, ∀ w ∈ Metric.ball (0 : V (nd X)) R, cpt X x w ∈ X.dom := by
  obtain ⟨R, hR, h⟩ := PoinPf.good_ball X 0
  exact ⟨R, hR, fun w hw => PoinPf.cpt_mem_dom X (mem_dom_of_orth X hx) hx (h w hw).1 (h w hw).2.1⟩

theorem gsU_zero (X : Data E r) (τ : X.Ψ) : gsU X 0 τ = 1 := by
  ext j c
  simp only [gsU, PoinPf.Gw_zero, FrameDegreeData.uMat, Matrix.of_apply, Matrix.one_apply]
  split_ifs with h1 h2
  · rfl
  · have : FrameDegreeData.rowc (PoinPf.Jd X) c = 0 := by
      funext m
      simp only [FrameDegreeData.rowc, PoinPf.Jd, Pi.zero_apply]
      rw [Matrix.diagonal_apply_ne]
      intro hc
      have : ((Fin.castLE c.isLt.le m : Fin r) : ℕ) < c := m.isLt
      rw [← hc] at this
      exact lt_irrefl _ this
    rw [this, Matrix.zero_vecMul, Pi.zero_apply, neg_zero]
  · rfl

theorem gsB_zero (X : Data E r) (τ : X.Ψ) : gsB X 0 τ = 1 := by
  have hS : ∀ k, gsS X 0 τ k = 1 := by
    intro k
    simp only [gsS, gsU_zero, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.mul_one, PoinPf.Gw_zero, PoinPf.Jd, Matrix.diagonal_apply_eq, Complex.ofReal_re, PoinPf.abs_sgn,
      Real.sqrt_one, inv_one]
  rw [gsB, gsU_zero, Matrix.one_mul]
  simp only [hS, Complex.ofReal_one, Matrix.diagonal_one]

theorem yM_zero (X : Data E r) (τ : X.Ψ) : yM X 0 τ = 1 := by
  rw [yM, PoinPf.nmat_zero, gsB_zero, Matrix.one_mul]

theorem secM_zero (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : secM X x 0 τ = 1 := by
  rw [secM, yM_zero, Matrix.mul_one, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ))]

theorem gsB_lower (X : Data E r) (w : V (nd X)) (τ : X.Ψ) {a b : Fin r} (h : b < a) : gsB X w τ a b = 0 := by
  rw [gsB, Matrix.mul_diagonal, gsU, FrameDegreeData.uMat_upper _ h, zero_mul]

theorem gsB_diag (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    gsB X w τ a a = ((gsS X w τ a : ℝ) : ℂ) := by
  rw [gsB, Matrix.mul_diagonal, gsU, FrameDegreeData.uMat_diag, one_mul]

end GlobalTheory.SUChartSection
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin

theorem exists_powPr_of_isGrpPullback : ∀ (S T : Scheme.{0}) (t : T ⟶ S) (A : Over S) [GrpObj A] (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left) (B' : Over T) [GrpObj B'] (r : ℕ) (φB : B'.left ⟶ (Out.powObj A r).left), IsGrpPullback A' A t φ' → IsGrpPullback B' (Out.powObj A r) t φB → ∃ pr' : Fin r → (B' ⟶ A'), (∀ u, IsMonHom (pr' u)) ∧ (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) ∧ ∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u := by
  intro S T t A _ A' _ φ' B' _ r φB hA hB
  have wu : ∀ u : Fin r, (φB ≫ (Out.powPr A u).left) ≫ A.hom = B'.hom ≫ t := fun u => by
    rw [Category.assoc, Over.w (Out.powPr A u)]; exact hB.1.w
  let pr' : Fin r → (B' ⟶ A') := fun u => Over.homMk (hA.1.lift _ _ (wu u)) (hA.1.lift_snd _ _ _)
  have hpr : ∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left := fun u => hA.1.lift_fst _ _ _
  have inj : ∀ {X : Over T} (a b : X ⟶ A'), a.left ≫ φ' = b.left ≫ φ' → a = b := fun a b h =>
    Over.OverMorphism.ext (hA.1.hom_ext h ((Over.w a).trans (Over.w b).symm))
  have key : ∀ {X : Over T} (z : X ⟶ B') (u : Fin r),
      pushPt hA.1.w (z ≫ pr' u) = pushPt hB.1.w z ≫ Out.powPr A u := fun z u =>
    Over.OverMorphism.ext (by
      show (z.left ≫ (pr' u).left) ≫ φ' = (z.left ≫ φB) ≫ (Out.powPr A u).left
      rw [Category.assoc, hpr, Category.assoc])
  have isMonHom_of_mul_comp (e : B' ⟶ A')
      (mul : ∀ (X : Over T) (x y : X ⟶ B'), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) :
      IsMonHom e := by
    have hone : (1 : 𝟙_ (Over T) ⟶ B') ≫ e = 1 := by
      have h1 := mul (𝟙_ (Over T)) 1 1
      rw [_root_.mul_one] at h1
      exact _root_.left_eq_mul.mp h1
    refine ⟨?_, ?_⟩
    · simpa [Hom.one_def] using hone
    · have h2 := mul (B' ⊗ B') (fst B' B') (snd B' B')
      simpa [Hom.mul_def] using h2
  refine ⟨pr', fun u => ?_, hpr, fun X y => ?_⟩
  · refine isMonHom_of_mul_comp _ fun X x y => inj _ _ ?_
    have hm : pushPt hB.1.w (x * y) = pushPt hB.1.w x * pushPt hB.1.w y := map_mul (pushHom hB X) x y
    calc ((x * y) ≫ pr' u).left ≫ φ' = (pushPt hA.1.w ((x * y) ≫ pr' u)).left := rfl
      _ = ((pushPt hB.1.w x * pushPt hB.1.w y) ≫ Out.powPr A u).left := by rw [key, hm]
      _ = ((pushPt hB.1.w x ≫ Out.powPr A u) * (pushPt hB.1.w y ≫ Out.powPr A u)).left := by
        rw [MonObj.mul_comp]
      _ = (pushPt hA.1.w (x ≫ pr' u) * pushPt hA.1.w (y ≫ pr' u)).left := by rw [key, key]
      _ = ((x ≫ pr' u) * (y ≫ pr' u)).left ≫ φ' := hA.2 X _ _ _ _ rfl rfl
  · let z : Over.mk (X.hom ≫ t) ⟶ Out.powObj A r :=
      (Out.powIsLimit A r).lift (Fan.mk (Over.mk (X.hom ≫ t)) fun u => pushPt hA.1.w (y u))
    have hz : ∀ u, z ≫ Out.powPr A u = pushPt hA.1.w (y u) := fun u =>
      (Out.powIsLimit A r).fac (Fan.mk (Over.mk (X.hom ≫ t)) fun u => pushPt hA.1.w (y u)) ⟨u⟩
    have hz0 : z.left ≫ (Out.powObj A r).hom = X.hom ≫ t := Over.w z
    let x : X ⟶ B' := Over.homMk (hB.1.lift z.left X.hom hz0) (hB.1.lift_snd _ _ _)
    have comp : ∀ (x₁ : X ⟶ B') (u : Fin r), (x₁ ≫ pr' u).left ≫ φ' = x₁.left ≫ φB ≫ (Out.powPr A u).left :=
      fun x₁ u => by
        show (x₁.left ≫ (pr' u).left) ≫ φ' = _
        rw [Category.assoc, hpr]
    have uniq : ∀ x₁ x₂ : X ⟶ B', (∀ u, x₁ ≫ pr' u = y u) → (∀ u, x₂ ≫ pr' u = y u) → x₁ = x₂ := by
      intro x₁ x₂ h₁ h₂
      refine Over.OverMorphism.ext (hB.1.hom_ext ?_ ((Over.w x₁).trans (Over.w x₂).symm))
      refine powext A r _ _ ?_ fun k => ?_
      · rw [Category.assoc, Category.assoc, hB.1.w, ← Category.assoc, ← Category.assoc, Over.w x₁, Over.w x₂]
      · rw [Category.assoc, Category.assoc, ← comp x₁ k, ← comp x₂ k, h₁, h₂]
    have hx : ∀ u, x ≫ pr' u = y u := fun u => inj _ _ (by
      rw [comp]
      show hB.1.lift z.left X.hom hz0 ≫ φB ≫ (Out.powPr A u).left = (y u).left ≫ φ'
      rw [← Category.assoc, hB.1.lift_fst]
      exact congrArg (fun w => w.left) (hz u))
    exact ⟨x, hx, fun x₁ h₁ => uniq _ _ h₁ hx⟩

end GlobalTheory.ActFin
end
end

section

open CategoryTheory AlgebraicGeometry Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AdicColimit

namespace GlobalTheory.FinitePointLimit

theorem existsUnique_of_isAdicColimit {B : Type} [CommRing B] (J : Ideal B)
    (h : IsAdicColimit J (Over.mk (𝟙 (Sp B)))) (X : Scheme.{0}) (z : ∀ e : ℕ, Sp (B ⧸ J ^ (e + 1)) ⟶ X)
    (hz : ∀ e : ℕ, Out.thickTrans B J e ≫ z (e + 1) = z e) :
    ∃! x : Sp B ⟶ X, ∀ e : ℕ, Out.thick B J e ≫ x = z e := by
  have hι : ∀ e : ℕ, thickι J e (Over.mk (𝟙 (Sp B))) =
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ Out.thick B J e := by
    intro e
    have hc := pullback.condition (f := (Over.mk (𝟙 (Sp B))).hom) (g := Out.thick B J e)
    show pullback.fst _ _ = _
    simpa using hc
  have hiso : ∀ e : ℕ, IsIso (pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e)) := by
    intro e
    have : IsIso (Over.mk (𝟙 (Sp B))).hom := by
      show IsIso (𝟙 _)
      infer_instance
    infer_instance
  have hmap : ∀ e : ℕ, Out.thickMap B J e (Over.mk (𝟙 (Sp B))) ≫
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J (e + 1)) =
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ Out.thickTrans B J e := by
    intro e
    rw [← cancel_mono (Out.thick B J (e + 1)), Category.assoc, Category.assoc,
      Out.thickTrans_comp, ← hι, ← hι, thickMap_ι]
  obtain ⟨g, hg, hu⟩ := h X
    (fun e => pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ z e) (by
      intro e
      rw [← Category.assoc, hmap, Category.assoc, hz])
  refine ⟨g, fun e => ?_, fun x hx => hu x fun e => ?_⟩
  · have he := hg e
    rw [hι, Category.assoc] at he
    have := hiso e
    exact (cancel_epi _).mp he
  · rw [hι, Category.assoc, hx]

end GlobalTheory.FinitePointLimit
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DimSplit

theorem idem_eq_of {S : Type} [CommRing S] {a b : S} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : ∀ q : PrimeSpectrum S, a ∉ q.asIdeal ↔ b ∉ q.asIdeal) : a = b := by
  have := (PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).injective
    (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (by
      ext q
      show q ∈ PrimeSpectrum.basicOpen a ↔ q ∈ PrimeSpectrum.basicOpen b
      simp only [PrimeSpectrum.mem_basicOpen]
      exact hab q)
  exact congrArg Subtype.val this

theorem exists_idempotents_of_isLocallyConstant {R α : Type} [CommRing R] (d : PrimeSpectrum R → α)
    (hd : IsLocallyConstant d) :
    ∃ (n : ℕ) (e : Fin n → R), CompleteOrthogonalIdempotents e ∧
      ∀ k, ∃ a : α, ∀ p : PrimeSpectrum R, 1 - e k ∈ p.asIdeal → d p = a := by
  classical
  have hfin : (Set.range d).Finite := hd.range_finite
  let s := hfin.toFinset
  let g : Fin s.card → α := fun k => (s.equivFin.symm k).1
  have hg : Function.Injective g := fun i j h => s.equivFin.symm.injective (Subtype.val_injective h)
  let C : Fin s.card → TopologicalSpace.Clopens (PrimeSpectrum R) := fun k =>
    ⟨d ⁻¹' {g k}, hd.isClopen_fiber _⟩
  let e : Fin s.card → R := fun k => ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (C k)).1
  have he : ∀ k, IsIdempotentElem (e k) := fun k =>
    ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (C k)).2
  have hmem : ∀ k (p : PrimeSpectrum R), e k ∉ p.asIdeal ↔ d p = g k := by
    intro k p
    have h := PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm (R := R) (C k)
    rw [← PrimeSpectrum.mem_basicOpen]
    show p ∈ PrimeSpectrum.basicOpen (e k) ↔ _
    rw [h]
    rfl
  have horth : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij => idem_eq_of ((he i).mul (he j)) IsIdempotentElem.zero fun q => ?_⟩
    refine ⟨fun h => ?_, fun h => absurd q.asIdeal.zero_mem h⟩
    have hi : e i ∉ q.asIdeal := fun hi => h (q.asIdeal.mul_mem_right _ hi)
    have hj : e j ∉ q.asIdeal := fun hj => h (q.asIdeal.mul_mem_left _ hj)
    exact absurd (hg (((hmem i q).1 hi).symm.trans ((hmem j q).1 hj))) hij
  refine ⟨s.card, e, ⟨horth, ?_⟩, fun k => ⟨g k, fun p hp => (hmem k p).1 fun hk => ?_⟩⟩
  · refine idem_eq_of horth.isIdempotentElem_sum IsIdempotentElem.one fun q => ?_
    refine ⟨fun _ => q.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).2, fun _ hsum => ?_⟩
    have hq : d q ∈ s := hfin.mem_toFinset.2 ⟨q, rfl⟩
    let k := s.equivFin ⟨d q, hq⟩
    have hk : g k = d q := by simp [g, k]
    have hrest : ∑ j ∈ Finset.univ.erase k, e j ∈ q.asIdeal := by
      refine Ideal.sum_mem _ fun j hj => ?_
      by_contra hj'
      exact (Finset.ne_of_mem_erase hj) (hg (((hmem j q).1 hj').symm.trans hk.symm))
    have : e k ∈ q.asIdeal := by
      have h2 := q.asIdeal.sub_mem hsum hrest
      rwa [← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_right] at h2
    exact (hmem k q).2 hk.symm this
  · exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using p.asIdeal.add_mem hp hk))

end GlobalTheory.DimSplit

namespace GlobalTheory.DimSplit

theorem exists_idempotents_smoothOfRelativeDimension : ∀ (R₀ : Type) [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A],
    IsAbelianScheme A → ∃ (n : ℕ) (e : Fin n → R₀), CompleteOrthogonalIdempotents e ∧ ∀ k, ∃ g : ℕ,
      SmoothOfRelativeDimension g (Limits.pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k})))) := by
  intro R₀ _ A _ hA
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n :=
    (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have fib : ∀ x y, A.hom x = A.hom y → n x = n y := fun x y h =>
    hc.apply_eq_of_isPreconnected (A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected
      rfl h.symm
  have hsurj : Function.Surjective A.hom := (inferInstance : Surjective A.hom).surj
  let d : PrimeSpectrum R₀ → ℕ := fun p => n (Classical.choose (hsurj p))
  have hdn : ∀ x, d (A.hom x) = n x := fun x => fib _ _ (Classical.choose_spec (hsurj (A.hom x)))
  have hdl : IsLocallyConstant d := by
    refine (IsLocallyConstant.iff_isOpen_fiber).2 fun g => ?_
    have hcl : IsClosed (A.hom '' (n ⁻¹' {g})ᶜ) :=
      A.hom.isClosedMap _ (hc.isOpen_fiber g).isClosed_compl
    have heq : (d ⁻¹' {g})ᶜ = A.hom '' (n ⁻¹' {g})ᶜ := by
      ext p
      refine ⟨fun hp => ⟨_, hp, Classical.choose_spec (hsurj p)⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact fun h => hx (show n x = g from (hdn x).symm.trans h)
    rw [← isClosed_compl_iff, heq]
    exact hcl
  obtain ⟨m, e, he, hk⟩ := exists_idempotents_of_isLocallyConstant d hdl
  refine ⟨m, e, he, fun k => ?_⟩
  obtain ⟨g, hg⟩ := hk k
  refine ⟨g, GlobalTheory.SmoothNearFibre.smoothOfRelativeDimension_pullback_snd A.hom _ g fun z w hzw => ⟨W z, hW z, ?_⟩⟩
  have hn : n z = g := by
    rw [← hdn z, hzw]
    apply hg
    show Ideal.Quotient.mk _ (1 - e k) ∈ w.asIdeal
    have h0 : Ideal.Quotient.mk (Ideal.span {1 - e k}) (1 - e k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))
    rw [h0]
    exact w.asIdeal.zero_mem
  rw [← hn]
  exact hd z

end GlobalTheory.DimSplit
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.semiAbelianTripleMap_isOpenImmersion_opensRange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) [IsOpenImmersion j] (m : SABMap t' t j), ∃ _ : IsOpenImmersion m.φ, m.φ.opensRange = t.G.hom ⁻¹ᵁ j.opensRange := by
  first | exact @GlobalTheory.sabMap_isOpenImmersion_opensRange | exact GlobalTheory.sabMap_isOpenImmersion_opensRange | (intros; apply GlobalTheory.sabMap_isOpenImmersion_opensRange <;> assumption)
end
