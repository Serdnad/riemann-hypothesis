module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem logCanonicalCut_of_step : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B →
      LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z →
      (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x →
      LcCut p n (Δ + (1 - δ) • D + c • B) x j := by
  intro X _ _ _ p n hp hn Δ D B δ c x z j hk hD hB hl hδ hδ1 hc hoff hsep hdim hlc hnk
  refine ⟨hlc, hnk, fun w hwx hw => ?_⟩
  have hx : KltAt p n (Δ + (1 - δ) • D) x :=
    kltAt_add_smul_of_lcAt X p n hp hn Δ D δ x hD hk hl hδ hδ1
  have hkw : KltAt p n (Δ + (1 - δ) • D) w :=
    (GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation X p n (Δ + (1 - δ) • D) x w hwx).1 hx
  by_cases hzw : z ⤳ w
  · by_cases hwz : w = z
    · subst hwz
      exact absurd ((off_add_smul X p n (Δ + (1 - δ) • D) B c w hoff).1.2 hkw) hw
    · exact topologicalKrullDim_closure_le_of_specializes X z w j hzw hwz hdim
  · exfalso
    have h1 : KltAt p n (Δ + (1 - δ) • D + (1 : ℚ) • B) w := by
      rw [one_smul]; exact hsep w hzw (1 - δ) (by linarith) hkw
    exact hw ((GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hn (Δ + (1 - δ) • D) B c 1 w hB hc).1 h1)

end GlobalTheory.PairStep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_dbl_of_genPair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ (W : Dbl Y) (j : W.Z.functionField →+* K), j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y K _ ψ₁ ψ₂ hg
  obtain ⟨h, hsp⟩ := GlobalTheory.T.genericPair_specializes_diagonal_genericPoint F Y K ψ₁ ψ₂ hg
  obtain ⟨Z, hZi, p₁, p₂, hZ, ζ, hci, hζ₁, hζ₂, hζg⟩ :=
    GlobalTheory.T.exists_reduced_closure_point_fibreSquare F Y K (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
  haveI := hZi
  have hcomp : ζ ≫ Limits.pullback.lift p₁ p₂ hZ =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst]; exact hζ₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Limits.pullback.lift_snd]; exact hζ₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hmem : Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ hZ) := by
    have hcl : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ hZ)) := hci.isClosedEmbedding.isClosed_range
    refine hsp.mem_closed hcl ⟨ζ (IsLocalRing.closedPoint K), ?_⟩
    rw [← hcomp]
    first | rfl | exact (Scheme.Hom.comp_apply _ _ _).symm | simp
  obtain ⟨hproj, δ, hδc, hδ₁, hδ₂, hdiag⟩ := GlobalTheory.T.doubleSpace_of_closedImmersion_contains_diagonal F Y Z p₁ p₂ hZ hci hmem
  let W : Dbl Y :=
    { Z := Z, integral := hZi, p₁ := p₁, p₂ := p₂, δ := δ, str_eq := hZ, proj := hproj, closed := hδc,
      δ₁ := hδ₁, δ₂ := hδ₂, diag := hdiag }
  obtain ⟨j, hj₁, hj₂⟩ := GlobalTheory.T.exists_functionField_map_doubleSpace_genericPoint F Y W K ψ₁ ψ₂ ζ hζg hζ₁ hζ₂
  exact ⟨W, j, hj₁, hj₂⟩

end GlobalTheory.FlagPush
end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.ChartGlue GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexConjugate

namespace GlobalTheory.GoodTop.CorrHolo

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def coordMat (L : V n →L[ℂ] V n) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => L (coordVec a) c

variable {φ : V n → V n} {w : V n}

end GlobalTheory.GoodTop.CorrHolo

namespace GlobalTheory.GoodTop

open CorrHolo

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma apply_coordVec_eq_sum_coordMat {n : ℕ} (L : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n)
    (a : Fin n) : L (_root_.GlobalTheory.GoodMetric.coordVec a) =
      ∑ c, _root_.GlobalTheory.GoodTop.CorrHolo.coordMat L c a • _root_.GlobalTheory.GoodMetric.coordVec c :=
  _root_.GlobalTheory.LineForm.chain_sum_coordVec _

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma mdel_sum_smul_coordVec {n : ℕ} {r : Type}
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (x : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.mdel G z (∑ c, x c • _root_.GlobalTheory.GoodMetric.coordVec c) =
      ∑ c, x c • _root_.GlobalTheory.HermFrame.mdel G z (_root_.GlobalTheory.GoodMetric.coordVec c) := by
  ext i j
  simp [_root_.GlobalTheory.HermFrame.mdel_apply, Matrix.sum_apply]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma mdbar_sum_smul_coordVec {n : ℕ} {r : Type}
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (y : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.mdbar G z (∑ d, y d • _root_.GlobalTheory.GoodMetric.coordVec d) =
      ∑ d, starRingEnd ℂ (y d) • _root_.GlobalTheory.HermFrame.mdbar G z (_root_.GlobalTheory.GoodMetric.coordVec d) := by
  ext i j
  simp [_root_.GlobalTheory.HermFrame.mdbar_apply, Matrix.sum_apply]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma mddbar_sum_smul_coordVec {n : ℕ} {r : Type}
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (x y : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.mddbar G z (∑ c, x c • _root_.GlobalTheory.GoodMetric.coordVec c)
        (∑ d, y d • _root_.GlobalTheory.GoodMetric.coordVec d) =
      ∑ c, ∑ d, (x c * starRingEnd ℂ (y d)) •
        _root_.GlobalTheory.HermFrame.mddbar G z (_root_.GlobalTheory.GoodMetric.coordVec c) (_root_.GlobalTheory.GoodMetric.coordVec d) := by
  ext i j
  simp [_root_.GlobalTheory.HermFrame.mddbar_apply, Matrix.sum_apply, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma curv_sum_smul_coordVec {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (hG : _root_.GlobalTheory.HermFrame.MContDiffAt 2 G z)
    (hu : IsUnit (G z).det) (x y : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.curv G z (∑ c, x c • _root_.GlobalTheory.GoodMetric.coordVec c)
        (∑ d, y d • _root_.GlobalTheory.GoodMetric.coordVec d) =
      ∑ c, ∑ d, (x c * starRingEnd ℂ (y d)) •
        _root_.GlobalTheory.HermFrame.curv G z (_root_.GlobalTheory.GoodMetric.coordVec c) (_root_.GlobalTheory.GoodMetric.coordVec d) := by
  simp only [_root_.GlobalTheory.HermFrame.curv_eq hG hu, mdel_sum_smul_coordVec,
    mdbar_sum_smul_coordVec, mddbar_sum_smul_coordVec,
    Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.smul_sum]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma conn_sum_smul {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (x : Fin n → ℂ) (v : Fin n → _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    _root_.GlobalTheory.HermFrame.conn G z (∑ c, x c • v c) =
      ∑ c, x c • _root_.GlobalTheory.HermFrame.conn G z (v c) := by
  let f : _root_.ReciprocityTheory.L2DbarEstimates.V n →+ Matrix r r ℂ :=
    { toFun := _root_.GlobalTheory.HermFrame.conn G z
      map_zero' := by simpa using _root_.GlobalTheory.HermFrame.conn_smul_vec G z 0 0
      map_add' := _root_.GlobalTheory.HermFrame.conn_add_vec G z }
  change f (∑ c, x c • v c) = _

  rw [map_sum]
  exact Finset.sum_congr rfl fun c _ => _root_.GlobalTheory.HermFrame.conn_smul_vec G z (x c) (v c)


set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
theorem _root_.GlobalTheory.GoodTop.corrC_comp_holo {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}
    {φ : _root_.ReciprocityTheory.L2DbarEstimates.V n → _root_.ReciprocityTheory.L2DbarEstimates.V n} {w : _root_.ReciprocityTheory.L2DbarEstimates.V n} (hφ : ContDiffAt ℂ 2 φ w)
    (hρ : DifferentiableAt ℝ ρ (φ w))
    (h₀ : _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₀ (φ w)) (u₀ : IsUnit (G₀ (φ w)).det)
    (h₁ : _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₁ (φ w))
    (u₁ : IsUnit (G₁ (φ w)).det) :
    _root_.GlobalTheory.GoodTop.corrC (fun x => ρ (φ x)) (fun x => G₀ (φ x)) (fun x => G₁ (φ x)) w =
      ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ (φ w) := by
  have hφd : DifferentiableAt ℂ φ w := hφ.differentiableAt (by norm_num)
  have h₀' : _root_.GlobalTheory.HermFrame.MContDiffAt 1 G₀ (φ w) := fun a b => (h₀ a b).of_le (by norm_num)
  have h₁' : _root_.GlobalTheory.HermFrame.MContDiffAt 1 G₁ (φ w) := fun a b => (h₁ a b).of_le (by norm_num)
  obtain ⟨J, hJ⟩ : ∃ J, J = _root_.GlobalTheory.GoodTop.CorrHolo.coordMat (fderiv ℂ φ w) := ⟨_, rfl⟩
  have hL : ∀ a, fderiv ℂ φ w (_root_.GlobalTheory.GoodMetric.coordVec a) =
      ∑ c, J c a • _root_.GlobalTheory.GoodMetric.coordVec c := by
    intro a
    rw [hJ]
    exact apply_coordVec_eq_sum_coordMat _ a
  have hcurv : ∀ G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G (φ w) →
      IsUnit (G (φ w)).det → _root_.GlobalTheory.GoodTop.curvAt (fun x => G (φ x)) w =
        fun a b => ∑ c, ∑ d, (J c a * (J.map (starRingEnd ℂ)) d b) •
          _root_.GlobalTheory.GoodTop.curvAt G (φ w) c d := by
    intro G hG hu
    funext a b
    simp only [_root_.GlobalTheory.GoodTop.curvAt, Matrix.map_apply]
    rw [_root_.GlobalTheory.HermFrame.curv_comp_holo hG hu hφ, hL, hL,
      curv_sum_smul_coordVec G _ hG hu]
  have hρc : DifferentiableAt ℝ (fun y => (ρ y : ℂ)) (φ w) :=
    Complex.ofRealCLM.differentiableAt.comp _ hρ
  have hdbar : _root_.GlobalTheory.GoodTop.cutForm (fun x => ρ (φ x)) (fun x => G₀ (φ x))
      (fun x => G₁ (φ x)) w = fun a b => ∑ c, ∑ d, (J c a * (J.map (starRingEnd ℂ)) d b) •
        _root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ (φ w) c d := by
    funext a b
    simp only [_root_.GlobalTheory.GoodTop.cutForm, Matrix.map_apply]
    have hw := _root_.GlobalTheory.dbar_comp_holo (u := fun y => (ρ y : ℂ)) hρc hφd


    rw [hw, _root_.GlobalTheory.HermFrame.conn_comp_holo h₁' hφd,
    _root_.GlobalTheory.HermFrame.conn_comp_holo h₀' hφd, hL, hL, conn_sum_smul,
    conn_sum_smul, map_sum, ← Finset.sum_sub_distrib, Finset.sum_smul]
    simp only [map_smulₛₗ, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [← smul_sub, smul_smul, smul_eq_mul]
    congr 1
    ring
  have hdet : J.det * (J.map (starRingEnd ℂ)).det = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : J.det = (fderiv ℂ φ w).det := by
      have hJm : J = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (fderiv ℂ φ w : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) := by
        ext c a
        simp [hJ, _root_.GlobalTheory.GoodTop.CorrHolo.coordMat, LinearMap.toMatrix_apply,
          _root_.GlobalTheory.GoodMetric.coordVec]
      rw [hJm, LinearMap.det_toMatrix]
    have h2 : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det :=
      (RingHom.map_det (starRingEnd ℂ) J).symm
    rw [h2, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  unfold _root_.GlobalTheory.GoodTop.corrC
  rw [hcurv G₁ h₁ u₁, hcurv G₀ h₀ u₀, hdbar, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hdet, ← _root_.GlobalTheory.GoodTop.mixTop_subst]
  congr 1
  funext i a b
  unfold _root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one
  split_ifs <;> rfl

end GlobalTheory.GoodTop
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.exists_goodPatch_of_complexPoint_openPart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ y ∈ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  first | exact @GlobalTheory.GoodTop.exists_goodPatch_of_mem | exact GlobalTheory.GoodTop.exists_goodPatch_of_mem | (intros; apply GlobalTheory.GoodTop.exists_goodPatch_of_mem <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integral_finite_sum_topForms : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ι : Type} [Fintype ι] {d : ι → κ → Y → ℝ} {t : ι → ℝ}, (∀ a, IsTopForm e (d a) S) → (∀ a, HasInt e (d a) S (t a)) → HasInt e (fun i y => ∑ a, d a i y) S (∑ a, t a) := by
  first | exact @GlobalTheory.GoodTop.hasInt_sum | exact GlobalTheory.GoodTop.hasInt_sum | (intros; apply GlobalTheory.GoodTop.hasInt_sum <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_mixTop_position_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) :
    ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = mixTop (fun _ => K₁) - mixTop fun _ => K₀ := by
  classical
  set T : ℕ → ℂ := fun k => mixTop (fun i : Fin n => if (i : ℕ) < k then K₁ else K₀) with hT
  have hterm : ∀ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = T ((j : ℕ) + 1) - T j := by
    intro j
    have hK : K₁ - K₀ = (1 : ℂ) • K₁ + (-1 : ℂ) • K₀ := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [hK, GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ K₁ K₀ 1 (-1) j, one_mul, neg_one_mul, ← sub_eq_add_neg]
    congr 1
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j + 1 := by have := Fin.lt_def.mp h1; omega
        simp [h1, this]
      · by_cases h2 : i = j
        · subst h2; simp
        · have h3 : ¬ ((i : ℕ) < j + 1) := by
            have : j < i := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
            have := Fin.lt_def.mp this; omega
          simp [h1, h2, h3]
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j := Fin.lt_def.mp h1
        simp [h1, this]
      · have : ¬ ((i : ℕ) < j) := fun h => h1 (Fin.lt_def.mpr h)
        by_cases h2 : i = j
        · simp [h1, h2, this]
        · simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Fin.sum_univ_eq_sum_range (fun k => T (k + 1) - T k) n, Finset.sum_range_sub]
  have e1 : (fun i : Fin n => if (i : ℕ) < n then K₁ else K₀) = fun _ => K₁ := by
    funext i; simp [i.isLt]
  have e0 : (fun i : Fin n => if (i : ℕ) < 0 then K₁ else K₀) = fun _ => K₀ := by
    funext i; simp
  show mixTop _ - mixTop _ = _
  rw [e1, e0]

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrC_sum_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ι : Type} [Fintype ι]
    (ρ : ι → V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n), (∀ i, DifferentiableAt ℝ (ρ i) v) →
    (∀ x, ∑ i, ρ i x = 1) → ∑ i, corrC (ρ i) G₀ G₁ v = 0 := by
  intro n r _ _ ι _ ρ G₀ G₁ v hd h1
  have hsum : ∀ w, ∑ i, dbar (fun x => (ρ i x : ℂ)) v w = 0 := by
    intro w
    have e : (fun x => ∑ i, (ρ i x : ℂ)) = fun _ => (1 : ℂ) := by
      funext x; rw [← Complex.ofReal_sum, h1]; simp
    have hs := dbar_sum (t := Finset.univ) (A := fun i x => (ρ i x : ℂ)) (z := v)
      (fun i _ => Complex.ofRealCLM.differentiableAt.comp v (hd i))
    rw [e, dbar_const] at hs
    rw [← ContinuousLinearMap.sum_apply, ← hs]; rfl
  have hadd : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r),
      mixTop (intersection_update_fsHerm_neg_one K₁ (L + L') K₀ j) = mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
    intro K₁ K₀ j L L'; simpa using GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ L L' 1 1 j
  have hzero : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n), mixTop (intersection_update_fsHerm_neg_one K₁ (0 : EndValuedForm11Coeffs n r) K₀ j) = 0 := by
    intro K₁ K₀ j; simpa using GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ 0 0 0 0 j
  have hc : ∑ i, cutForm (ρ i) G₀ G₁ v = 0 := by
    funext a b
    simp only [Finset.sum_apply, cutForm, ← Finset.sum_smul, hsum, zero_smul]
    rfl
  unfold corrC
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  let F : EndValuedForm11Coeffs n r →+ ℂ :=
    { toFun := fun L => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) L (curvAt G₀ v) j)
      map_zero' := hzero _ _ _
      map_add' := fun L L' => hadd _ _ _ L L' }
  have hF : ∑ i, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm (ρ i) G₀ G₁ v) (curvAt G₀ v) j) =
      F (∑ i, cutForm (ρ i) G₀ G₁ v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; rfl
  rw [hF, hc, map_zero]

end GlobalTheory.GoodTop
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eigenvalue_integral_norm_bound : ∀ (p : ℕ) [Fact p.Prime] (Kw : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (N : Matrix (Fin n) (Fin n) Kw) (H k : GL (Fin n) (KQ p Kw r)), k ∈ Kres p Kw n r → N.map (inclK p Kw r) = ((H * k * H⁻¹ : GL (Fin n) (KQ p Kw r)) : Matrix (Fin n) (Fin n) (KQ p Kw r)) → ∀ (v : Fin n → PadicAlgCl p) (c : PadicAlgCl p), v ≠ 0 → N.map (fun x => (x : PadicAlgCl p)) *ᵥ v = c • v → ‖c‖ ≤ 1 := by
  first | (exact @GlobalTheory.StabFin.norm_eigen_le_one_of_conj_Kres) | (exact GlobalTheory.StabFin.norm_eigen_le_one_of_conj_Kres) | (intros; apply GlobalTheory.StabFin.norm_eigen_le_one_of_conj_Kres  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_ample_power_section_nonvanishing_on_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ S : Set X, S.Finite → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, S ⊆ NV P e 0 f := by
  first | exact @GlobalTheory.HSAmp.exists_sec_nonvanishing_finite | exact GlobalTheory.HSAmp.exists_sec_nonvanishing_finite | (intros; apply GlobalTheory.HSAmp.exists_sec_nonvanishing_finite <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.fubiniStudyWeightIncrement_semiPositive_curvature : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (up P.L u).SemiPos D := by
  first | exact @GlobalTheory.HSAmp.semiPos_up_of_isCan | exact GlobalTheory.HSAmp.semiPos_up_of_isCan | (intros; apply GlobalTheory.HSAmp.semiPos_up_of_isCan <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), (upperParabolic P u).nu e 0 σ y (x l) ≤ 1) ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, Real.exp (-(Real.log (D + 1) / (2 * n))) ≤ (upperParabolic P u).nu e 0 σ y (x l)) ∧ Gens (upperParabolic P u) D e x ∧ Gens P D (e * n) (fun l => x l ^ n) ∧ IsCan P (e * n) 1 (fun l => x l ^ n) u := by
  first | exact @GlobalTheory.HSAmp.canNorms | exact GlobalTheory.HSAmp.canNorms | (intros; apply GlobalTheory.HSAmp.canNorms <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.sectionValueUnitFrame_conj_point_eq_phase_conj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ (σ' : k →+* ℂ) (y' : CxPts p σ') (θ : ℂ), ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ' y' f = θ * (starRingEnd ℂ) (val P a b σ y f) := by
  first | exact @GlobalTheory.HSAmp.val_conj | exact GlobalTheory.HSAmp.val_conj | (intros; apply GlobalTheory.HSAmp.val_conj <;> assumption)
end
