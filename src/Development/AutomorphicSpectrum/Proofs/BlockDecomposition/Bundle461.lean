module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle443
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.NegStep

theorem integral_neg_of_secondCountable {G E : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → E) :
    ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  have : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  exact integral_neg_eq_self f μ

theorem colJoin_zero_mul {R : Type*} [NonUnitalNonAssocSemiring R] {m r s : ℕ} (p : Matrix (Fin m) (Fin r) R)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) R) (c : Matrix (Fin r) (Fin (r + s)) R)
    (h : ∀ j : Fin r, a (Fin.castAdd s j) = c j) :
    colJoin p (0 : Matrix (Fin m) (Fin s) R) * a = p * c := by
  ext i k
  simp [Matrix.mul_apply, Fin.sum_univ_add, h]

theorem inner_neg_neg {D : D7} (V : HSp D) {n : ℕ} (t : Mx D V.rank n) : inner V (-t) (-t) = inner V t t := by
  unfold GlobalTheory.StdUnn.inner
  rw [adj_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem integral_colJoin_neg_eq_J : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (r s : ℕ) (μr : Measure (Mx D V.rank r))
    (𝓕r : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μr 𝓕r →
    ∀ (c : Matrix (Fin r) (Fin (r + s)) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsCompl c a →
    ∀ (b : HermE D r) (Φ : Mx D V.rank (r + s) → ℂ),
      ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr = J ψ V μr (pull c Φ) b := by
  intro D ψ V r s μr 𝓕r hcov c a hca b Φ
  obtain ⟨h1, h2, h3, h4, -⟩ := lattice_Mx D V.rank r
  have hB : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  have hH : μr.IsAddHaarMeasure := hcov.1
  have hrow : ∀ j : Fin r, rat a (Fin.castAdd s j) = rat c j := by
    intro j
    have := hca.2 (Fin.castAdd s j) j.isLt
    funext k
    show incA D (a (Fin.castAdd s j) k) = incA D (c j k)
    rw [this]
    rfl
  have key : ∀ t : Mx D V.rank r,
      ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) =
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))) (-t) := by
    intro t
    have e : (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a) : Mx D V.rank (r + s)) = HMul.hMul (-t) (rat c) :=
      colJoin_zero_mul (-t) (rat a) (rat c) hrow
    show _ = Φ (HMul.hMul (-t) (rat c)) * _
    rw [e, inner_neg_neg, mul_comm]
  exact (integral_congr_ae (Filter.Eventually.of_forall key)).trans
    (integral_neg_of_secondCountable (E := ℂ) μr
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))))

end GlobalTheory.CompanionTheory.EisUnfold.NegStep
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Summand

variable {D : D7}

theorem trace_inner_join (V : HSp D) {r s : ℕ} (x₁ y₁ : Mx D V.rank r) (x₂ y₂ : Mx D V.rank s) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (colJoin x₁ x₂) (colJoin y₁ y₂)) =
      Matrix.trace (GlobalTheory.StdUnn.inner V x₁ y₁) + Matrix.trace (GlobalTheory.StdUnn.inner V x₂ y₂) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;>
    simp [GlobalTheory.StdUnn.inner, adj, Matrix.mul_apply]

theorem trace_inner_mul (V : HSp D) {n : ℕ} (U W : Mx D V.rank n) (A A' : Mx D n n)
    (h : HMul.hMul A' (adj A) = (1 : Mx D n n)) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A')) = Matrix.trace (GlobalTheory.StdUnn.inner V U W) := by
  have e : GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A') =
      HMul.hMul (adj A) (HMul.hMul (GlobalTheory.StdUnn.inner V U W) A') := by
    simp only [GlobalTheory.StdUnn.inner, adj_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]

theorem inner_neg_left (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (-x) y = -GlobalTheory.StdUnn.inner V x y := by
  have : adj (-x) = -adj x := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.neg_mul]

theorem inner_neg_right (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V x (-y) = -GlobalTheory.StdUnn.inner V x y := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_neg]

theorem inner_sub_left (V : HSp D) {n : ℕ} (x x' y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (x - x') y = GlobalTheory.StdUnn.inner V x y - GlobalTheory.StdUnn.inner V x' y := by
  have : adj (x - x') = adj x - adj x' := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.sub_mul]

theorem inner_sub_right (V : HSp D) {n : ℕ} (x y y' : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V x (y - y') = GlobalTheory.StdUnn.inner V x y - GlobalTheory.StdUnn.inner V x y' := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_sub]

theorem inner_zero_left (V : HSp D) {n : ℕ} (y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
  have : adj (0 : Mx D V.rank n) = 0 := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.zero_mul]

theorem inner_mul_right (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) (B : Mx D n n) :
    GlobalTheory.StdUnn.inner V x (HMul.hMul y B) = HMul.hMul (GlobalTheory.StdUnn.inner V x y) B := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_assoc]

theorem trace_adj {n : ℕ} (M : Mx D n n) : Matrix.trace (adj M) = cA D (Matrix.trace M) := by

  simp [Matrix.trace, adj, map_sum]

theorem adj_inner (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    adj (GlobalTheory.StdUnn.inner V x y) = GlobalTheory.StdUnn.inner V y x := by
  simp only [GlobalTheory.StdUnn.inner, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem trace_swap (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) (B : Mx D n n) (hB : adj B = B) :
    Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y x) B) =
      cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V x y) B)) := by
  rw [← trace_adj, adj_mul, adj_inner, hB, Matrix.trace_mul_comm]

theorem exp_ring {R : Type*} [CommRing R] (c t₁ t₃ t₄ t₅ : R) (h : c + c = 1) :
    -t₁ + t₅ + c * t₃ + c * t₄ = t₅ + c * (t₃ - t₁ - t₁ + t₄) := by
  linear_combination t₁ * h

theorem sub_group {G : Type*} [AddCommGroup G] (a b c d : G) : a - b - (c - d) = a - b - c + d := by
  abel

theorem halfTr_eq (z : AE D) : halfTr z = algebraMap D.host.F (AF D.host.F) (1 / 2) * trA z := rfl

theorem half_add_half : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
  rw [← map_add (f := _), add_halves, map_one]

theorem psi_halfTr_incA (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (e : D.host.E) :
    ψ (halfTr (incA D e)) = 1 := by
  have : halfTr (incA D e) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e) := by
    have h : Algebra.trace (AF D.host.F) (AE D) (incA D e) =
        algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
      show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
      rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
    rw [halfTr_eq, map_mul, trA, h]
  rw [this]
  exact hψ.2.2.1 _

theorem trace_inner_rat (V : HSp D) {n : ℕ} (p : Matrix (Fin V.rank) (Fin n) D.host.E) (b : Matrix (Fin n) (Fin n) D.host.E) :
    ∃ e : D.host.E, Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)) = incA D e := by
  refine ⟨Matrix.trace (pᴴ * (HSpace.gram V * p) * b), ?_⟩
  have : HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b) = rat (pᴴ * (HSpace.gram V * p) * b) := by
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose]
    rfl
  rw [this]

  simp only [Matrix.trace, Matrix.diag_apply, rat, Matrix.map_apply, map_sum]

theorem psi_combine (ψ : AddChar (AF D.host.F) ℂ) (X Y T t₁ t₃ t₄ t₅ : AE D) (e₁ : X = -t₁ + t₅) (e₂ : Y = t₃)
    (e₃ : T = t₃ - cA D t₁ - t₁ + t₄) (e₄ : ψ (halfTr t₄) = 1) :
    ψ (trA X + halfTr Y) = ψ (trA t₅) * ψ (halfTr T) := by
  subst e₁ e₂ e₃
  have h : trA (-t₁ + t₅) + halfTr Y + halfTr t₄ = trA t₅ + halfTr (Y - cA D t₁ - t₁ + t₄) := by
    simp only [halfTr_eq, trA, map_add (f := _), map_sub, map_neg, GlobalTheory.DualPairCheck.trace_cA]
    exact exp_ring _ _ _ _ _ half_add_half
  rw [← AddChar.map_add_eq_mul, ← h, AddChar.map_add_eq_mul ψ _ (halfTr t₄), e₄, mul_one]

theorem summand (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (hb : (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (ha : IsUnit a.det)
    (Φ : Mx D V.rank (r + s) → ℂ) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) (v : Mx D V.rank ((r + s) + (r + s)))
    (hx : xPart v = -HMul.hMul (colJoin y₁ (0 : Mx D V.rank s)) (rat a))
    (hy : yPart v = HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹))
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E) :
    Heisenberg₂ ψ V v Φ (rat (colJoin p q * a)) = cellTerm ψ V b a Φ p q y₁ y₂ := by
  have hunit : IsUnit (aᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact ha.star
  have hA : HMul.hMul (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) (adj (rat a)) = (1 : Mx D (r + s) (r + s)) := by
    have : cT (D.sp.cm.sig : D.host.E →+* D.host.E) a = aᴴ := rfl
    rw [this, ← rat_conjTranspose, ← rat_mul, Matrix.nonsing_inv_mul _ hunit, rat_one]
  have hB : adj (rat b) = rat b := by
    rw [← rat_conjTranspose]
    exact congrArg rat hb
  have hz : rat (colJoin p q * a) = HMul.hMul (colJoin (rat p) (rat q)) (rat a) := by
    rw [rat_mul, rat_colJoin]
  have hzx : rat (colJoin p q * a) + xPart v = HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a) := by
    rw [hz, hx, ← sub_eq_add_neg, ← Matrix.sub_mul, ← colJoin_sub, sub_zero]
  obtain ⟨e, he⟩ := trace_inner_rat V p b
  have e₄ : ψ (halfTr (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)))) = 1 := by
    rw [he]
    exact psi_halfTr_incA ψ hψ e
  have e1 : Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v)) =
      -Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)) + Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) y₂) := by
    rw [hz, hy, trace_inner_mul V _ _ _ _ hA, trace_inner_join, inner_neg_right, inner_mul_right, Matrix.trace_neg]
  have e2 : Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)) =
      Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b)) := by
    rw [hx, hy, ← Matrix.neg_mul, trace_inner_mul V _ _ _ _ hA]
    have : -colJoin y₁ (0 : Mx D V.rank s) = colJoin (-y₁) (0 : Mx D V.rank s) := by
      rw [← colJoin_neg, neg_zero]
    rw [this, trace_inner_join, inner_zero_left, inner_neg_left, inner_neg_right, inner_mul_right]
    simp
  have e3 : Matrix.trace (HMul.hMul (rat b) (GlobalTheory.StdUnn.inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r) =
      Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b))
        - cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)))
        - Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b))
        + Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)) := by
    rw [Matrix.trace_mul_comm, ← trace_swap V (rat p) y₁ (rat b) hB, inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [Matrix.sub_mul, Matrix.trace_sub]
    exact sub_group _ _ _ _
  have hc := psi_combine ψ _ _ _ _ _ _ _ e1 e2 e3 e₄
  show ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v))) +
      halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)))) * Φ (rat (colJoin p q * a) + xPart v) = _
  rw [hc, hzx, mul_assoc]
  rfl

end GlobalTheory.CompanionTheory.EisUnfold.Summand
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Parts

section Field

variable {K : Type} [Field K]

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem extB_castAdd {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i j : Fin r) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) (Fin.castAdd s i) (Fin.castAdd s j) = b i j := by
  simp [extB]

theorem extB_natAdd_left {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i : Fin s) (j : Fin (r + s)) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) (Fin.natAdd r i) j = 0 := by
  simp [extB]

theorem extB_natAdd_right {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) (i : Fin (r + s)) (j : Fin s) :
    (extB b : Matrix (Fin (r + s)) (Fin (r + s)) K) i (Fin.natAdd r j) = 0 := by
  simp [extB]

theorem eId_mul_extB {r s : ℕ} (b : Matrix (Fin r) (Fin r) K) :
    eId K (r + s) r * extB b = extB b := by
  ext i j
  rw [eId, Matrix.diagonal_mul]
  by_cases h : (i : ℕ) < r
  · simp [h]
  · simp [h, extB]

theorem representation_matrix_block_form (σ : K →+* K) {r s : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) K) :
    repMat σ b a = blk4 ((1 - eId K (r + s) r) * a)
        (((1 - eId K (r + s) r) * extB b + eId K (r + s) r) * (cT σ a)⁻¹)
        (-(eId K (r + s) r * a))
        ((1 - eId K (r + s) r - extB b) * (cT σ a)⁻¹) := by
  simp only [repMat, wr, nB, mA]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have h : -eId K (r + s) r * extB b + (1 - eId K (r + s) r) * 1 =
      1 - eId K (r + s) r - extB b := by
    rw [Matrix.neg_mul, eId_mul_extB, Matrix.mul_one]
    abel
  rw [h]
  simp

end Field

variable {D : D7}

theorem block_matrix_map {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map (incA D) = blk4 (a.map (incA D)) (b.map (incA D)) (c.map (incA D)) (d.map (incA D)) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem xPart_zy_mul {m n : ℕ} (y : Mx D m n) (A B C E' : Mx D n n) :
    xPart (HMul.hMul (zy y) (blk4 A B C E') : Mx D m (n + n)) = HMul.hMul y C := by
  ext i j
  simp only [xPart, zy, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [Fintype.sum_equiv finSumFinEquiv.symm _
    (fun t => Sum.elim (fun _ => (0 : AE D)) (y i) t * Matrix.fromBlocks A B C E' t (Sum.inl j))
    (fun _ => rfl), Fintype.sum_sum_type]
  simp

theorem yPart_zy_mul {m n : ℕ} (y : Mx D m n) (A B C E' : Mx D n n) :
    yPart (HMul.hMul (zy y) (blk4 A B C E') : Mx D m (n + n)) = HMul.hMul y E' := by
  ext i j
  simp only [yPart, zy, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [Fintype.sum_equiv finSumFinEquiv.symm _
    (fun t => Sum.elim (fun _ => (0 : AE D)) (y i) t * Matrix.fromBlocks A B C E' t (Sum.inr j))
    (fun _ => rfl), Fintype.sum_sum_type]
  simp

theorem colJoin_mul_eId {m r s : ℕ} (y₁ : Mx D m r) (y₂ : Mx D m s) :
    (HMul.hMul (colJoin y₁ y₂) ((eId D.host.E (r + s) r).map (incA D)) : Mx D m (r + s)) =
      colJoin y₁ (0 : Mx D m s) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [eId, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply]
  · simp [eId, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply]

theorem colJoin_mul_extB {m r s : ℕ} (y₁ : Mx D m r) (y₂ : Mx D m s) (b : Matrix (Fin r) (Fin r) D.host.E) :
    (HMul.hMul (colJoin y₁ y₂) ((extB b : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E).map (incA D)) : Mx D m (r + s)) =
      colJoin (HMul.hMul y₁ (rat b) : Mx D m r) (0 : Mx D m s) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [Matrix.mul_apply, Fin.sum_univ_add, extB_castAdd, extB_natAdd_left, rat]
  · simp [Matrix.mul_apply, Fin.sum_univ_add, extB_natAdd_right]

theorem parts : ∀ (D : D7) (m r s : ℕ) (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (y₁ : Mx D m r) (y₂ : Mx D m s),
    xPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        -HMul.hMul (colJoin y₁ (0 : Mx D m s)) (rat a) ∧
      yPart (HMul.hMul (zy (colJoin y₁ y₂)) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b a).map (incA D))) =
        HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) := by
  intro D m r s b a y₁ y₂
  set e := eId D.host.E (r + s) r with he
  set y : Mx D m (r + s) := colJoin y₁ y₂ with hy
  have hmap : ∀ X : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E,
      X.map (incA D) = (incA D).mapMatrix X := fun _ => rfl
  rw [representation_matrix_block_form, block_matrix_map, xPart_zy_mul, yPart_zy_mul]
  constructor
  · have h1 : (-(e * a)).map (incA D) = -(e.map (incA D) * rat a) := by
      simp only [hmap, map_neg, map_mul]; rfl
    rw [h1, Matrix.mul_neg, ← Matrix.mul_assoc, colJoin_mul_eId]
  · have h2 : ((1 - e - extB b) * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹).map (incA D) =
        (1 - e.map (incA D) - (extB b : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E).map (incA D)) *
          rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹ := by
      simp only [hmap, map_sub, map_mul, map_one]; rfl
    rw [h2, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, hy, colJoin_mul_eId,
      colJoin_mul_extB, ← colJoin_sub, ← colJoin_sub]
    congr 2
    · simp
    · simp

end GlobalTheory.CompanionTheory.EisUnfold.Parts
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

variable {D : D7} {n : ℕ}

theorem heis_apply (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (v : Mx D V.rank (n + n)) (Φ : Mx D V.rank n → ℂ)
    (z : Mx D V.rank n) : PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂ ψ V v Φ z =
      ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V z (yPart v))) + halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)))) *
        Φ (z + xPart v) := rfl

theorem mat_inv_levi (g : G D n) (a : GL (Fin n) (AE D)) (hg : mat g = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    mat g⁻¹ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 : (a⁻¹).1 * a.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    have := adj_mul (a⁻¹).1 a.1
    rw [show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D n n) from h1, adj_one] at this
    exact this.symm
  have h3 : blk4 (a⁻¹).1 0 0 (adj a.1) * mat g = 1 := by
    rw [hg, submatrix_fromBlocks_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, h2]
    exact block_matrix_one
  calc mat g⁻¹ = (blk4 (a⁻¹).1 0 0 (adj a.1) * mat g) * mat g⁻¹ := by rw [h3, Matrix.one_mul]
    _ = blk4 (a⁻¹).1 0 0 (adj a.1) := by rw [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]

theorem trace_inner_levi (V : HSp D) (z y : Mx D V.rank n) (a : Mx D n n) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul z a : Mx D V.rank n) y) =
      Matrix.trace (GlobalTheory.StdUnn.inner V z (HMul.hMul y (adj a) : Mx D V.rank n)) := by
  simp only [GlobalTheory.StdUnn.inner, adj_mul]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem trace_inner_levi_both (V : HSp D) (x y : Mx D V.rank n) (a : GL (Fin n) (AE D)) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul x (a⁻¹).1 : Mx D V.rank n) (HMul.hMul y (adj a.1) : Mx D V.rank n)) =
      Matrix.trace (GlobalTheory.StdUnn.inner V x y) := by
  have h1 : (a⁻¹).1 * a.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    have := adj_mul (a⁻¹).1 a.1
    rw [show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D n n) from h1, adj_one] at this
    exact this.symm
  simp only [GlobalTheory.StdUnn.inner, adj_mul]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one]

theorem covAt_levi : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hW g a hg v Φ Ψ hΨ
  have hinv := mat_inv_levi g a hg
  have hx : xPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = HMul.hMul (xPart v) (a⁻¹).1 := by
    rw [hinv, x_part_mul_block, Matrix.mul_zero, add_zero]
  have hy : yPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = HMul.hMul (yPart v) (adj a.1) := by
    rw [hinv, y_part_mul_block, Matrix.mul_zero, zero_add]
  have h1 : (a⁻¹).1 * a.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  funext z
  rw [hW.levi g a hg Ψ z, hΨ]
  rw [heis_apply, heis_apply, hx, hy, hW.levi g a hg Φ, trace_inner_levi V z (yPart v) a.1, trace_inner_levi_both]
  have e3 : HMul.hMul (z + HMul.hMul (xPart v) (a⁻¹).1 : Mx D V.rank n) a.1 =
      (HMul.hMul z a.1 + xPart v : Mx D V.rank n) := by
    rw [Matrix.add_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [e3]
  ring

end GlobalTheory.CompanionTheory.EisCovar
end
end
