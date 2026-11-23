module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IntegralModuleBases.DetToMatrixSq

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cusp_coefficient_bound_of_unipotent_lattice_lift (hL2 : UnipotentLatticeLift (E := E)) : CuspCoefficientBound (E := E) := by
  intro r X u hu huΛ la P hP hchi ν
  have hiso : X.IsIso (u 0) := ⟨huΛ 0, hu.1 0 0, hu.2.ne_zero 0⟩
  refine ⟨CuspCoefficientFlow.fj_diffOn X.toData la P hP.1 hiso ν, ?_, ?_⟩
  · intro x hx b hb
    have hfl : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b) =
        rmul (X.flow (u 0) (fun τ => (s τ : ℂ)) x) b := fun s => by
      funext τ
      show X.flowMat (u 0) τ (s τ : ℂ) * (mat x τ * mat b τ) =
        (X.flowMat (u 0) τ (s τ : ℂ) * mat x τ) * mat b τ
      rw [Matrix.mul_assoc]
    have hPb : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b)) =
        bchar la b * P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl]
      exact hP.1.1.2.1 _ (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1 b hb
    unfold Data.fj
    split_ifs with h1 h2
    · simp_rw [hPb, mul_assoc]
      rw [integral_const_mul]
      ring
    · simp
    · simp
  · intro b hb x hx
    let a0 : X.Ψ → Fin 2 → ℂ := fun _ => ![1, 0]
    have hemb : X.embV (u 0) = X.uvec u a0 := by
      funext τ
      simp [Data.uvec, a0, Fin.sum_univ_two, Data.embV]
    have hfl : ∀ (s : X.Ψ → ℝ) y, X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.Zb u (fun τ i k => (s τ : ℂ) * a0 τ i * conj (a0 τ k)) y := fun s y => by
      rw [show X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.flowV (X.embV (u 0)) (fun τ => (s τ : ℂ)) y from rfl, hemb, Data.flowV_uvec]
    have hZ : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x) =
        X.Zb u b (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl, hfl, Data.Zb_Zb X.toData u hu.1, Data.Zb_Zb X.toData u hu.1, add_comm]
    have hPZ : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x)) =
        P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hZ]
      exact (hL2 r X u hu huΛ).2.1 la P hP.1.1 hchi b hb _
        (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1
    unfold Data.fj
    simp_rw [hPZ]

end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma bound_castLE {n : ℕ} (h : n ≤ X.p0) (Z : X.Coord) (τ : X.Ψ) (y : Fin n → ℂ) :
    nsq ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) ≤
      X.zN Z ^ 2 * nsq y := by
  classical
  set z : Fin X.p0 → ℂ := fun c => if h' : (c : ℕ) < n then y ⟨c, h'⟩ else 0 with hz
  have hinj : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  have hzc : ∀ b : Fin n, z (Fin.castLE h b) = y b := by
    intro b
    simp [hz, b.isLt]
  have hz0 : ∀ c ∉ Set.range (Fin.castLE h), z c = 0 := by
    intro c hc
    simp only [hz]
    rw [dite_eq_right]
    intro hcn
    exact hc ⟨⟨c, hcn⟩, Fin.ext rfl⟩
  have hvec : ((Matrix.of fun (m : Fin (r - X.p0)) (b : Fin n) => Z τ m (Fin.castLE h b)).map (starRingEnd ℂ) *ᵥ y) =
      (Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ z := by
    funext m
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply]
    refine Fintype.sum_of_injective (M := ℂ) (Fin.castLE h) hinj _ _ ?_ ?_
    · intro c hc
      simp [hz0 c hc]
    · intro b
      simp [hzc b]
  have hnz : nsq z = nsq y := by
    unfold nsq
    exact (Fintype.sum_of_injective (M := ℝ) (Fin.castLE h) hinj _ _ (fun c hc => by simp [hz0 c hc])
      (fun b => by simp [hzc b])).symm
  have hconj : ∀ {q : ℕ} (w : Fin q → ℂ), nsq (fun m => conj (w m)) = nsq w := by
    intro q w
    unfold nsq
    simp
  have hmap : ∀ w : Fin X.p0 → ℂ, nsq ((Matrix.of (Z τ)).map (starRingEnd ℂ) *ᵥ w) =
      nsq (Matrix.of (Z τ) *ᵥ fun c => conj (w c)) := by
    intro w
    rw [← hconj (Matrix.of (Z τ) *ᵥ fun c => conj (w c))]
    congr 1
    funext m

    simp [Matrix.mulVec, dotProduct, map_sum]
  have hop0 : 0 ≤ Data.opN (Matrix.of (Z τ)) := by
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hop : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z := by
    unfold Data.zN
    exact le_ciSup (f := fun τ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ
  rw [hvec, hmap, ← hnz, ← hconj z]
  calc nsq (Matrix.of (Z τ) *ᵥ fun c => conj (z c))
      ≤ Data.opN (Matrix.of (Z τ)) ^ 2 * nsq (fun c => conj (z c)) := nsq_mulVec_le_opN _ _
    _ ≤ X.zN Z ^ 2 * nsq (fun c => conj (z c)) := by
      gcongr
      exact nsq_nonneg _

lemma det_lowBlock (Z : X.Coord) (τ : X.Ψ) : (X.lowBlock Z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro a _
    simp only [Data.lowBlock, Matrix.of_apply, if_true]
    rw [dite_eq_right (by omega)]
    simp
  · intro a b hab
    have hab' : a < b := hab
    simp only [Data.lowBlock, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab'), dite_eq_right]
    · simp
    · intro hh
      have : (a : ℕ) < b := hab'
      omega

lemma psgn_add (p0 k : ℕ) : psgn p0 (p0 + k) = (-1) ^ k := by
  induction k with
  | zero => simp [psgn_eq_one le_rfl]
  | succ k ih =>
    rw [← add_assoc, psgn_succ, ih, sgn, if_neg (by omega), pow_succ]

lemma signType_cancel_identity (k : ℕ) (D : ℂ) (hD : 0 < D.re) : 0 < (-1 : ℝ) ^ k * (((-1 : ℂ) ^ k) * D).re := by
  have h1 : ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, Complex.re_ofReal_mul, ← mul_assoc, ← mul_pow]
  norm_num
  exact hD

lemma pos_re_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) : 0 < M.det.re := by
  exact (Complex.pos_iff.mp hM.det_pos).1

lemma minor_le {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (i : Fin (r + 1)) (hip : (i : ℕ) ≤ X.p0) : 0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  rw [psgn_eq_one hip, one_mul]
  set A : Matrix (Fin (r - X.p0)) (Fin (i : ℕ)) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE hip b) with hA
  set B : Matrix (Fin 0) (Fin (i : ℕ)) ℂ := 0 with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X hip Z τ) hs0
  have heq : dmin X.Gm (X.xZ x Z) τ i = (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ]
    congr 1
    ext a b
    have hca : (Fin.castLE (Nat.le_of_lt_succ i.isLt) a : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip a) :=
      Fin.ext rfl
    have hcb : (Fin.castLE (Nat.le_of_lt_succ i.isLt) b : Fin r) = Fin.castLE X.p0_le (Fin.castLE hip b) :=
      Fin.ext rfl
    rw [Matrix.submatrix_apply, hca, hcb, Gp_pp]
    simp [hA, hB, Matrix.one_apply, Matrix.mul_apply, Fin.castLE_inj]
  rw [heq]
  exact pos_re_of_posDef hpd

lemma minor_gt {x : Frame X.Ψ r} (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) (τ : X.Ψ)
    (k : ℕ) (hk : k ≤ r - X.p0) (i : Fin (r + 1)) (hik : (i : ℕ) = X.p0 + k) :
    0 < psgn X.p0 i * (dmin X.Gm (X.xZ x Z) τ i).re := by
  classical
  obtain ⟨i, hi⟩ := i
  simp only at hik
  subst hik
  rw [show ((⟨X.p0 + k, hi⟩ : Fin (r + 1)) : ℕ) = X.p0 + k from rfl, psgn_add]
  set A : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
    Matrix.of fun m b => Z τ m (Fin.castLE (le_refl X.p0) b) with hA
  set B : Matrix (Fin k) (Fin X.p0) ℂ := Matrix.of fun m c => Z τ (Fin.castLE hk m) c with hB
  have hs0 : 0 ≤ X.zN Z := by
    unfold Data.zN
    apply Real.iSup_nonneg
    intro τ'
    unfold Data.opN
    apply Real.sSup_nonneg
    rintro t ⟨v, -, rfl⟩
    positivity
  have hpd := posDef_of_bound A B hZ (bound_castLE X (le_refl X.p0) Z τ) hs0
  haveI : Invertible (1 : Matrix (Fin k) (Fin k) ℂ) := invertibleOne
  haveI : Invertible (-1 : Matrix (Fin k) (Fin k) ℂ) := invertibleNeg 1
  have heq : dmin X.Gm (X.xZ x Z) τ ⟨X.p0 + k, hi⟩ =
      (-1 : ℂ) ^ k * (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [gram_xZ X ho Z τ, ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
    have hc1 : ∀ a : Fin X.p0, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inl a)) : Fin r) =
        Fin.castLE X.p0_le a := fun a => Fin.ext (by simp)
    have hc2 : ∀ m : Fin k, (Fin.castLE (Nat.le_of_lt_succ hi) (finSumFinEquiv (Sum.inr m)) : Fin r) =
        nI X (Fin.castLE hk m) := fun m => Fin.ext (by simp [nI])
    have hblk : ((Gp X Z τ).submatrix (Fin.castLE (Nat.le_of_lt_succ hi)) (Fin.castLE (Nat.le_of_lt_succ hi))).submatrix
        finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (1 - Aᵀ * A.map (starRingEnd ℂ)) (-Bᵀ) (-(B.map (starRingEnd ℂ))) (-1) := by
      ext (a | m) (b | m')
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, Gp_pp, Matrix.fromBlocks_apply₁₁]
        simp [hA, Matrix.one_apply, Matrix.mul_apply]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_pn, Matrix.fromBlocks_apply₁₂]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc1, hc2, Gp_np, Matrix.fromBlocks_apply₂₁]
        simp [hB]
      · simp only [Matrix.submatrix_apply, Function.comp_apply, hc2, Gp_nn, Matrix.fromBlocks_apply₂₂]
        simp [Matrix.one_apply, Fin.castLE_inj]
    rw [hblk, Matrix.det_fromBlocks₂₂, invOf_neg, invOf_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin,
      mul_one]
    congr 2
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg, sub_neg_eq_add]
  rw [heq]
  exact signType_cancel_identity k _ (pos_re_of_posDef hpd)

theorem xZ_mem_dom {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1) :
    X.xZ x Z ∈ X.dom := by
  rw [Data.mem_dom_iff] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * X.lowBlock Z τ).det ≠ 0
    rw [Matrix.det_mul, det_lowBlock, mul_one]
    exact (hx τ).1
  · by_cases hip : (i : ℕ) ≤ X.p0
    · exact minor_le X ho hZ τ i hip
    · have hi := i.isLt
      have := X.p0_le
      exact minor_gt X ho hZ τ ((i : ℕ) - X.p0) (by omega) i (by omega)

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace IntegralBasisReduction

open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma sum4_lemma {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  calc ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ a, ∑ i, ∑ b, ∑ j, f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ j, f a b i j := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ j, ∑ b, f a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm

private lemma hermC_mulVec_lemma_2 {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (Y : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    hermC τ G (Y *ᵥ u) (Y *ᵥ v) = ∑ i, ∑ j, u i * gram τ G Y i j * conj (v j) := by
  calc hermC τ G (Y *ᵥ u) (Y *ᵥ v)
      = ∑ a, ∑ b, ∑ i, ∑ j, Y a i * u i * τ (G a b) * (conj (Y b j) * conj (v j)) := by
        simp only [hermC, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_

        rw [map_sum, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
    _ = ∑ i, ∑ j, ∑ a, ∑ b, Y a i * u i * τ (G a b) * (conj (Y b j) * conj (v j)) := sum4_lemma _
    _ = ∑ i, ∑ j, u i * gram τ G Y i j * conj (v j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [gram, hermC, col, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring

theorem hermC_normal {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0) (s : Fin r → ℂ)
    (hg : gram τ X.Gm Y = diagonal s) (p q : Fin r → ℂ) :
    hermC τ X.Gm p q = ∑ a, s a * (Y⁻¹ *ᵥ p) a * conj ((Y⁻¹ *ᵥ q) a) := by
  have hu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
  have key := hermC_mulVec_lemma_2 τ X.Gm Y (Y⁻¹ *ᵥ p) (Y⁻¹ *ᵥ q)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec, Matrix.one_mulVec, hg] at key
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]; ring
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

def IsNormal (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : X.Ψ, (y τ).det ≠ 0 ∧ gram τ.1 X.Gm (y τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

theorem ip_Sg {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (p q : Fin r → E) :
    ip X (Ly X y (X.embV p)) (Sg X (Ly X y (X.embV q))) = ∑ τ, X.c τ * (τ.1 (herm X.Gm p q)).re := by
  simp only [ip, Sg, Ly, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨hdet, hg⟩ := hy τ
  have hτ : τ.1 (herm X.Gm p q) = hermC τ.1 X.Gm (X.embV p τ) (X.embV q τ) := by
    first
      | simp [herm, hermC, Data.embV, Data.emb, cc, map_sum, map_mul,
          IsCMField.complexEmbedding_complexConj]
      | simp [herm, hermC, Data.embV, Data.emb, cc, map_sum, map_mul,
          NumberField.IsCMField.complexEmbedding_complexConj]
  rw [hτ, hermC_normal X hdet _ hg]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def zbas {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    Basis ι ℝ (X.Ψ → Fin r → ℂ) :=
  (Basis.mk (RealPlaceEmbeddings.linIndR X g) (RealPlaceEmbeddings.span_embV X g).ge).map
    (LinearEquiv.ofBijective (Ly X y) ⟨Ly_injective X y fun τ => (hy τ).1,
      Ly_surjective X y fun τ => (hy τ).1⟩)

theorem zbas_apply {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ)
    (i : ι) : zbas X hy g i = Ly X y (X.embV (g i : Fin r → E)) := by
  simp only [zbas, Basis.map_apply, Basis.mk_apply]
  exact LinearEquiv.ofBijective_apply _ _

private lemma ip_sum_lemma_3 (u : X.Ψ → Fin r → ℂ) (a : ι → ℝ) (w : ι → X.Ψ → Fin r → ℂ) :
    ip X u (∑ k, a k • w k) = ∑ k, a k * ip X u (w k) := by
  have h1 : ∀ τ b, u τ b * conj ((∑ k, a k • w k) τ b) =
      ∑ k, ((a k : ℂ) * (u τ b * conj (w k τ b))) := by
    intro τ b

    rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  simp only [ip, h1, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
  calc ∑ τ, ∑ b, ∑ k, X.c τ * (a k * (u τ b * conj (w k τ b)).re)
      = ∑ τ, ∑ k, ∑ b, X.c τ * (a k * (u τ b * conj (w k τ b)).re) :=
        Finset.sum_congr rfl fun τ _ => Finset.sum_comm
    _ = ∑ k, ∑ τ, ∑ b, X.c τ * (a k * (u τ b * conj (w k τ b)).re) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

theorem Bm_eq {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    Bm X g = Am X y g * LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) := by
  ext i j
  rw [Matrix.mul_apply]
  have hS := (zbas X hy g).sum_repr (Sg X (zbas X hy g j))
  simp only [LinearMap.toMatrix_apply]
  rw [show Bm X g i j = ip X (zbas X hy g i) (Sg X (zbas X hy g j)) by
    simp only [Bm, Matrix.of_apply, zbas_apply]
    exact (ip_Sg X hy _ _).symm]
  conv_lhs => rw [← hS]
  rw [ip_sum_lemma_3]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Am, Matrix.of_apply, zbas_apply]
  ring

theorem det_Am_le {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    (Am X y g).det ≤ |(Bm X g).det| := by
  have hSS : Sg X * Sg X = 1 := by
    refine LinearMap.ext fun u => funext fun τ => funext fun a => ?_
    show ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * u τ a) = u τ a
    rw [← mul_assoc, ← Complex.ofReal_mul]
    unfold sgn
    split_ifs <;> simp
  have hM : LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) *
      LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) = 1 := by
    rw [← LinearMap.toMatrix_mul, hSS, LinearMap.toMatrix_one]
  have h2 : |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| *
      |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| = 1 := by
    rw [← abs_mul, ← Matrix.det_mul, hM, Matrix.det_one, abs_one]
  have hd : |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| = 1 := by
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · linarith [abs_nonneg (LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det]
  rw [Bm_eq X hy g, Matrix.det_mul, abs_mul, hd, mul_one]
  exact le_abs_self _

theorem reduce {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ v ∈ X.Λ, v ≠ 0 → m ≤ Qy X y v) :
    ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ,
      (∀ i, Qy X y (f i) ≤ 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
        |(Bm X (RealPlaceEmbeddings.zb X)).det| / m ^ (finrank ℤ X.Λ - 1)) ∧
      ∀ (v : X.Λ) (i : Fin (finrank ℤ X.Λ)),
        ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ 9 ^ (finrank ℤ X.Λ) * Qy X y v / m := by
  set g := RealPlaceEmbeddings.zb X with hgdef
  have hcoe : ∀ x : Fin (finrank ℤ X.Λ) → ℤ,
      ((∑ i, x i • g i : X.Λ) : Fin r → E) = ∑ i, x i • (g i : Fin r → E) := by
    intro x; simp
  have hint : ∀ x : Fin (finrank ℤ X.Λ) → ℤ, x ≠ 0 →
      m ≤ (fun i => (x i : ℝ)) ⬝ᵥ (Am X y g *ᵥ fun i => (x i : ℝ)) := by
    intro x hx
    rw [quad_int]
    refine hmin _ ?_ ?_
    · rw [← hcoe]; exact (∑ i, x i • g i : X.Λ).2
    · intro h0
      rw [← hcoe] at h0
      have h1 : (∑ i, x i • g i : X.Λ) = 0 := Subtype.ext h0
      exact hx (funext (Fintype.linearIndependent_iff.mp g.linearIndependent x h1))
  obtain ⟨eb, h1, h2⟩ := ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.redGram_holds (finrank ℤ X.Λ) (Am X y g) m
    |(Bm X g).det| (Am_posDef X y (fun τ => (hy τ).1) g) hm hint (det_Am_le X hy g)
  refine ⟨eb.map g.equivFun.symm, fun i => ?_, fun v i => ?_⟩
  · have h3 := h1 i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.equivFun_symm_apply] using h3
  · have h3 := h2 (g.equivFun v) i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.map_repr, Basis.equivFun_symm_apply, g.sum_repr] using h3

end IntegralBasisReduction

end ReciprocityTheory.ChartRestriction.G.FD
end
