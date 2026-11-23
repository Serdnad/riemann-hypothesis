module

public import Formalism.HermitianCurvature.Bundle007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle043
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle098
public import Formalism.HermitianCurvature.Bundle009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BorderedDeterminants
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BranchingSystems
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliAbstractCharacter
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ClosureOperators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarSumLemmas
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictBoxOrder
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightMonotonicity
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle099
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle102
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle095
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomUBL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddingMulVecFactorization
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GeometryEquivarianceEmbedding
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle101
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactZetaLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul

@[expose] public section

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

theorem integral_formula_passes_to_limits : Formalism.FourierDecayAlt.KB.LimitInt := by
  intro E _ _ _ Wp Wq _ _ _ _ S RR hg1 hg2 hU hconv hInt hB
  have hbd : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h',
      D.ptSize h = i - 1 → D.ptSize h' = i - 1 → ∃ M : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 →
        ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ M * ((1 + ‖c‖) ^ 3)⁻¹ := by
    intro v ε hε i hi1 hi2 a ha h h' hh hh'
    obtain ⟨M, hM⟩ := hB v ε hε i hi1 hi2 a ha h h' hh hh'
    exact ⟨M, fun n => (hM n).1⟩
  refine ⟨PBB.K8.intAll_limit S RR hg1 hg2 hconv hInt hB, ?_⟩
  intro X hX ε hε i hi1 hi2 w hw hcnt
  set B := S.base.Wb (S.base.cnt w + C.Kst) with hBdef
  have hθ : ∀ n, ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb B (θ A)) ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ l ∈ S.base.Lad i, l ≠ 0 → ∀ A : Finset (Fin S.f),
          (∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖(KB.withRR S (RR n)).Nhat ε i w.1 Y κ l‖ ≤
            (∏ v ∈ A, X i v ^ C.Kst) *
              ∑ w' ∈ B, θ A w' * (KB.withRR S (RR n)).base.N0 ε (i - 1) w' Y κ :=
    fun n => hX n ε hε i hi1 hi2 w hw hcnt
  choose θ hprob hineq using hθ

  let F : ℕ → (Finset (Fin S.f) → B → ℝ) := fun n A x => θ n A x.1
  have hFb : ∀ n, F n ∈ Metric.closedBall (0 : Finset (Fin S.f) → B → ℝ) 1 := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro A
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro x
    have h0 := (hprob n A).1 x.1
    show ‖θ n A x.1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    calc θ n A x.1 ≤ ∑ w' ∈ B, θ n A w' :=
          Finset.single_le_sum (fun w' _ => (hprob n A).1 w') x.2
      _ = 1 := (hprob n A).2.2
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hFb
  have hco : ∀ A (x : B), Filter.Tendsto (fun n => θ (φ n) A x.1) Filter.atTop (nhds (a A x)) := by
    intro A x
    exact ((continuous_apply x).comp (continuous_apply A)).tendsto a |>.comp hlim
  let θ' : Finset (Fin S.f) → S.W → ℝ := fun A w' => if h : w' ∈ B then a A ⟨w', h⟩ else 0
  have hθ' : ∀ A w' (h : w' ∈ B), θ' A w' = a A ⟨w', h⟩ := fun A w' h => dif_pos h
  refine ⟨θ', ?_, ?_⟩
  · intro A
    refine ⟨?_, ?_, ?_⟩
    · intro w'
      by_cases h : w' ∈ B
      · rw [hθ' A w' h]
        exact ge_of_tendsto' (hco A ⟨w', h⟩) fun n => (hprob (φ n) A).1 w'
      · show 0 ≤ (if h : w' ∈ B then a A ⟨w', h⟩ else 0)
        rw [dite_eq_right h]
    · intro w' h
      show (if h : w' ∈ B then a A ⟨w', h⟩ else 0) = 0
      rw [dite_eq_right h]
    · have e1 : ∑ w' ∈ B, θ' A w' = ∑ x : B, a A x := by
        rw [← Finset.sum_coe_sort B]
        exact Finset.sum_congr rfl fun x _ => hθ' A x.1 x.2
      have e2 : ∀ n, ∑ x : B, θ (φ n) A x.1 = 1 := fun n => by
        rw [Finset.sum_coe_sort B (θ (φ n) A)]
        exact (hprob (φ n) A).2.2
      rw [e1]
      refine tendsto_nhds_unique (tendsto_finsetSum _ fun x _ => hco A x) ?_
      simp_rw [e2]
      exact tendsto_const_nhds
  · intro Y hY κ hκ l hl hl0 A
    have hL : Filter.Tendsto (fun n => (∏ v ∈ A, S.base.av v l ^ C.Kst) *
        ‖(KB.withRR S (RR (φ n))).Nhat ε i w.1 Y κ l‖) Filter.atTop
        (nhds ((∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖S.Nhat ε i w.1 Y κ l‖)) :=
      (((PBB.tendsto_Nhat S RR hconv hInt hbd ε hε i hi1 hi2 w Y hY κ l).comp
        hφ.tendsto_atTop).norm).const_mul _
    have hR : Filter.Tendsto (fun n => (∏ v ∈ A, X i v ^ C.Kst) *
        ∑ w' ∈ B, θ (φ n) A w' * (KB.withRR S (RR (φ n))).base.N0 ε (i - 1) w' Y κ) Filter.atTop
        (nhds ((∏ v ∈ A, X i v ^ C.Kst) * ∑ w' ∈ B, θ' A w' * S.base.N0 ε (i - 1) w' Y κ)) := by
      refine Filter.Tendsto.const_mul _ (tendsto_finsetSum _ fun w' hw' => ?_)
      refine Filter.Tendsto.mul ?_ ((PBB.tendsto_base_norm_of_regularization S RR hconv ε hε (i - 1) (by omega) w' Y κ).comp
        hφ.tendsto_atTop)
      rw [hθ' A w' hw']
      exact hco A ⟨w', hw'⟩
    exact le_of_tendsto_of_tendsto' hL hR fun n => hineq (φ n) Y hY κ hκ l hl hl0 A

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem capelli_singular : Qr.CapSing := qr_capSing_of singular_dominant exists_singular_maximal_vector

theorem top_weight_singular : Qr.TopWeightSing := qr_topWeightSing_of exists_singular_maximal_vector capelli_singular

theorem vector_descent : Qr.VecDown := qr_vecDown_of quantum_minor_polynomial polynomial_vanishing

theorem raising_nonzero : Qr.RaiseNZ := qr_raiseNZ_of covariant_raising

theorem lowering_nonzero : Qr.LowerNZ := qr_lowerNZ_of vector_descent

theorem branching_decomposition : Qr.Decomp :=
  qr_decomp_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations covariant_raising vector_descent
    raising_nonzero lowering_nonzero

theorem multiplicity_one : Qr.MultOne := qr_multOne_of exists_singular_maximal_vector dual_minor span_singular_vectors

theorem irreducible_capelli_modules : Qr.IrredCap :=
  qr_irredCap_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations top_weight_singular
    dual_minor span_top_vectors multiplicity_one branching_decomposition capelli_independence

theorem branching_algebraic : Qr.BranchingAlg := qr_branchingAlg_of branching_decomposition capelli_independence irreducible_capelli_modules

end Formalism.FourierDecayAlt.P
end

section

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

def DecayData (n : ℕ) (C : ℝ) (D : ℂ → ℂ) : Prop :=
  Integrable D ∧ Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) ∧ (∀ t, t ≠ 0 → ContinuousAt D t) ∧
    (∀ s, ‖∫ t, fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))) ∧
    ∀ s, ‖∫ t, fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

section Gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Gen

end Formalism.FourierDecayAlt.P5.HerC
end
end

section

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG

section entries

theorem ptEntry_cons (s1 : ℕ) (t1 : ℂ) (rest : C.LPt) (a b : ℕ) :
    D.ptEntry ((s1, t1) :: rest) a b =
      if a < s1 ∧ b < s1 then (if a + b + 1 = s1 then t1 else 0)
      else if s1 ≤ a ∧ s1 ≤ b then D.ptEntry rest (a - s1) (b - s1) else 0 := rfl

theorem ptEntry_append (h : C.LPt) (s : ℕ) (t : ℂ) (a b : ℕ) :
    D.ptEntry (h ++ [(s, t)]) a b =
      if a < D.ptSize h ∧ b < D.ptSize h then D.ptEntry h a b
      else if D.ptSize h ≤ a ∧ D.ptSize h ≤ b then
        (if a - D.ptSize h < s ∧ b - D.ptSize h < s ∧ (a - D.ptSize h) + (b - D.ptSize h) + 1 = s then t else 0)
      else 0 := by
  induction h generalizing a b with
  | nil =>
    simp only [List.nil_append, D.ptSize, List.map_nil, List.sum_nil, Nat.sub_zero]
    rw [ptEntry_cons]
    simp only [D.ptEntry]
    split_ifs <;> first | rfl | omega
  | cons blk h ih =>
    obtain ⟨s1, t1⟩ := blk
    have hsz : D.ptSize ((s1, t1) :: h) = s1 + D.ptSize h := by simp [D.ptSize]
    rw [List.cons_append, hsz, ptEntry_cons, ih]
    split_ifs <;> first | rfl | omega | (rw [ptEntry_cons]; split_ifs <;> first | rfl | omega)

theorem ptMatN_zb (h : C.LPt) (s : ℕ) (t : ℂ) (n : ℕ) (hn : n = D.ptSize h + s) (a b : Fin n) :
    D.ptMatN (h ++ [(s, t)]) n a b = C3.Zb (D.ptSize h) s (D.ptMatN h (D.ptSize h)) t a.val b.val := by
  unfold D.ptMatN
  rw [ptEntry_append]
  unfold C3.Zb
  have ha := a.isLt
  have hb := b.isLt
  by_cases h1 : a.val < D.ptSize h
  · rw [dif_pos h1]
    by_cases h2 : b.val < D.ptSize h
    · rw [if_pos ⟨h1, h2⟩, dif_pos h2]
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => by omega), dif_neg h2]
  · rw [dif_neg h1, if_neg (fun h => h1 h.1)]
    by_cases h2 : D.ptSize h ≤ b.val
    · rw [if_pos ⟨by omega, h2⟩]
      by_cases h3 : a.val - D.ptSize h + (b.val - D.ptSize h) + 1 = s
      · rw [if_pos ⟨by omega, by omega, h3⟩, if_pos ⟨h2, by omega, by omega, h3⟩]
      · rw [if_neg (fun h => h3 h.2.2), if_neg (fun h => h3 h.2.2.2)]
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.1)]

end entries

section point

variable {k r : ℕ}

theorem corner_matrix_right_translate (z z' : Fin (2 * r + k + 1) → ℂ) (γ n0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hn0 : n0 ∈ C3.N0set k r z') : Zhat k r z z' (γ * n0) = Zhat k r z z' γ := by
  ext a b
  unfold Zhat
  rw [← Matrix.mulVec_mulVec]
  congr 2
  unfold fvec
  split_ifs with hb
  · exact hn0.2.1 ⟨b.val, hb⟩
  · exact hn0.2.2.1

theorem dmin_zb (z z' : Fin (2 * r + k + 1) → ℂ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ)
    (hZ : ∀ a b : Fin (r + 1), Zhat k r z z' x a b = C3.Zb i0 s hh t a.val b.val) (l : Fin (r + 2)) :
    Dmin k r z z' x l = C3.Dlead i0 s hh t l.val := by
  unfold Dmin C3.Dlead
  congr 1
  ext a b
  rw [Matrix.submatrix_apply, hZ]
  rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

theorem La_one (hD : IsOpen D) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D) : La hD K hK x₁ 1 = K x₁ := by
  show ((vK hD K hK : VS k r 0 D E) : Q.Mx k r → E) x₁ = K x₁
  exact cut_of_mem K hx₁

theorem top_poly (hD : IsOpen D) (z z' yb : Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (hs : 2 ≤ s) (hj : i0 + s = r + 1)
    (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hdet : hh.det ≠ 0) (ht : t ≠ 0) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D) (hz' : inWb k r z') (hyb : inWb k r yb) (hzy : herm (Hpk k r) z' yb = t)
    (hnf1 : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val ≠ i0 →
      xi0 x₁ a p = if p.val < r ∧ p.val ≠ i0 then C3.Zb i0 s hh t a.val p.val else 0)
    (hnf2 : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val = i0 → xi0 x₁ a p = herm (Hpk k r) (bvec p) yb)
    (hZ : ∀ a b : Fin (r + 1), Zhat k r z z' x₁ a b = C3.Zb i0 s hh t a.val b.val)
    (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g) :
    ∃ c : Fin (i0 + 1) → E, c (Fin.last i0) = ((-1) ^ (s - 1) / t) • K x₁ ∧
      ∀ y : ℝ, (Dmin k r z z' x₁ (Fin.last _))⁻¹ •
          C3.AAop k r r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) K x₁ =
        ∑ n : Fin (i0 + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  have hi0 : i0 ≤ r := by omega
  have hDl : ∀ l : Fin (r + 2), Dmin k r z z' x₁ l = C3.Dlead i0 s hh t l.val := dmin_zb z z' x₁ i0 s hh t hZ
  have hDi0 : C3.Dlead i0 s hh t i0 = hh.det := (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh t).1
  obtain ⟨B, hB⟩ := Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_identity (Module.End ℂ (VS k r 0 D E)) k r (E0 hD) (xi0 x₁) i0 hi0
  have hdetxi : (Matrix.of fun a b : Fin i0 => xi0 x₁ (Fin.castLE hi0 a) (C3.xR k r i0 hi0 b)).det = hh.det := by
    rw [det_upper_minor_eq_minor z z' x₁ i0 hi0, hDl, ← hDi0]

  have hpoly : PolyRepN i0 (fun u => (Dmin k r z z' x₁ (Fin.last _))⁻¹ • C3.AAop k r r le_rfl u K x₁)
      (((-1 : ℂ) ^ (s - 1) * t⁻¹) • K x₁) := by
    refine ⟨fun l => if hl : l < i0 then ((-1 : ℂ) ^ (s - 1) * t⁻¹) • ((hh.det)⁻¹ • La hD K hK x₁ (B ⟨l, hl⟩))
      else ((-1 : ℂ) ^ (s - 1) * t⁻¹) • K x₁, by simp, fun u => ?_⟩
    have hE := Formalism.FourierDecayAlt.P.SignAntidiagonal.column_indicator_expansion (Module.End ℂ (VS k r 0 D E)) E k r z' yb (E0 hD) (La hD K hK x₁)
      (xi0 x₁) i0 s hh t u hs hj (La_rule hD z' K hK hR x₁) hdet ht hz' hyb hzy hnf1 hnf2
    rw [La_AAx hD K hK x₁ hx₁] at hE
    have hlast : Dmin k r z z' x₁ (Fin.last (r + 1)) = C3.Dlead i0 s hh t (r + 1) := by rw [hDl]; rfl
    simp only
    rw [hlast, hE, hDi0, hB u]

    simp only [map_add (f := _), map_sum, Finset.sum_range_succ, dif_neg (lt_irrefl i0)]
    have hm : ∀ (c : ℂ) (X : Module.End ℂ (VS k r 0 D E)),
        La hD K hK x₁ (algebraMap ℂ (Module.End ℂ (VS k r 0 D E)) c * X) = c • La hD K hK x₁ X := by
      intro c X
      rw [← Algebra.smul_def, map_smul]
    have ha : ∀ c : ℂ, La hD K hK x₁ (algebraMap ℂ (Module.End ℂ (VS k r 0 D E)) c) = c • K x₁ := by
      intro c
      rw [← mul_one (algebraMap ℂ _ c), hm, La_one hD K hK x₁ hx₁]
    rw [ha, Finset.sum_range (fun l => u ^ l • if hl : l < i0 then ((-1 : ℂ) ^ (s - 1) * t⁻¹) •
      ((hh.det)⁻¹ • La hD K hK x₁ (B ⟨l, hl⟩)) else ((-1 : ℂ) ^ (s - 1) * t⁻¹) • K x₁)]
    simp only [hm, dif_pos (Fin.isLt _), Fin.eta]
    rw [smul_add, smul_add, Finset.smul_sum, Finset.smul_sum, add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro l _
      rw [smul_comm ((hh.det)⁻¹) (u ^ (l : ℕ)), smul_comm ((-1 : ℂ) ^ (s - 1) * t⁻¹) (u ^ (l : ℕ))]
    · simp only [smul_smul]
      rw [hdetxi]
      congr 1
      field_simp
  obtain ⟨c, hc, hf⟩ := polyRepN_shift hpoly (((2 * r + k : ℕ) : ℂ) / 2)
  refine ⟨fun n => c n.val, ?_, fun y => ?_⟩
  · simp only [Fin.val_last]
    rw [hc, div_eq_mul_inv]
  · have := hf (y : ℂ)
    simp only at this
    rw [this, Fin.sum_univ_eq_sum_range (fun l => ((y : ℂ) ^ l) • c l)]

end point

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

section

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.RE

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

section gen

variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def inE : α × (β × γ) ≃ᵐ β × (α × γ) :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ)).trans MeasurableEquiv.prodAssoc)

theorem inE_mp (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving (inE : α × (β × γ) ≃ᵐ β × (α × γ)) (μa.prod (μb.prod μc)) (μb.prod (μa.prod μc)) := by
  have e1 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μb μc)
  have e2 := (Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod (MeasurePreserving.id μc)
  have e3 := measurePreserving_prodAssoc μb μa μc
  exact e3.comp (e2.comp e1)

end gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def rearr (k r : ℕ) (w : Equiv.Perm (Fin (r + 1))) :
    OD.RR k r w ≃ᵐ ((C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ)) × B.SS k r :=
  (MeasurableEquiv.prodCongr inE inE).trans Dx2.SL.swap4

@[simp] theorem rearr_apply (w : Equiv.Perm (Fin (r + 1))) (q : OD.RR k r w) :
    rearr k r w q = ((q.1.2.1, q.2.2.1), ((q.1.1, q.1.2.2), (q.2.1, q.2.2.2))) := rfl

private theorem measurePreserving_swap4 {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ) [SFinite μa]
    [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (Dx2.SL.swap4 : (α × β) × γ × δ ≃ᵐ (α × γ) × β × δ) ((μa.prod μb).prod (μc.prod μd))
      ((μa.prod μc).prod (μb.prod μd)) := by
  have e1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have e2 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μb μc μd)
  have e3 := (Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd)
  have e4 := measurePreserving_prodAssoc μc μb μd
  have e5 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μc (μb.prod μd))
  have h := (e5.comp ((MeasurePreserving.id μa).prod (e4.comp (e3.comp e2)))).comp e1
  convert h using 1
  funext p
  rfl

theorem mp_rearr (S : B.RealPlaceData k r Wp Wq) (w : Equiv.Perm (Fin (r + 1))) {μ0 μ0' : Measure (Mt k r)}
    (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0) (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') :
    MeasurePreserving (rearr k r w) (OD.nuR S w μ0 μ0')
      (((volume : Measure (C2.LPidx w → ℂ)).prod (volume : Measure (G.UT (r + 1) → ℂ))).prod
        ((S.μW.prod μ0).prod (S.μW'.prod μ0'))) := by
  haveI : IsFiniteMeasureOnCompacts S.μW := ⟨fun K hK => S.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts S.μW' := ⟨fun K hK => S.haarW'.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0 := ⟨fun K hK => hμ0.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0' := ⟨fun K hK => hμ0'.finite_compact K hK⟩
  haveI t1 : SFinite S.μW := inferInstance
  haveI t2 : SFinite μ0 := inferInstance
  haveI t5 : SFinite S.μW' := inferInstance
  haveI t6 : SFinite μ0' := inferInstance
  haveI t3 : SFinite (volume : Measure (C2.LPidx w → ℂ)) := inferInstance
  haveI t4 : SFinite (volume : Measure (G.UT (r + 1) → ℂ)) := inferInstance
  have h1 := (inE_mp S.μW (volume : Measure (C2.LPidx w → ℂ)) μ0).prod
    (inE_mp S.μW' (volume : Measure (G.UT (r + 1) → ℂ)) μ0')
  have h2 := measurePreserving_swap4 (volume : Measure (C2.LPidx w → ℂ)) (S.μW.prod μ0)
    (volume : Measure (G.UT (r + 1) → ℂ)) (S.μW'.prod μ0')
  exact h2.comp h1

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.RE
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

def PolyRadialS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ (n : ℕ) (q : Polynomial ℂ), ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def ThConstOfCutS : Prop := PolyRadialS → ModConst → LineNonzero → PolyFinish → ThConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem second_shift_geometry_holds : SSn.SSnGeom :=
  SSn.Geom.geometry_assembly_holds SSn.Geom.geometry_smoothness_holds SSn.Geom.geometry_equivariance_first_vector SSn.Geom.geometry_equivariance_embedding
    SSn.Geom.geometry_at_level_function SSn.Geom.geometry_boundedness_at_zero SSn.Geom.geometry_unipotent_bound_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end
