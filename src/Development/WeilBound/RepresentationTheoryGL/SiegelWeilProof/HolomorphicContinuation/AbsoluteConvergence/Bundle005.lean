module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem first_cayley_block_one (n : ℕ) : u1 (1 : M2 n) = 1 := by
  have h21 : toBlocks₂₁ (1 : M2 n) = 0 := by
    ext i j
    simp [toBlocks₂₁, Matrix.one_apply]
  have h22 : toBlocks₂₂ (1 : M2 n) = 1 := by
    ext i j
    simp [toBlocks₂₂, Matrix.one_apply]
  simp [u1, h21, h22]

theorem second_cayley_block_one (n : ℕ) : u2 (1 : M2 n) = 1 := by
  have h21 : toBlocks₂₁ (1 : M2 n) = 0 := by
    ext i j
    simp [toBlocks₂₁, Matrix.one_apply]
  have h22 : toBlocks₂₂ (1 : M2 n) = 1 := by
    ext i j
    simp [toBlocks₂₂, Matrix.one_apply]
  simp [u2, h21, h22]

theorem weight_factor_one (n p q : ℕ) (e : ℤ) : F0 p q e (1 : GR n) = 1 := by
  show det (1 : M2 n) ^ e * f0 p q (1 : M2 n) = 1
  simp [f0, first_cayley_block_one, second_cayley_block_one]

theorem spherical_character_inv_mul (hM : Mult) (n p q : ℕ) (e : ℤ) (k : GR n) (hk : k ∈ KR n) :
    F0 p q e k⁻¹ * F0 p q e k = 1 := by
  rw [← ((hM n p q e).1 k⁻¹ k hk).1, inv_mul_cancel, weight_factor_one]

theorem sph (hI : Iwa) (hM : Mult) : Sph := by
  intro n p q e _ _ μ _ _ y z
  obtain ⟨b, k0, hb, hk0, rfl⟩ := hI n y
  have hmul := (hM n p q e).1
  have hup := (hM n p q e).2
  have step1 : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e (b * k0 * (k : GR n) * z)
      = F0 p q e b * ((F0 p q e (k : GR n))⁻¹ * F0 p q e (k0 * (k : GR n) * z)) := by
    intro k
    rw [show b * k0 * (k : GR n) * z = b * (k0 * (k : GR n) * z) by simp only [mul_assoc],
      (hup b _ hb).1]
    ring
  simp_rw [step1]
  rw [integral_const_mul, (hmul b k0 hk0).1, mul_assoc]
  congr 1
  let k0' : KR n := ⟨k0, hk0⟩
  let f : KR n → ℂ := fun k' => (F0 p q e (k0⁻¹ * (k' : GR n)))⁻¹ * F0 p q e ((k' : GR n) * z)
  have h1 : ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e (k0 * (k : GR n) * z) ∂μ
      = ∫ k : KR n, f (k0' * k) ∂μ := by
    congr 1
    ext k
    show _ = (F0 p q e (k0⁻¹ * (k0 * (k : GR n))))⁻¹ * F0 p q e (k0 * (k : GR n) * z)
    rw [inv_mul_cancel_left]
  rw [h1, integral_mul_left_eq_self f k0']
  have h2 : ∀ k' : KR n, f k' = F0 p q e k0 * ((F0 p q e (k' : GR n))⁻¹ * F0 p q e ((k' : GR n) * z)) := by
    intro k'
    simp only [f]
    rw [(hmul k0⁻¹ k' k'.2).1, mul_inv,
      inv_eq_of_mul_eq_one_right (spherical_character_inv_mul hM n p q e k0 hk0)]
    ring
  simp_rw [h2]
  rw [integral_const_mul]

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.BasisPf

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem continuous_mR : Continuous (fun g : GR n => mR g) := by
  unfold mR; fun_prop

theorem det_mR_ne (g : GR n) : (mR g).det ≠ 0 :=
  IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 g.1.isUnit)

theorem continuous_group_lower_left_block : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
  have : (fun M : M2 n => M.toBlocks₂₁) = fun M => M.submatrix Sum.inr Sum.inl := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_group_lower_right_block : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
  have : (fun M : M2 n => M.toBlocks₂₂) = fun M => M.submatrix Sum.inr Sum.inr := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_first_cayley_block_map : Continuous (fun M : M2 n => u1 M) := by
  unfold u1
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_group_lower_left_block).add continuous_group_lower_right_block

theorem continuous_second_cayley_block_map : Continuous (fun M : M2 n => u2 M) := by
  unfold u2
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_group_lower_left_block).neg.add continuous_group_lower_right_block

theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  unfold F0 f0
  refine Continuous.mul ((continuous_mR.matrix_det).zpow₀ e fun g => Or.inl (det_mR_ne g)) (Continuous.mul ?_ ?_)
  · exact ((continuous_first_cayley_block_map.comp continuous_mR).matrix_det).zpow₀ _ fun g => Or.inl (hD n g).1
  · exact ((continuous_second_cayley_block_map.comp continuous_mR).matrix_det).zpow₀ _ fun g => Or.inl (hD n g).2

theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  have : (u1 (mR g)).det ≠ 0 := (hD n g).1
  positivity

theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  unfold hLoc
  refine Continuous.inv₀ ?_ fun g => ?_
  · exact (((continuous_first_cayley_block_map.comp continuous_mR).matrix_det).norm).pow 2
  · have : (u1 (mR g)).det ≠ 0 := (hD n g).1
    positivity

theorem hLoc_one : hLoc (1 : GR n) = 1 := by
  have h1 : u1 (1 : M2 n) = 1 := by
    ext i j
    simp [u1, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]
  simp [hLoc, mR_one, h1]

theorem hLoc_K (hM : Mult) (k : GR n) (hk : k ∈ KR n) : hLoc k = 1 := by
  have := ((hM n 0 0 0).1 1 k hk).2
  rw [one_mul, hLoc_one] at this
  exact this

def uSet (n : ℕ) : Set (M2 n) := {u | uᴴ * u = 1 ∧ InG u}

theorem isCompact_uSet (n : ℕ) : IsCompact (uSet n) := by
  have hbox : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hbox.of_isClosed_subset ?_ ?_
  · change IsClosed ({u : M2 n | uᴴ * u = 1} ∩ {u : M2 n | InG u})
    refine IsClosed.inter ?_ ?_
    · exact isClosed_eq ((continuous_id : Continuous (fun u : M2 n => u)).matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    · exact isClosed_eq (((continuous_id : Continuous (fun u : M2 n => u)).matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
  · intro u hu
    have hU : u ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hu.1
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary hU i j

def toK (u : uSet n) : KR n :=
  ⟨⟨⟨u.1, u.1ᴴ, mul_eq_one_comm.1 u.2.1, u.2.1⟩, u.2.2⟩, ⟨u.2.2, u.2.1⟩⟩

theorem continuous_toK : Continuous (toK (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

instance compactKR (n : ℕ) : CompactSpace (KR n) := by
  have : CompactSpace (uSet n) := isCompact_iff_compactSpace.1 (isCompact_uSet n)
  refine ⟨?_⟩
  have : (univ : Set (KR n)) = toK '' univ := by
    ext k
    simp only [mem_univ, mem_image, true_and, true_iff]
    refine ⟨⟨mR (k : GR n), ⟨k.2.2, k.2.1⟩⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext; rfl
  rw [this]
  exact isCompact_univ.image continuous_toK

theorem exists_pts {X : Type*} : ∀ (N : ℕ) (f : Fin N → X → ℂ), LinearIndependent ℂ f →
    ∃ x : Fin N → X, (Matrix.of fun j l => f j (x l)).det ≠ 0 := by
  intro N
  induction N with
  | zero => intro f _; exact ⟨Fin.elim0, by simp⟩
  | succ N ih =>
    intro f hf
    obtain ⟨x', hx'⟩ := ih (fun j => f (Fin.castSucc j)) (hf.comp _ (Fin.castSucc_injective N))
    let c : Fin (N + 1) → ℂ := fun i => (-1) ^ ((i : ℕ) + N) * (Matrix.of fun a b => f (i.succAbove a) (x' b)).det
    have hdet : ∀ y : X, (Matrix.of fun j l => f j (Fin.lastCases (motive := fun _ => X) y x' l)).det =
        ∑ i, c i * f i y := by
      intro y
      rw [Matrix.det_succ_column _ (Fin.last N)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hs : (Matrix.of fun j l => f j (Fin.lastCases (motive := fun _ => X) y x' l)).submatrix i.succAbove
          (Fin.last N).succAbove = Matrix.of fun a b => f (i.succAbove a) (x' b) := by
        ext a b
        simp [Fin.succAbove_last]
      rw [hs]
      simp only [c, Matrix.of_apply, Fin.lastCases_last, Fin.val_last]
      ring
    by_contra hcon
    push Not at hcon
    have key : ∑ i, c i • f i = 0 := by
      funext y
      have h := hcon (Fin.lastCases (motive := fun _ => X) y x')
      rw [hdet y] at h
      simpa [Finset.sum_apply] using h
    have h0 := Fintype.linearIndependent_iff.1 hf c key (Fin.last N)
    have hc : c (Fin.last N) ≠ 0 := by
      simp only [c, Fin.val_last, Fin.succAbove_last]
      refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
      simpa using hx'
    exact hc h0

end PositivityTheory.Rg.Sw.AbsSt.BasisPf
end
end

section

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem inK_entry_le (M : M2 n) (hM : InK M) (i j : Fin n ⊕ Fin n) : ‖M i j‖ ≤ 1 := by
  exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hM.2) i j

theorem isCompact_inK : IsCompact {M : M2 n | InK M} := by
  have hB : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset ?_ ?_
  · have c1 : Continuous fun M : M2 n => Mᴴ * JJ n * M :=
      (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
    have c2 : Continuous fun M : M2 n => Mᴴ * M := continuous_id.matrix_conjTranspose.matrix_mul continuous_id
    exact (isClosed_eq c1 continuous_const).inter (isClosed_eq c2 continuous_const)
  · intro M hM
    simp only [Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact inK_entry_le M hM i j

def embK (k : KR n) : M2 n × (M2 n)ᵐᵒᵖ := Units.embedProduct (M2 n) (k : GR n).1

theorem isEmbedding_embK : Topology.IsEmbedding (embK (n := n)) :=
  Units.isEmbedding_embedProduct.comp (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)

theorem range_embK : Set.range (embK (n := n)) = (fun M : M2 n => (M, MulOpposite.op Mᴴ)) '' {M | InK M} := by
  ext ⟨A, B⟩
  constructor
  · rintro ⟨k, hk⟩
    have hK : InK (mR (k : GR n)) := k.2
    have hinv : ((((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) =
        (mR (k : GR n))ᴴ :=
      Units.inv_eq_of_mul_eq_one_left hK.2
    refine ⟨mR (k : GR n), hK, ?_⟩
    rw [← hk]
    simp only [embK, Units.embedProduct_apply, hinv]
    rfl
  · rintro ⟨M, hM, hMAB⟩
    have hM' : M * Mᴴ = 1 := mul_eq_one_comm.1 hM.2
    let u : GL (Fin n ⊕ Fin n) ℂ := ⟨M, Mᴴ, hM', hM.2⟩
    let g : GR n := ⟨u, hM.1⟩
    have hg : g ∈ KR n := hM
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [← hMAB]
    rfl

theorem isCompact_KR : IsCompact (univ : Set (KR n)) := by
  rw [isEmbedding_embK.isCompact_iff, Set.image_univ, range_embK]
  exact isCompact_inK.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_conjTranspose))

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem ext_mR {g h : GR n} (e : mR g = mR h) : g = h := Subtype.ext (Units.ext e)

def dg (X : Fin n → ℝ) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((Real.exp (s * X j) : ℝ) : ℂ)

theorem dg_mul (X : Fin n → ℝ) (s s' : ℝ) : dg X s * dg X s' = dg X (s + s') := by
  rw [dg, dg, dg, diagonal_mul_diagonal]
  congr 1
  funext j
  rw [← Complex.ofReal_mul, ← Real.exp_add, add_mul]

theorem dg_zero (X : Fin n → ℝ) : dg X 0 = 1 := by
  simp [dg]

theorem isDil_iff {X : Fin n → ℝ} {s : ℝ} {g : GR n} (h : IsDil X s g) :
    mR g = fromBlocks (dg X s) 0 0 (dg X (-s)) := by
  rw [h]
  simp only [dg, neg_mul]

theorem dil_mul {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s s' : ℝ) :
    a (s + s') = a s * a s' := by
  apply ext_mR
  rw [mR_mul, isDil_iff (ha _), isDil_iff (ha _), isDil_iff (ha _), fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, dg_mul, neg_add]

theorem dil_zero {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) : a 0 = 1 := by
  apply ext_mR
  rw [isDil_iff (ha _), mR_one, neg_zero, dg_zero, fromBlocks_one]

theorem dil_up {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s : ℝ) : IsUp (a s) := by
  show toBlocks₂₁ (mR (a s)) = 0
  rw [isDil_iff (ha s), toBlocks_fromBlocks₂₁]

theorem dil_inv {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s : ℝ) : (a s)⁻¹ = a (-s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← dil_mul ha, add_neg_cancel, dil_zero ha]

theorem up_mul {y g : GR n} (hy : IsUp y) (hg : IsUp g) : IsUp (y * g) := by
  show toBlocks₂₁ (mR (y * g)) = 0
  have hy' : toBlocks₂₁ (mR y) = 0 := hy
  have hg' : toBlocks₂₁ (mR g) = 0 := hg
  rw [mR_mul, ← fromBlocks_toBlocks (mR y), ← fromBlocks_toBlocks (mR g), hy', hg',
    fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

theorem cont_dil {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) : Continuous a := by
  have hc : Continuous fun s : ℝ => fromBlocks (dg X s) 0 0 (dg X (-s)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        dg, diagonal_apply, Matrix.zero_apply] <;> (try split_ifs) <;> fun_prop
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨hc.congr fun s => (isDil_iff (ha s)).symm, ?_⟩
  refine (hc.comp continuous_neg).congr fun s => ?_
  simp only [Function.comp_apply]
  rw [← isDil_iff (ha (-s)), ← dil_inv ha s]
  rfl

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add]
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def DN (ε : Fin m → Bool) (t : ℝ) (h : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  C (Complex.I * t) * (∑ i, ∑ j, C (h i j) * Qp ε j i) * R

def eulH (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  ∑ a : Fin m, ∑ j : Fin n, ((∑ i, X (a, i, false) * C (H i j)) * pderiv (a, j, false) R +
    (∑ i, X (a, i, true) * C (star (H i j))) * pderiv (a, j, true) R)

def DM (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  C ((m : ℂ) * H.trace) * R + eulH H R -
    C (2 * (c : ℂ)) * (∑ i, ∑ j, C (H i j) * (Qb ε true j i + Qb ε false j i)) * R

def SecDer : Prop := ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
  (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ (R : PX m n),
    R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) → ∀ (y : GR n)
    (H : Matrix (Fin n) (Fin n) ℂ), H.IsHermitian →
    (∃ f : ℝ → GR n, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s - sL (DN ε t H R) ((k : GR n) * y)‖ ≤ δ) ∧
    (∃ f : ℝ → GR n, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s - sL (DM ε c H R) ((k : GR n) * y)‖ ≤ δ)

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def hz {m n : ℕ} {G : Type} (Ht : G → ℝ≥0) (sec : PX m n →ₗ[ℂ] (G → ℂ)) (s₀ z : ℂ) (Q : PX m n) (x : G) : ℂ :=
  ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec Q x

def FarRight : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)) (Λ : Set ((G → ℂ) → ℂ)), GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ →
      ∃ σ : ℝ, (∀ Q g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z Q) g) (GlobalTheory.Cont.rightOf σ)) ∧
        (∀ Q g (z : ℂ), σ < z.re → Summable fun q => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q) ∧
        ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (ν : Measure (KR n)) (κ : KR n → ℂ) (N : ℕ) (yy : Fin N → GR n)
          (QQ : Fin N → PX m n) (M : ℂ → Matrix (Fin N) (Fin N) ℂ), IsFiniteMeasure ν → Continuous κ →
          (∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
              F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y') →
          ∀ (z : ℂ), σ < z.re → ∀ (g : G) (i : Fin N),
            ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
              ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g

end PositivityTheory.Rg.Sw.AbsSt
end
end
