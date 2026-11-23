module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockCycleExpand.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ a b : ℕ, twoBlockVert x (matAct B x) c l (fun _ : Fin D => ![(a : ℤ), (b : ℤ)]) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * (a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockPieceCycle.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a b : ℕ, a₀ ≤ a → a₀ ≤ b →
      |twoBlockStep x (matAct B x) a b -
          twoBlockVert x (matAct B x) c l (fun _ : Fin D => ![(a : ℤ), (b : ℤ)]) / (D.factorial : ℝ)| ≤
        C * ((a + b : ℝ) + 1) ^ D / ((a + b : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PullGradedAlgebraic

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

def blockDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ := ∑ i, m ⟨k, i⟩

theorem blockDeg_add (m m' : (Σ k, ι k) →₀ ℕ) (k : K) :
    blockDeg (m + m') k = blockDeg m k + blockDeg m' k := by
  simp [blockDeg, Finset.sum_add_distrib]

theorem blockDeg_sum {α : Type} (s : Finset α) (f : α → (Σ k, ι k) →₀ ℕ) (k : K) :
    blockDeg (∑ a ∈ s, f a) k = ∑ a ∈ s, blockDeg (f a) k := by
  simp only [blockDeg, Finsupp.finsetSum_apply]
  exact Finset.sum_comm

theorem blockDeg_single [DecidableEq K] (s : Σ k, ι k) (a : ℕ) (k' : K) :
    blockDeg (Finsupp.single s a) k' = if k' = s.1 then a else 0 := by
  classical
  obtain ⟨k0, i0⟩ := s
  simp only [blockDeg]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i0]
    · simp
    · intro i _ hi
      rw [Finsupp.single_apply, if_neg]
      intro h'
      exact hi (eq_of_heq (Sigma.mk.inj_iff.mp h').2).symm
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h'
    exact h (congrArg Sigma.fst h').symm

theorem isMultiHomog_monomial {m : (Σ k, ι k) →₀ ℕ} {b : K → ℕ} (h : ∀ k, blockDeg m k = b k) :
    IsMultiHomog (monomial m (1 : ℚ)) b := by
  intro m' hm' k
  rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm'
  subst hm'
  exact h k

theorem le_of_blockDeg {m : (Σ k, ι k) →₀ ℕ} {b : K → ℕ} (h : ∀ k, blockDeg m k = b k)
    (v : Σ k, ι k) : m v ≤ b v.1 := by
  rw [← h v.1, blockDeg]
  exact Finset.single_le_sum (f := fun i => m ⟨v.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)

def diagMono [Fintype K] (c : ∀ k, ι k) (b : K → ℕ) : (Σ k, ι k) →₀ ℕ := ∑ k, Finsupp.single ⟨k, c k⟩ (b k)

theorem blockDeg_diagMono [Fintype K] (c : ∀ k, ι k) (b : K → ℕ) (k : K) : blockDeg (diagMono c b) k = b k := by
  classical
  rw [diagMono, blockDeg_sum, Finset.sum_eq_single k]
  · rw [blockDeg_single, if_pos rfl]
  · intro k' _ hk'
    rw [blockDeg_single, if_neg (Ne.symm hk')]
  · simp

omit [∀ k, Fintype (ι k)] in
theorem aeval_diagMono_ne_zero [Fintype K] {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℕ) : aeval y (monomial (diagMono c b) (1 : ℚ)) ≠ 0 := by
  classical
  rw [diagMono, monomial_sum_one, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => by
    rw [← X_pow_eq_monomial, map_pow, aeval_X]
    exact pow_ne_zero _ (hc k)

end PullGradedAlgebraic


open PullGradedAlgebraic in
theorem PullGradedAlgebraic.proof : PullGradedAlgebraic.Statement := by
  intro K _ ι _ Ω _ _ y D e L d₀ hy he hL hgr p q hpq
  classical
  choose c hc using hy
  obtain ⟨j₀, hw⟩ : ∃ j₀, aeval y (L j₀) ≠ 0 := by
    obtain ⟨a, -, ha⟩ := hgr d₀ (monomial (diagMono c d₀) 1)
      (isMultiHomog_monomial (blockDeg_diagMono c d₀)) (fun _ => le_rfl)
    by_contra h
    simp only [not_exists, not_not] at h
    rw [Finset.sum_eq_zero (fun j _ => by rw [h j, mul_zero])] at ha
    exact aeval_diagMono_ne_zero y c hc d₀ ha
  set F := pullField y L
  set w := aeval y (L j₀)
  set n₀ := ∑ k, d₀ k
  set T : Set Ω := {x | ∃ n ≤ n₀, ∃ m : (Σ k, ι k) →₀ ℕ, (∀ k, blockDeg m k = n * e k) ∧
    x = aeval y (monomial m (1 : ℚ)) / w ^ n} with hT
  set W : Submodule F Ω := Submodule.span F T with hW
  have hratio : ∀ j, aeval y (L j) / w ∈ F := fun j =>
    IntermediateField.subset_adjoin _ _ ⟨j, j₀, hw, rfl⟩
  have claim : ∀ n (g : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog g (fun k => n * e k) →
      aeval y g / w ^ n ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro g hg
    by_cases hn : n ≤ n₀
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [g.as_sum, map_sum, Finset.sum_div]
      refine Submodule.sum_mem _ fun m hm => ?_
      have hmono : monomial m (AddMonoidAlgebra.coeff g m) = AddMonoidAlgebra.coeff g m • monomial m (1 : ℚ) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [hmono, map_smul, smul_div_assoc]
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨n, hn, m, fun k => hg m hm k, rfl⟩)
    · replace hn := Nat.lt_of_not_le hn
      obtain ⟨a, ha, hga⟩ := hgr (fun k => n * e k) g hg (fun k => by
        have h1 : d₀ k ≤ n₀ := Finset.single_le_sum (f := d₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        have h2 := Nat.mul_le_mul_left n (he k)
        omega)
      have hdeg : (fun k => n * e k) - e = fun k => (n - 1) * e k := by
        funext k
        show n * e k - e k = (n - 1) * e k
        rw [Nat.sub_one_mul]
      rw [hga, Finset.sum_div]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h1 := ih (n - 1) (by omega) (a j) (by rw [← hdeg]; exact ha j)
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hj : aeval y (a j) * aeval y (L j) / w ^ (n' + 1) =
          (⟨aeval y (L j) / w, hratio j⟩ : F) • (aeval y (a j) / w ^ (n' + 1 - 1)) := by
        rw [Algebra.smul_def, IntermediateField.algebraMap_apply, Nat.add_sub_cancel]
        field_simp
        ring
      rw [hj]
      exact W.smul_mem _ h1
  have hTfin : T.Finite := by
    let B : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun v => n₀ * e v.1)
    refine (((Set.finite_Iic n₀).prod (Set.finite_Iic B)).image
      (fun nm : ℕ × ((Σ k, ι k) →₀ ℕ) => aeval y (monomial nm.2 (1 : ℚ)) / w ^ nm.1)).subset ?_
    rintro x ⟨n, hn, m, hm, rfl⟩
    refine ⟨(n, m), ⟨hn, fun v => ?_⟩, rfl⟩
    show m v ≤ n₀ * e v.1
    exact (le_of_blockDeg hm v).trans (Nat.mul_le_mul_right _ hn)
  have hWfg : W.FG := ⟨hTfin.toFinset, by rw [Set.Finite.coe_toFinset]⟩
  have hW0 : W ≠ ⊥ := by
    intro h
    have h1 : (1 : Ω) ∈ W := Submodule.subset_span ⟨0, Nat.zero_le _, 0, fun k => by simp [blockDeg], by simp⟩
    rw [h, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  have hint : ∀ n (m : (Σ k, ι k) →₀ ℕ), (∀ k, blockDeg m k = n * e k) →
      IsIntegral F (aeval y (monomial m (1 : ℚ)) / w ^ n) := by
    intro n m hm
    refine isIntegral_of_smul_mem_submodule W hW0 hWfg _ fun z hz => ?_
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n', -, m', hm', rfl⟩ := hx
      have hmul : monomial (m + m') (1 : ℚ) = monomial m 1 * monomial m' 1 := by
        rw [monomial_mul, one_mul]
      have hx : (aeval y (monomial m (1 : ℚ)) / w ^ n) • (aeval y (monomial m' (1 : ℚ)) / w ^ n') =
          aeval y (monomial (m + m') (1 : ℚ)) / w ^ (n + n') := by
        rw [smul_eq_mul, hmul, map_mul, pow_add]
        field_simp
      rw [hx]
      exact claim _ _ (isMultiHomog_monomial fun k => by rw [blockDeg_add, hm, hm', add_mul])
    | zero => simp
    | add x x' _ _ hx hx' => rw [smul_add]; exact W.add_mem hx hx'
    | smul a x _ hx => rw [smul_comm]; exact W.smul_mem a hx
  set n := n₀ + 1
  set μ := diagMono c (fun k' => n * e k' - if k' = p.1 then 1 else 0)
  have hdeg : ∀ s : Σ k, ι k, s.1 = p.1 → ∀ k', blockDeg (Finsupp.single s 1 + μ) k' = n * e k' := by
    intro s hs k'
    rw [blockDeg_add, blockDeg_diagMono, blockDeg_single, hs]
    have h1 := Nat.mul_le_mul (show 1 ≤ n by omega) (he k')
    generalize n * e k' = t at *
    split_ifs <;> omega
  have hval : ∀ s : Σ k, ι k, aeval y (monomial (Finsupp.single s 1 + μ) (1 : ℚ)) =
      y s * aeval y (monomial μ (1 : ℚ)) := by
    intro s
    rw [monomial_single_add, pow_one, map_mul, aeval_X]
  have hμ0 : aeval y (monomial μ (1 : ℚ)) ≠ 0 := aeval_diagMono_ne_zero y c hc _
  have hr : ∀ s : Σ k, ι k, s.1 = p.1 →
      y s * aeval y (monomial μ (1 : ℚ)) / w ^ n ∈ algebraicClosure F Ω := fun s hs => by
    rw [mem_algebraicClosure_iff, ← hval s]
    exact (hint n _ (hdeg s hs)).isAlgebraic
  have key : y p * aeval y (monomial μ (1 : ℚ)) / w ^ n / (y q * aeval y (monomial μ (1 : ℚ)) / w ^ n) =
      y p / y q := by
    rw [div_div_div_cancel_right₀ (pow_ne_zero _ hw), mul_div_mul_right _ _ hμ0]
  rw [← key, ← mem_algebraicClosure_iff]
  exact (algebraicClosure F Ω).div_mem (hr p rfl) (hr q hpq.symm)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullConeDegreeInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (N M : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, IsMultiHomog (L j) e) →
    (∀ c : ∀ k, ι k, (M : MRing ι) * (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N ∈ coneNullIdealZ y L) →
    ∀ (d : K → ℕ) (g : MRing ι), IsMultiHomog g d → (∀ k, e k + N * Fintype.card (ι k) ≤ d k) →
      ∃ a : Fin (D + 1) → MRing ι, (∀ j, IsMultiHomog (a j) (d - e)) ∧
        (M : Ω) * aeval y g = ∑ j, aeval y (a j) * aeval y (L j)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormDehomIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
        (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
          ∃ F : MvPolynomial (Fin (D + 1)) ℤ,
            map (Int.castRingHom ℚ) F = ((M₀ : ℚ) ^ τ) • c (Module.finrank (pullField y L) Ω)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormDehomRoots.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
      (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
        ∀ ζ : Fin (D + 1) → ℂ, ζ ≠ 0 → ∀ w : ℂ,
          ∑ i ∈ Finset.range (Module.finrank (pullField y L) Ω + 1),
            eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (Module.finrank (pullField y L) Ω - i) = 0 →
          ∃ z ∈ mcPts (mCoordIdeal y), ∃ t : ℂ, t ≠ 0 ∧
            (∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) ∧
            ∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh →
              (∀ k, dg k = dh k + τ * (q * e k)) → aeval y g = s * aeval y h →
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 →
              eval z (map (Int.castRingHom ℂ) g) = w * t ^ (q * τ) * eval z (map (Int.castRingHom ℂ) h)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormPrimeBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p : ℕ, p.Prime → ∃ C : ℕ,
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
        (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
          ∀ m : Fin (D + 1) →₀ ℕ,
            -((C * τ : ℕ) : ℤ) ≤ padicValRat p ((c (Module.finrank (pullField y L) Ω)).coeff m)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionInterpIntegral.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)), IsSmoothMetric m₁ →
    ((D : ℝ) + 1) * resMetricInt d m₁ =
      ∑ i ∈ Finset.range (D + 1),
        mInt d.R.A (fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m)
          (fun y => logRatio d.m m₁ (resPt d y))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionMixedBridge.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (M : Fin D → ConeMetric ℂ (Ix κ)) (m₁ : ConeMetric ℂ (Ix κ)),
    (∀ j, IsSmoothMetric (M j)) → IsSmoothMetric m₁ →
    ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ d.x) (fun j z => Real.log ((M j).ρ z)) (logRatio d.m m₁) =
      mInt d.R.A (fun j => resPot d (M j)) (fun y => logRatio d.m m₁ (resPt d y))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResolutionMixedIntegral.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)), IsSmoothMetric m₁ →
    ∑ i ∈ Finset.range (D + 1),
        ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ d.x) (mixPot d.m m₁ D i) (logRatio d.m m₁) =
      ((D : ℝ) + 1) * resMetricInt d m₁

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
