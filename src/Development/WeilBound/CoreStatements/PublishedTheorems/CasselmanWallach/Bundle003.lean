module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CommutatorAdjointLower

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem comm_eq (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    (Mm E * Md ε E - Md ε E * Mm E) a b = ∑ c, (adjSign ε c b - adjSign ε a c) • (E a c * E c b) := by
  simp only [Mm, Md, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, mul_smul_comm, smul_mul_assoc,
    sub_smul, Finset.sum_sub_distrib]

theorem Z_eq (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ V} (hE : IsGlRep E) (a b : Fin n) :
    Z ε E a b = ∑ c, ((if ε c = ε a then E a c * E c b + E c b * E a c else 0) -
      (if ε c = ε b then E a c * E c b + E c b * E a c else 0)) := by
  unfold IsGlRep at hE
  rw [← sub_eq_zero]
  unfold Z casimirK
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ite_mul_sub_mul_ite, mul_mul_sub_mul_mul_eq_add, hE]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [ite_sub_add_sub_eq, ← ite_and, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [and_comm (b := _ = a), and_comm (b := b = _), Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [@eq_comm _ (ε a), @eq_comm _ (ε b), ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x _
  split_ifs <;> abel

end CommutatorAdjointLower

theorem commutator_adjoint_holds : A1 → CommutatorAdjointModLower := by
  intro hA n ε V _ _ E h a b
  obtain ⟨-, -, hE1, -, hcomm, -, -⟩ := hA n ε V E h
  rw [CommutatorAdjointLower.comm_eq, CommutatorAdjointLower.Z_eq ε h.gl, ← Finset.sum_add_distrib]
  have key : ∀ c, (adjSign ε c b - adjSign ε a c) • (E a c * E c b) +
      ((if ε c = ε a then E a c * E c b + E c b * E a c else 0) -
        (if ε c = ε b then E a c * E c b + E c b * E a c else 0)) =
      ((if ε c = ε a then (1 : ℂ) else 0) - (if ε c = ε b then 1 else 0)) • (E c b * E a c - E a c * E c b) := by
    intro c
    simp only [adjSign, @eq_comm _ (ε a) (ε c)]
    split_ifs <;> module
  rw [Finset.sum_congr rfl fun c _ => key c]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hcomm 1 1 _ (hE1 c b) _ (hE1 a c))

end PositivityTheory.CW

end
end

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenspaceOrthogonality

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {A : Module.End ℂ V}

lemma nc_sum (f : Fin n × Fin n → ℂ) :
    ∑ p ∈ nc ε, f p = ∑ a, ∑ b, if ε a ≠ ε b then f (a, b) else 0 := by
  unfold nc
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

lemma s1 (g : Fin n → Fin n → ℂ) (c : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if c = a then g a b else 0) else 0) =
      ∑ b, if ε c ≠ ε b then g c b else 0 := by
  rw [Finset.sum_eq_single c]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp
  · intro a _ hac
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm hac]
  · simp

lemma s2 (g : Fin n → Fin n → ℂ) (d : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if b = d then g a b else 0) else 0) =
      ∑ a, if ε a ≠ ε d then g a d else 0 := by
  rw [Finset.sum_comm, Finset.sum_eq_single d]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp
  · intro b _ hbd
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [hbd]
  · simp

lemma comm_apply (hgl : IsGlRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) +
      ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h := congrArg (fun T : Module.End ℂ V => T x) (hgl a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [← sub_eq_iff_eq_add', h]
  split_ifs <;> simp

lemma pt (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (a b : Fin n) (x y : V) :
    inner ℂ (E a b (E c d x)) (A (E a b y)) =
      inner ℂ (E a b x) (A (E a b (E d c y)))
      + (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0)
      - (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0)
      + (if b = c then inner ℂ (E a d x) (A (E a b y)) else 0)
      - (if d = a then inner ℂ (E c b x) (A (E a b y)) else 0) := by
  have hsgn : adjSign ε c d = 1 := by simp [adjSign, hcd]
  have h1 : inner ℂ (E c d (E a b x)) (A (E a b y)) = inner ℂ (E a b x) (A (E a b (E d c y)))
      + (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0)
      - (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0) := by
    rw [huni c d, hsgn, one_mul, ← hA d c hcd.symm, comm_apply hgl d c a b y]
    rw [map_add (f := _), map_sub, inner_add_right, inner_sub_right]
    split_ifs <;> (try simp) <;> ring
  rw [comm_apply hgl a b c d x, inner_add_left, h1, inner_sub_left]
  split_ifs <;> (try simp) <;> ring

lemma key (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (x y : V) :
    beta ε E A (E c d x) y = beta ε E A x (E d c y) := by
  have e : ∀ a b, (if ε a ≠ ε b then inner ℂ (E a b (E c d x)) (A (E a b y)) else 0) =
      (if ε a ≠ ε b then inner ℂ (E a b x) (A (E a b (E d c y))) else 0)
      + (if ε a ≠ ε b then (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0) else 0)
      - (if ε a ≠ ε b then (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0) else 0)
      + (if ε a ≠ ε b then (if b = c then inner ℂ (E a d x) (A (E a b y)) else 0) else 0)
      - (if ε a ≠ ε b then (if d = a then inner ℂ (E c b x) (A (E a b y)) else 0) else 0) := by
    intro a b
    by_cases hab : ε a ≠ ε b
    · simp only [if_pos hab]
      exact pt hgl huni hA hcd a b x y
    · simp only [if_neg hab]
      simp
  have h1 := s1 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E d b y))) c
  have h4 := s1 (ε := ε) (fun a b => inner ℂ (E c b x) (A (E a b y))) d
  have h2 := s2 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E a c y))) d
  have h3 := s2 (ε := ε) (fun a b => inner ℂ (E a d x) (A (E a b y))) c
  simp only [beta, nc_sum]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4, hcd]
  ring

lemma beta_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    beta ε E A (∑ i ∈ s, f i) w = ∑ i ∈ s, beta ε E A (f i) w := by

  simp only [beta, map_sum, sum_inner]
  exact Finset.sum_comm

lemma beta_sum_right {ι : Type*} (s : Finset ι) (f : ι → V) (v : V) :
    beta ε E A v (∑ i ∈ s, f i) = ∑ i ∈ s, beta ε E A v (f i) := by

  simp only [beta, map_sum, inner_sum]
  exact Finset.sum_comm

lemma Lsym (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z)) (v w : V) :
    beta ε E A (casimirK ε E v) w = beta ε E A v (casimirK ε E w) := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, beta_sum_left, beta_sum_right]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.mp hb).2
  rw [key hgl huni hA hab.symm, key hgl huni hA hab]

lemma beta_smul_left (r : ℝ) (v w : V) :
    beta ε E A ((r : ℂ) • v) w = (r : ℂ) * beta ε E A v w := by
  unfold beta
  simp [Finset.mul_sum]

lemma beta_smul_right (r : ℂ) (v w : V) :
    beta ε E A v (r • w) = r * beta ε E A v w := by
  unfold beta
  simp [Finset.mul_sum]

end EigenspaceOrthogonality

theorem eigenspaces_orthogonal_of_calculus : A0 → FunctionalCalculusLaws → EigenspacesOrthogonalAlt := by
  intro hA0 hA11b n ε V _ _ E h ι b μ hB φ ν ν' v w hne hv hw
  obtain ⟨-, -, hZ, -⟩ := hA0 n ε V E h
  obtain ⟨hfc, -⟩ := hA11b n ε V E h ι b μ hB
  have hcomm : ∀ c d, ε c = ε d → ∀ z, fc b μ φ (E c d z) = E c d (fc b μ φ z) := by
    intro c d hcd z
    have heig : ∀ i, Eig ε E (μ i) (E c d (b i)) := by
      intro i
      have hz := congrArg (fun T : Module.End ℂ V => T (b i)) (hZ c d hcd)
      simp only [Z, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at hz
      show casimirK ε E (E c d (b i)) = ((μ i : ℝ) : ℂ) • E c d (b i)
      rw [sub_eq_zero.mp hz, show casimirK ε E (b i) = ((μ i : ℝ) : ℂ) • b i from hB.eig i, map_smul]
    have hT : (fc b μ φ).comp (E c d) = (E c d).comp (fc b μ φ) := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply]
      rw [hfc φ (μ i) _ (heig i), hfc φ (μ i) _ (hB.eig i), map_smul]
    exact LinearMap.congr_fun hT z
  have hL := EigenspaceOrthogonality.Lsym (A := fc b μ φ) h.gl h.uni hcomm v w
  rw [show casimirK ε E v = ((ν : ℝ) : ℂ) • v from hv,
    show casimirK ε E w = ((ν' : ℝ) : ℂ) • w from hw,
    EigenspaceOrthogonality.beta_smul_left, EigenspaceOrthogonality.beta_smul_right] at hL
  have hm : (((ν : ℝ) : ℂ) - ((ν' : ℝ) : ℂ)) * beta ε E (fc b μ φ) v w = 0 := by
    rw [sub_mul, hL, sub_self]
  rcases mul_eq_zero.mp hm with h0 | h0
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h0)) hne
  · exact h0

end PositivityTheory.CW

end
end

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace GrowthPolynomialOperator

variable {n : ℕ}

lemma actM_Xp {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Xp a b) = ((1 + Complex.I) / 2) • E a b + ((1 - Complex.I) / 2) • E b a := by
  simp only [actM, Xp, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.single_apply, ite_smul, zero_smul, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma sum_nc_swap {β : Type*} [AddCommMonoid β] (ε : Fin n → Bool) (g : Fin n × Fin n → β) :
    ∑ p ∈ nc ε, g p.swap = ∑ p ∈ nc ε, g p := by
  apply Finset.sum_nbij' Prod.swap Prod.swap <;> simp [nc, ne_comm]

lemma norm_id (x y : ℂ) :
    ‖(1 + Complex.I) / 2 * x + (1 - Complex.I) / 2 * y‖ ^ 2 +
      ‖(1 + Complex.I) / 2 * y + (1 - Complex.I) / 2 * x‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  ring

lemma coef1 : ((1 + Complex.I) / 2) ^ 2 + ((1 - Complex.I) / 2) ^ 2 = 0 := by
  ring_nf; simp [Complex.I_sq]

lemma coef2 : (1 + Complex.I) / 2 * ((1 - Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 + Complex.I) / 2) = 1 := by
  linear_combination (-1/2 : ℂ) * Complex.I_sq

lemma inP_Xp (ε : Fin n → Bool) (a b : Fin n) (h : ε a ≠ ε b) : inP ε (Xp a b) := by
  have hab : a ≠ b := fun e => h (e ▸ rfl)
  refine ⟨?_, ?_⟩
  · unfold inG
    ext i j
    simp [Jm, Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.single_apply, ← sub_eq_add_neg]
    by_cases h1 : a = i ∧ b = j
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a
      subst h1b
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
    · by_cases h2 : b = i ∧ a = j
      · obtain ⟨h2a, h2b⟩ := h2
        subst h2a
        subst h2b
        cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
      · simp [h1, h2]
  · ext i j
    simp [Jm, Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    by_cases h1 : a = i ∧ b = j
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a
      subst h1b
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
    · by_cases h2 : b = i ∧ a = j
      · obtain ⟨h2a, h2b⟩ := h2
        subst h2a
        subst h2b
        cases ha : ε a <;> cases hb : ε b <;> simp_all <;> ring
      · simp [h1, h2]

end GrowthPolynomialOperator

open GrowthPolynomialOperator in
theorem growth_of_basic : A0 → B1 := by
  intro hA n ε V _ _ E hm
  obtain ⟨_, _, _, h4⟩ := hA n ε V E hm
  refine ⟨fun p hp => inP_Xp ε p.1 p.2 (by simpa [nc] using hp), fun κ hκ v => ?_, fun f w => ?_⟩
  · have hterm : ∀ a b : Fin n, actM E (Xp a b) (actM E (Xp a b) v) =
        ((1 + Complex.I) / 2) ^ 2 • E a b (E a b v) + ((1 + Complex.I) / 2 * ((1 - Complex.I) / 2)) • E a b (E b a v) +
        ((1 - Complex.I) / 2 * ((1 + Complex.I) / 2)) • E b a (E a b v) + ((1 - Complex.I) / 2) ^ 2 • E b a (E b a v) := by
      intro a b
      rw [actM_Xp]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul]
      module
    rw [Finset.sum_congr rfl (fun p _ => hterm p.1 p.2)]
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
    have s1 := sum_nc_swap ε (fun p => E p.1 p.2 (E p.1 p.2 v))
    have s2 := sum_nc_swap ε (fun p => E p.1 p.2 (E p.2 p.1 v))
    simp only [Prod.fst_swap, Prod.snd_swap] at s1 s2
    rw [s1, s2, ← (h4 κ hκ v).2.2]
    calc _ = (((1 + Complex.I) / 2) ^ 2 + ((1 - Complex.I) / 2) ^ 2) • ∑ p ∈ nc ε, E p.1 p.2 (E p.1 p.2 v) +
          ((1 + Complex.I) / 2 * ((1 - Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 + Complex.I) / 2)) •
            ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 v) := by module
      _ = _ := by rw [coef1, coef2]; simp
  · have key : ∀ p ∈ nc ε, ‖f (actM E (Xp p.1 p.2) w)‖ ^ 2 + ‖f (actM E (Xp p.2 p.1) w)‖ ^ 2 =
        ‖f (E p.1 p.2 w)‖ ^ 2 + ‖f (E p.2 p.1 w)‖ ^ 2 := by
      intro p _
      simp only [actM_Xp, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul, smul_eq_mul]
      exact norm_id _ _
    have h1 := sum_nc_swap ε (fun p => ‖f (actM E (Xp p.1 p.2) w)‖ ^ 2)
    have h2 := sum_nc_swap ε (fun p => ‖f (E p.1 p.2 w)‖ ^ 2)
    simp only [Prod.fst_swap, Prod.snd_swap] at h1 h2
    have h3 := Finset.sum_congr rfl key
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2] at h3
    linarith

end PositivityTheory.CW

end
end

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace AdjointWordFiltration

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem U_mono (E : Fin n → Fin n → Module.End ℂ V) {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by
  unfold U
  apply Submodule.span_mono
  rintro x ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

theorem word_mem (E : Fin n → Fin n → Module.End ℂ V) (l : List (Fin n × Fin n)) :
    (l.map fun p => E p.1 p.2).prod ∈ U E l.length :=
  Submodule.subset_span ⟨l, le_rfl, rfl⟩

theorem mul_E_mem (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) {j : ℕ} {w : Module.End ℂ V}
    (hw : w ∈ U E j) : w * E a b ∈ U E (j + 1) := by
  unfold U at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l ++ [(a, b)], by simp; omega, ?_⟩
    simp [List.prod_append]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem adjSign_mul_self (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b * adjSign ε a b = 1 := by
  unfold adjSign; split_ifs <;> norm_num

theorem word_adj (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (l : List (Fin n × Fin n)) :
    ∃ u' ∈ U E l.length, ∀ x y, inner ℂ x ((l.map fun p => E p.1 p.2).prod y) = inner ℂ (u' x) y := by
  induction l with
  | nil =>
    refine ⟨1, by simpa using word_mem E [], fun x y => ?_⟩
    simp
  | cons p t ih =>
    obtain ⟨w', hw', hw⟩ := ih
    refine ⟨(starRingEnd ℂ (adjSign ε p.2 p.1)) • (w' * E p.2 p.1), ?_, fun x y => ?_⟩
    · exact Submodule.smul_mem _ _ (by simpa using mul_E_mem E p.2 p.1 hw')
    · have h1 := hu p.2 p.1 x ((t.map fun p => E p.1 p.2).prod y)
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.smul_apply, inner_smul_left,
        Complex.conj_conj, Module.End.mul_apply, ← hw, h1, ← mul_assoc, adjSign_mul_self, one_mul]

end AdjointWordFiltration

theorem adjoint_stable_filtration : FiltrationAdjointStable := by
  intro n ε V _ _ E hM k u hu
  unfold U at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨u', hu', h⟩ := AdjointWordFiltration.word_adj ε E hM.uni l
    exact ⟨u', AdjointWordFiltration.U_mono E hl hu', h⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun x y => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', hx⟩ := hx
    obtain ⟨y', hy', hy⟩ := hy
    exact ⟨x' + y', Submodule.add_mem _ hx' hy', fun a b => by
      simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hx, hy]⟩
  | smul c x _ hx =>
    obtain ⟨x', hx', hx⟩ := hx
    refine ⟨starRingEnd ℂ c • x', Submodule.smul_mem _ _ hx', fun a b => ?_⟩
    rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_conj, hx]

end PositivityTheory.CW

end
end
