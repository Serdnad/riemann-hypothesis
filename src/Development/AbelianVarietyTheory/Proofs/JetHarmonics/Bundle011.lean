module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism.REAL Finset

namespace GlobalTheory

theorem abs_list_prod_map_le_of_abs_le {α : Type} (L : List α) (f n : α → ℝ)
    (h : ∀ a ∈ L, |f a| ≤ n a) : |(L.map f).prod| ≤ (L.map n).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

theorem sum_weight_blockDiagonal_eq {ι κ : Type} [Fintype ι] [DecidableEq κ] (B : ι → ι → ℂ)
    (k : ι → κ) (hB : ∀ i j, k i ≠ k j → B i j = 0) (f : κ → ℝ) :
    (∑ i, ∑ j, ((f (k i) : ℝ) : ℂ) * B i j).re =
      ∑ t ∈ Finset.univ.image k, f t *
        (∑ i ∈ Finset.univ.filter (fun i => k i = t),
          ∑ j ∈ Finset.univ.filter (fun j => k j = t), B i j).re := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image k) (g := k)
    (fun i _ => Finset.mem_image_of_mem k (Finset.mem_univ i)), Complex.re_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : k i = t := (Finset.mem_filter.mp hi).2
  rw [← Finset.mul_sum, hi', Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · rfl
  · exact hB i j (fun e => h (e ▸ hi'))

theorem gram_blockDiagonal_energy_bound :
    ∀ (ι α : Type) [Fintype ι] (B : ι → ι → ℂ) (c : ι → α → ℝ) (L : List α) (n : α → ℝ), (∀ S : Finset ι, 0 ≤ (∑ i ∈ S, ∑ j ∈ S, B i j).re) → (∀ i j, ∀ a ∈ L, c i a ≠ c j a → B i j = 0) → (∀ i, ∀ a ∈ L, |c i a| ≤ n a) → (∑ i, ∑ j, (((L.map (c i)).prod : ℝ) : ℂ) * B i j).re ≤ (L.map n).prod * (∑ i, ∑ j, B i j).re := by
  intro ι α _ B c L n hpos hzero hbd
  classical
  have hB : ∀ i j, L.map (c i) ≠ L.map (c j) → B i j = 0 := by
    intro i j hij
    by_contra hne
    apply hij
    refine List.map_congr_left (fun a ha => ?_)
    by_contra h
    exact hne (hzero i j a ha h)
  have e1 := sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB List.prod
  have e2 := sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at e2
  rw [e1, e2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun t ht => ?_)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
  exact mul_le_mul_of_nonneg_right
    ((le_abs_self _).trans (abs_list_prod_map_le_of_abs_le L (c i) n (hbd i))) (hpos _)

end GlobalTheory
end

section

open Formalism.REAL Finset

namespace GlobalTheory

theorem shift_coeff_of_eval_identity {N : Type} [AddCommGroup N] [Module ℂ N]
    (Ω : Module.End ℂ N) (M : ℕ) (a : ℕ → N) (ha : ∀ i, M ≤ i → a i = 0) (p : Polynomial ℂ)
    (w : N) (h : ∀ u : ℂ, u • (∑ i ∈ Finset.range M, u ^ i • a i)
      + Ω (∑ i ∈ Finset.range M, u ^ i • a i) = p.eval u • w) :
    Ω (a 0) = p.coeff 0 • w ∧ ∀ k, a k + Ω (a (k + 1)) = p.coeff (k + 1) • w := by
  have hc : ∀ (f : N →ₗ[ℂ] ℂ) (k : ℕ),
      (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i))).coeff k = f (a k) := by
    intro f k
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply]
    rw [Finset.sum_ite_eq']
    split_ifs with hk
    · rfl
    · rw [ha k (by simpa using hk), map_zero]
  have key : ∀ f : N →ₗ[ℂ] ℂ,
      Polynomial.X * (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i)))
        + (∑ i ∈ Finset.range M, Polynomial.monomial i ((f ∘ₗ Ω) (a i)))
        = p * Polynomial.C (f w) := by
    intro f
    apply Polynomial.funext
    intro u
    have h1 := congrArg f (h u)

    simp only [map_add (f := _), map_smul, map_sum, smul_eq_mul] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_C,
      LinearMap.comp_apply]
    rw [← h1]
    simp only [mul_comm]
  refine ⟨?_, fun k => ?_⟩
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h1 := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P 0) (key f)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, hc, Polynomial.coeff_mul_C,
      zero_add] at h1
    rw [LinearMap.comp_apply] at h1
    rw [map_sub, map_smul, smul_eq_mul, h1, sub_self]
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h1 := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P (k + 1)) (key f)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul, hc, Polynomial.coeff_mul_C] at h1
    rw [LinearMap.comp_apply] at h1
    rw [map_sub, map_add (f := _), map_smul, smul_eq_mul, h1, sub_self]

theorem aeval_neg_eq_zero_and_eigen_of_resolvent_identity :
    ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (p : Polynomial ℂ), (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = p.eval u • w) → Polynomial.aeval (-Ω) p = 0 ∧ ∀ (α : ℂ) (w : N), Ω w = α • w → ∀ (q : Polynomial ℂ), p = (Polynomial.X + Polynomial.C α) * q → ∀ u : ℂ, X u w = q.eval u • w := by
  intro N _ _ Ω X d c p hX h
  let a : N → ℕ → N := fun w i => if i < d then c i w else 0
  have ha : ∀ w i, d ≤ i → a w i = 0 := fun w i hi => if_neg (by omega)
  have hXa : ∀ (M : ℕ), d ≤ M → ∀ (u : ℂ) (w : N),
      X u w = ∑ i ∈ Finset.range M, u ^ i • a w i := by
    intro M hM u w
    rw [hX u, LinearMap.sum_apply]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 hM)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp only [a, if_pos (Finset.mem_range.1 hi), LinearMap.smul_apply]
    · intro i _ hi
      rw [ha w i (by simpa using hi), smul_zero]
  have hco : ∀ w, Ω (a w 0) = p.coeff 0 • w ∧
      ∀ k, a w k + Ω (a w (k + 1)) = p.coeff (k + 1) • w := by
    intro w
    refine shift_coeff_of_eval_identity Ω d (a w) (ha w) p w fun u => ?_
    rw [← hXa d le_rfl u w]
    exact h u w
  refine ⟨?_, ?_⟩
  · ext w
    have tel : ∀ n, ∑ i ∈ Finset.range (n + 1), p.coeff i • ((-Ω) ^ i) w
        = ((-Ω) ^ n) (Ω (a w n)) := by
      intro n
      induction n with
      | zero => simp [(hco w).1]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, ← map_smul, ← (hco w).2 n, map_add (f := _), ← add_assoc]
        have : ((-Ω) ^ (n + 1)) (a w n) = - ((-Ω) ^ n) (Ω (a w n)) := by
          rw [pow_succ, Module.End.mul_apply, LinearMap.neg_apply, map_neg]
        rw [this, add_neg_cancel, zero_add]
    rw [Polynomial.aeval_eq_sum_range' (n := d + p.natDegree + 1) (by omega), LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [tel, ha w _ (by omega), map_zero, map_zero, LinearMap.zero_apply]
  · intro α w hw q hq u
    have step : ∀ k, a w (k + 1) = q.coeff (k + 1) • w → a w k = q.coeff k • w := by
      intro k hk
      have h1 := (hco w).2 k
      rw [hk, map_smul, hw, hq, add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_mul, add_smul, smul_smul, mul_comm] at h1
      exact add_right_cancel h1
    have all : ∀ k, a w k = q.coeff k • w := by
      intro k
      have hk : k ≤ k + d + q.natDegree + 1 := by omega
      refine Nat.decreasingInduction (motive := fun k _ => a w k = q.coeff k • w)
        (fun j _ hj => step j hj) ?_ hk
      rw [ha w _ (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]
    rw [hXa (d + q.natDegree + 1) (by omega), Polynomial.eval_eq_sum_range' (n := d + q.natDegree + 1) (by omega), Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [all, smul_smul, mul_comm]

end GlobalTheory
end

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem exists_integral_poly_of_character (K : Type) [NormedField K] [IsUltrametricDist K]
    (G : Type) [AddCommGroup G] [Fintype G] (x χ : G → K) (hx : Function.Injective x)
    (hχ : ∀ i j, χ (i + j) = χ i * χ j)
    (hc : ∀ k : Fin (Fintype.card G), ∃ c : Fin (Fintype.card G) → Fin (Fintype.card G) → K,
      (∀ a b, ‖c a b‖ ≤ 1) ∧
        ∀ i j, x (i + j) ^ (k : ℕ) = ∑ a, ∑ b, c a b * x i ^ (a : ℕ) * x j ^ (b : ℕ)) :
    ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ i, g.eval (x i) = χ i := by
  classical
  choose c hc1 hc2 using hc
  have van : ∀ v : Fin (Fintype.card G) → K, (∀ i, ∑ a, v a * x i ^ (a : ℕ) = 0) → v = 0 := by
    intro v hv
    exact Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (f := fun j => x ((Fintype.equivFin G).symm j))
      (hx.comp (Fintype.equivFin G).symm.injective) (fun j => hv _)
  set g : Polynomial K := Lagrange.interpolate Finset.univ x χ with hg
  have hinj : Set.InjOn x (Finset.univ : Finset G) := hx.injOn
  have hdeg : g.degree < (Fintype.card G : ℕ) := by
    exact Lagrange.degree_interpolate_lt (r := χ) hinj
  have hev : ∀ i, g.eval (x i) = χ i := fun i =>
    Lagrange.eval_interpolate_at_node χ hinj (Finset.mem_univ i)
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  have hnat : g.natDegree < Fintype.card G := by
    by_cases h0 : g = 0
    · simpa [h0] using hpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hdeg
  have hsum : ∀ i, χ i = ∑ a : Fin (Fintype.card G), g.coeff a * x i ^ (a : ℕ) := by
    intro i
    rw [← hev i, Polynomial.eval_eq_sum_range' hnat,
      Fin.sum_univ_eq_sum_range (fun a => g.coeff a * x i ^ a)]
  have key : ∀ a b : Fin (Fintype.card G),
      g.coeff a * g.coeff b = ∑ k : Fin (Fintype.card G), g.coeff k * c k a b := by
    have h1 : ∀ j, (fun a : Fin (Fintype.card G) => ∑ b : Fin (Fintype.card G),
        (g.coeff a * g.coeff b - ∑ k : Fin (Fintype.card G), g.coeff k * c k a b)
          * x j ^ (b : ℕ)) = 0 := by
      intro j
      apply van
      intro i
      have e1 : χ i * χ j = ∑ a : Fin (Fintype.card G), ∑ b : Fin (Fintype.card G),
          g.coeff a * g.coeff b * x j ^ (b : ℕ) * x i ^ (a : ℕ) := by
        rw [hsum i, hsum j, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      have e2 : χ (i + j) = ∑ a : Fin (Fintype.card G), ∑ b : Fin (Fintype.card G),
          (∑ k : Fin (Fintype.card G), g.coeff k * c k a b) * x j ^ (b : ℕ) * x i ^ (a : ℕ) := by
        rw [hsum (i + j)]
        simp_rw [hc2, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
      have e3 := hχ i j
      rw [e1, e2] at e3
      simp_rw [Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      exact e3.symm
    intro a b
    have h2 := van _ (fun j => congrFun (h1 j) a)
    exact sub_eq_zero.1 (congrFun h2 b)
  haveI : Nonempty (Fin (Fintype.card G)) := ⟨⟨0, hpos⟩⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : Fin (Fintype.card G) => ‖g.coeff a‖) Finset.univ_nonempty
  have hM : ‖g.coeff m‖ * ‖g.coeff m‖ ≤ ‖g.coeff m‖ := by
    rw [← norm_mul, key]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro k _
    rw [norm_mul]
    calc ‖g.coeff k‖ * ‖c k m m‖ ≤ ‖g.coeff k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hc1 k m m) (norm_nonneg _)
      _ ≤ ‖g.coeff m‖ := by simpa using hm k (Finset.mem_univ k)
  have hM1 : ‖g.coeff m‖ ≤ 1 := by nlinarith [norm_nonneg (g.coeff m)]
  refine ⟨g, fun k => ?_, hev⟩
  by_cases hk : k < Fintype.card G
  · exact (hm ⟨k, hk⟩ (Finset.mem_univ _)).trans hM1
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

end GlobalTheory.ConvSer
end

section

noncomputable section

namespace GlobalTheory.GenTorsor

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Z : Scheme.{0}}

section Cover

variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

end Cover

theorem isRepresentable_of_cover (F : Scheme.{0}ᵒᵖ ⥤ Type)
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) (p : F ⟶ yoneda.obj X)
    {J : Type} (W : J → X.Opens) (hW : iSup W = ⊤) (T : J → Scheme.{0})
    (y : ∀ i, F.obj (op (T i))) (π : ∀ i, T i ⟶ W i)
    (hπ : ∀ i, p.app _ (y i) = π i ≫ (W i).ι)
    (h : ∀ i (Z : Scheme.{0}) (x : F.obj (op Z)) (b : Z ⟶ W i), p.app _ x = b ≫ (W i).ι →
      ∃! c : Z ⟶ T i, F.map c.op (y i) = x) : F.IsRepresentable := by
  let G : Sheaf Scheme.zariskiTopology.{0} Type := ⟨F, (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩
  let f : ∀ i, yoneda.obj (T i) ⟶ G.1 := fun i => yonedaEquiv.symm (y i)
  have hp : ∀ i (Z : Scheme.{0}) (c : Z ⟶ T i), p.app _ (F.map c.op (y i)) = c ≫ π i ≫ (W i).ι := by
    intro i Z c
    rw [← hπ]
    exact ConcreteCategory.congr_hom (p.naturality c.op) (y i)
  have hf : ∀ i, IsOpenImmersion.presheaf (f i) := by
    intro i
    have : IsPullback (f i) (yoneda.map (π i)) p (yoneda.map (W i).ι) := by
      apply IsPullback.of_forall_isPullback_app
      rintro ⟨Z⟩
      rw [Types.isPullback_iff]
      refine ⟨?_, ?_, ?_⟩
      · ext c
        exact (hp i Z c).trans (Category.assoc _ _ _).symm
      · rintro c c' ⟨h1, -⟩
        exact (h i Z (F.map (Quiver.Hom.op c) (y i)) (c ≫ π i)
          ((hp i Z c).trans (Category.assoc _ _ _).symm)).unique rfl h1.symm
      · intro x b hb
        obtain ⟨c, hc, -⟩ := h i Z x b hb
        refine ⟨c, hc, ?_⟩
        change c ≫ π i = b
        rw [← cancel_mono (W i).ι, Category.assoc, ← hp, hc]
        exact hb
    exact (MorphismProperty.relative_isStableUnderBaseChange @IsOpenImmersion).of_isPullback this.flip
      (MorphismProperty.relative_map (inferInstanceAs (IsOpenImmersion (W i).ι)))
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    constructor
    intro Z x
    let q : Z ⟶ X := p.app _ x
    let 𝒰 := Z.openCoverOfIsOpenCover (fun i => q ⁻¹ᵁ W i) (by
      rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hW]; rfl)
    refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    obtain ⟨c, hc, -⟩ := h i _ (F.map (q ⁻¹ᵁ W i).ι.op x) (q ∣_ W i) (by
      rw [morphismRestrict_ι]
      exact ConcreteCategory.congr_hom (p.naturality (q ⁻¹ᵁ W i).ι.op) x)
    refine ⟨(Sigma.ι (fun i => yoneda.obj (T i)) i).app _ c, ?_⟩
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (Sigma.ι_desc f i) _) c).trans hc
  exact Scheme.LocalRepresentability.isRepresentable hf

end GlobalTheory.GenTorsor
end
end

section

open scoped BigOperators

namespace GlobalTheory.AlgJetComb

theorem pow_mem (δ : ℂ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h : ∀ n, δ ^ n * iteratedDeriv n f 0 ∈ algebraicClosure ℚ ℂ) (a : ℕ) :
    ∀ n, δ ^ n * iteratedDeriv n (fun x => f x ^ a) 0 ∈ algebraicClosure ℚ ℂ := by
  induction a with
  | zero =>
    intro n
    simp only [pow_zero, iteratedDeriv_const]
    split_ifs with hn
    · subst hn; simpa using one_mem _
    · simpa using zero_mem _
  | succ a ih =>
    intro n
    have e : (fun x => f x ^ (a + 1)) = (fun x => f x ^ a) * f := by
      funext x; simp [pow_succ]
    have h1 : ContDiffAt ℂ n (fun x => f x ^ a) 0 := (hf.pow a).contDiff.contDiffAt
    have h2 : ContDiffAt ℂ n f 0 := hf.contDiff.contDiffAt
    rw [e, iteratedDeriv_mul h1 h2, Finset.mul_sum]
    refine sum_mem fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e2 : δ ^ n * ((n.choose i : ℂ) * iteratedDeriv i (fun x => f x ^ a) 0
        * iteratedDeriv (n - i) f 0) = (n.choose i : ℂ) *
        ((δ ^ i * iteratedDeriv i (fun x => f x ^ a) 0)
          * (δ ^ (n - i) * iteratedDeriv (n - i) f 0)) := by
      have : δ ^ n = δ ^ i * δ ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
      rw [this]; ring
    rw [e2]
    exact mul_mem (natCast_mem _ _) (mul_mem (ih i) (h _))

theorem iteratedFDeriv_comb_mem :
    ∀ (g m k : ℕ) (δ : ℂ) (a : Fin g → ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ)
      (ys : Fin k → Fin g → ℂ), (∀ j i, Differentiable ℂ (f j i)) →
      (∀ j i n, δ⁻¹ ^ n * iteratedDeriv n (f j i) 0 ∈ algebraicClosure ℚ ℂ) →
      (∀ j, c j ∈ algebraicClosure ℚ ℂ) → (∀ l i, ys l i ∈ algebraicClosure ℚ ℂ) →
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, f j i (z i) ^ a i) 0
        (fun l => δ⁻¹ • ys l) ∈ algebraicClosure ℚ ℂ := by
  intro g m k δ a c f ys hf hj hc hy
  have hF : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, f j i (z i) ^ a i) := fun j =>
    contDiff_prod fun i _ => (((hf j i).contDiff).comp (contDiff_apply ℂ (fun _ => ℂ) i)).pow _
  rw [iteratedFDeriv_fun_sum_apply (f := fun j (z : Fin g → ℂ) => c j * ∏ i, f j i (z i) ^ a i)
    (fun j _ => (contDiff_const.mul (hF j)).contDiffAt), ContinuousMultilinearMap.sum_apply]
  refine sum_mem fun j _ => ?_
  have e := iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hF j).contDiffAt
  simp only [smul_eq_mul] at e
  rw [e, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  refine mul_mem (hc j) ?_
  rw [GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k (fun i x => f j i x ^ a i) _
    (fun i => (hf j i).pow _)]
  refine sum_mem fun σ _ => ?_
  have hk : ∑ i, (Finset.univ.filter (fun l => σ l = i)).card = k := by
    rw [← Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := σ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    simp
  have e2 : (∏ l, (δ⁻¹ • ys l) (σ l)) *
      ∏ i, iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun x => f j i x ^ a i) 0
      = (∏ l, ys l (σ l)) * ∏ i, (δ⁻¹ ^ (Finset.univ.filter (fun l => σ l = i)).card *
        iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun x => f j i x ^ a i) 0) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hk]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  rw [e2]
  exact mul_mem (prod_mem fun l _ => hy _ _)
    (prod_mem fun i _ => pow_mem δ⁻¹ (f j i) (hf j i) (hj j i) _ _)

end GlobalTheory.AlgJetComb
end
