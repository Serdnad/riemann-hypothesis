module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofTorMkCIsQuotientMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormSqNonnegGaussianTorus
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem z_eq_inner {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    (v : EuclideanSpace ℂ ι) : z K k v = innerSL ℂ (e K k) v := by
  unfold z e Hf
  rw [innerSL_apply_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply]

theorem zmG_differentiable {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    Differentiable ℂ (zmG I s) := by
  unfold zmG
  have hs' : Differentiable ℂ s := (show Differentiable ℂ s ∧ _ from hs).1
  have h1 : Differentiable ℂ fun v : Vsp X.dim => s fun _ => v :=
    hs'.comp (differentiable_pi.2 fun _ => differentiable_id)
  refine h1.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
  unfold S
  have hz : ∀ k, Differentiable ℂ fun v : Vsp X.dim => z (IR I) k v ^ 2 := by
    intro k
    refine Differentiable.pow ?_ 2
    have hk : z (IR I) k = ⇑(innerSL ℂ (e (IR I) k)) :=
      funext fun v => z_eq_inner _ _ _
    rw [hk]
    exact (innerSL ℂ (e (IR I) k)).differentiable
  first
    | exact Differentiable.fun_sum fun k _ => hz k
    | exact Differentiable.sum fun k _ => hz k

theorem zmG_continuous {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    Continuous (zmG I s) := (zmG_differentiable hs).continuous

def tb (hI : IsSplit P I) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) : Vsp X.dim :=
  ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)

theorem tb_mem (hI : IsSplit P I) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) : tb hI t ∈ IR I :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Ib hI i).2

theorem tb_add (hI : IsSplit P I) (t t' : Fin (Module.finrank ℝ (IR I)) → ℝ) :
    tb hI (t + t') = tb hI t + tb hI t' := by
  simp only [tb, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem tb_int (hI : IsSplit P I) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) :
    tb hI (fun i => (n i : ℝ)) ∈ I := by
  unfold tb
  refine Submodule.sum_mem _ fun i _ => ?_
  have hK : (Ib hI i : IR I) ∈ IK I := by
    simp only [Ib, Module.Basis.reindex_apply, Module.Basis.ofZLatticeBasis_apply]
    exact SetLike.coe_mem _
  have hmem : ((Ib hI i : IR I) : Vsp X.dim) ∈ I := hK
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ hmem

theorem zmC_eq (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) (n) (v : Vsp X.dim) :
    zmC hI s n v = ∫ t in zmBox (Module.finrank ℝ (IR I)),
      Complex.exp (-(2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * (t i : ℂ))) * zmG I s (v + tb hI t) := rfl

theorem fib_continuous (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) : Continuous fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => zmG I s (v + tb hI t) := by
  refine (zmG_continuous hs).comp (continuous_const.add ?_)
  unfold tb
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

private lemma im_inner_eq_zero_on_real_span (S₀ : Set (Vsp X.dim))
    (hS : ∀ x ∈ S₀, ∀ y ∈ S₀, (inner ℂ x y).im = 0) :
    ∀ x ∈ Submodule.span ℝ S₀, ∀ y ∈ Submodule.span ℝ S₀, (inner ℂ x y).im = 0 := by
  have key : ∀ x : Vsp X.dim, (∀ y ∈ S₀, (inner ℂ x y).im = 0) →
      ∀ y ∈ Submodule.span ℝ S₀, (inner ℂ x y).im = 0 := by
    intro x hx y hy
    let f : Vsp X.dim →ₗ[ℝ] ℝ := Complex.imLm.comp ((innerSL ℂ x).toLinearMap.restrictScalars ℝ)
    have hf : ∀ u, f u = (inner ℂ x u).im := fun u => rfl
    have hle : Submodule.span ℝ S₀ ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      intro u hu
      rw [SetLike.mem_coe, LinearMap.mem_ker, hf]
      exact hx u hu
    have h := hle hy
    rwa [LinearMap.mem_ker, hf] at h
  intro x hx y hy
  have h1 : ∀ u ∈ S₀, (inner ℂ y u).im = 0 := by
    intro u hu
    have h := key u (hS u hu) y hy
    rw [← inner_conj_symm, Complex.conj_im, h, neg_zero]
  have h := key y h1 x hx
  rw [← inner_conj_symm, Complex.conj_im, h, neg_zero]

private lemma Hf_eq_inner_swap {ι : Type} [Fintype ι] (x y : EuclideanSpace ℂ ι) : Hf y x = inner ℂ x y := by
  unfold Hf
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply]

private lemma zmG_add_mem_of_isSplit (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (w γ : Vsp X.dim) (hγI : γ ∈ I) : zmG I s (w + γ) = zmG I s w := by
  have hγR : γ ∈ IR I := Submodule.subset_span hγI
  have hreal : ∀ x ∈ IR I, ∀ y ∈ IR I, (inner ℂ x y).im = 0 := by
    refine im_inner_eq_zero_on_real_span (I : Set (Vsp X.dim)) ?_
    intro x hx y hy
    have h := hI.iso y hy x hx
    rwa [Hf_eq_inner_swap] at h
  have hz : ∀ k u, z (IR I) k u = inner ℂ (e (IR I) k) u := by
    intro k u
    rw [z_eq_inner, innerSL_apply_apply]
  have hzadd : ∀ k (u u' : Vsp X.dim), z (IR I) k (u + u') = z (IR I) k u + z (IR I) k u' := by
    intro k u u'
    rw [hz, hz, hz, inner_add_right]
  let b := stdOrthonormalBasis ℝ (IR I)
  have heb : ∀ k : Fin (dK (IR I)), e (IR I) k = ((b k : IR I) : Vsp X.dim) := fun k => rfl
  have he_mem : ∀ k : Fin (dK (IR I)), e (IR I) k ∈ IR I := fun k => (b k).2
  obtain ⟨γ', hγ'⟩ : ∃ γ' : IR I, (γ' : Vsp X.dim) = γ := ⟨⟨γ, hγR⟩, rfl⟩
  have hexp : γ = ∑ k : Fin (dK (IR I)), (b.repr γ' k) • ((b k : IR I) : Vsp X.dim) := by
    have h := congrArg (fun x : IR I => (x : Vsp X.dim)) (b.sum_repr γ')
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← hγ', ← h]
  have hzγ : ∀ k : Fin (dK (IR I)), z (IR I) k γ = ((b.repr γ' k : ℝ) : ℂ) := by
    intro k
    rw [hz]
    apply Complex.ext
    · rw [Complex.ofReal_re, OrthonormalBasis.repr_apply_apply, ← hγ', Submodule.coe_inner, heb]
      first
        | exact (real_inner_eq_re_inner (𝕜 := ℂ) _ _).symm
        | (rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
           refine Finset.sum_congr rfl fun i _ => ?_
           first
             | (rw [RCLike.inner_apply, Complex.inner, mul_comm])
             | (rw [RCLike.inner_apply, Complex.inner])
             | exact (real_inner_eq_re_inner (𝕜 := ℂ) _ _).symm
             | simp [Complex.inner, RCLike.inner_apply, mul_comm])
    · rw [Complex.ofReal_im]
      exact hreal _ (he_mem k) _ hγR
  have hstar : ∀ u : Vsp X.dim, ∑ k : Fin (dK (IR I)), z (IR I) k u * z (IR I) k γ = Hf u γ := by
    intro u
    rw [Hf_eq_inner_swap]
    conv_rhs => rw [hexp]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    first
      | (rw [hzγ, hz, heb, ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, mul_comm])
      | (rw [hzγ, hz, heb, ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, mul_comm]; rfl)
      | (rw [hzγ, hz, heb, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
          mul_comm]; congr 1)
  have hS : ∀ u : Vsp X.dim, S (IR I) (u + γ) = S (IR I) u + 2 * Hf u γ + Hf γ γ := by
    intro u
    unfold S
    rw [← hstar u, ← hstar γ, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hzadd]
    ring
  have hHC : ∀ a c : Vsp X.dim, HC (fun _ : Fin 1 => a) (fun _ => c) = Hf a c := by
    intro a c
    unfold HC Hf
    simp
  have hsec : s (fun _ => w + γ) =
      Complex.exp (↑Real.pi * Hf w γ + ↑Real.pi * Hf γ γ / 2) * s (fun _ => w) := by
    have h := (show Differentiable ℂ s ∧ _ from hs).2 (fun _ => γ) (fun _ => hI.le hγI) (fun _ => w)
    simpa [hHC, hI.eps γ hγI, Pi.add_def] using h
  unfold zmG
  rw [hsec, hS w]
  rw [show ∀ (a c d : ℂ), Complex.exp a * c * Complex.exp d = c * Complex.exp (a + d) from
    fun a c d => by rw [Complex.exp_add]; ring]
  congr 2
  ring

theorem fib_periodic (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) :
    zmG I s (v + tb hI (t + fun i => (n i : ℝ))) = zmG I s (v + tb hI t) := by
  rw [tb_add, ← add_assoc]
  exact zmG_add_mem_of_isSplit hI hs _ _ (tb_int hI n)

theorem zeroMode_add_realSpan (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) {a : Vsp X.dim} (ha : a ∈ IR I) : zmC hI s 0 (v + a) = zmC hI s 0 v := by
  set c := (Ib hI).repr ⟨a, ha⟩ with hc
  have hac : a = tb hI (fun i => c i) := by
    have h := congrArg Subtype.val ((Ib hI).sum_repr ⟨a, ha⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [tb]; exact h.symm
  simp only [zmC_eq, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, mul_zero,
    neg_zero, Complex.exp_zero, one_mul]
  have hsh := tof_box_shift (fun t => zmG I s (v + tb hI t)) (fib_continuous hI hs v)
    (fun t n => fib_periodic hI hs v t n) (fun i => c i)
  rw [zmBox]
  rw [← hsh]
  congr 1
  funext t
  rw [hac, add_assoc, ← tb_add, add_comm t]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Count
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

theorem c_le_DF (j : Fin nb) (hi : 1 ≤ (bs j).i) : (bs j).c ≤ DF bs := by
  unfold DF
  exact le_trans (Nat.le_mul_of_pos_left _ hi)
    (Finset.single_le_sum (f := fun j => (bs j).i * (bs j).c) (fun j _ => Nat.zero_le _) (Finset.mem_univ j))

theorem card_choice_le (r : ℕ) (hr : ∀ j, (bs j).i ≤ r) :
    Fintype.card (Choice bs) ≤ r ^ DF bs := by
  unfold DF
  rw [Fintype.card_pi, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
  intro j _
  rw [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin, pow_mul]
  exact Nat.pow_le_pow_left (le_trans (Nat.factorial_le_pow _) (Nat.pow_le_pow_left (hr j) _)) _

theorem prod_two_pow :
    ∏ p : (Σ j : Fin nb, Fin (bs j).i), (2 : ℝ) ^ (bs p.1).c = 2 ^ DF bs := by
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  unfold DF
  congr 1
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem card_pos_le : Fintype.card (Σ j : Fin nb, Fin (bs j).i) ≤ DF bs := by
  rw [Fintype.card_sigma]
  unfold DF
  exact Finset.sum_le_sum (fun j _ => by rw [Fintype.card_fin]; exact Nat.le_mul_of_pos_right _ (bs j).hc)

theorem card_pos_pos (h : 1 ≤ DF bs) : 1 ≤ Fintype.card (Σ j : Fin nb, Fin (bs j).i) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  by_contra hc
  push_neg at hc
  have h0 : ∀ j, (bs j).i = 0 := by
    intro j
    have := Finset.single_le_sum (f := fun j => (bs j).i) (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  unfold DF at h
  simp [h0] at h

theorem prod_det_ge (d : ∀ j : Fin nb, ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hd : ∀ j, 1 ≤ (bs j).i → δ ≤ d j) (hd1 : ∀ j, (bs j).i = 0 → d j = 1) :
    δ ^ DF bs ≤ ∏ j, d j ^ (bs j).c := by
  unfold DF
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun j _ => pow_nonneg hδ0 _)
  intro j _
  by_cases hi : (bs j).i = 0
  · rw [hi, zero_mul, pow_zero, hd1 j hi, one_pow]
  · have hi1 : 1 ≤ (bs j).i := Nat.one_le_iff_ne_zero.mpr hi
    calc δ ^ ((bs j).i * (bs j).c) ≤ δ ^ (bs j).c :=
          pow_le_pow_of_le_one hδ0 hδ1 (Nat.le_mul_of_pos_left _ hi1)
      _ ≤ d j ^ (bs j).c := pow_le_pow_left₀ hδ0 (hd j hi1) _

end Count

section Data
variable [IsCMField E] (X : PT E) (bs : Fin nb → Block E n X.dim)

open Classical in
theorem block_data_all (hx : Ext.All) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) (P : Par X (DF bs)) (I : Submodule ℤ (Vsp X.dim)) (hI : IsSplit P I)
    (j : Fin nb) :
    ∃ (y : Fin (bs j).i → Vsp X.dim) (s : Fin (bs j).i → (Fin 1 → Vsp X.dim) → ℂ)
      (μ : Fin (bs j).i → ℂ),
      (∀ b, s b ∈ X.Sec P.q 1) ∧
      (∀ b (xs : Fin (bs j).c → Vsp X.dim), (∀ k, InPart (bs j).τ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 (s b) (bs j).c xs - μ b * ∏ k, Hf (xs k) (y b)‖ ≤ P.eps1 * ‖μ b‖) ∧
      (∀ b, P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (s b) ≤
        ‖μ b‖ ^ 2) ∧
      (∀ b, ‖y b‖ ≤ 2) ∧
      (2 : ℝ) ^ (-(X.r : ℝ) / 2) / 2 ≤
        ‖(Matrix.of fun a b => Hf (EuclideanSpace.single
          (⟨(bs j).τ, Fin.castLE (bs j).hi a⟩ : Idx X.dim) (1 : ℂ)) (y b)).det‖ ∧
      (∀ b, μ b ≠ 0) := by
  rcases Nat.eq_zero_or_pos (bs j).i with h0 | hpos
  · haveI : IsEmpty (Fin (bs j).i) := by rw [h0]; infer_instance
    refine ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, fun b => isEmptyElim b,
      isEmptyElim, isEmptyElim, ?_, isEmptyElim⟩
    rw [Matrix.det_isEmpty, norm_one]
    have h1 : (2 : ℝ) ^ (-(X.r : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have := Nat.cast_nonneg (α := ℝ) X.r; linarith)
    linarith
  · exact block_data hx hc ht ha X P I hI (bs j).τ (bs j).i (bs j).hi (bs j).c (c_le_DF bs j hpos)

end Data

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Cols
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

def colB (p : Σ j : Fin nb, Fin (bs j).i) : Fin n := (bs p.1).col p.2

variable {bs}

theorem colB_inj (hD : Disj bs) : Function.Injective (colB bs) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  by_cases hj : j = j'
  · subst hj
    have ha : a = a' := (bs j).col_inj h
    subst ha
    rfl
  · exact absurd h (hD j j' hj a a')

variable (bs)


open Classical in
def owner (k : Fin n) : Option (Σ j : Fin nb, Fin (bs j).i) :=
  if h : ∃ p, colB bs p = k then some h.choose else none

variable {bs}

theorem owner_colB (hD : Disj bs) (p : Σ j : Fin nb, Fin (bs j).i) : owner bs (colB bs p) = some p := by
  have h' : ∃ q, colB bs q = colB bs p := ⟨p, rfl⟩
  rw [owner, dite_eq_left h']
  exact congrArg some (colB_inj hD h'.choose_spec)

theorem colB_of_owner {k : Fin n} {p : Σ j : Fin nb, Fin (bs j).i} (h : owner bs k = some p) :
    colB bs p = k := by
  by_cases h' : ∃ q, colB bs q = k
  · rw [owner, dite_eq_left h'] at h
    obtain rfl := Option.some_injective _ h
    exact h'.choose_spec
  · rw [owner, dite_eq_right h'] at h
    cases h

theorem owner_eq_none {k : Fin n} (h : ∀ p, colB bs p ≠ k) : owner bs k = none := by
  rw [owner, dite_eq_right (show ¬∃ q, colB bs q = k from fun ⟨q, hq⟩ => h q hq)]

theorem owner_none_iff (hD : Disj bs) (k : Fin n) : owner bs k = none ↔ ∀ p, colB bs p ≠ k := by
  refine ⟨fun h p hp => ?_, owner_eq_none⟩
  subst hp
  rw [owner_colB hD] at h
  cases h

theorem prod_cols {M : Type*} [CommMonoid M] (hD : Disj bs) (f : Fin n → M) :
    ∏ k, f k = (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), f k) * ∏ p, f (colB bs p) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => owner bs k = none)]
  congr 1
  rw [← Finset.prod_image (s := Finset.univ) (g := colB bs) (by
    intro a _ b _ h
    exact colB_inj hD h)]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, owner_none_iff hD,
    not_forall, ne_eq, not_not]

end Cols

section Letters
variable (X : PT E) {bs : Fin nb → Block E n X.dim}

theorem filter_positions (hD : Disj bs) (T : Choice bs) (p : Σ j : Fin nb, Fin (bs j).i) :
    (Multiset.map (letter bs T) Finset.univ.val).filter (fun l => l.1 = colB bs p) =
      Multiset.map (fun r : Fin (bs p.1).c => letter bs T ⟨p.1, (r, p.2)⟩) Finset.univ.val := by
  obtain ⟨j0, a0⟩ := p
  rw [Multiset.filter_map]
  calc _ = Multiset.map (letter bs T)
        (Multiset.map (fun r : Fin (bs j0).c => (⟨j0, (r, a0)⟩ : Slot bs)) Finset.univ.val) := by
        congr 1
        refine (Multiset.Nodup.ext (Finset.univ.nodup.filter _)
          (Finset.univ.nodup.map (fun r r' h => by simpa using h))).2 ?_
        rintro ⟨j, r, a⟩
        simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, Function.comp,
          Multiset.mem_map]
        constructor
        · intro h
          have hja : (⟨j, a⟩ : Σ j : Fin nb, Fin (bs j).i) = ⟨j0, a0⟩ := colB_inj hD h
          cases hja
          exact ⟨r, rfl⟩
        · rintro ⟨r', h⟩
          cases h
          rfl
    _ = _ := by rw [Multiset.map_map]; rfl

open Classical in
theorem colL_block (hD : Disj bs) (T : Choice bs) (p : Σ j : Fin nb, Fin (bs j).i) :
    ((colL (lst X bs T) (colB bs p) : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
      Multiset.map (fun r : Fin (bs p.1).c => EuclideanSpace.single
        (⟨(bs p.1).τ, Fin.castLE (bs p.1).hi (T p.1 r p.2)⟩ : Idx X.dim) (1 : ℂ)) Finset.univ.val := by
  have hc : ∀ (L : List (Fin n × Vsp X.dim)) (k : Fin n),
      ((colL L k : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
        Multiset.map Prod.snd (Multiset.filter (fun x => x.1 = k) (L : Multiset _)) := by
    intro L k
    simp [colL]
  rw [hc, lst, ← Multiset.map_coe, Multiset.coe_toList, Multiset.filter_map, Multiset.map_map]
  have h2 := congrArg (Multiset.map (fun l : Letter n X.dim => EuclideanSpace.single l.2 (1 : ℂ)))
    (filter_positions X hD T p)
  rw [Multiset.map_map] at h2
  convert h2 using 2
  all_goals first
    | rfl
    | exact Multiset.filter_congr fun _ _ => Iff.rfl

theorem colL_empty (hD : Disj bs) (T : Choice bs) {k : Fin n} (hk : owner bs k = none) :
    colL (lst X bs T) k = [] := by
  rw [owner_none_iff hD] at hk
  unfold colL
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx
  unfold lst at hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨t, -, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toList.1 hl)
  intro h
  exact hk ⟨t.1, t.2.2⟩ (of_decide_eq_true h)

end Letters

end

end ReciprocityTheory.ChartRestriction.G.I2
end
