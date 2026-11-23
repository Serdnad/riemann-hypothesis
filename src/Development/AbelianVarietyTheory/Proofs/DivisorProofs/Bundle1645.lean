module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsion_point_comp_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left) (f : A ⟶ A) (N : ℕ), M.IsLB → 1 ≤ N →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) → y ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ≫ f = 1 := by
  intro A _ hA M f N hM hN hf T x hx hgen
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.Scheme.hom_ext_of_forall
  intro t
  obtain ⟨U, y, htU, hU⟩ := GlobalTheory.T.torsionPoint_locally_constant_complexAbelian A hA N hN T x hx t
  have hy : y ≫ f = 1 := hf y (GlobalTheory.T.hasGenerator_lambdaPullback_complexPoint_of_eqOnOpen A hA M hM T x U y t htU hU hgen)
  refine ⟨U, htU, ?_⟩
  have h1 : (1 : T ⟶ A) = toUnit T ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) := (comp_one _).symm
  have h2 : (toUnit T).left = T.hom := by
    simpa using Over.w (toUnit T)
  rw [h1, ← hy]
  simp only [Over.comp_left, h2]
  rw [← Category.assoc, hU, Category.assoc, Category.assoc]

end GlobalTheory
end
end

section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n), ∃ (N : ℕ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧ (∀ j, tsupport (χ j) ⊆ (A.e (c j)).source) ∧ ∀ y, ∑ j, χ j y = 1 := by
  first | exact @GlobalTheory.exists_finite_smooth_partition_holAtlas | exact GlobalTheory.exists_finite_smooth_partition_holAtlas | (intros; apply GlobalTheory.exists_finite_smooth_partition_holAtlas <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm.ChernDbar

variable {n : ℕ}

theorem dbar_dbar_comm {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (v w : V n) :
    dbar (fun x => dbar u x v) z w = dbar (fun x => dbar u x w) z v := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e (a b : V n) : dbar (fun x => dbar u x a) z b = (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ u) z b a
      + Complex.I * fderiv ℝ (fderiv ℝ u) z (Complex.I • b) a + Complex.I * fderiv ℝ (fderiv ℝ u) z b (Complex.I • a)
      - fderiv ℝ (fderiv ℝ u) z (Complex.I • b) (Complex.I • a)) := by
    have e0 : (fun x => dbar u x a) = fun x => (1 / 2 : ℂ) • (fderiv ℝ u x a + Complex.I • fderiv ℝ u x (Complex.I • a)) :=
      funext fun x => dbar_apply u x a
    rw [e0, dbar_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul Complex.I)),
      dbar_add (h1 _) ((h1 _).fun_const_smul Complex.I), dbar_const_smul _ (h1 _)]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, dbar_apply,
      fderiv_fderiv_apply hu, smul_eq_mul]
    linear_combination (1 / 4 : ℂ) * fderiv ℝ (fderiv ℝ u) z (Complex.I • b) (Complex.I • a) * Complex.I_mul_I
  rw [e, e, hs.eq w v, hs.eq (Complex.I • w) v, hs.eq w (Complex.I • v), hs.eq (Complex.I • w) (Complex.I • v)]
  ring

theorem dbarAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {g : ι → V n → ℂ} (hg : ∀ p, DifferentiableAt ℝ (g p) v)
    (c : ι → Alt n) : dbarAt (fun x => ∑ p, g p x • c p) v =
      ∑ a, ∑ p, dbar (g p) v (coordVec a) • (dzb a * c p) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  have : coefwise (fun f => dbar f v (coordVec a)) (fun x => ∑ p, g p x • c p) =
      ∑ p, dbar (g p) v (coordVec a) • c p := by
    refine (bas n).ext_elem fun S => ?_
    rw [FormMul.repr_coefwise]

    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [dbar_sum (A := fun p x => g p x * (bas n).repr (c p) S) (fun p _ => (hg p).mul (differentiableAt_const _)),
      ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dbar_mul (hg p) (differentiableAt_const _)]
    simp
  rw [this, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem differentiableAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {g : ι → V n → ℂ}
    (hg : ∀ p, DifferentiableAt ℝ (g p) v) (c : ι → Alt n) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun x => (bas n).repr (∑ p, g p x • c p) S) v := by

  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact DifferentiableAt.fun_sum fun p _ => (hg p).mul (differentiableAt_const _)

theorem dbarAt_add {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    dbarAt (fun x => F x + G x) v = dbarAt F v + dbarAt G v := by
  simp only [dbarAt, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun a _ => congrArg _ ((bas n).ext_elem fun S => ?_)
  simp only [map_add (f := _), Finsupp.add_apply, FormMul.repr_coefwise]
  rw [dbar_add (hF S) (hG S), ContinuousLinearMap.add_apply]

theorem dbarAt_const (c : Alt n) (v : V n) : dbarAt (fun _ => c) v = 0 := by
  simp [dbarAt, coefwise]

def IsClosedAt (v : V n) (F : V n → Ev n) : Prop :=
  (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧ dbarAt (fun x => (F x : Alt n)) v = 0

theorem isClosedAt_const (v : V n) (c : Ev n) : IsClosedAt v fun _ => c :=
  ⟨fun _ => differentiableAt_const _, dbarAt_const _ _⟩

def closedAt (v : V n) : Subsemiring (V n → Ev n) where
  carrier := {F | IsClosedAt v F}
  mul_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · rw [show (fun x => (bas n).repr ((F * G) x : Alt n) S) = _ from
        funext fun x => FormMul.repr_mul (F x : Alt n) (G x : Alt n) S]
      exact DifferentiableAt.fun_sum fun p _ => ((hF _).mul (hG _)).mul (differentiableAt_const _)
    · obtain ⟨y, hy⟩ := FormMul.dbarAt_mul hF hG
      simp only [Pi.mul_apply, Subalgebra.coe_mul]
      rw [hy, hF0, hG0, zero_mul, mul_zero, add_zero]
  one_mem' := isClosedAt_const v 1
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.add_apply, Subalgebra.coe_add, map_add (f := _), Finsupp.add_apply]
      exact (hF S).add (hG S)
    · simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [dbarAt_add hF hG, hF0, hG0, add_zero]
  zero_mem' := isClosedAt_const v 0

theorem const_mem (v : V n) (c : Ev n) : (fun _ => c) ∈ closedAt v := isClosedAt_const v c

def closedRing (v : V n) : Subring (V n → Ev n) :=
  { closedAt v with
    neg_mem' := fun {F} hF => by
      have := (closedAt v).mul_mem (const_mem v (-1)) hF
      have e : (fun _ => (-1 : Ev n)) * F = -F := funext fun x => neg_one_mul _
      rwa [e] at this }

theorem dzb_dz_dzb (a b c : Fin n) : dzb c * (dz a * dzb b) = -(dzb b * (dz a * dzb c)) := by
  have h (b c : Fin n) : dzb c * (dz a * dzb b) = dz a * dzb b * dzb c :=
    Subalgebra.mem_center_iff.1 (sym (a, b)).2 (dzb c)
  rw [h, h, mul_assoc, mul_assoc, ← mul_neg]
  exact congrArg _ (eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _))

theorem dbar_form_mem {v : V n} {θ : Fin n → V n → ℂ} (hθ : ∀ a, ContDiffAt ℝ 2 (θ a) v) :
    (fun x => ∑ a, ∑ b, dbar (θ a) x (coordVec b) • sym (a, b)) ∈ closedRing v := by
  have e (x : V n) : ((∑ a, ∑ b, dbar (θ a) x (coordVec b) • sym (a, b) : Ev n) : Alt n) =
      ∑ p : Fin n × Fin n, dbar (θ p.1) x (coordVec p.2) • (dz p.1 * dzb p.2) := by
    simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, sym, Fintype.sum_prod_type]
  have hd (p : Fin n × Fin n) : DifferentiableAt ℝ (fun x => dbar (θ p.1) x (coordVec p.2)) v :=
    differentiableAt_dbar_apply (hθ p.1) _
  change IsClosedAt v _
  refine ⟨fun S => ?_, ?_⟩
  · simp only [e]
    exact differentiableAt_sum_smul hd _ S
  · simp only [e]
    rw [dbarAt_sum_smul hd]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    set s : Alt n := ∑ c, ∑ b, dbar (fun x => dbar (θ a) x (coordVec b)) v (coordVec c) • (dzb c * (dz a * dzb b))
      with hs
    have h2 : s = -s := by
      conv_lhs => rw [hs, Finset.sum_comm]
      rw [hs, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dzb_dz_dzb a b c, dbar_dbar_comm (hθ a), smul_neg]
    have h3 : (2 : ℂ) • s = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 h2
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

theorem coeff_charpolyRev_map {A B r : Type} [CommRing A] [CommRing B] [Fintype r] [DecidableEq r] (f : A →+* B)
    (M : Matrix r r A) (j : ℕ) : (M.map f).charpolyRev.coeff j = f (M.charpolyRev.coeff j) := by
  rw [← Polynomial.coeff_map, charpolyRev, charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  apply congrArg (fun p : Polynomial B => p.coeff j)
  apply congrArg Matrix.det
  ext i k
  by_cases h : i = k <;> simp [h, Matrix.one_apply]

theorem dbarAt_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)),
    IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s,
    dbarAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  intro n r _ _ H s hs hH hu j v hv
  have h3 : MContDiffAt 3 H v := fun a b => ((hH a b).contDiffAt (hs.mem_nhds hv)).of_le (by norm_cast)
  have hθ (i k : r) (a : Fin n) : ContDiffAt ℝ 2 (fun x => conn H x (coordVec a) i k) v :=
    h3.conn (hu v hv) (by norm_num) (coordVec a) i k
  let M : Matrix r r (closedRing v) := Matrix.of fun i k => ⟨_, dbar_form_mem (hθ i k)⟩
  have key (w : V n) : MvPolynomial.aeval sym (chernPoly H w j) = (M.charpolyRev.coeff j : V n → Ev n) w := by
    have h1 := coeff_charpolyRev_map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom (-curvPoly H w) j
    have h2 := coeff_charpolyRev_map ((Pi.evalRingHom (fun _ : V n => Ev n) w).comp (closedRing v).subtype) M j
    refine h1.symm.trans (Eq.trans ?_ h2)
    apply congrArg (fun N : Matrix r r (Ev n) => N.charpolyRev.coeff j)
    ext i k
    simp [M, curvPoly, curv, Algebra.smul_def]
  have hm : IsClosedAt v _ := (closedRing v).mul_mem (const_mem v (algebraMap ℂ _ (kappa ^ j))) (M.charpolyRev.coeff j).2
  have e : (fun w => (chernAt H w j : Alt n)) = fun w =>
      ((algebraMap ℂ (Ev n) (kappa ^ j) * (M.charpolyRev.coeff j : V n → Ev n) w : Ev n) : Alt n) :=
    funext fun w => by rw [chernAt, key, Algebra.smul_def]
  rw [e]
  exact hm.2

end GlobalTheory.CxForm.ChernDbar
end
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.FormMul

theorem leibniz_of_comm : ∀ (n : ℕ) (F G : V n → Alt n) (v : V n) (F' : Alt n),
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
    ((∀ a, dz a * F v = F' * dz a) → delAt (fun x => F x * G x) v = delAt F v * G v + F' * delAt G v) ∧
    ((∀ a, dzb a * F v = F' * dzb a) → dbarAt (fun x => F x * G x) v = dbarAt F v * G v + F' * dbarAt G v) := by
  intro n F G v F' hF hG
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold delAt
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_mul (T := fun f => del f v (coordVec a))
      (fun f hf => by rw [del_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
      (fun f g hf hg => del_mul hf hg _) (fun c => by rw [del_const]; rfl) hF hG]
    simp only [mul_add, ← mul_assoc, h]
  · unfold dbarAt
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_mul (T := fun f => dbar f v (coordVec a))
      (fun f hf => by rw [dbar_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
      (fun f g hf hg => dbar_mul hf hg _) (fun c => by rw [dbar_const]; rfl) hF hG]
    simp only [mul_add, ← mul_assoc, h]

end GlobalTheory.CxForm.FormMul
end
end

section

open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.contDiffOn_chernFormOfGramMatrixAt_coefficients : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (bas n).repr (chernAt H v j : Alt n) S) s := by
  first | exact @GlobalTheory.ChernSmooth.contDiffOn_chernAt | exact GlobalTheory.ChernSmooth.contDiffOn_chernAt | (intros; apply GlobalTheory.ChernSmooth.contDiffOn_chernAt <;> assumption)
end

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

theorem _root_.GlobalTheory.T.del_loc_repr_contDiffOn_target : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → ∀ (i : A.ι) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S) (A.e i).target := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn | exact GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn | (intros; apply GlobalTheory.CxForm.HolAtlas.del_loc_repr_contDiffOn <;> assumption)
end

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm

variable {n : ℕ}

theorem differentiableAt_repr_map_toLin' {M : V n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {v : V n}
    (hM : ∀ i j, DifferentiableAt ℝ (fun w => M w i j) v) (γ : Alt n) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun w => (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) γ) S) v := by
  induction γ using ExteriorAlgebra.induction generalizing S with
  | algebraMap r =>
    simp only [AlgHom.commutes]
    exact differentiableAt_const _
  | ι x =>
    simp only [ExteriorAlgebra.map_apply_ι]
    let ℓ : (Fin n ⊕ Fin n → ℂ) →ₗ[ℂ] ℂ :=
      Finsupp.lapply S ∘ₗ (bas n).repr.toLinearMap ∘ₗ ExteriorAlgebra.ι ℂ
    have hu : DifferentiableAt ℝ (fun w => Matrix.toLin' (M w) x) v := by
      simp only [Matrix.toLin'_apply]
      refine differentiableAt_pi.2 fun i => ?_
      simp only [mulVec, dotProduct]
      exact DifferentiableAt.fun_sum fun j _ => (hM i j).mul_const _
    exact ((LinearMap.toContinuousLinearMap ℓ).restrictScalars ℝ).differentiableAt.comp v hu
  | mul a b ha hb =>
    have e : (fun w => (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) (a * b)) S) = fun w =>
        ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)), (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) a) p.1 *
          (bas n).repr (ExteriorAlgebra.map (Matrix.toLin' (M w)) b) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
      funext fun w => by rw [map_mul, FormMul.repr_mul]
    rw [e]
    exact DifferentiableAt.fun_sum fun p _ => ((ha p.1).mul (hb p.2)).mul_const _
  | add a b ha hb =>
    simp only [map_add (f := _), Finsupp.add_apply]
    exact (ha S).add (hb S)

theorem differentiableAt_repr_pull_fderiv : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n}
    {v : ReciprocityTheory.L2DbarEstimates.V n}, ContDiffAt ℂ 2 φ v → ∀ (γ : GlobalTheory.CxForm.Alt n) (S : Finset (Fin (n + n))),
    DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.pull (fderiv ℂ φ w) γ) S) v := by
  intro n φ v h γ S
  have hd : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (b a : Fin n) : DifferentiableAt ℝ (fun w => fderiv ℂ φ w (coordVec b) a) v :=
    (((EuclideanSpace.proj a : V n →L[ℂ] ℂ).differentiableAt).comp v
      (hd.clm_apply (differentiableAt_const (coordVec b)))).restrictScalars ℝ
  have hc (b a : Fin n) : DifferentiableAt ℝ (fun w => conj (fderiv ℂ φ w (coordVec b) a)) v :=
    Complex.conjCLE.differentiableAt.comp v (he b a)
  refine differentiableAt_repr_map_toLin' (M := fun w => fromBlocks (of fun b a => fderiv ℂ φ w (coordVec b) a) 0 0
    (of fun b a => conj (fderiv ℂ φ w (coordVec b) a))) ?_ γ S
  rintro (i | i) (j | j)
  · simpa only [fromBlocks_apply₁₁, of_apply] using he i j
  · simp only [fromBlocks_apply₁₂, Matrix.zero_apply]; exact differentiableAt_const _
  · simp only [fromBlocks_apply₂₁, Matrix.zero_apply]; exact differentiableAt_const _
  · simpa only [fromBlocks_apply₂₂, of_apply] using hc i j

end GlobalTheory.CxForm
end
end

section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.holAtlas_del_finset_sum : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld), (∀ j, A.IsForm (α j)) → A.del (∑ j, α j) = ∑ j, A.del (α j) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_finset_sum | exact GlobalTheory.CxForm.HolAtlas.del_finset_sum | (intros; apply GlobalTheory.CxForm.HolAtlas.del_finset_sum <;> assumption)
end

section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero : ∀ {n : ℕ} (F : V n → GlobalTheory.CxForm.Alt n), (∀ S, ContDiff ℝ 1 (fun v => (GlobalTheory.CxForm.bas n).repr (F v) S)) → HasCompactSupport F → ∫ v, (GlobalTheory.CxForm.dens (GlobalTheory.CxForm.dbarAt F v)).re = 0 := by
  first | exact @GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero | exact GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero | (intros; apply GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero <;> assumption)
end

section

open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernFormOfGramMatrixAt_holomorphic_frameChange : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H K A : V n → Matrix r r ℂ) (v : V n), MContDiffAt 2 K v → IsUnit (K v).det → (∀ i j, AnalyticAt ℂ (fun w => A w i j) v) → IsUnit (A v).det → (H =ᶠ[𝓝 v] fun w => chg (A w) (K w)) → ∀ j, chernAt H v j = chernAt K v j := by
  first | exact @GlobalTheory.CxForm.chernAt_changeFrame | exact GlobalTheory.CxForm.chernAt_changeFrame | (intros; apply GlobalTheory.CxForm.chernAt_changeFrame <;> assumption)
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.contDiffOn_coefficients_complexForm_mul : ∀ (n m : ℕ) (F G : V m → Alt n),
    (∀ s : Set (V m), (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
      (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (G v) S) s) →
      ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v * G v) S) s) ∧
    (∀ v : V m, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x * G x) S) v) := by
  first | exact @GlobalTheory.CxForm.contDiff_coeff_mul | exact GlobalTheory.CxForm.contDiff_coeff_mul | (intros; apply GlobalTheory.CxForm.contDiff_coeff_mul <;> assumption)
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local : ∀ (n : ℕ) (v : V n),
    (∀ F G : V n → Alt n, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      delAt (fun x => F x + G x) v = delAt F v + delAt G v ∧ dbarAt (fun x => F x + G x) v = dbarAt F v + dbarAt G v) ∧
    (∀ (F : V n → Alt n) (c : ℂ), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      delAt (fun x => c • F x) v = c • delAt F v ∧ dbarAt (fun x => c • F x) v = c • dbarAt F v) ∧
    (∀ (ι : Type) (t : Finset ι) (F : ι → V n → Alt n),
      (∀ i ∈ t, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) →
      delAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, delAt (F i) v ∧ dbarAt (fun x => ∑ i ∈ t, F i x) v = ∑ i ∈ t, dbarAt (F i) v) ∧
    (∀ F G : V n → Alt n, F =ᶠ[𝓝 v] G → delAt F v = delAt G v ∧ dbarAt F v = dbarAt G v) ∧
    (∀ c : Alt n, delAt (fun _ => c) v = 0 ∧ dbarAt (fun _ => c) v = 0) := by
  first | exact @GlobalTheory.CxForm.delAt_dbarAt_linear_local | exact GlobalTheory.CxForm.delAt_dbarAt_linear_local | (intros; apply GlobalTheory.CxForm.delAt_dbarAt_linear_local <;> assumption)
end
