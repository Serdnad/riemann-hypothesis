module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.CxForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DensPow

variable {n : ℕ}

theorem ι_mul_ι_mul_ι_mul_ι_left (u w w' : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w') = (0 : Alt n) := by
  have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) w u)
  calc _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) * ExteriorAlgebra.ι ℂ w' := by
          simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ w') := by
          rw [h]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

theorem ι_mul_ι_mul_ι_mul_ι_right (u u' w : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ u' * ExteriorAlgebra.ι ℂ w) = (0 : Alt n) := by
  have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) w u')
  calc _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u') * ExteriorAlgebra.ι ℂ w := by
          simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ u' * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ w)) := by
          rw [h]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

def row (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n where
  toFun w := ∑ b, w b • sym (a, b)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum, smul_smul]

theorem coe_row (a : Fin n) (w : Fin n → ℂ) :
    (row a w : Alt n) = dz a * ExteriorAlgebra.ι ℂ (∑ b, w b • Pi.single (Sum.inr b) (1 : ℂ)) := by
  simp [row, sym, dzb, Finset.mul_sum, mul_smul_comm]

theorem row_mul_row (a : Fin n) (w : Fin n → ℂ) : row a w * row a w = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_row, dz]
  exact ι_mul_ι_mul_ι_mul_ι_left _ _ _

theorem row_mul_row_of_ne {a a' : Fin n} (w : Fin n → ℂ) : row a w * row a' w = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_row, coe_row, dz, dz]
  exact ι_mul_ι_mul_ι_mul_ι_right _ _ _

def altRows (n : ℕ) : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] Ev n where
  toMultilinearMap := (MultilinearMap.mkPiAlgebra ℂ (Fin n) (Ev n)).compLinearMap row
  map_eq_zero_of_eq' v i j hij hne := by
    change ∏ a, row a (v a) = 0
    rw [← Finset.mul_prod_erase Finset.univ (fun a => row a (v a)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (fun a => row a (v a))
        (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩), ← mul_assoc, hij, row_mul_row_of_ne, zero_mul]

theorem altRows_apply (v : Fin n → Fin n → ℂ) : altRows n v = ∏ a, row a (v a) := by
  first
  | rfl
  | simp only [altRows, AlternatingMap.coe_mk, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

theorem alt_eq_det_smul {K M N : Type} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {m : ℕ} (e : Module.Basis (Fin m) K M)
    (f : M [⋀^Fin m]→ₗ[K] N) (h : Fin m → M) : f h = e.det h • f e := by
  have key : f = (LinearMap.toSpanSingleton K N (f e)).compAlternatingMap e.det := by
    refine e.ext_alternating (fun v hv => ?_)
    have hb : Function.Bijective v := Finite.injective_iff_bijective.1 hv
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective v hb
    have hσ : (fun i => e (v i)) = (⇑e) ∘ ⇑σ := rfl
    rw [hσ, LinearMap.compAlternatingMap_apply, LinearMap.toSpanSingleton_apply,
      AlternatingMap.map_perm, AlternatingMap.map_perm, e.det_self, Units.smul_def,
      Units.smul_def, smul_one_smul]
  rw [DFunLike.congr_fun key h]
  rfl

theorem prod_row (H : Matrix (Fin n) (Fin n) ℂ) : ∏ a, row a (H a) = H.det • ∏ a, sym (a, a) := by
  have h1 : ∏ a, row a (H a) = altRows n (fun a b => H a b) := (altRows_apply _).symm
  rw [h1, alt_eq_det_smul (Pi.basisFun ℂ (Fin n)), Pi.basisFun_det, altRows_apply]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  simp [row, Pi.single_apply]

theorem add_pow_of_mul_self {R : Type*} [CommRing R] {x : R} (hx : x * x = 0) (y : R) (m : ℕ) :
    (x + y) ^ (m + 1) = y ^ (m + 1) + ((m : R) + 1) * x * y ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((m : R) + 1) * y ^ m * hx

theorem sum_pow_card {R ι : Type*} [CommRing R] [DecidableEq ι] (f : ι → R) (hf : ∀ a, f a * f a = 0) (s : Finset ι) :
    (∀ m, (∑ a ∈ s, f a) ^ (s.card + 1 + m) = 0) ∧ (∑ a ∈ s, f a) ^ s.card = (s.card.factorial : R) * ∏ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun m => by simp, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine ⟨fun m => ?_, ?_⟩
    · rw [show s.card + 1 + 1 + m = (s.card + 1 + m) + 1 by omega, add_pow_of_mul_self (hf a),
        show s.card + 1 + m + 1 = s.card + 1 + (m + 1) by omega, ih.1, ih.1]
      simp
    · rw [add_pow_of_mul_self (hf a), show s.card + 1 = s.card + 1 + 0 by rfl, ih.1, ih.2, Nat.factorial_succ]
      push_cast
      ring

theorem dens_smul (c : ℂ) (x : Alt n) : dens (c • x) = c * dens x := by
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

theorem vol_eq_smul_prod (n : ℕ) : vol n = (Complex.I / 2) ^ n • ∏ a, sym (a, a) := by
  simp only [vol, Algebra.smul_def, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    map_pow]

theorem dens_pow (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CxForm.dens (((∑ a, ∑ b, H a b • GlobalTheory.CxForm.sym (a, b) : GlobalTheory.CxForm.Ev n) ^ n : GlobalTheory.CxForm.Ev n) :
      GlobalTheory.CxForm.Alt n) = (n.factorial : ℂ) * H.det / (Complex.I / 2) ^ n := by
  have hω : (∑ a, ∑ b, H a b • sym (a, b) : Ev n) = ∑ a, row a (H a) := by simp [row]
  have hp : (∑ a, row a (H a)) ^ n = (n.factorial : Ev n) * ∏ a, row a (H a) := by
    simpa using (sum_pow_card (fun a => row a (H a)) (fun a => row_mul_row a _) Finset.univ).2
  have hP : (n.factorial : Ev n) * ∏ a, row a (H a) = ((n.factorial : ℂ) * H.det) • ∏ a, sym (a, a) := by
    rw [prod_row, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h1 := dens_vol n
  rw [vol_eq_smul_prod, Subalgebra.coe_smul, dens_smul] at h1
  rw [hω, hp, hP, Subalgebra.coe_smul, dens_smul, div_eq_mul_inv, eq_inv_of_mul_eq_one_right h1]

end GlobalTheory.CxForm.DensPow

end
end

section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem dbarAt_congr {n : ℕ} {γ δ : V n → Alt n} {v : V n} (h : γ =ᶠ[𝓝 v] δ) :
    dbarAt γ v = dbarAt δ v := by
  unfold dbarAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS : (fun x => (bas n).repr (γ x) S) =ᶠ[𝓝 v] fun x => (bas n).repr (δ x) S := h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx
  show GlobalTheory.dbar _ v (coordVec a) • _ = GlobalTheory.dbar _ v (coordVec a) • _
  rw [GlobalTheory.dbar_congr hS]

end GlobalTheory.CxForm
end

section

open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm

theorem chernAt_changeFrame : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H K A : V n → Matrix r r ℂ) (v : V n), MContDiffAt 2 K v → IsUnit (K v).det → (∀ i j, AnalyticAt ℂ (fun w => A w i j) v) → IsUnit (A v).det → (H =ᶠ[𝓝 v] fun w => chg (A w) (K w)) → ∀ j, chernAt H v j = chernAt K v j := by
  intro n r _ _ H K A v hK hKu hg hAu hH j
  have hconj : ∀ (M P Q : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)), Q * P = 1 →
      (Q * M * P).charpolyRev = M.charpolyRev := by
    intro M P Q hQP
    have hQP' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
      rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
    have e : (1 : Matrix r r (Polynomial (MvPolynomial (Fin n × Fin n) ℂ))) -
        (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) • (Q * M * P).map Polynomial.C =
        Q.map Polynomial.C * (1 - (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) •
          M.map Polynomial.C) * P.map Polynomial.C := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP',
        Matrix.mul_smul, Matrix.smul_mul]
    rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
      ← Matrix.det_mul, hQP', Matrix.det_one, one_mul]
  have hsum : ∀ G : V n → Matrix r r ℂ, curvPoly G v =
      ∑ a, ∑ b, (MvPolynomial.X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
        (curv G v (coordVec a) (coordVec b)).map MvPolynomial.C := by
    intro G
    ext i j
    simp [curvPoly, Matrix.sum_apply, mul_comm]
  have hA : MContDiffAt 2 A v := fun a b => (hg a b).contDiffAt.restrict_scalars ℝ
  have hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0 := by
    have hev : ∀ᶠ x in 𝓝 v, ∀ a b, AnalyticAt ℂ (fun w => A w a b) x :=
      eventually_all.2 fun a => eventually_all.2 fun b => (hg a b).eventually_analyticAt
    filter_upwards [hev] with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b).differentiableAt]
    rfl
  have hGe : H =ᶠ[𝓝 v] fun u => (A u)ᵀ * K u * (A u)ᴴᵀ := hH
  have hcurv : ∀ ξ η, curv H v ξ η = (A v)⁻¹ * curv K v ξ η * A v :=
    fun ξ η => by rw [curv_congr hGe, curv_changeFrame hK hKu hA hAu hA0]
  have key : curvPoly H v = ((A v)⁻¹).map MvPolynomial.C * curvPoly K v * (A v).map MvPolynomial.C := by
    rw [hsum, hsum]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, hcurv]
  have key2 : chernPoly H v j = chernPoly K v j := by
    rw [chernPoly, chernPoly, key, show ∀ (Q M P : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)),
      -(Q * M * P) = Q * (-M) * P from fun Q M P => by rw [Matrix.mul_neg, Matrix.neg_mul], hconj]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hAu, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [chernAt, chernAt, key2]

end GlobalTheory.CxForm
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm

theorem bas_repr_mul (n : ℕ) (x y : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (x * y) S =
      ∑ T, ∑ U, (bas n).repr x T * (bas n).repr y U * (bas n).repr (bas n T * bas n U) S := by
  conv_lhs => rw [← (bas n).sum_repr x, ← (bas n).sum_repr y]

  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
  Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_comm

theorem contDiff_coeff_mul : ∀ (n m : ℕ) (F G : V m → Alt n),
    (∀ s : Set (V m), (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
      (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (G v) S) s) →
      ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v * G v) S) s) ∧
    (∀ v : V m, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x * G x) S) v) := by
  intro n m F G
  refine ⟨fun s hF hG S => ?_, fun v hF hG S => ?_⟩
  · rw [show (fun v => (bas n).repr (F v * G v) S) = _ from funext fun v => bas_repr_mul n (F v) (G v) S]
    exact ContDiffOn.sum fun T _ => ContDiffOn.sum fun U _ => ((hF T).mul (hG U)).mul contDiffOn_const
  · rw [show (fun x => (bas n).repr (F x * G x) S) = _ from funext fun x => bas_repr_mul n (F x) (G x) S]
    exact DifferentiableAt.fun_sum fun T _ => DifferentiableAt.fun_sum fun U _ =>
      ((hF T).fun_mul (hG U)).fun_mul (differentiableAt_const _)

end GlobalTheory.CxForm
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

noncomputable section

namespace GlobalTheory.CxForm

variable {n : ℕ}

theorem coefwise_add_of {T : (V n → ℂ) → ℂ} {F G : V n → Alt n}
    (h : ∀ S, T (fun x => (bas n).repr (F x) S + (bas n).repr (G x) S) =
      T (fun x => (bas n).repr (F x) S) + T (fun x => (bas n).repr (G x) S)) :
    coefwise T (fun x => F x + G x) = coefwise T F + coefwise T G := by
  simp only [coefwise, map_add (f := _), Finsupp.add_apply, h, add_smul, Finset.sum_add_distrib]

theorem coefwise_const_smul_of {T : (V n → ℂ) → ℂ} {F : V n → Alt n} (c : ℂ)
    (h : ∀ S, T (fun x => c • (bas n).repr (F x) S) = c • T (fun x => (bas n).repr (F x) S)) :
    coefwise T (fun x => c • F x) = c • coefwise T F := by
  simp only [coefwise, map_smul, Finsupp.smul_apply, h, Finset.smul_sum, smul_assoc]

theorem coefwise_sum_of {T : (V n → ℂ) → ℂ} {ι : Type} (t : Finset ι) {F : ι → V n → Alt n}
    (h : ∀ S, T (fun x => ∑ i ∈ t, (bas n).repr (F i x) S) = ∑ i ∈ t, T (fun x => (bas n).repr (F i x) S)) :
    coefwise T (fun x => ∑ i ∈ t, F i x) = ∑ i ∈ t, coefwise T (F i) := by

  simp only [coefwise, map_sum, Finsupp.finsetSum_apply, h, Finset.sum_smul]
  exact Finset.sum_comm

theorem delAt_dbarAt_linear_local : ∀ (n : ℕ) (v : V n),
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
  intro n v
  refine ⟨fun F G hF hG => ⟨?_, ?_⟩, fun F c hF => ⟨?_, ?_⟩, fun ι t F hF => ⟨?_, ?_⟩, fun F G h => ⟨?_, ?_⟩,
    fun c => ⟨?_, ?_⟩⟩
  · rw [delAt, delAt, delAt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_add_of fun S => by rw [GlobalTheory.del_add (hF S) (hG S)]; rfl, mul_add]
  · rw [dbarAt, dbarAt, dbarAt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_add_of fun S => by rw [GlobalTheory.dbar_add (hF S) (hG S)]; rfl, mul_add]
  · rw [delAt, delAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_const_smul_of c fun S => by rw [GlobalTheory.del_const_smul c (hF S)]; rfl, mul_smul_comm]
  · rw [dbarAt, dbarAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_const_smul_of c fun S => by rw [GlobalTheory.dbar_const_smul c (hF S)]; rfl, mul_smul_comm]
  · simp only [delAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_sum_of t fun S => by
      rw [GlobalTheory.del_sum fun i hi => hF i hi S, ContinuousLinearMap.sum_apply], Finset.mul_sum]
  · simp only [dbarAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_sum_of t fun S => by
      rw [GlobalTheory.dbar_sum fun i hi => hF i hi S, ContinuousLinearMap.sum_apply], Finset.mul_sum]
  · have e (S) : del (fun x => (bas n).repr (F x) S) v = del (fun x => (bas n).repr (G x) S) v :=
      GlobalTheory.del_congr (h.fun_comp fun y => (bas n).repr y S)
    simp only [delAt, coefwise, e]
  · have e (S) : dbar (fun x => (bas n).repr (F x) S) v = dbar (fun x => (bas n).repr (G x) S) v :=
      GlobalTheory.dbar_congr (h.fun_comp fun y => (bas n).repr y S)
    simp only [dbarAt, coefwise, e]
  · simp [delAt, coefwise]
  · simp [dbarAt, coefwise]

end GlobalTheory.CxForm
end
end

section

set_option autoImplicit false

noncomputable section

open Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate

namespace GlobalTheory.CxForm

open Module

variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

theorem exterior_repr_univ_of_mem {N k : ℕ} (b : Basis (Fin N) K M) (hk : k ≠ N) {x : ExteriorAlgebra K M}
    (hx : x ∈ ⋀[K]^k M) : b.ExteriorAlgebra.repr x Finset.univ = 0 := by
  rw [Basis.ExteriorAlgebra, Basis.repr_reindex_apply]
  have h1 : (Set.powersetCard.prodEquiv.symm (Finset.univ : Finset (Fin N))).1 = N := by
    simp [Set.powersetCard.prodEquiv]
  rcases e : Set.powersetCard.prodEquiv.symm (Finset.univ : Finset (Fin N)) with ⟨j, a⟩
  rw [e] at h1
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ (fun h => hk (h.trans h1)) hx

theorem exterior_repr_univ_map {N : ℕ} (b : Basis (Fin N) K M) (f : M →ₗ[K] M) (x : ExteriorAlgebra K M) :
    b.ExteriorAlgebra.repr (ExteriorAlgebra.map f x) Finset.univ =
      LinearMap.det f * b.ExteriorAlgebra.repr x Finset.univ := by
  have key : ∀ s, b.ExteriorAlgebra.repr (ExteriorAlgebra.map f (b.ExteriorAlgebra s)) Finset.univ =
      LinearMap.det f * b.ExteriorAlgebra.repr (b.ExteriorAlgebra s) Finset.univ := by
    intro s
    by_cases hs : s = Finset.univ
    · subst hs
      set g : M [⋀^Fin N]→ₗ[K] K :=
        (Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap).compAlternatingMap
          (ExteriorAlgebra.ιMulti K N) with hg
      have hb : ∀ w : Fin N → M, g w = b.ExteriorAlgebra.repr (ExteriorAlgebra.ιMulti K N w) Finset.univ := fun _ => rfl
      have he := AlternatingMap.eq_smul_basis_det b g
      rw [ExteriorAlgebra.basis_apply_ofCard _ (by simp : (Finset.univ : Finset (Fin N)).card = N)]
      dsimp only [ExteriorAlgebra.ιMulti_family]
      rw [ExteriorAlgebra.map_apply_ιMulti, ← hb, ← hb, he,
        AlternatingMap.smul_apply, AlternatingMap.smul_apply, Basis.det_comp, smul_eq_mul, smul_eq_mul]
      ring
    · have hc : s.card ≠ N := fun h => hs (Finset.eq_univ_of_card s (by simpa using h))
      rw [Basis.repr_self, Finsupp.single_apply, if_neg hs, mul_zero,
        ExteriorAlgebra.basis_apply]
      dsimp only [ExteriorAlgebra.ιMulti_family]
      rw [ExteriorAlgebra.map_apply_ιMulti]
      exact exterior_repr_univ_of_mem b hc (ExteriorAlgebra.ιMulti_range K _ ⟨_, rfl⟩)
  have := b.ExteriorAlgebra.ext
    (f₁ := Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ (ExteriorAlgebra.map f).toLinearMap)
    (f₂ := LinearMap.det f • (Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap))
    (fun s => by simpa using key s)
  simpa using LinearMap.congr_fun this x

theorem det_pull_gen {n : ℕ} (L : V n →L[ℂ] V n) :
    LinearMap.det (Matrix.toLin' (fromBlocks (of fun b a => L (coordVec b) a) 0 0
      (of fun b a => conj (L (coordVec b) a)))) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [LinearMap.det_toLin', det_fromBlocks_zero₂₁]
  have hP : (of fun b a => L (coordVec b) a).det = L.det := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis,
      ← det_transpose]
    congr 1
  have hQ : (of fun b a => conj (L (coordVec b) a)) = (starRingEnd ℂ).mapMatrix (of fun b a => L (coordVec b) a) := by
    ext i j; simp
  rw [hQ, ← RingHom.map_det, hP, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem dens_pull {n : ℕ} (L : V n →L[ℂ] V n) (ω : Alt n) :
    dens (pull L ω) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) * dens ω := by
  simp only [dens, pull, bas]
  rw [exterior_repr_univ_map, det_pull_gen, mul_div_assoc]

end GlobalTheory.CxForm
end
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm

theorem pull_comp_entry {k m n : ℕ} (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (b : Fin n) (a : Fin k) :
    (L' (L (coordVec b))).ofLp a = ∑ c, (L (coordVec b)).ofLp c * (L' (coordVec c)).ofLp a := by
  have hx : L (coordVec b) = ∑ c, (L (coordVec b)).ofLp c • (coordVec c : V m) := by
    simpa [coordVec] using (EuclideanSpace.basisFun (Fin m) ℂ).sum_repr (L (coordVec b)) |>.symm

  rw [hx, map_sum]
  simp [map_smul, PiLp.smul_apply]
  simp [Pi.single_apply]

theorem pull_comp (k m n : ℕ) (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (γ : Alt k) :
    pull (L'.comp L) γ = pull L (pull L' γ) := by
  have hM : (Matrix.fromBlocks (Matrix.of fun b a => ((L'.comp L) (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj (((L'.comp L) (coordVec b)).ofLp a)) : Matrix (Fin n ⊕ Fin n) (Fin k ⊕ Fin k) ℂ) =
      Matrix.fromBlocks (Matrix.of fun b a => (L (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj ((L (coordVec b)).ofLp a)) *
      Matrix.fromBlocks (Matrix.of fun b a => (L' (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj ((L' (coordVec b)).ofLp a)) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · ext b a; simp only [Matrix.of_apply, ContinuousLinearMap.comp_apply, pull_comp_entry]
      simp [Matrix.mul_apply]
    · simp
    · simp
    · ext b a

      simp only [Matrix.mul_apply, Matrix.of_apply, ContinuousLinearMap.comp_apply, pull_comp_entry, map_sum, map_mul]
      simp [Matrix.mul_apply]
  simp only [pull]
  rw [hM, Matrix.toLin'_mul, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

end GlobalTheory.CxForm
end
