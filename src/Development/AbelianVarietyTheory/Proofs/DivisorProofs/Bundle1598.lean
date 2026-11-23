module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.CuspidalMirabolic
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
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.FormMul

variable {n : ℕ}

theorem repr_mul (a b : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (a * b) S = ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
      (bas n).repr a p.1 * (bas n).repr b p.2 * (bas n).repr (bas n p.1 * bas n p.2) S := by
  conv_lhs => rw [← (bas n).sum_repr a, ← (bas n).sum_repr b]

  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_

  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_coefwise (T : (V n → ℂ) → ℂ) (H : V n → Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (coefwise T H) S = T (fun x => (bas n).repr (H x) S) := by

  simp [coefwise, map_sum, Finsupp.single_apply]

theorem coefwise_mul {v : V n} {T : (V n → ℂ) → ℂ}
    (hsum : ∀ f : Finset (Fin (n + n)) × Finset (Fin (n + n)) → V n → ℂ, (∀ p, DifferentiableAt ℝ (f p) v) →
      T (fun x => ∑ p, f p x) = ∑ p, T (f p))
    (hmul : ∀ f g : V n → ℂ, DifferentiableAt ℝ f v → DifferentiableAt ℝ g v →
      T (fun x => f x * g x) = f v * T g + T f * g v)
    (hconst : ∀ c : ℂ, T (fun _ => c) = 0)
    {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    coefwise T (fun x => F x * G x) = coefwise T F * G v + F v * coefwise T G := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (F x * G x) S) = fun x => ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
      (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
    funext fun x => repr_mul _ _ _
  rw [repr_coefwise, e, map_add (f := _), Finsupp.add_apply, repr_mul (coefwise T F), repr_mul (F v)]
  simp only [repr_coefwise]
  rw [hsum (fun p x => (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S)
    (fun p => ((hF p.1).mul (hG p.2)).mul (differentiableAt_const _)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hmul (fun x => (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2) (fun _ => (bas n).repr (bas n p.1 * bas n p.2) S)
    ((hF p.1).mul (hG p.2)) (differentiableAt_const _), hconst,
    hmul (fun x => (bas n).repr (F x) p.1) (fun x => (bas n).repr (G x) p.2) (hF p.1) (hG p.2)]
  ring

theorem exists_ι_mul (y : Alt n) : ∃ y' : Alt n, ∀ m, ExteriorAlgebra.ι ℂ m * y = y' * ExteriorAlgebra.ι ℂ m := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r => exact ⟨algebraMap ℂ _ r, fun m => (Algebra.commutes r _).symm⟩
  | ι x => exact ⟨-ExteriorAlgebra.ι ℂ x, fun m => by
      rw [neg_mul]; exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m x)⟩
  | mul a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' * b', fun m => by rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]⟩
  | add a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' + b', fun m => by rw [mul_add, ha, hb, add_mul]⟩

theorem sum_mul_leibniz {v : V n} (g : Fin n → (Fin n ⊕ Fin n → ℂ)) (T : Fin n → (V n → ℂ) → ℂ)
    (hsum : ∀ a, ∀ f : Finset (Fin (n + n)) × Finset (Fin (n + n)) → V n → ℂ, (∀ p, DifferentiableAt ℝ (f p) v) →
      T a (fun x => ∑ p, f p x) = ∑ p, T a (f p))
    (hmul : ∀ a, ∀ f g : V n → ℂ, DifferentiableAt ℝ f v → DifferentiableAt ℝ g v →
      T a (fun x => f x * g x) = f v * T a g + T a f * g v)
    (hconst : ∀ a, ∀ c : ℂ, T a (fun _ => c) = 0)
    {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, ∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) (fun x => F x * G x) =
      (∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) F) * G v +
        y * ∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) G := by
  obtain ⟨y, hy⟩ := exists_ι_mul (F v)
  refine ⟨y, ?_⟩
  have h (a : Fin n) : ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) (fun x => F x * G x) =
      ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) F * G v + y * (ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) G) := by
    simp only [coefwise_mul (hsum a) (hmul a) (hconst a) hF hG, mul_add, ← mul_assoc, hy]
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

theorem delAt_mul {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, delAt (fun x => F x * G x) v = delAt F v * G v + y * delAt G v :=
  sum_mul_leibniz (fun a => Pi.single (.inl a) 1) (fun a f => del f v (coordVec a))
    (fun a f hf => by rw [del_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
    (fun a f g hf hg => del_mul hf hg _) (fun a c => by rw [del_const]; rfl) hF hG

theorem dbarAt_mul {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, dbarAt (fun x => F x * G x) v = dbarAt F v * G v + y * dbarAt G v :=
  sum_mul_leibniz (fun a => Pi.single (.inr a) 1) (fun a f => dbar f v (coordVec a))
    (fun a f hf => by rw [dbar_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
    (fun a f g hf hg => dbar_mul hf hg _) (fun a c => by rw [dbar_const]; rfl) hF hG

variable {M : Type} [TopologicalSpace M]

theorem loc_mul (A : HolAtlas M n) (α β : A.Fld) (i : A.ι) (v : V n) :
    A.loc (α * β) i v = A.loc α i v * A.loc β i v := by
  unfold HolAtlas.loc
  split_ifs
  · rfl
  · simp

theorem differentiableAt_coef {A : HolAtlas M n} {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt ((A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt
    (by simp)

end GlobalTheory.CxForm.FormMul
end
end

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

variable {n : ℕ}

def dOne (f : V n → ℂ) (v : V n) : Alt n := ∑ a, del f v (coordVec a) • dz a

theorem delAt_eq_sum_dOne (β : V n → Alt n) (u : V n) :
    delAt β u = ∑ T, dOne (fun x => (bas n).repr (β x) T) u * bas n T := by
  simp only [delAt, coefwise, dOne, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_comm

theorem delAt_congr {F G : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] G) : delAt F v = delAt G v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
  have e : del (fun x => (bas n).repr (F x) S) v = del (fun x => (bas n).repr (G x) S) v :=
    del_congr (h.fun_comp fun y => (bas n).repr y S)
  simp only [e]

end GlobalTheory.CxForm.DelForm
end
end

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.CxForm.HolAtlas

open GlobalTheory.GoodMetric (coordVec)

theorem del_loc_repr_contDiffOn : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → ∀ (i : A.ι) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S) (A.e i).target := by
  intro M _ n A α hα i S
  have key : ∀ v ∈ (A.e i).target, (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S =
      ∑ a, ∑ T, GlobalTheory.del (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v (coordVec a) *
        (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.dz a * GlobalTheory.CxForm.bas n T) S := by
    intro v hv
    have h1 : A.loc (A.del α) i v = GlobalTheory.CxForm.delAt (A.loc α i) v := by
      rw [GlobalTheory.CxForm.HolAtlas.loc, dite_eq_left hv]
      simp only [GlobalTheory.CxForm.HolAtlas.del, GlobalTheory.CxForm.HolAtlas.Pt.crd, GlobalTheory.CxForm.HolAtlas.Pt.ch, GlobalTheory.CxForm.HolAtlas.Pt.pt, (A.e i).right_inv hv]
    rw [h1, GlobalTheory.CxForm.delAt]

    simp only [GlobalTheory.CxForm.coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine ContDiffOn.congr ?_ key
  have ho := (A.e i).open_target
  refine ContDiffOn.sum fun a _ => ContDiffOn.sum fun T _ => ContDiffOn.mul ?_ contDiffOn_const
  have hf := hα.smooth i T
  have hd := hf.fderiv_of_isOpen ho (m := ∞) (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v (coordVec a))
      (A.e i).target := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v
      (Complex.I • coordVec a)) (A.e i).target := hd.clm_apply contDiffOn_const
  refine ((h1.sub (h2.const_smul Complex.I)).const_smul (1 / 2 : ℂ)).congr fun v _ => ?_
  rfl

end GlobalTheory.CxForm.HolAtlas
end
end

section

open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

noncomputable section
namespace GlobalTheory.ChernSmooth

section General

variable {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CommRing B] [Algebra ℂ B]

def WeakSmooth (s : Set E) (F : E → B) : Prop := ∀ φ : B →ₗ[ℂ] ℂ, ContDiffOn ℝ ∞ (fun v => φ (F v)) s

def mult (B : Type) [CommRing B] [Algebra ℂ B] (s : Set E) : Subring (E → B) where
  carrier := {G | ∀ F, WeakSmooth s F → WeakSmooth s (G * F)}
  mul_mem' {a b} ha hb F hF := by rw [mul_assoc]; exact ha _ (hb _ hF)
  one_mem' F hF := by rwa [one_mul]
  add_mem' {a b} ha hb F hF φ := by
    simpa [add_mul] using (ha F hF φ).add (hb F hF φ)
  zero_mem' F hF φ := by simpa using contDiffOn_const
  neg_mem' {a} ha F hF φ := by simpa using (ha F hF φ).neg

theorem smul_mem {s : Set E} {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f s) (b : B) : (fun v => f v • b) ∈ mult B s := by
  intro F hF φ
  simpa using hf.mul (hF (φ ∘ₗ LinearMap.mulLeft ℂ b))

theorem const_mem (s : Set E) (b : B) : (fun _ => b) ∈ mult B s := by
  simpa using smul_mem (s := s) (f := fun _ => (1 : ℂ)) contDiffOn_const b

theorem weakSmooth_of_mem {s : Set E} {G : E → B} (h : G ∈ mult B s) : WeakSmooth s G := by
  simpa using h 1 fun φ => by simpa using contDiffOn_const

theorem det_mem {s : Set E} {r : Type} [Fintype r] [DecidableEq r] {M : E → Matrix r r B}
    (h : ∀ i j, (fun v => M v i j) ∈ mult B s) : (fun v => (M v).det) ∈ mult B s := by
  have : (fun v => (M v).det) = ∑ σ : Equiv.Perm r, ((Equiv.Perm.sign σ : ℤ) : E → B) * ∏ i, fun v => M v (σ i) i := by
    funext v
    simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

end General

theorem contDiffOn_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (bas n).repr (chernAt H v j : Alt n) S) s := by
  intro n r _ _ H s hs hH hu j S
  have hc : ∀ ξ η a b, ContDiffOn ℝ ∞ (fun v => curv H v ξ η a b) s := fun ξ η a b v hv =>
    (MContDiffAt.curv (k := ∞) (j := ∞) (fun a b => (hH a b).contDiffAt (hs.mem_nhds hv)) (hu v hv)
      (by norm_cast) ξ η a b).contDiffWithinAt
  have hd : (fun v => (-curvPoly H v).charpolyRev) ∈ mult (Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) s := by
    unfold Matrix.charpolyRev
    refine det_mem fun a b => ?_
    have : (fun v => (1 - (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) •
        (-curvPoly H v).map Polynomial.C) a b) = (fun _ => (1 : Matrix r r _) a b) + ∑ c, ∑ d, fun v =>
          curv H v (coordVec c) (coordVec d) a b • (Polynomial.X * Polynomial.C (MvPolynomial.X (c, d))) := by
      funext v
      simp [curvPoly, Finset.sum_apply, Finset.mul_sum, MvPolynomial.C_mul', ← Polynomial.smul_C]
    rw [this]
    exact add_mem (const_mem _ _) (sum_mem fun c _ => sum_mem fun d _ => smul_mem (hc _ _ _ _) _)
  let φ : Polynomial (MvPolynomial (Fin n × Fin n) ℂ) →ₗ[ℂ] ℂ :=
    (bas n).coord S ∘ₗ (Subalgebra.center ℂ (Alt n)).val.toLinearMap ∘ₗ (kappa ^ j • (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toLinearMap) ∘ₗ
      (Polynomial.lcoeff _ j).restrictScalars ℂ
  exact weakSmooth_of_mem hd φ

end GlobalTheory.ChernSmooth
end
end

section

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm

theorem integrable_dbar_integral_eq_zero {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ G y w) := fun w =>
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  refine ⟨?_, ?_⟩
  · simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  · simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc]
    simp

theorem dens_dbarAt_eq_sum {n : ℕ} (F : V n → Alt n) (v : V n) :
    dens (dbarAt F v) = ∑ a, ∑ S, dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dens, dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_re_dens_dbarAt_eq_zero {n : ℕ} (F : V n → Alt n)
    (hF : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S)) (hc : HasCompactSupport F) :
    ∫ v, (dens (dbarAt F v)).re = 0 := by
  have h (a : Fin n) (S : Finset (Fin (n + n))) :=
    integrable_dbar_integral_eq_zero (hF S)
      (hc.comp_left (g := fun α : Alt n => (bas n).repr α S) (by simp)) (coordVec a)
  have hi (a : Fin n) (S : Finset (Fin (n + n))) :
      Integrable fun v => dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) :=
    (h a S).1.mul_const _
  have hD : Integrable fun v => dens (dbarAt F v) := by
    simp only [dens_dbarAt_eq_sum]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S
  have h0 : ∫ v, dens (dbarAt F v) = 0 := by
    simp only [dens_dbarAt_eq_sum]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [integral_finsetSum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [integral_mul_const, (h a S).2, zero_mul]
  have := Complex.reCLM.integral_comp_comm hD
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm
end
end

section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.HolAtlas

theorem del_finset_sum {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ}
    (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) : A.del (∑ j, α j) = ∑ j, A.del (α j) := by
  funext x
  have hloc : ∀ w, A.loc (∑ j, α j) x.1.1 w = ∑ j, A.loc (α j) x.1.1 w := by
    intro w
    by_cases hw : w ∈ (A.e x.1.1).target
    · simp only [GlobalTheory.CxForm.HolAtlas.loc, hw, dif_pos]
      exact Finset.sum_apply _ _ _
    · simp [GlobalTheory.CxForm.HolAtlas.loc, hw]
  have hx : x.crd ∈ (A.e x.1.1).target := x.ch.map_source x.2
  have hdiff : ∀ j S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S) x.crd :=
    fun j S => (((hα j).smooth x.1.1 S).differentiableOn (by simp)).differentiableAt
      ((A.e x.1.1).open_target.mem_nhds hx)
  have key : ∀ S u, GlobalTheory.del (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) x.crd u =
      ∑ j, GlobalTheory.del (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S) x.crd u := by
    intro S u
    have e : (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) =
        fun w => ∑ j ∈ Finset.univ, (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S := by
      funext w; rw [hloc, map_sum, Finsupp.finsetSum_apply]
    rw [e, GlobalTheory.del_sum (fun j _ => hdiff j S), ContinuousLinearMap.sum_apply]
  rw [Finset.sum_apply]
  simp only [GlobalTheory.CxForm.HolAtlas.del, GlobalTheory.CxForm.delAt, GlobalTheory.CxForm.coefwise, key, Finset.sum_smul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

end GlobalTheory.CxForm.HolAtlas
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate

namespace GlobalTheory.CxForm.PullType

variable {n m : ℕ}

def scale (n : ℕ) (s t : ℂ) : Alt n →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (Matrix.fromBlocks (s • 1) 0 0 (t • 1)))

theorem scale_single (s t : ℂ) (i : Fin (n + n)) :
    scale n s t (bas n {i}) = (if i.val < n then s else t) • bas n {i} := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [bas_singleton, ← map_smul]
  refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_))
  rcases i with i | i <;> rintro (b | b) <;> simp [Pi.single_apply, Matrix.one_apply]

theorem scale_bas (s t : ℂ) (S : Finset (Fin (n + n))) :
    scale n s t (bas n S) = (s ^ (S.filter (·.val < n)).card * t ^ (S.filter (n ≤ ·.val)).card) • bas n S := by
  induction S using Finset.induction_on with
  | empty => simp [bas_empty]
  | insert a S ha ih =>
    obtain ⟨ε, h⟩ := bas_mul (n := n) (S := {a}) (T := S) (by simpa using ha)
    have h' : bas n (insert a S) = ε • (bas n {a} * bas n S) := by
      rw [h, smul_smul, Int.units_mul_self, one_smul, Finset.insert_eq]
    rw [h', Units.smul_def, map_zsmul, map_mul, scale_single, ih, smul_mul_smul_comm, smul_comm]
    congr 1
    rw [Finset.filter_insert, Finset.filter_insert]
    by_cases hn : a.val < n
    · rw [if_pos hn, if_pos hn, if_neg (not_le.2 hn), Finset.card_insert_of_notMem (by simp [ha])]
      ring
    · rw [if_neg hn, if_neg hn, if_pos (not_lt.1 hn), Finset.card_insert_of_notMem (by simp [ha])]
      ring

theorem repr_scale (s t : ℂ) (α : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (scale n s t α) S =
      (s ^ (S.filter (·.val < n)).card * t ^ (S.filter (n ≤ ·.val)).card) * (bas n).repr α S := by
  conv_lhs => rw [← (bas n).sum_repr α]

  simp only [map_sum, map_smul, scale_bas, Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
  Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem scale_pull (L : V n →L[ℂ] V m) (s t : ℂ) (α : Alt m) :
    scale n s t (pull L α) = pull L (scale m s t α) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, scale, scale, pull, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
  simp [Matrix.fromBlocks_multiply]

end GlobalTheory.CxForm.PullType

namespace GlobalTheory.CxForm

end GlobalTheory.CxForm
end
end

section


theorem _root_.GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula : GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ArProj := by
  first | exact @GlobalTheory.Published.arProj_of_heightProjection | exact GlobalTheory.Published.arProj_of_heightProjection | (intros; apply GlobalTheory.Published.arProj_of_heightProjection <;> assumption)
end

section

namespace GlobalTheory

theorem cuspidalMirabolic_holds : GlobalTheory.Published.CuspidalMirabolic :=
  CompanionTheory.Mirab.cuspidalMirabolic

end GlobalTheory
end
