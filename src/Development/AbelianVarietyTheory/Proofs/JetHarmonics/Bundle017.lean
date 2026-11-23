module

public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Formalism.RealPlaceAnalysis.Bundle002
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.MvPowerSeries.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002

@[expose] public section

section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.HeisOps

variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem hf_add_left (x y z : Fin g → ℂ) : hf Hm (x + y) z = hf Hm x z + hf Hm y z := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : Fin g → ℂ) : hf Hm x (y + z) = hf Hm x y + hf Hm x z := by
  simp only [hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hf_zero_right (x : Fin g → ℂ) : hf Hm x 0 = 0 := by simp [hf]

theorem hf_swap (h : Hm.IsHermitian) (x y : Fin g → ℂ) : hf Hm y x = conj (hf Hm x y) := by

  simp only [hf, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : conj (Hm i j) = Hm j i := h.apply j i
  rw [e]; ring

theorem opU_opU (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) :
    opU Hm x (opU Hm y F) = fun z =>
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf Hm x y).im : ℝ) : ℂ)) * opU Hm (x + y) F z := by
  funext z
  simp only [opU]
  rw [add_assoc z x y, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [hf_add_left, hf_add_right]
  have e := Complex.sub_conj (hf Hm x y)
  rw [hf_swap h x y]
  push_cast at e
  linear_combination (-(Real.pi : ℂ) / 2) * e

theorem opU_comm (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) :
    opU Hm x (opU Hm y F) = fun z => kap Hm x y * opU Hm y (opU Hm x F) z := by
  funext z
  rw [opU_opU h x y, opU_opU h y x, add_comm y x, kap, ← mul_assoc, ← Complex.exp_add, hf_swap h x y,
    Complex.conj_im]
  push_cast
  ring_nf

theorem im_eq {d : ℕ} (hd : 0 < d) (x y : Fin g → ℂ) (u v : ℤ) (h : beta d Hm x y = u + v * w0 d) :
    (hf Hm x y).im = v := by
  have hs : Real.sqrt d ≠ 0 := by positivity
  have e := congrArg Complex.im h
  rw [beta, Complex.im_ofReal_mul] at e
  have e2 : ((u : ℂ) + v * w0 d).im = Real.sqrt d / 2 * v := by
    simp [w0, rtd]; ring
  rw [e2] at e
  exact mul_left_cancel₀ (div_ne_zero hs two_ne_zero) e

theorem opU_const_mul (c : ℂ) (x : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) :
    opU Hm x (fun w => c * F w) z = c * opU Hm x F z := by
  simp only [opU]; ring

theorem opW_opW {d : ℕ} (hd : 0 < d) (h : Hm.IsHermitian) (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ)
    (hb : beta d Hm x y ∈ OK d) : opW d Hm x (opW d Hm y F) = opW d Hm (x + y) F := by
  obtain ⟨u, v, huv⟩ := hb
  have him := im_eq hd x y u v huv
  have hre : (beta d Hm x y).re = u + v / 2 := by
    rw [huv]; simp [w0, rtd]; ring
  have hq : (beta d Hm (x + y) (x + y)).re = (beta d Hm x x).re + (beta d Hm y y).re + (2 * u + v) := by
    simp only [beta, Complex.re_ofReal_mul, hf_add_left, hf_add_right, Complex.add_re] at hre ⊢
    rw [hf_swap h x y, Complex.conj_re]
    linear_combination 2 * hre
  funext z
  have e : opW d Hm x (opW d Hm y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ)) *
      (Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm y y).re : ℂ)) * opU Hm x (opU Hm y F) z) := by
    rw [← opU_const_mul]; rfl
  rw [e, opU_opU h, him]
  simp only [opW]
  rw [hq, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(u + v), ?_⟩
  push_cast
  ring

theorem contDiff_opU (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ} (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (opU Hm x F) := by
  unfold opU hf
  refine (hF.comp (contDiff_id.add contDiff_const)).mul (ContDiff.cexp ?_)
  fun_prop

theorem contDiff_opW (d : ℕ) (x : Fin g → ℂ) {F : (Fin g → ℂ) → ℂ} (hF : ContDiff ℂ ⊤ F) :
    ContDiff ℂ ⊤ (opW d Hm x F) :=
  contDiff_const.mul (contDiff_opU x hF)

theorem heisenberg : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), 0 < d → Hm.IsHermitian → (∀ (x y : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ), opU Hm x (opU Hm y F) = (fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf Hm x y).im : ℝ) : ℂ)) * opU Hm (x + y) F z) ∧ opU Hm x (opU Hm y F) = (fun z => kap Hm x y * opU Hm y (opU Hm x F) z) ∧ (beta d Hm x y ∈ OK d → opW d Hm x (opW d Hm y F) = opW d Hm (x + y) F)) ∧ (∀ F, opU Hm 0 F = F ∧ opW d Hm 0 F = F) ∧ (∀ (x : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ (opU Hm x F) ∧ ContDiff ℂ ⊤ (opW d Hm x F)) ∧ (∀ x y : Fin g → ℂ, hf Hm y x = conj (hf Hm x y)) ∧ (∀ (x y : Fin g → ℂ) (u v : ℤ), beta d Hm x y = u + v * w0 d → (hf Hm x y).im = v) ∧ ∀ x y z : Fin g → ℂ, kap Hm x (y + z) = kap Hm x y * kap Hm x z ∧ kap Hm (x + y) z = kap Hm x z * kap Hm y z := by
  intro g d Hm hd h
  refine ⟨fun x y F => ⟨opU_opU h x y F, opU_comm h x y F, opW_opW hd h x y F⟩, fun F => ?_,
    fun x F hF => ⟨contDiff_opU x hF, contDiff_opW d x hF⟩, hf_swap h, im_eq hd, fun x y z => ⟨?_, ?_⟩⟩
  · constructor <;> funext z <;> simp [opW, opU, beta, hf_zero_right]
  · simp only [kap, hf_add_right, ← Complex.exp_add]; congr 1; push_cast [Complex.add_im]; ring
  · simp only [kap, hf_add_left, ← Complex.exp_add]; congr 1; push_cast [Complex.add_im]; ring

end GlobalTheory.HeisOps
end

section

open Formalism.REAL

namespace GlobalTheory

inductive LoweringWord {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : ℕ → V → Prop
  | base : LoweringWord E v 0 v
  | step {N : ℕ} {x : V} (a b : Fin n) (h : b < a) :
      LoweringWord E v N x → LoweringWord E v (N + (a.val - b.val)) (E a b x)

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℂ} {v : V}

theorem glRel_apply_comm (hE : GlRel E) (a b c d : Fin n) (y : V) :
    E a b (E c d y) = E c d (E a b y) + (if b = c then E a d y else 0)
      - (if d = a then E c b y else 0) := by
  have h := congrArg (fun f : Module.End ℂ V => f y) (hE a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h1 : (if b = c then E a d else 0) y = if b = c then E a d y else 0 := by
    split_ifs <;> simp
  have h2 : (if d = a then E c b else 0) y = if d = a then E c b y else 0 := by
    split_ifs <;> simp
  rw [h1, h2] at h
  rw [add_sub_assoc, ← h]
  abel

theorem loweringWord_span_lower (a b : Fin n) (hab : b < a) :
    ∀ x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x},
      E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨N, hN⟩ := hx
    exact Submodule.subset_span ⟨_, hN.step a b hab⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem loweringWord_apply_mem (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    ∀ a b, E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  induction hx with
  | base =>
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hv.2 a b h]; exact Submodule.zero_mem _
    · subst h
      rw [hv.1 a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, LoweringWord.base⟩)
    · exact Submodule.subset_span ⟨_, LoweringWord.base.step a b h⟩
  | step c d h _ ih =>
    intro a b
    rw [glRel_apply_comm hE]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (loweringWord_span_lower c d h _ (ih a b)) ?_) ?_
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _

theorem loweringWord_height (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) x
      = ((∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a) + (N : ℂ)) • x := by
  induction hx with
  | base =>
    simp [LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
  | @step N y c d h _ ih =>
    have key : (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) (E c d y)
        = E c d ((∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) y)
          + ((c.val : ℕ) : ℂ) • E c d y - ((d.val : ℕ) : ℂ) • E c d y := by

      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      simp only [glRel_apply_comm hE _ _ c d y, smul_sub, smul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [key, ih, map_smul]
    have hle : d.val ≤ c.val := le_of_lt h
    push_cast [Nat.cast_sub hle]
    module

theorem loweringWord_zero_or_pos {N : ℕ} {x : V} (hx : LoweringWord E v N x) :
    x = v ∨ 0 < N := by
  cases hx with
  | base => exact Or.inl rfl
  | step c d h _ =>
    right
    have : d.val < c.val := h
    omega

end

theorem exists_stable_submodule_topWeight_line :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
      (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
      ∃ S : Submodule ℂ V, (∀ a b, ∀ x ∈ S, E a b x ∈ S) ∧ v ∈ S ∧
        ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v := by
  intro V _ _ n E ν v hE hv
  refine ⟨Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}, ?_,
    Submodule.subset_span ⟨0, LoweringWord.base⟩, ?_⟩
  · intro a b x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨N, hN⟩ := hx
      exact loweringWord_apply_mem hE hv hN a b
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · intro x hx hw
    set H : Module.End ℂ V := ∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a with hH
    set h : ℂ := ∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a with hh
    have hle : Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}
        ≤ Submodule.span ℂ {v} ⊔ ⨆ (μ : ℂ) (_ : μ ≠ h), H.eigenspace μ := by
      rw [Submodule.span_le]
      rintro y ⟨N, hN⟩
      rcases loweringWord_zero_or_pos hN with rfl | hpos
      · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · refine Submodule.mem_sup_right ?_
        have hne : h + (N : ℂ) ≠ h := by
          have : (N : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
          simpa using this
        refine Submodule.mem_iSup_of_mem (h + (N : ℂ)) (Submodule.mem_iSup_of_mem hne ?_)
        rw [Module.End.mem_eigenspace_iff]
        exact loweringWord_height hE hv hN
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hxe : x ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hw, Finset.sum_smul, mul_smul]
    have hve : v ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
    have hze : z ∈ H.eigenspace h := by
      have : z = x - c • v := by rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hxe (Submodule.smul_mem _ _ hve)
    have hd := Module.End.eigenspaces_iSupIndep H h
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd) z hze hz
    exact ⟨c, by rw [← hyz, hz0, add_zero]⟩

end GlobalTheory
end

section

open Formalism.REAL

namespace GlobalTheory

theorem highestWeight_tensor_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (θ : Fin (n + 1) → ℂ) (lam : ℂ) (y : (PiLp 2 (fun _ : Fin (n + 1) => V))), (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → y ≠ 0 → IsHW Et θ y → Om y = lam • y → ∃ c, y c ≠ 0 ∧ IsHW E (fun a => θ a - if a = c then 1 else 0) (y c) ∧ lam = θ c - 1 - ((c : ℕ) : ℂ) := by
  classical
  intro V _ _ _ n E Et Om θ lam y hEt hOm hy hw hlam
  obtain ⟨h1, h2⟩ := hw
  have hne : (Finset.univ.filter (fun c => y c ≠ 0)).Nonempty := by
    by_contra h
    apply hy
    ext c
    by_contra hc
    exact h ⟨c, by simpa using hc⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ id hne
  have hc0 : y c ≠ 0 := by simpa using hc
  have hz : ∀ d, c < d → y d = 0 := by
    intro d hd
    by_contra h
    exact absurd (hmax d (by simpa using h)) (not_le.mpr hd)
  have hup : ∀ a b, a < b → ∀ e, E a b (y e) = - if e = a then y b else 0 := by
    intro a b hab e
    have h := hEt a b y e
    have h0 : Et a b y = 0 := h2 a b hab
    rw [h0] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hdiag : ∀ a, E a a (y c) = (θ a - if a = c then 1 else 0) • y c := by
    intro a
    have h := hEt a a y c
    have h0 : Et a a y = θ a • y := h1 a
    rw [h0] at h
    have h' : E a a (y c) = θ a • y c - if c = a then y a else 0 := by
      rw [eq_sub_iff_add_eq, ← h]; rfl
    rw [h']
    by_cases hca : c = a
    · subst hca; simp [sub_smul]
    · simp [hca, Ne.symm hca]
  have hraise : ∀ a b, a < b → E a b (y c) = 0 := by
    intro a b hab
    rw [hup a b hab c]
    by_cases hca : c = a
    · subst hca; simp [hz b hab]
    · simp [hca]
  refine ⟨c, hc0, ⟨hdiag, hraise⟩, ?_⟩
  have hterm : ∀ d, E d c (y d) =
      ((if d = c then θ c - 1 else 0) - if d < c then 1 else 0 : ℂ) • y c := by
    intro d
    rcases lt_trichotomy d c with h | h | h
    · rw [hup d c h d]; simp [h, h.ne]
    · subst h; rw [hdiag]; simp
    · simp [hz d h, h.ne', not_lt.mpr h.le]
  have hsum : lam • y c = (θ c - 1 - ((c : ℕ) : ℂ)) • y c := by
    have h := hOm y c
    rw [hlam] at h
    have h' : lam • y c = ∑ d, E d c (y d) := h
    rw [h', Finset.sum_congr rfl (fun d _ => hterm d), ← Finset.sum_smul,
      Finset.sum_sub_distrib]
    congr 2
    · simp
    · rw [Finset.sum_boole]
      have : Finset.univ.filter (fun d => d < c) = Finset.Iio c := by ext d; simp
      rw [this, Fin.card_Iio]
  exact smul_left_injective ℂ hc0 hsum

end GlobalTheory
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory


open MvPowerSeries in
theorem _root_.GlobalTheory.minorHarm_pderiv_comm {σ k : Type*} [CommRing k] (i j : σ)
    (p : MvPolynomial σ k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  have h : ⁅MvPolynomial.pderiv (R := k) i, MvPolynomial.pderiv (R := k) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro n
    rw [Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
    by_cases hj : j = n <;> by_cases hi : i = n <;>
      simp [Pi.single_apply, hj, hi]
  have := DFunLike.congr_fun h p
  rw [Derivation.commutator_apply] at this
  simpa [sub_eq_zero] using this


open MvPowerSeries in
theorem _root_.GlobalTheory.minorHarm_pderiv_eq_zero {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) {v : σ} (hv : v ∉ S) :
    MvPolynomial.pderiv v p = 0 := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact MvPolynomial.pderiv_X_of_ne (fun h => hv (h ▸ hs))
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [MvPolynomial.pderiv_mul, hx, hy]; simp

open MvPowerSeries in
private theorem pderiv_mem_supported' {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) (w : σ) :
    MvPolynomial.pderiv w p ∈ MvPolynomial.supported k S := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    rw [MvPolynomial.pderiv_X]
    by_cases h : w = s
    · subst h; simp only [Pi.single_eq_same]; exact Subalgebra.one_mem _
    · rw [Pi.single_eq_of_ne' h]; exact Subalgebra.zero_mem _
  | algebraMap r =>
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [MvPolynomial.pderiv_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx hy') (Subalgebra.mul_mem _ hx' hy)


open MvPowerSeries in
theorem _root_.GlobalTheory.minors_disjoint_columns_harmonic :
    ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → ∀ τ τ' : T, (∀ i i', col τ i ≠ col τ' i') → ∀ (i : Fin (r τ)) (i' : Fin (r τ')), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) (MvPolynomial.pderiv ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), b) P) = 0 := by
  intro k _ T _ _ r n col m P hP τ τ' hdisj i i'
  let S : Set ((Σ τ : T, Fin (r τ)) × Fin n) := {x | ∃ c, col x.1.1 c = x.2}
  have hPS : P ∈ MvPolynomial.supported k S := by
    rw [hP]
    refine Subalgebra.prod_mem _ fun σ _ => Subalgebra.prod_mem _ fun s _ => ?_
    refine Subalgebra.pow_mem _ ?_ _
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun π _ => ?_
    rw [Units.smul_def]
    refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun a _ => ?_) _
    rw [Matrix.of_apply, MvPolynomial.supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨_, ⟨_, rfl⟩, rfl⟩
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : ∃ c, col τ c = b
  · obtain ⟨c, rfl⟩ := hb
    have hnot : ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), col τ c) ∉ S := by
      rintro ⟨c', hc'⟩
      exact hdisj c c' hc'.symm
    rw [_root_.GlobalTheory.minorHarm_pderiv_eq_zero hPS hnot, map_zero]
  · have hnot : ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) ∉ S := hb
    exact _root_.GlobalTheory.minorHarm_pderiv_eq_zero
      (pderiv_mem_supported' hPS _) hnot

end GlobalTheory
end
