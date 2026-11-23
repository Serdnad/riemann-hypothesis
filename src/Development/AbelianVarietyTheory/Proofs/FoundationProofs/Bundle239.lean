module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle228
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem al_add (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N'))
    (h1 : ∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) (h2 : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m)
    (h3 : ∀ x ∈ A, w0 D • x ∈ A) : ∀ x ∈ A, ∀ y ∈ A, al D T (x + y) =
      al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) := by
  intro x hx y hy
  obtain ⟨a, ha⟩ := h2 x hx
  obtain ⟨c, hc⟩ := h2 y hy
  obtain ⟨b, hb⟩ := h1 x hx y hy
  obtain ⟨k, hk⟩ := h1 _ (h3 x hx) y hy
  have hal : ∀ z : VC D N N', ∀ m : ℤ, qH D T z = m → al D T z = (-1 : ℂ) ^ m := by
    intro z m hm
    have e : al D T z = (-1 : ℂ) ^ (round (qH D T z)) := rfl
    rw [e, hm, round_intCast]
  have hk' : Real.sqrt D.host.d * (Hf D T x y).re = 2 * k - b := by
    rw [Hf_smul_left] at hk
    rw [← hk, ← hb]
    simp [w0, Complex.mul_im]
    ring
  have hs : qH D T (x + y) = ((a + c + (2 * k - b) : ℤ) : ℝ) := by
    push_cast
    rw [← ha, ← hc, ← hk']
    simp only [qH, Hf_add_left, Hf_add_right, Complex.add_re, Hf_re_swap D T x y]
    ring
  have he : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) = (-1 : ℂ) ^ (-b) := by
    rw [hb, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  rw [hal _ _ hs, hal _ _ ha, hal _ _ hc, he, sub_eq_add_neg, zpow_add₀ hn, zpow_add₀ hn, zpow_add₀ hn,
    zpow_mul]
  simp

end GlobalTheory.GalTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.GalTheta.Period

variable (D : D7) (T : Tor D) {N N' : ℕ}

theorem Hf_two_mul (m : ℕ) (y l : VC D N N') : Hf D T y ((2 * m) • l) = 2 * Hf D T (m • y) l := by
  rw [Hf_nsmul_right, Hf_nsmul_left]; push_cast; ring

theorem qH_add (a b : VC D N N') :
    qH D T (a + b) = qH D T a + qH D T b + Real.sqrt D.host.d * (Hf D T a b).re := by
  simp only [qH, Hf_add_left, Hf_add_right, Complex.add_re, Hf_re_swap D T a b]
  ring

theorem qH_nsmul (n : ℕ) (a : VC D N N') : qH D T (n • a) = (n : ℝ) ^ 2 * qH D T a := by
  simp only [qH, Hf_nsmul_left, Hf_nsmul_right]
  have : ((n : ℂ) * ((n : ℂ) * Hf D T a a)).re = (n : ℝ) ^ 2 * (Hf D T a a).re := by
    simp; ring
  rw [this]; ring

theorem exp_even (r : ℝ) (m : ℤ) (h : r = 2 * m) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (r : ℂ)) = 1 := by
  rw [h, Complex.exp_eq_one_iff]
  exact ⟨-m, by push_cast; ring⟩

theorem period (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N'))
    (hIm : ∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) (hq : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m)
    (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (e₀ : VC D N N' → ℂ) (x : VC D N N') (m₀ : ℕ)
    (he : e₀ ∈ ThSp D T A) (hx : m₀ • x ∈ A) (ht : ∀ i, m₀ • t i ∈ A) (l : VC D N N') (hl : l ∈ A) :
    U D T (x + (2 * m₀) • l) (comb D T c t e₀) = U D T x (comb D T c t e₀) ∧
      wdPh D T (x + (2 * m₀) • l) = wdPh D T x := by
  obtain ⟨ql, hql⟩ := hq l hl
  have hqμ : qH D T ((2 * m₀) • l) = ((2 * (2 * (m₀ : ℤ) ^ 2 * ql) : ℤ) : ℝ) := by
    rw [qH_nsmul, hql]; push_cast; ring
  have hμ : U D T ((2 * m₀) • l) e₀ = e₀ := by
    funext z
    have h := he.2 _ (A.nsmul_mem hl (2 * m₀)) z
    have hal : al D T ((2 * m₀) • l) = 1 := by
      change (-1 : ℂ) ^ (round (qH D T ((2 * m₀) • l))) = 1
      rw [hqμ, round_intCast, zpow_mul]
      norm_num
    rwa [hal, one_mul] at h
  have hev : ∀ y : VC D N N', m₀ • y ∈ A → ∃ m : ℤ, (Hf D T y ((2 * m₀) • l)).im = 2 * m := by
    intro y hy
    obtain ⟨m, hm⟩ := hIm _ hy _ hl
    exact ⟨m, by rw [Hf_two_mul, ← hm]; simp⟩
  refine ⟨?_, ?_⟩
  · have key : ∀ (s : VC D N N'), m₀ • s ∈ A → ∀ z,
        U D T (x + (2 * m₀) • l) (U D T s e₀) z = U D T x (U D T s e₀) z := by
      intro s hs z
      have h1 : U D T (x + s) e₀ z = U D T (x + (2 * m₀) • l + s) e₀ z := by
        obtain ⟨m, hm⟩ := hev (x + s) (by rw [smul_add]; exact A.add_mem hx hs)
        conv_lhs => rw [← hμ]
        rw [U_U, exp_even _ m hm, one_mul, add_right_comm]
      obtain ⟨m, hm⟩ := hev s hs
      have h2 : (Hf D T ((2 * m₀) • l) s).im = 2 * ((-m : ℤ) : ℝ) := by
        rw [Hf_im_swap, hm]; push_cast; ring
      rw [U_U, U_U, h1, Hf_add_left, Complex.add_im, Complex.ofReal_add, mul_add, Complex.exp_add,
        exp_even _ _ h2, mul_one]
    have h : ∀ y z, U D T y (comb D T c t e₀) z = ∑ j, c j * U D T y (U D T (t j) e₀) z := by
      intro y z
      have := U_sum D T Finset.univ y (fun j w => c j * U D T (t j) e₀ w) z
      simp only [U_mul] at this
      exact this
    funext z
    rw [h, h]
    exact Finset.sum_congr rfl fun j _ => by rw [key _ (ht j)]
  · obtain ⟨a, ha⟩ := hq _ hx
    obtain ⟨b, hb⟩ := hq _ (A.add_mem hx hl)
    have h1 := qH_add D T (m₀ • x) l
    have h2 := qH_add D T x ((2 * m₀) • l)
    have h3 : (Hf D T x ((2 * m₀) • l)).re = 2 * (Hf D T (m₀ • x) l).re := by
      rw [Hf_two_mul]; simp
    have h4 : qH D T (x + (2 * m₀) • l) / 2 =
        qH D T x / 2 + ((2 * (m₀ : ℤ) ^ 2 * ql + (b - a - ql) : ℤ) : ℝ) := by
      rw [h2, hqμ, h3]
      rw [ha, hb, hql] at h1
      push_cast
      linarith
    unfold wdPh ee
    rw [h4, Complex.ofReal_add, mul_add, Complex.exp_add, Complex.ofReal_intCast,
      mul_comm _ ((_ : ℤ) : ℂ), Complex.exp_int_mul_two_pi_mul_I, mul_one]

end GlobalTheory.GalTheta.Period
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

theorem _root_.GlobalTheory.T.cmFiniteAdele_strong_approx_mod_adelicIdeal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ → (∀ (y : AE D) (m : ℕ), 0 < m → ∃ e : D.host.E, ∃ t ∈ IhE D cc, inc D e - y = (m : AE D) * t) ∧ (∀ y : AE D, ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D) ∧ (∀ s ∈ OhE D, ∀ t ∈ IhE D cc, s * t ∈ IhE D cc) := by
  first | exact @GlobalTheory.AdelicApprox.approx_mod_ideal | exact GlobalTheory.AdelicApprox.approx_mod_ideal | (intros; apply GlobalTheory.AdelicApprox.approx_mod_ideal <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.orthoProductTheta_mem_thetaSpace_of_lattice : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ), (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D T b k z * (starRingEnd ℂ) (coordB D T b k w)) → (∀ x : VC D N N', x ∈ LaB D T b ↔ ∀ k, coordB D T b k x ∈ T.abelian₂) → Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = m ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  first | exact @GlobalTheory.ProdTheta.pullB_mem_ThSp | exact GlobalTheory.ProdTheta.pullB_mem_ThSp | (intros; apply GlobalTheory.ProdTheta.pullB_mem_ThSp <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.orthonormalProductTheta_mem_thetaSpace : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  first | exact @GlobalTheory.OrthoProdTheta.pullB_mem_ThSp | exact GlobalTheory.OrthoProdTheta.pullB_mem_ThSp | (intros; apply GlobalTheory.OrthoProdTheta.pullB_mem_ThSp <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.coords_along_orthonormal_realSubfield_basis : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ z : VC D N N', z = ∑ k, coordB D (tor0 D cc δ) b k z • embV D (tor0 D cc δ) (b k)) ∧ (∀ j k, coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if k = j then 1 else 0) ∧ (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D (tor0 D cc δ) b k z * (starRingEnd ℂ) (coordB D (tor0 D cc δ) b k w)) ∧ (∀ x : VC D N N', x ∈ LaB D (tor0 D cc δ) b ↔ ∀ k, coordB D (tor0 D cc δ) b k x ∈ (lamOf D cc δ)) ∧ Function.Bijective (fun (z : VC D N N') (k : Fin r) => coordB D (tor0 D cc δ) b k z) := by
  first | exact @GlobalTheory.OnCoord.coords_of_orthonormal_basis | exact GlobalTheory.OnCoord.coords_of_orthonormal_basis | (intros; apply GlobalTheory.OnCoord.coords_of_orthonormal_basis <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.NormSum.MovedLattice

theorem halfDifferent_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  rw [h] at h2
  simp at h2

theorem inverseHalfDifferent_ne_zero (D : D7) : D.host.AA0 ≠ 0 := by
  unfold Host.AA0
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 (halfDifferent_ne_bot D))

def ext (D : D7) (cc : Ideal (𝓞 D.host.K)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

theorem ext_ne_zero (D : D7) {cc : Ideal (𝓞 D.host.K)} (h : cc ≠ ⊥) : ext D cc ≠ 0 := by
  unfold ext
  rw [FractionalIdeal.coeIdeal_ne_zero, Ne, Ideal.map_eq_bot_iff_of_injective]
  · exact h
  · exact FaithfulSMul.algebraMap_injective _ _

theorem coe_alg (D : D7) (c : 𝓞 D.host.K) :
    algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) =
      ((c : D.host.K) : D.host.E) := rfl

theorem mem_ext (D : D7) {cc : Ideal (𝓞 D.host.K)} {c : 𝓞 D.host.K} (h : c ∈ cc) :
    ((c : D.host.K) : D.host.E) ∈ ext D cc := by
  rw [← coe_alg]
  exact FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem _ h)

theorem inc_mul_mem (D : D7) {cc : Ideal (𝓞 D.host.K)} (h : cc ≠ ⊥) {j : D.host.E}
    (hj : j ∈ (ext D cc * D.host.AA0)⁻¹) {y : AE D} (hy : y ∈ IhE D cc) : inc D j * y ∈ OhE D := by
  have hJ : ext D cc * D.host.AA0 ≠ 0 := mul_ne_zero (ext_ne_zero D h) (inverseHalfDifferent_ne_zero D)
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s, hs, rfl⟩ := hy
    rw [← mul_assoc, ← map_mul]
    refine mul_mem ?_ hs
    have h1 := FractionalIdeal.mul_mem_mul hj (FractionalIdeal.mul_mem_mul (mem_ext D hc) ha)
    rw [inv_mul_cancel₀ hJ, FractionalIdeal.mem_one_iff] at h1
    exact (AdLattice.incl_mem_iff (F := ℚ) _).2 h1
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem smul_mem_homL (D : D7) {N N' : ℕ} (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D))
    {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L₁) (h' : Moves D g' L₁') (z : Matrix (Fin N') (Fin N) D.host.E) (j : D.host.E)
    (hz : ∀ a b, inc D j * (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (g : Matrix (Fin N) (Fin N) (AE D))) a b ∈ OhE D) : j • z ∈ homL D L₁ L₁' := by
  refine Submodule.subset_span fun x hx => ?_
  rw [h] at hx
  rw [h']
  intro i
  have key : ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)).mulVec
      (fun k => inc D ((j • z).mulVec x k)) =
      (inc D j • (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (g : Matrix (Fin N) (Fin N) (AE D)))).mulVec
        (((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec (fun k => inc D (x k))) := by
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul _ (inc D j)]
    congr 1
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
      RingHom.map_mulVec]
    rfl
  rw [key]
  simp only [Matrix.mulVec, dotProduct] at hx ⊢
  exact sum_mem fun k _ => mul_mem (hz i k) (hx k)

theorem pt_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (y y' : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (y + y') = pt D (tor0 D cc δ) δ y + pt D (tor0 D cc δ) δ y' := by
  funext τ a b
  simp [pt, embV, tor0, mul_add]

theorem pt_smul_mem (D : D7) (hD : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    {m : D.host.E} (hm : m ∈ ext D cc) {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ YYl D L₁ L₁') :
    pt D (tor0 D cc δ) δ (m • y) ∈ La D (tor0 D cc δ) L₁ L₁' := by
  obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
  clear hm
  induction hb using Submodule.span_induction generalizing y with
  | mem b hb =>
    obtain ⟨c, hc, rfl⟩ := hb
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ ((c : D.host.K) : D.host.E),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, y, hy, ?_⟩
    funext τ a b
    rw [coe_alg]
    simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hD τ, mul_assoc]
  | zero =>
    have : pt D (tor0 D cc δ) δ (algebraMap (𝓞 D.host.E) D.host.E 0 • y) = 0 := by
      funext τ a b
      simp [pt, embV, tor0]
    rw [this]; exact zero_mem _
  | add b b' _ _ hb hb' =>
    rw [map_add (f := _), add_smul, pt_add]
    exact add_mem (hb hy) (hb' hy)
  | smul r b _ hb =>
    have := hb ((YYl D L₁ L₁').smul_mem r hy)
    rwa [← algebraMap_smul D.host.E r y, smul_smul, ← map_mul, mul_comm] at this

end GlobalTheory.NormSum.MovedLattice


open GlobalTheory.NormSum.MovedLattice in
theorem GlobalTheory.NormSum.pt_mem_La_of_adelic : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ z : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc) → pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) L₁ L₁' := by
  intro D hD cc δ hcc N N' g g' L₁ L₁' h h' z hz
  have hJ : ext D cc * D.host.AA0 ≠ 0 := mul_ne_zero (ext_ne_zero D hcc) (inverseHalfDifferent_ne_zero D)
  have hY : ∀ n ∈ D.host.AA0 * (ext D cc * D.host.AA0)⁻¹, n • z ∈ YYl D L₁ L₁' := by
    intro n hn
    refine FractionalIdeal.mul_induction_on hn (fun a ha j hj => ?_) (fun x y hx hy => ?_)
    · refine Submodule.subset_span ⟨a, ha, j • z, ?_, mul_smul _ _ _⟩
      exact smul_mem_homL D _ _ h h' z j fun a b => inc_mul_mem D hcc hj (hz a b)
    · rw [add_smul]; exact add_mem hx hy
  have h1 : (1 : D.host.E) ∈ ext D cc * (D.host.AA0 * (ext D cc * D.host.AA0)⁻¹) := by
    rw [← mul_assoc, mul_inv_cancel₀ hJ]
    exact FractionalIdeal.one_mem_one _
  have h2 : ∀ e ∈ ext D cc * (D.host.AA0 * (ext D cc * D.host.AA0)⁻¹),
      pt D (tor0 D cc δ) δ (e • z) ∈ La D (tor0 D cc δ) L₁ L₁' := by
    intro e he
    refine FractionalIdeal.mul_induction_on he (fun m hm n hn => ?_) (fun x y hx hy => ?_)
    · rw [mul_smul]
      exact pt_smul_mem D hD.1 cc δ L₁ L₁' hm (hY n hn)
    · rw [add_smul, pt_add]; exact add_mem hx hy
  simpa using h2 1 h1
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_cj_Qbar_eq : ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ),
    ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x : ℂ, x ∈ Qbar → x ∈ M → cj M ρ x = cj Qbar ρ' x := by
  intro M ρ
  let L : IntermediateField ℚ ℂ := M ⊓ Qbar
  have h1 : L ≤ M := inf_le_left
  have h2 : L ≤ Qbar := inf_le_right
  letI : Algebra L Qbar := (IntermediateField.inclusion h2).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ L Qbar := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    exact (map_ratCast (algebraMap ℚ ℂ) r).trans (by simp)
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic L Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := L) (M := ℂ)
    (E := Qbar) (ρ.comp (IntermediateField.inclusion h1))
  refine ⟨φ, fun x hx hM => ?_⟩
  rw [cj_mem ρ hM, cj_mem φ hx]
  have := DFunLike.congr_fun hφ (⟨x, ⟨hM, hx⟩⟩ : L)
  exact this.symm

end GlobalTheory.ThetaConj
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_periodPair_idealCurveLattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := by
  first | exact @GlobalTheory.CurveLattice.exists_periodPair_lamOf | exact GlobalTheory.CurveLattice.exists_periodPair_lamOf | (intros; apply GlobalTheory.CurveLattice.exists_periodPair_lamOf <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.finiteDimensional_modularForm_cuspForm_of_gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le | exact GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le | (intros; apply GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le <;> assumption)
end
