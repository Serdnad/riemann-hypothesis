module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SatakeDualWeyl.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem exists_endomorphism_representing_sesquilinear_form
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : ∃ A : W →ₗ[ℂ] W, ∀ x y, B x y = ⟪x, A y⟫_ℂ := by
  classical
  let e := stdOrthonormalBasis ℂ W
  refine ⟨∑ j, (B (e j)).smulRight (e j), fun x y => ?_⟩
  conv_lhs => rw [← e.sum_repr' x]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
  LinearMap.smulRight_apply, inner_sum, inner_smul_right, smul_eq_mul, inner_conj_symm]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem invariant_posDef_form_eq_smul_inner_of_irreducible :
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (I : Type) (π : I → (W →L[ℂ] W)) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ i v, ‖π i v‖ = ‖v‖) → (∀ S : Submodule ℂ W, (∀ i, ∀ v ∈ S, π i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i x y, B (π i x) (π i y) = B x y) → (∀ x y, B y x = star (B x y)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → ∃ c : ℝ, 0 < c ∧ (Nontrivial W → ∀ x y, B x y = c * ⟪x, y⟫_ℂ) := by
  intro W _ _ _ I π B hiso hirr hinv hherm hpos
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact ⟨1, one_pos, fun h => absurd h (not_nontrivial W)⟩
  obtain ⟨A, hA⟩ := exists_endomorphism_representing_sesquilinear_form W B
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hAv : A v = μ • v := hv.apply_eq_smul
  have hinner : ∀ i x y, ⟪π i x, π i y⟫_ℂ = ⟪x, y⟫_ℂ := fun i x y =>
    (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).inner_map_map x y
  have hsurj : ∀ i, Function.Surjective (π i) := fun i =>
    (LinearMap.injective_iff_surjective (f := (π i : W →ₗ[ℂ] W))).1
      (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).injective
  let S : Submodule ℂ W :=
    { carrier := {y | ∀ x, B x y = μ * ⟪x, y⟫_ℂ}
      add_mem' := fun {a b} ha hb x => by
        rw [map_add (f := _), inner_add_right, ha x, hb x, mul_add]
      zero_mem' := fun x => by simp
      smul_mem' := fun c a ha x => by
        rw [map_smul, inner_smul_right, ha x, smul_eq_mul]; ring }
  have hS : ∀ y, y ∈ S ↔ ∀ x, B x y = μ * ⟪x, y⟫_ℂ := fun y => Iff.rfl
  have hvS : v ∈ S := by
    rw [hS]; intro x
    rw [hA, hAv, inner_smul_right]
  have hstab : ∀ i, ∀ y ∈ S, π i y ∈ S := by
    intro i y hy
    rw [hS] at hy ⊢
    intro x
    obtain ⟨x', rfl⟩ := hsurj i x
    rw [hinv, hinner, hy]
  have htop : S = ⊤ := by
    rcases hirr S hstab with h | h
    · rw [h] at hvS
      exact absurd ((Submodule.mem_bot ℂ).1 hvS) hv0
    · exact h
  have hall : ∀ x y, B x y = μ * ⟪x, y⟫_ℂ := fun x y =>
    (hS y).1 (htop ▸ Submodule.mem_top) x
  have hvv : B v v = μ * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hall, inner_self_eq_norm_sq_to_K]; simp
  have hn : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv0) 2
  have him : μ.im = 0 := by
    have h1 := congrArg Complex.im (hherm v v)
    rw [hvv] at h1
    simp only [Complex.star_def, Complex.conj_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, mul_zero, zero_add] at h1
    have h2 : μ.im * ‖v‖ ^ 2 = 0 := by linarith
    exact (mul_eq_zero.1 h2).resolve_right hn.ne'
  have hre : 0 < μ.re := by
    have h1 := hpos v hv0
    rw [hvv] at h1
    simp only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero] at h1
    exact (mul_pos_iff_of_pos_right hn).1 h1
  refine ⟨μ.re, hre, fun _ x y => ?_⟩
  have : (μ.re : ℂ) = μ := Complex.ext rfl (by simp [him])
  rw [this, hall]

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem frameForm_symm_zero {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} (hH : Hᴴ = H)
    (x y : Fin N → ℂ) : star x ⬝ᵥ (H *ᵥ y) = star (star y ⬝ᵥ (H *ᵥ x)) := by
  rw [star_dotProduct, star_mulVec, hH, ← dotProduct_mulVec]

private theorem dotProduct_mulVec_sum_smul {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ} {ι : Type}
    [Fintype ι] (x : Fin N → ℂ) (g : ι → ℂ) (v : ι → Fin N → ℂ) :
    star x ⬝ᵥ (H *ᵥ ∑ i, g i • v i) = ∑ i, g i * (star x ⬝ᵥ (H *ᵥ v i)) := by
  simp [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul]

theorem frame_orthogonal_eq_zero {N r k : ℕ} {H : Matrix (Fin N) (Fin N) ℂ}
    {e f : Fin r → Fin N → ℂ} {z : Fin N → ℂ} {w : Fin k → Fin N → ℂ}
    (hN : N = 2 * r + k + 1) (hH : Hᴴ = H)
    (hee : ∀ a b, star (e a) ⬝ᵥ (H *ᵥ e b) = 0) (hff : ∀ a b, star (f a) ⬝ᵥ (H *ᵥ f b) = 0)
    (hef : ∀ a b, star (e a) ⬝ᵥ (H *ᵥ f b) = if a = b then 1 else 0)
    (hz : ∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 ∧ star (f a) ⬝ᵥ (H *ᵥ z) = 0)
    (hzz : star z ⬝ᵥ (H *ᵥ z) ≠ 0)
    (hww : ∀ a b, star (w a) ⬝ᵥ (H *ᵥ w b) = if a = b then 1 else 0)
    (hw : ∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ w a) = 0) ∧
      star z ⬝ᵥ (H *ᵥ w a) = 0)
    (u : Fin N → ℂ) (hu : (∀ c, star (e c) ⬝ᵥ (H *ᵥ u) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ u) = 0) ∧
      star z ⬝ᵥ (H *ᵥ u) = 0) (huw : ∀ a, star (w a) ⬝ᵥ (H *ᵥ u) = 0) : u = 0 := by
  have sym := fun x y => frameForm_symm_zero hH x y
  have hfe : ∀ a b, star (f a) ⬝ᵥ (H *ᵥ e b) = if a = b then 1 else 0 := by
    intro a b
    rw [sym, hef b a]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab, hab.symm]
  have hze : ∀ a, star z ⬝ᵥ (H *ᵥ e a) = 0 := fun a => by rw [sym, (hz a).1, star_zero]
  have hzf : ∀ a, star z ⬝ᵥ (H *ᵥ f a) = 0 := fun a => by rw [sym, (hz a).2, star_zero]
  have hwe : ∀ a c, star (w a) ⬝ᵥ (H *ᵥ e c) = 0 := fun a c => by rw [sym, ((hw a).1 c).1, star_zero]
  have hwf : ∀ a c, star (w a) ⬝ᵥ (H *ᵥ f c) = 0 := fun a c => by rw [sym, ((hw a).1 c).2, star_zero]
  have hwz : ∀ a, star (w a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => by rw [sym, (hw a).2, star_zero]
  have hew : ∀ c a, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 := fun c a => ((hw a).1 c).1
  have hfw : ∀ c a, star (f c) ⬝ᵥ (H *ᵥ w a) = 0 := fun c a => ((hw a).1 c).2
  have hzw : ∀ a, star z ⬝ᵥ (H *ᵥ w a) = 0 := fun a => (hw a).2
  have hez : ∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => (hz a).1
  have hfz : ∀ a, star (f a) ⬝ᵥ (H *ᵥ z) = 0 := fun a => (hz a).2
  set v : (Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit) → Fin N → ℂ :=
    Sum.elim (Sum.elim e f) (Sum.elim w fun _ => z) with hv
  have key : ∀ g : (Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit) → ℂ,
      (∀ j, star (v j) ⬝ᵥ (H *ᵥ ∑ i, g i • v i) = 0) → g = 0 := by
    intro g hg
    simp only [dotProduct_mulVec_sum_smul] at hg
    simp only [Fintype.sum_sum_type] at hg
    funext i
    rcases i with ((a | a) | (a | u))
    · have := hg (.inl (.inr a))
      simpa [hv, hfe, hff, hwe, hfw, hfz, mul_ite] using this
    · have := hg (.inl (.inl a))
      simpa [hv, hee, hef, hew, hez, mul_ite] using this
    · have := hg (.inr (.inl a))
      simpa [hv, hwe, hwf, hww, hwz, mul_ite] using this
    · have := hg (.inr (.inr u))
      simpa [hv, hze, hzf, hzw, hzz] using this
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := key g (fun j => by rw [hg, mulVec_zero, dotProduct_zero])
    exact congrFun this i
  have hcard : Fintype.card ((Fin r ⊕ Fin r) ⊕ (Fin k ⊕ Unit)) = Module.finrank ℂ (Fin N → ℂ) := by
    simp [hN]
    ring
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hu' : u ∈ Submodule.span ℂ (Set.range v) := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu'
  have hg0 := key g (fun j => by
    rw [hg]
    rcases j with ((a | a) | (a | _))
    · simpa [hv] using (hu.1 a).1
    · simpa [hv] using (hu.1 a).2
    · simpa [hv] using huw a
    · simpa [hv] using hu.2)
  rw [← hg, hg0]
  simp

theorem frame_complement_change_of_basis : ∀ (N r k n : ℕ) (h : k = n) (H : Matrix (Fin N) (Fin N) ℂ) (e f : Fin r → Fin N → ℂ) (z : Fin N → ℂ) (w : Fin k → Fin N → ℂ) (q : Fin n → Fin N → ℂ), N = 2 * r + k + 1 → Hᴴ = H → IsUnit H.det → (∀ a b, star (e a) ⬝ᵥ (H *ᵥ e b) = 0) → (∀ a b, star (f a) ⬝ᵥ (H *ᵥ f b) = 0) → (∀ a b, star (e a) ⬝ᵥ (H *ᵥ f b) = if a = b then 1 else 0) → (∀ a, star (e a) ⬝ᵥ (H *ᵥ z) = 0 ∧ star (f a) ⬝ᵥ (H *ᵥ z) = 0) → star z ⬝ᵥ (H *ᵥ z) ≠ 0 → (∀ a b, star (w a) ⬝ᵥ (H *ᵥ w b) = if a = b then 1 else 0) → (∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ w a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ w a) = 0) ∧ star z ⬝ᵥ (H *ᵥ w a) = 0) → (∀ a, (∀ c, star (e c) ⬝ᵥ (H *ᵥ q a) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ q a) = 0) ∧ star z ⬝ᵥ (H *ᵥ q a) = 0) → ∀ G : Matrix (Fin n) (Fin n) ℂ, (∀ a b, G a b = star (q a) ⬝ᵥ (H *ᵥ q b)) → IsUnit G.det → ∃ o : Matrix (Fin n) (Fin n) ℂ, IsUnit o.det ∧ oᴴ * G * o = 1 ∧ ∀ s : Matrix (Fin N) (Fin N) ℂ, sᴴ * H * s = H → (∀ a, s *ᵥ e a = e a ∧ s *ᵥ f a = f a) → s *ᵥ z = z → ∃ m ∈ Matrix.unitaryGroup (Fin n) ℂ, m.submatrix (Fin.cast h) (Fin.cast h) = (Matrix.of fun a b => star (w a) ⬝ᵥ (H *ᵥ (s *ᵥ w b))) ∧ G⁻¹ * (Matrix.of fun a b => star (q a) ⬝ᵥ (H *ᵥ (s *ᵥ q b))) = o * m * o⁻¹ := by
  intro N r k n h H e f z w q hN hH _hdet hee hff hef hz hzz hww hw hq G hG hGdet
  subst h
  have sym := fun x y => frameForm_symm_zero hH x y
  have expand : ∀ x : Fin N → ℂ, ((∀ c, star (e c) ⬝ᵥ (H *ᵥ x) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ x) = 0) ∧
      star z ⬝ᵥ (H *ᵥ x) = 0) → x = ∑ a, (star (w a) ⬝ᵥ (H *ᵥ x)) • w a := by
    intro x hx
    have h0 := frame_orthogonal_eq_zero hN hH hee hff hef hz hzz hww hw
      (x - ∑ a, (star (w a) ⬝ᵥ (H *ᵥ x)) • w a) ?_ ?_
    · exact sub_eq_zero.mp h0
    · refine ⟨fun c => ⟨?_, ?_⟩, ?_⟩
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, (hx.1 c).1, fun a => ((hw a).1 c).1]
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, (hx.1 c).2, fun a => ((hw a).1 c).2]
      · simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, hx.2, fun a => (hw a).2]
    · intro a
      simp [mulVec_sub, dotProduct_sub, dotProduct_mulVec_sum_smul, hww, mul_ite]
  have parseval : ∀ x y : Fin N → ℂ,
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ y) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ y) = 0) ∧ star z ⬝ᵥ (H *ᵥ y) = 0) →
      star x ⬝ᵥ (H *ᵥ y) = ∑ c, star (star (w c) ⬝ᵥ (H *ᵥ x)) * (star (w c) ⬝ᵥ (H *ᵥ y)) := by
    intro x y hy
    conv_lhs => rw [expand y hy]
    rw [dotProduct_mulVec_sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sym x (w c), mul_comm]
  set P := Matrix.of fun c b => star (w c) ⬝ᵥ (H *ᵥ q b) with hPdef
  have hGP : G = Pᴴ * P := by
    ext a b
    rw [hG, parseval (q a) (q b) (hq b), Matrix.mul_apply]
    simp [hPdef, Matrix.conjTranspose_apply]
  have hP : IsUnit P.det := by
    rw [hGP, Matrix.det_mul, Matrix.det_conjTranspose] at hGdet
    exact isUnit_of_mul_isUnit_right hGdet
  have hPh : IsUnit Pᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hP.star
  refine ⟨P⁻¹, Matrix.isUnit_nonsing_inv_det _ hP, ?_, ?_⟩
  · rw [hGP, Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_assoc (Pᴴ)⁻¹,
      Matrix.nonsing_inv_mul _ hPh, Matrix.one_mul, Matrix.mul_nonsing_inv _ hP]
  intro s hs hfix hzfix
  have pres : ∀ x y : Fin N → ℂ, star (s *ᵥ x) ⬝ᵥ (H *ᵥ (s *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
    intro x y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hs]
  have sperp : ∀ x : Fin N → ℂ,
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ x) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ x) = 0) ∧ star z ⬝ᵥ (H *ᵥ x) = 0) →
      ((∀ c, star (e c) ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0 ∧ star (f c) ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0) ∧
        star z ⬝ᵥ (H *ᵥ (s *ᵥ x)) = 0) := by
    intro x hx
    refine ⟨fun c => ⟨?_, ?_⟩, ?_⟩
    · rw [← (hfix c).1, pres]; exact (hx.1 c).1
    · rw [← (hfix c).2, pres]; exact (hx.1 c).2
    · rw [← hzfix, pres]; exact hx.2
  set M := Matrix.of fun a b => star (w a) ⬝ᵥ (H *ᵥ (s *ᵥ w b)) with hMdef
  refine ⟨M, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply, ← hww a b, ← pres (w a) (w b),
      parseval _ _ (sperp _ (hw b))]
    simp [hMdef, Matrix.conjTranspose_apply]
  · ext a b
    simp [hMdef]
  · have hQ : (Matrix.of fun a b => star (q a) ⬝ᵥ (H *ᵥ (s *ᵥ q b))) = Pᴴ * (M * P) := by
      ext a b
      have hsq : s *ᵥ q b = ∑ d, P d b • (s *ᵥ w d) := by
        conv_lhs => rw [expand (q b) (hq b)]
        rw [mulVec_sum]
        simp [mulVec_smul, hPdef]
      rw [Matrix.of_apply, parseval _ _ (sperp _ (hq b)), Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hsq, dotProduct_mulVec_sum_smul, Matrix.mul_apply]
      simp [hPdef, hMdef, Matrix.conjTranspose_apply, mul_comm]
    rw [hQ, hGP, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Pᴴ)⁻¹, Matrix.nonsing_inv_mul _ hPh, Matrix.one_mul, Matrix.mul_assoc]

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.TypePrimeProduct

theorem natPrime_not_mem_of_other (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpv : (p : 𝓞 F) ∈ v.asIdeal) : (q : 𝓞 F) ∉ v.asIdeal := by
  intro hqv
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hZ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hO : IsCoprime (p : 𝓞 F) (q : 𝓞 F) := by
    have := hZ.map (Int.castRingHom (𝓞 F))
    simpa using this
  obtain ⟨a, b, hab⟩ := hO
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hab]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hpv) (v.asIdeal.mul_mem_left b hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem isUnit_natCast_of_not_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (q : ℕ) (hq : (q : 𝓞 F) ∉ v.asIdeal) :
    IsUnit ((q : ℕ) : v.adicCompletionIntegers F) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (q : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hq] at h
  simpa using h

theorem main_two (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpv : (p : 𝓞 F) ∈ v.asIdeal)
    (hm : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((p : ℕ) : v.adicCompletionIntegers F)}) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((p * q : ℕ) : v.adicCompletionIntegers F)} ∧
      ((p * q : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hqv := natPrime_not_mem_of_other F v hp hq hpq hpv
  refine ⟨?_, ?_⟩
  · rw [hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit (isUnit_natCast_of_not_mem F v q hqv)]
  · rw [Nat.cast_mul]; exact v.asIdeal.mul_mem_right _ hpv

end GlobalTheory.St.G.TypePrimeProduct


open GlobalTheory.St.G.TypePrimeProduct in
theorem GlobalTheory.St.G.TypePrimeProduct.uniformiser_prod : ∀ (F : Type) [Field F] [NumberField F] (gp : Fin 2 → ℕ), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp i : ℕ) : v.adicCompletionIntegers F)} → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp 0 * gp 1 : ℕ) : v.adicCompletionIntegers F)} ∧ ((gp 0 * gp 1 : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ∃ q : ℕ, 0 < q ∧ gp 0 * gp 1 = gp i * q := by
  intro F _ _ gp hgp hne i v hv hm
  fin_cases i
  · obtain ⟨h1, h2⟩ := main_two F v (hgp 0) (hgp 1) hne hv hm
    exact ⟨h1, h2, gp 1, (hgp 1).pos, rfl⟩
  · obtain ⟨h1, h2⟩ := main_two F v (hgp 1) (hgp 0) hne.symm hv hm
    rw [mul_comm (gp 0)]
    exact ⟨h1, h2, gp 0, (hgp 0).pos, rfl⟩
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.invariant_posDef_form_eq_smul_inner_of_irreducible' : ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (I : Type) (π : I → (W →L[ℂ] W)) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ i v, ‖π i v‖ = ‖v‖) → (∀ S : Submodule ℂ W, (∀ i, ∀ v ∈ S, π i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i x y, B (π i x) (π i y) = B x y) → (∀ x y, B y x = star (B x y)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → ∃ c : ℝ, 0 < c ∧ (Nontrivial W → ∀ x y, B x y = c * ⟪x, y⟫_ℂ) := by
  first | exact @GlobalTheory.invariant_posDef_form_eq_smul_inner_of_irreducible | exact GlobalTheory.invariant_posDef_form_eq_smul_inner_of_irreducible | (intros; apply GlobalTheory.invariant_posDef_form_eq_smul_inner_of_irreducible <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.uniformiser_product_type_primes : ∀ (F : Type) [Field F] [NumberField F] (gp : Fin 2 → ℕ), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp i : ℕ) : v.adicCompletionIntegers F)} → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp 0 * gp 1 : ℕ) : v.adicCompletionIntegers F)} ∧ ((gp 0 * gp 1 : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ∃ q : ℕ, 0 < q ∧ gp 0 * gp 1 = gp i * q := by
  first | exact @GlobalTheory.St.G.TypePrimeProduct.uniformiser_prod | exact GlobalTheory.St.G.TypePrimeProduct.uniformiser_prod | (intros; apply GlobalTheory.St.G.TypePrimeProduct.uniformiser_prod <;> assumption)

end
end
