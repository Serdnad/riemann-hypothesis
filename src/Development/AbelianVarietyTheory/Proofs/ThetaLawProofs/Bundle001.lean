module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Nontrivial
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section

section

namespace GlobalTheory.EmbC

open Cardinal TensorProduct

theorem mk_tensor_le (R A B : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (hA : #A ≤ 𝔠) (hB : #B ≤ 𝔠) : #(A ⊗[R] B) ≤ 𝔠 := by
  have h1 : Function.Surjective (fun l : List (A × B) => (l.map (fun p => p.1 ⊗ₜ[R] p.2)).sum) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨[], by simp⟩
    | tmul a b => exact ⟨[(a, b)], by simp⟩
    | add x y hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨m, rfl⟩ := hy
      exact ⟨l ++ m, by simp⟩
  refine (Cardinal.mk_le_of_surjective h1).trans ((Cardinal.mk_list_le_max _).trans ?_)
  refine max_le Cardinal.aleph0_le_continuum ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc #A * #B ≤ 𝔠 * 𝔠 := mul_le_mul' hA hB
    _ = 𝔠 := Cardinal.continuum_mul_self

theorem exists_emb (R A B : Type) [CommRing R] [IsDomain R] [Field A] [Field B] [CharZero A]
    [Algebra R A] [Algebra R B] (hA : #A = 𝔠) (hB : #B = 𝔠)
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B)) :
    ∃ (σ : A →+* ℂ) (σ' : B →+* ℂ), σ.comp (algebraMap R A) = σ'.comp (algebraMap R B) := by
  haveI : Nontrivial (A ⊗[R] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain R A B ha hb
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A ⊗[R] B)
  letI : Field ((A ⊗[R] B) ⧸ m) := Ideal.Quotient.field m
  let L := (A ⊗[R] B) ⧸ m
  let Ω := AlgebraicClosure L
  let p : (A ⊗[R] B) →+* Ω := (algebraMap L Ω).comp (Ideal.Quotient.mk m)
  let i : A →+* Ω := p.comp (Algebra.TensorProduct.includeLeftRingHom)
  let j : B →+* Ω := p.comp (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
  haveI : CharZero Ω := charZero_of_injective_ringHom i.injective
  have hL : #L ≤ 𝔠 :=
    (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (mk_tensor_le R A B hA.le hB.le)
  have hΩ : #Ω = 𝔠 := by
    apply le_antisymm
    · exact (Algebra.IsAlgebraic.cardinalMk_le_max L Ω).trans (max_le hL Cardinal.aleph0_le_continuum)
    · rw [← hA]; exact Cardinal.mk_le_of_injective i.injective
  obtain ⟨e⟩ : Nonempty (Ω ≃+* ℂ) :=
    IsAlgClosed.ringEquiv_of_equiv_of_charZero (by rw [hΩ]; exact Cardinal.aleph0_lt_continuum)
      (Cardinal.eq.mp (by rw [hΩ, Cardinal.mk_complex]))
  refine ⟨e.toRingHom.comp i, e.toRingHom.comp j, ?_⟩
  ext r
  have : (algebraMap R A r) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B r) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  show e (p ((algebraMap R A r) ⊗ₜ[R] (1 : B))) = e (p ((1 : A) ⊗ₜ[R] (algebraMap R B r)))
  rw [this]

theorem exists_comp_eq (R : Type) [CommRing R] [IsDomain R] (f f' : R →+* ℂ)
    (hf : Function.Injective f) (hf' : Function.Injective f') :
    ∃ σ σ' : ℂ →+* ℂ, σ.comp f = σ'.comp f' :=
  @exists_emb R ℂ ℂ _ _ _ _ _ f.toAlgebra f'.toAlgebra Cardinal.mk_complex Cardinal.mk_complex hf hf'

end GlobalTheory.EmbC
end

section

namespace GlobalTheory

open Finset

theorem fwdDiff_iter_affine_pow (g : ℕ) (a b y : ℤ) :
    (fwdDiff (1 : ℤ))^[g] (fun r : ℤ => (a * r + b) ^ g) y = g.factorial * a ^ g := by
  have hsplit : (fun r : ℤ => (a * r + b) ^ g) =
      (fun r : ℤ => ∑ k ∈ range g, (a ^ k * b ^ (g - k) * (g.choose k : ℤ)) * r ^ k) +
        a ^ g • (fun r : ℤ => r ^ g) := by
    funext r
    rw [Pi.add_apply, add_pow, sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, Pi.smul_apply,
      smul_eq_mul]
    congr 1
    · exact sum_congr rfl fun k _ => by ring
    · ring
  have hlow : (fwdDiff (1 : ℤ))^[g]
      (fun r : ℤ => ∑ k ∈ range g, (a ^ k * b ^ (g - k) * (g.choose k : ℤ)) * r ^ k) = 0 :=
    fwdDiff_iter_sum_mul_pow_eq_zero _
  rw [hsplit, fwdDiff_iter_add, hlow, fwdDiff_iter_const_smul, fwdDiff_iter_eq_factorial]
  simp [mul_comm]

theorem alternating_sum_choose_mul_sub_pow :
    ∀ g n l : ℕ, g * n ≤ l → ∑ j ∈ Finset.range (g + 1),
      (-1 : ℤ) ^ j * (g.choose j : ℤ) * (((l - j * n) ^ g : ℕ) : ℤ)
        = (g.factorial * n ^ g : ℕ) := by
  intro g n l hgl
  have key := fwdDiff_iter_affine_pow g (-(n : ℤ)) (l : ℤ) 0
  rw [fwdDiff_iter_eq_sum_shift] at key
  simp only [smul_eq_mul, nsmul_eq_mul, zero_add, mul_one] at key
  have hterm : ∀ k ∈ range (g + 1),
      (-1 : ℤ) ^ k * (g.choose k : ℤ) * (((l - k * n) ^ g : ℕ) : ℤ) =
        (-1) ^ g * ((-1 : ℤ) ^ (g - k) * (g.choose k : ℤ) * (-(n : ℤ) * (k : ℤ) + l) ^ g) := by
    intro k hk
    have hkg : k ≤ g := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkn : k * n ≤ l := le_trans (Nat.mul_le_mul_right n hkg) hgl
    have hsign : (-1 : ℤ) ^ k = (-1) ^ g * (-1) ^ (g - k) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkg
      rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    rw [hsign, Nat.cast_pow, Nat.cast_sub hkn]
    push_cast
    ring
  rw [sum_congr rfl hterm, ← mul_sum, key]
  have hsq : (-1 : ℤ) ^ g * (-1) ^ g = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  push_cast
  rw [neg_pow]
  linear_combination ((g.factorial : ℤ) * (n : ℤ) ^ g) * hsq

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.KeyFin

theorem finite_preimage_of_isPullback_of_finite_base :
    ∀ (X X' S S' : Scheme.{0}) (h : X ⟶ S) (h' : X' ⟶ S') (φ : X' ⟶ X) (f : S' ⟶ S) (Z : Set X),
      LocallyOfFiniteType h → QuasiCompact h → IsPullback φ h' h f → Finite S' → IsClosed Z →
      Z.Finite → (φ ⁻¹' Z).Finite := by
  intro X X' S S' h h' φ f Z _ _ H _ hZ hfin
  let I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hf : Finite I.subscheme := by
    have : Finite (Set.range I.subschemeι) := by rw [hr]; exact hfin.to_subtype
    exact Finite.of_injective_finite_range I.subschemeι.isClosedEmbedding.injective
  have hq : LocallyQuasiFinite (I.subschemeι ≫ h) :=
    .of_finite_preimage_singleton _ fun _ => Set.toFinite _
  have P := (IsPullback.of_hasPullback I.subschemeι φ).paste_vert H
  have h1 : LocallyQuasiFinite (pullback.snd I.subschemeι φ ≫ h') :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) P hq
  have h2 : QuasiCompact (pullback.snd I.subschemeι φ ≫ h') :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) P inferInstance
  have h3 : (Set.univ : Set ↑(pullback I.subschemeι φ)).Finite := by
    have := (Set.toFinite (Set.univ : Set S')).preimage'
      (f := (pullback.snd I.subschemeι φ ≫ h')) fun _ _ =>
        (pullback.snd I.subschemeι φ ≫ h').finite_preimage_singleton _
    simpa using this
  rw [← hr, ← Scheme.Pullback.range_snd, ← Set.image_univ]
  exact h3.image _

end GlobalTheory.KeyFin
end

section

namespace GlobalTheory

theorem entire_eq_zero_or_eq_zero_of_mul_eq_zero {g : ℕ} (A B : (Fin g → ℂ) → ℂ)
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hAB : ∀ z, A z * B z = 0) :
    (∀ z, A z = 0) ∨ (∀ z, B z = 0) := by
  by_cases hz : ∀ z, A z = 0
  · exact Or.inl hz
  right
  obtain ⟨z0, hz0⟩ := not_forall.1 hz
  intro z
  have hLd : Differentiable ℂ (fun t : ℂ => z0 + t • (z - z0)) := by fun_prop
  have ha : Differentiable ℂ (fun t : ℂ => A (z0 + t • (z - z0))) := hA.comp hLd
  have hb : Differentiable ℂ (fun t : ℂ => B (z0 + t • (z - z0))) := hB.comp hLd
  have ha0 : ∀ᶠ t in nhds (0 : ℂ), A (z0 + t • (z - z0)) ≠ 0 := by
    have h0 : A (z0 + (0 : ℂ) • (z - z0)) ≠ 0 := by simpa using hz0
    exact ha.continuous.continuousAt.eventually_ne h0
  have hb0 : (fun t : ℂ => B (z0 + t • (z - z0))) =ᶠ[nhds (0 : ℂ)] 0 := by
    filter_upwards [ha0] with t ht
    exact (mul_eq_zero.1 (hAB (z0 + t • (z - z0)))).resolve_left ht
  have hbA : AnalyticOnNhd ℂ (fun t : ℂ => B (z0 + t • (z - z0))) Set.univ := fun t _ => hb.analyticAt t
  have h1 := hbA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hb0
    (Set.mem_univ (1 : ℂ))
  simpa using h1

theorem entire_eq_mul_of_sq_eq_mul_sq :
    ∀ (g : ℕ) (f h q : (Fin g → ℂ) → ℂ) (C : ℂ), Differentiable ℂ f → Differentiable ℂ h →
      Differentiable ℂ q → (∀ z, f z ^ 2 = C * Complex.exp (2 * q z) * h z ^ 2) →
      ∃ c : ℂ, c ^ 2 = C ∧ ∀ z, f z = c * Complex.exp (q z) * h z := by
  intro g f h q C hf hh hq hsq
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq C (by norm_num : 0 < 2)
  have hF : Differentiable ℂ fun z => f z * Complex.exp (-q z) := hf.mul hq.neg.cexp
  have key : ∀ z, (f z * Complex.exp (-q z) - c * h z) * (f z * Complex.exp (-q z) + c * h z) = 0 := by
    intro z
    have e1 : Complex.exp (-q z) ^ 2 * Complex.exp (2 * q z) = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      convert Complex.exp_zero using 2
      push_cast
      ring
    linear_combination Complex.exp (-q z) ^ 2 * hsq z + C * h z ^ 2 * e1 - h z ^ 2 * hc
  have e2 : ∀ z, Complex.exp (-q z) * Complex.exp (q z) = 1 := by
    intro z
    rw [← Complex.exp_add]
    simp
  rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero (fun z => f z * Complex.exp (-q z) - c * h z)
      (fun z => f z * Complex.exp (-q z) + c * h z) (hF.sub ((differentiable_const c).mul hh))
      (hF.add ((differentiable_const c).mul hh)) key with h1 | h1
  · refine ⟨c, hc, fun z => ?_⟩
    linear_combination Complex.exp (q z) * h1 z - f z * e2 z
  · refine ⟨-c, by rw [neg_sq]; exact hc, fun z => ?_⟩
    linear_combination Complex.exp (q z) * h1 z - f z * e2 z

end GlobalTheory
end

section

namespace GlobalTheory

open Filter Topology

theorem differentiableAt_det_of_entries {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype I] [DecidableEq I] (A : E → Matrix I I ℂ) (x : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun e => A e i j) x) :
    DifferentiableAt ℂ (fun e => (A e).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  exact (HasFDerivAt.finsetProd (fun i _ => (h (σ i) i).hasFDerivAt)).differentiableAt

theorem differentiableOn_coord_of_linearIndependent :
    ∀ (E Z I : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype I] (W : Set E) (Th : I → E → Z → ℂ) (F : E → Z → ℂ) (c : E → I → ℂ), IsOpen W → (∀ k z, DifferentiableOn ℂ (fun e => Th k e z) W) → (∀ z, DifferentiableOn ℂ (fun e => F e z) W) → (∀ e ∈ W, LinearIndependent ℂ (fun k => Th k e)) → (∀ e ∈ W, ∀ z, F e z = ∑ k, c e k * Th k e z) → ∀ k, DifferentiableOn ℂ (fun e => c e k) W := by
  intro E Z I _ _ _ W Th F c hW hTh hF hli hc k e₀ he₀
  classical
  apply DifferentiableAt.differentiableWithinAt
  have hnh : W ∈ 𝓝 e₀ := hW.mem_nhds he₀
  have hspan : Submodule.span ℂ (Set.range (flip (fun k => Th k e₀))) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.2 (hli e₀ he₀)
  have hl : ∀ i : I, ∃ l : Z →₀ ℂ, ∀ j, (∑ z ∈ l.support, l z * Th j e₀ z) = (1 : Matrix I I ℂ) i j := by
    intro i
    have hm : (fun j => (1 : Matrix I I ℂ) i j) ∈
        Submodule.span ℂ (Set.range (flip (fun k => Th k e₀))) := by
      rw [hspan]; trivial
    obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hm
    refine ⟨l, fun j => ?_⟩
    have := congrFun hl j
    simpa [Finsupp.sum, flip, Finset.sum_apply] using this
  choose l hl using hl
  let A : E → Matrix I I ℂ := fun e => Matrix.of fun i j => ∑ z ∈ (l i).support, l i z * Th j e z
  let b : E → I → ℂ := fun e i => ∑ z ∈ (l i).support, l i z * F e z
  have hA0 : A e₀ = 1 := by
    ext i j; exact hl i j
  have hAd : ∀ i j, DifferentiableAt ℂ (fun e => A e i j) e₀ := by
    intro i j
    simp only [A, Matrix.of_apply]
    exact DifferentiableAt.fun_sum fun z _ => ((hTh j z).differentiableAt hnh).const_mul _
  have hbd : ∀ i, DifferentiableAt ℂ (fun e => b e i) e₀ := by
    intro i
    exact DifferentiableAt.fun_sum fun z _ => ((hF z).differentiableAt hnh).const_mul _
  have hdet := differentiableAt_det_of_entries A e₀ hAd
  have hne : (A e₀).det ≠ 0 := by rw [hA0]; simp
  have hnum : DifferentiableAt ℂ (fun e => ((A e).updateCol k (b e)).det) e₀ := by
    refine differentiableAt_det_of_entries _ e₀ fun i j => ?_
    simp only [Matrix.updateCol_apply]
    by_cases h : j = k
    · simpa [h] using hbd i
    · simpa [h] using hAd i j
  have hb : ∀ e ∈ W, b e = (A e).mulVec (c e) := by
    intro e he
    funext i
    simp only [b, A, Matrix.mulVec, dotProduct, Matrix.of_apply, hc e he, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun z _ => by ring
  refine (hnum.mul (hdet.inv hne)).congr_of_eventuallyEq ?_
  filter_upwards [hnh, hdet.continuousAt.eventually_ne hne] with e he hne'
  have h1 : ((A e).updateCol k (b e)).det = (A e).det * c e k := by
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, hb e he, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul]
    simp [Matrix.smul_mulVec]
  simp only [Pi.mul_apply, Pi.inv_apply, h1]
  field_simp

end GlobalTheory
end

section

namespace GlobalTheory.TransposeMulCommute

theorem mul_transpose_eq_of_transpose_mul_eq :
    ∀ {al : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ} {m : ℕ}, (1 : ℕ) ≤ m →
      Matrix.transpose al * al = (↑m : ℤ) • (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ) →
      al * Matrix.transpose al = (↑m : ℤ) • (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ) := by
  intro al m hm h
  have hm0 : (m : ℤ) ≠ 0 := by
    have : m ≠ 0 := by omega
    exact_mod_cast this
  have hdet : al.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hm0 h1.symm
  have h2 : (al * al.transpose) * al = ((m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) * al := by
    rw [Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have h3 := congrArg (fun X => X * al.adjugate) h2
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h3
  ext i j
  have h4 := congrFun (congrFun h3 i) j
  rw [Matrix.smul_apply, Matrix.smul_apply al.det, smul_eq_mul, smul_eq_mul al.det] at h4
  exact mul_left_cancel₀ hdet h4

end GlobalTheory.TransposeMulCommute
end

section

namespace GlobalTheory

open Kronecker

theorem det_kroneckerPower (R : Type) [CommRing R] (N r : ℕ) (B : Matrix (Fin N) (Fin N) R) :
    (Matrix.of fun (I I' : Fin (r + 1) → Fin N) => ∏ c, B (I c) (I' c)).det
      = B.det ^ ((r + 1) * N ^ r) := by
  induction r with
  | zero =>
    have h : (Matrix.of fun (I I' : Fin (0 + 1) → Fin N) => ∏ c, B (I c) (I' c))
        = B.submatrix (Equiv.funUnique (Fin 1) (Fin N)) (Equiv.funUnique (Fin 1) (Fin N)) := by
      ext I I'
      simp
    rw [h, Matrix.det_submatrix_equiv_self]
    simp
  | succ r ih =>
    have h : (Matrix.of fun (I I' : Fin (r + 1 + 1) → Fin N) => ∏ c, B (I c) (I' c))
        = (B ⊗ₖ (Matrix.of fun (I I' : Fin (r + 1) → Fin N) => ∏ c, B (I c) (I' c))).submatrix
          (Fin.consEquiv (fun _ : Fin (r + 1 + 1) => Fin N)).symm
          (Fin.consEquiv (fun _ : Fin (r + 1 + 1) => Fin N)).symm := by
      ext I I'
      rw [Matrix.of_apply, Fin.prod_univ_succ]
      rfl
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, ih, ← pow_mul, ← pow_add]
    congr 1
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_isSymm_mulVec_add_diag_mod_two :
    ∀ (g : ℕ) (n n' : Fin g → ℤ), Even (n ⬝ᵥ n') →
      ∃ S : Matrix (Fin g) (Fin g) ℤ, S.IsSymm ∧
        ∀ i, (2 : ℤ) ∣ (S.mulVec n) i + S i i - n' i := by
  intro g n n' h
  by_cases hall : ∀ i, Even (n i)
  · refine ⟨Matrix.diagonal n', Matrix.isSymm_diagonal _, fun i => ?_⟩
    obtain ⟨k, hk⟩ := hall i
    rw [Matrix.mulVec_diagonal, Matrix.diagonal_apply_eq, hk]
    exact ⟨n' i * k, by ring⟩
  · obtain ⟨p, hp⟩ := not_forall.mp hall
    obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hp
    obtain ⟨m, hm⟩ := h
    refine ⟨Matrix.of fun i j => (if i = p then n' j else 0) + (if j = p then n' i else 0),
      ?_, fun i => ?_⟩
    · ext i j
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      ring
    · have hm' : ∑ j, n' j * n j = m + m := by
        rw [← hm]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      have h2 : ∑ j, (if j = p then n' i else 0) * n j = n' i * n p := by
        simp
      by_cases hi : i = p
      · subst hi
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_true, hm', h2, hk]
        exact ⟨m + n' i * k + n' i, by ring⟩
      · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_neg hi, h2, hk, zero_mul, Finset.sum_const_zero]
        exact ⟨n' i * k, by ring⟩

end GlobalTheory
end
