module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle002
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
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
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.RowExt

theorem exists_right_inv {E : Type} [Field E] [NumberField E] {κ ι : Type} [Fintype κ] [Fintype ι]
    [DecidableEq κ] (c : E) (W : Matrix κ ι E) (hW : IntM W)
    (hli : LinearIndependent E (fun i => W i))
    (hprim : ∀ t : κ → E, (∀ j, IsIntegral ℤ ((t ᵥ* W) j)) → ∀ i, IsIntegral ℤ (c * t i)) :
    ∃ X : Matrix ι κ E, IntM X ∧ W * X = c • (1 : Matrix κ κ E) := by
  classical
  have hinj : LinearMap.ker W.vecMulLinear = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Matrix.vecMul_injective_iff.mpr hli
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hg' : ∀ t, g (t ᵥ* W) = t := fun t => LinearMap.congr_fun hg t
  let j : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → E) := (Algebra.linearMap (𝓞 E) E).compLeft ι
  let q : (ι → E) →ₗ[E] (ι → E) := LinearMap.id - W.vecMulLinear ∘ₗ g
  let φ : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → E) := (q.restrictScalars (𝓞 E)) ∘ₗ j
  haveI : Module.Finite (𝓞 E) (LinearMap.range φ) := inferInstance
  haveI : Module.FinitePresentation (𝓞 E) (LinearMap.range φ) :=
    Module.finitePresentation_of_finite _ _
  haveI : Module.Flat (𝓞 E) (LinearMap.range φ) := inferInstance
  haveI : Module.Projective (𝓞 E) (LinearMap.range φ) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ.rangeRestrict LinearMap.id
    φ.surjective_rangeRestrict
  let r : (ι → 𝓞 E) →ₗ[𝓞 E] (ι → 𝓞 E) := LinearMap.id - s ∘ₗ φ.rangeRestrict
  have hr : ∀ m, φ (r m) = 0 := by
    intro m
    have := congrArg Subtype.val (LinearMap.congr_fun hs (φ.rangeRestrict m))
    simp only [r, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
    rw [sub_eq_zero]
    exact this.symm
  have hr' : ∀ m, g (j (r m)) ᵥ* W = j (r m) := by
    intro m
    have : j (r m) - g (j (r m)) ᵥ* W = 0 := hr m
    exact (sub_eq_zero.mp this).symm
  let h : (ι → 𝓞 E) →ₗ[𝓞 E] (κ → E) := (g.restrictScalars (𝓞 E)) ∘ₗ j ∘ₗ r
  refine ⟨Matrix.of fun a k => c * h (Pi.single a 1) k, ?_, ?_⟩
  · intro a k
    refine hprim _ (fun b => ?_) k
    show IsIntegral ℤ ((g (j (r _)) ᵥ* W) b)
    rw [hr']
    exact RingOfIntegers.isIntegral_coe _
  · ext i k
    let w : ι → 𝓞 E := fun a => ⟨W i a, hW i a⟩
    have hjw : j w = Pi.single i 1 ᵥ* W := by
      rw [Matrix.single_one_vecMul]; rfl
    have hφw : φ.rangeRestrict w = 0 := by
      apply Subtype.ext
      show j w - g (j w) ᵥ* W = 0
      rw [hjw, hg', sub_self]
    have hw : h w = Pi.single i 1 := by
      show g (j (w - s (φ.rangeRestrict w))) = _
      rw [hφw, map_zero, sub_zero, hjw, hg']
    have hw2 : w = ∑ a, w a • Pi.single a 1 := pi_eq_sum_univ' w

    rw [hw2, map_sum] at hw
    have := congrFun hw k
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply] at this
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : (1 : Matrix κ κ E) i k = (Pi.single i 1 : κ → E) k := by
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [h1, ← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, mul_left_comm]
    rfl

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {α β γ : Type}

theorem ccT_eq (A : Matrix α β E) : ccT A = Aᴴ := rfl

omit [NumberField E] [IsCMField E] in
theorem intM_mul [Fintype β] {A : Matrix α β E} {B : Matrix β γ E} (hA : IntM A) (hB : IntM B) :
    IntM (A * B) := fun a c => by
  rw [Matrix.mul_apply]
  exact IsIntegral.sum _ fun b _ => (hA a b).mul (hB b c)

theorem intM_conj {A : Matrix α β E} (hA : IntM A) : IntM Aᴴ := fun a b =>
  (hA b a).map ((IsCMField.complexConj E).toAlgHom.restrictScalars ℤ)

omit [NumberField E] [IsCMField E] in
theorem intM_nat {A : Matrix α β E} (n : ℕ) (hA : IntM A) : IntM ((n : E) • A) := fun a b =>
  (isIntegral_natCast n).mul (hA a b)

omit [NumberField E] [IsCMField E] in
theorem intM_J [DecidableEq α] : IntM (Matrix.J α E) := by
  rintro (a | a) (b | b) <;> by_cases h : a = b <;>
    simp [Matrix.J, Matrix.one_apply, h, isIntegral_zero, isIntegral_one, isIntegral_one.neg]

theorem J_conj [DecidableEq α] : (Matrix.J α E)ᴴ = -Matrix.J α E := by
  simp [Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]

end

theorem exists_unitary_ext :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N c : ℕ), 0 < c → ∃ c' : ℕ, 0 < c' ∧
      ∀ W : Matrix (Fin N) (Fin N ⊕ Fin N) E, IntM W → LinearIndependent E (fun i => W i) →
        W * Matrix.J (Fin N) E * ccT W = 0 →
        (∀ t : Fin N → E, (∀ j, IsIntegral ℤ ((t ᵥ* W) j)) → ∀ i, IsIntegral ℤ ((c : E) * t i)) →
        ∃ γ ∈ UU E N, Den c' γ ∧ ∀ a, γ (Sum.inr a) = W a := by
  intro E _ _ _ N c hc
  refine ⟨2 * c * c, by positivity, fun W hW hli hiso hprim => ?_⟩
  obtain ⟨X, hX, hWX⟩ := exists_right_inv (c : E) W hW hli hprim
  rw [ccT_eq] at hiso
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  set J := Matrix.J (Fin N) E with hJ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hJc : Jᴴ = -J := J_conj
  have hJi : IntM J := intM_J
  obtain ⟨V₀, hV₀⟩ : ∃ V₀ : Matrix (Fin N) (Fin N ⊕ Fin N) E, V₀ = (c : E)⁻¹ • (Xᴴ * J) := ⟨_, rfl⟩
  have hcV : (c : E) • V₀ = Xᴴ * J := by rw [hV₀, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hVi : IntM ((c : E) • V₀) := hcV ▸ intM_mul (intM_conj hX) hJi
  have h1 : V₀ * J * Wᴴ = -1 := by
    rw [hV₀, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc Xᴴ, hJJ, Matrix.mul_neg,
      Matrix.mul_one, Matrix.neg_mul, ← Matrix.conjTranspose_mul, hWX]
    simp [smul_smul, hc0]
  have skew : ∀ A B : Matrix (Fin N) (Fin N ⊕ Fin N) E, (A * J * Bᴴ)ᴴ = -(B * J * Aᴴ) := by
    intro A B
    simp [Matrix.conjTranspose_mul, hJc, Matrix.mul_assoc]
  have h2 : W * J * V₀ᴴ = 1 := by
    have := skew V₀ W
    rw [h1] at this
    simpa using this.symm
  obtain ⟨S, hS⟩ : ∃ S, S = V₀ * J * V₀ᴴ := ⟨_, rfl⟩
  have hSc : Sᴴ = -S := hS ▸ skew V₀ V₀
  obtain ⟨T, hT⟩ : ∃ T, T = (-(2 : E)⁻¹) • S := ⟨_, rfl⟩
  have hTc : Tᴴ = -T := by
    rw [hT, Matrix.conjTranspose_smul, hSc]; simp
  obtain ⟨V, hV⟩ : ∃ V, V = V₀ + T * W := ⟨_, rfl⟩
  have k2 : W * J * Vᴴ = 1 := by
    rw [hV, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.mul_add, h2,
      ← Matrix.mul_assoc, hiso, Matrix.zero_mul, add_zero]
  have k1 : V * J * Wᴴ = -1 := by
    have := skew W V
    rw [k2] at this
    rw [← neg_neg (V * J * Wᴴ), ← this]; simp
  have k0 : V * J * Vᴴ = 0 := by
    have e : V * J * V₀ᴴ = S + T := by
      rw [hV, Matrix.add_mul, Matrix.add_mul, ← hS, Matrix.mul_assoc T, Matrix.mul_assoc T, h2,
        Matrix.mul_one]
    conv_lhs => rw [show Vᴴ = V₀ᴴ + Wᴴ * Tᴴ by
      rw [hV, Matrix.conjTranspose_add, Matrix.conjTranspose_mul]]
    rw [Matrix.mul_add, e, ← Matrix.mul_assoc, k1, hTc, hT]
    simp only [Matrix.neg_mul, Matrix.one_mul, neg_neg]
    rw [add_assoc, ← add_smul, show (-(2 : E)⁻¹ + -(2 : E)⁻¹) = -1 by norm_num]
    simp
  have key : Matrix.fromRows V W * J * (Matrix.fromRows V W)ᴴ = J := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, k0, k1, k2, hiso]
    rfl
  refine ⟨Matrix.fromRows V W, ?_, ?_, fun a => rfl⟩
  · generalize Matrix.fromRows V W = g at key
    show gᴴ * J * g = J
    have e1 : g * (J * gᴴ * -J) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key, Matrix.mul_neg, hJJ, neg_neg]
    have e2 := mul_eq_one_comm.mp e1
    have e3 : J * (J * gᴴ * -J * g) = J := by rw [e2, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ] at e3
    simpa using e3
  · have hVV : ((2 * c * c : ℕ) : E) • V = ((2 * c : ℕ) : E) • ((c : E) • V₀) -
        ((c : E) • V₀) * J * ((c : E) • V₀)ᴴ * W := by
      rw [hV, hT, hS]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
        star_natCast, sub_eq_add_neg, ← neg_smul]
      congr 2
      · push_cast; ring
      · push_cast; field_simp
    have i1 := intM_nat (2 * c) hVi
    have i2 := intM_mul (intM_mul (intM_mul hVi hJi) (intM_conj hVi)) hW
    rintro (a | a) b
    · show IsIntegral ℤ ((((2 * c * c : ℕ) : E) • V) a b)
      rw [hVV]
      exact (i1 a b).sub (i2 a b)
    · exact intM_nat (2 * c * c) hW a b

end GlobalTheory.SW.RowExt
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.HaarAlg

variable {K : Type} [Field K] {κ ι : Type}

theorem intM_add {x y : Matrix κ ι K} (hx : IntM x) (hy : IntM y) : IntM (x + y) :=
  fun k i => (hx k i).add (hy k i)

theorem intM_natCast_smul (n : ℕ) {x : Matrix κ ι K} (hx : IntM x) : IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul, ← nsmul_eq_mul]
  exact (hx k i).nsmul n

theorem hasLevel_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (S : ℕ) :
    HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact intM_natCast_smul S (h.1 x hx)
  · rw [Nat.cast_mul, mul_smul]
    exact h.2 x _ (intM_natCast_smul S hy)

theorem exists_common_level {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ∃ R : ℕ, 0 < R ∧ HasLevel R φ ∧ HasLevel R ψ := by
  obtain ⟨R, hR, h1⟩ := hφ
  obtain ⟨S, hS, h2⟩ := hψ
  exact ⟨R * S, Nat.mul_pos hR hS, hasLevel_mul h1 S, mul_comm S R ▸ hasLevel_mul h2 R⟩

theorem hasLevel_map₂ {R : ℕ} {φ ψ : Matrix κ ι K → ℂ} (h1 : HasLevel R φ) (h2 : HasLevel R ψ)
    (f : ℂ → ℂ → ℂ) (hf : f 0 0 = 0) : HasLevel R fun x => f (φ x) (ψ x) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_cases a : φ x = 0
    · by_cases b : ψ x = 0
      · exact (hx (by simp only [a, b, hf])).elim
      · exact h2.1 x b
    · exact h1.1 x a
  · simp only [h1.2 x y hy, h2.2 x y hy]

theorem apply_add_of_mem_perSub {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ)
    {p : Matrix κ ι K} (hp : p ∈ perSub K κ ι R) : ∀ x, φ (x + p) = φ x := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact fun x => h.2 x y hy
  | zero => simp
  | add p q _ _ hp hq => intro x; rw [← add_assoc, hq, hp]
  | neg p _ hp => intro x; rw [← hp (x + -p)]; simp

theorem apply_out_mk {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (x : Matrix κ ι K) :
    φ (Quotient.out (QuotientAddGroup.mk x : Matrix κ ι K ⧸ perSub K κ ι R)) = φ x := by
  obtain ⟨p, hp⟩ := QuotientAddGroup.mk_out_eq_mul (perSub K κ ι R) x
  rw [hp]
  exact apply_add_of_mem_perSub h p.2 x

theorem exists_natCast_smul_intM [NumberField K] [Fintype κ] [Fintype ι] (b : Matrix κ ι K) :
    ∃ N : ℕ, 0 < N ∧ IntM ((N : K) • b) := by
  classical
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : κ × ι => b p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, fun k i => ?_⟩
  have h := hy (b k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e, Int.cast_natCast] at h; exact h
  · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at h
    simpa using h.neg

theorem hasLevel_translate {R N : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) {b : Matrix κ ι K}
    (hb : IntM ((N : K) • b)) : HasLevel (R * N) fun x => φ (x - b) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have e : ((R * N : ℕ) : K) • x = (N : K) • ((R : K) • (x - b)) + (R : K) • ((N : K) • b) := by
      rw [Nat.cast_mul]; module
    rw [e]
    exact intM_add (intM_natCast_smul N (h.1 _ hx)) (intM_natCast_smul R hb)
  · show φ _ = φ _
    rw [add_sub_right_comm]
    exact (hasLevel_mul h N).2 _ y hy

theorem finsum_translate {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (b : Matrix κ ι K) :
    ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ (q.out - b) =
      ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ q.out := by
  rw [← finsum_comp_equiv (Equiv.subRight (QuotientAddGroup.mk b :
    Matrix κ ι K ⧸ perSub K κ ι R)) (f := fun q => φ q.out)]
  refine finsum_congr fun q => ?_
  rw [← apply_out_mk h (q.out - b), QuotientAddGroup.mk_sub, QuotientAddGroup.out_eq']
  rfl

end GlobalTheory.SW.HaarAlg


open GlobalTheory.SW.HaarAlg in
theorem GlobalTheory.SW.isSB_algebra_haar_linear : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (φ ψ : Matrix κ ι K → ℂ), IsSB φ → IsSB ψ → IsSB (φ + ψ) ∧ (∀ c : ℂ, IsSB (c • φ)) ∧ IsSB (φ * ψ) ∧ IsSB (fun x : Matrix κ ι K => conj (φ x)) ∧ haar (φ + ψ) = haar φ + haar ψ ∧ (∀ c : ℂ, haar (c • φ) = c * haar φ) ∧ haar (fun x : Matrix κ ι K => conj (φ x)) = conj (haar φ) ∧ ∀ b : Matrix κ ι K, IsSB (fun x : Matrix κ ι K => φ (x - b)) ∧ haar (fun x : Matrix κ ι K => φ (x - b)) = haar φ := by
  intro K κ ι _ _ _ _ φ ψ hφ hψ
  obtain ⟨R, hR, h1, h2⟩ := exists_common_level hφ hψ
  have hadd : HasLevel R (φ + ψ) := hasLevel_map₂ h1 h2 (fun a b => a + b) (by simp)
  have hsmul : ∀ c : ℂ, HasLevel R (c • φ) := fun c =>
    hasLevel_map₂ h1 h2 (fun a _ => c * a) (by simp)
  have hmul : HasLevel R (φ * ψ) := hasLevel_map₂ h1 h2 (fun a b => a * b) (by simp)
  have hconj : HasLevel R (fun x => conj (φ x)) :=
    hasLevel_map₂ h1 h2 (fun a _ => conj a) (by simp)
  obtain ⟨e1, f1⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R φ hR h1
  obtain ⟨e2, f2⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R ψ hR h2
  refine ⟨⟨R, hR, hadd⟩, fun c => ⟨R, hR, hsmul c⟩, ⟨R, hR, hmul⟩, ⟨R, hR, hconj⟩, ?_,
    fun c => ?_, ?_, fun b => ?_⟩
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hadd).1, e1, e2]
    unfold haarAt
    rw [← mul_add, ← finsum_add_distrib f1 f2]
    rfl
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR (hsmul c)).1, e1]
    unfold haarAt
    rw [mul_left_comm c]
    congr 1
    exact ((AddMonoidHom.mulLeft c).map_finsum f1).symm
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hconj).1, e1]
    unfold haarAt
    rw [map_mul, map_inv₀, map_pow, map_natCast]
    congr 1
    exact ((starRingEnd ℂ).toAddMonoidHom.map_finsum f1).symm
  · obtain ⟨N, hN, hb⟩ := exists_natCast_smul_intM b
    have hRN := Nat.mul_pos hR hN
    have ht := hasLevel_translate h1 hb
    refine ⟨⟨_, hRN, ht⟩, ?_⟩
    rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN ht).1, (GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN (hasLevel_mul h1 N)).1]
    unfold haarAt
    rw [finsum_translate (hasLevel_mul h1 N) b]
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι, (spDen σ τ).det ≠ 0 ∧ spAct σ τ ∈ Siegel ι ∧ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁).IsSymm ∧ (spDen σ τ)ᵀ * (spAct σ τ).map (fun z => (z.im : ℂ)) * (spDen σ τ).map conj = τ.map (fun z => (z.im : ℂ)) ∧ ∀ σ' ∈ Matrix.symplecticGroup ι ℚ, spDen (σ' * σ) τ = spDen σ' (spAct σ τ) * spDen σ τ ∧ spAct (σ' * σ) τ = spAct σ' (spAct σ τ) := by
  first | exact @GlobalTheory.SiegelAction.symplectic_action | exact GlobalTheory.SiegelAction.symplectic_action | (intros; apply GlobalTheory.SiegelAction.symplectic_action <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.Calc

theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m n,
    pow_mul b, hb, ← pow_mul]

theorem ph_inv {a : ℂ} (ha : Ph a) : Ph a⁻¹ := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [inv_pow, ha, norm_inv, Complex.ofReal_inv, inv_pow]

theorem isMu_of_ph {a : ℂ} (ha : Ph a) (h : ‖a‖ = 1) : IsMu a := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [ha, h]; simp⟩

theorem ph_cancel {a b : ℂ} (hb0 : b ≠ 0) (hb : Ph b) (hab : Ph (a * b)) : Ph a := by
  have h := ph_mul hab (ph_inv hb)
  rwa [mul_assoc, mul_inv_cancel₀ hb0, mul_one] at h


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.Phase.Calc.calculus : (∀ a b : ℂ, _root_.GlobalTheory.Phase.Ph a → _root_.GlobalTheory.Phase.Ph b → _root_.GlobalTheory.Phase.Ph (a * b)) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.Ph a → _root_.GlobalTheory.Phase.Ph (conj a) ∧ _root_.GlobalTheory.Phase.Ph a⁻¹) ∧
    (∀ t : ℝ, _root_.GlobalTheory.Phase.Ph (t : ℂ)) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.IsMu a → _root_.GlobalTheory.Phase.Ph a ∧ ‖a‖ = 1) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.Ph a → ‖a‖ = 1 → _root_.GlobalTheory.Phase.IsMu a) ∧
    (∀ a b : ℂ, _root_.GlobalTheory.Phase.IsMu a → _root_.GlobalTheory.Phase.IsMu b → _root_.GlobalTheory.Phase.IsMu (a * b) ∧ _root_.GlobalTheory.Phase.IsMu a⁻¹ ∧ _root_.GlobalTheory.Phase.IsMu (conj a)) ∧
    (∀ (a : ℂ) (k : ℕ), 0 < k → (_root_.GlobalTheory.Phase.IsMu (a ^ k) → _root_.GlobalTheory.Phase.IsMu a) ∧ (_root_.GlobalTheory.Phase.Ph (a ^ k) → _root_.GlobalTheory.Phase.Ph a)) ∧
    (∀ q : ℚ, _root_.GlobalTheory.Phase.IsMu (cexp (π * I * (q : ℂ)))) ∧ ∀ a b : ℂ, b ≠ 0 → _root_.GlobalTheory.Phase.Ph b → _root_.GlobalTheory.Phase.Ph (a * b) → _root_.GlobalTheory.Phase.Ph a := by
  refine ⟨fun a b ha hb => ha.mul hb, fun a ha => ⟨?_, ha.inv⟩, fun t => ?_, fun a ha => ?_,
    fun a ha h1 => ?_, fun a b ha hb => ⟨?_, ?_, ?_⟩, fun a k hk => ⟨?_, ?_⟩, fun q => ?_,
    fun a b hb0 hb hab => ?_⟩
  · obtain ⟨m, hm, h⟩ := ha
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, h, Complex.norm_conj, map_pow, Complex.conj_ofReal]
  · refine ⟨2, two_pos, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, ← ofReal_pow, ← ofReal_pow, sq_abs]
  · obtain ⟨m, hm, h⟩ := ha
    have hn : ‖a‖ = 1 := by
      have h' : ‖a‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 h'
    exact ⟨⟨m, hm, by rw [h, hn, ofReal_one, one_pow]⟩, hn⟩
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [h, h1, ofReal_one, one_pow]⟩
  · obtain ⟨m, hm, h⟩ := ha
    obtain ⟨n, hn, h'⟩ := hb
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [mul_pow, pow_mul, h, pow_mul', h', one_pow, one_pow, one_mul]
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [inv_pow, h, inv_one]⟩
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [← map_pow, h, map_one]⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul, h]⟩
  · rintro ⟨m, hm, h⟩
    refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
    rw [pow_mul, h, norm_pow, ofReal_pow, ← pow_mul]
  · refine ⟨2 * q.den, by positivity, ?_⟩
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨q.num, ?_⟩
    have hq : (q : ℂ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    have hd : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [hq]
    field_simp
    push_cast
    ring
  · have := hab.mul hb.inv
    rwa [mul_inv_cancel_right₀ hb0] at this

end GlobalTheory.Phase.Calc
end
