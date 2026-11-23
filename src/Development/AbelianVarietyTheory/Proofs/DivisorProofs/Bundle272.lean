module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.WeightedHomogeneousComponentMemElimIdeal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.MvPolynomial.Funext
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle005
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Hom.PowersetCard
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle159
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

open scoped ComplexOrder

namespace GlobalTheory

theorem IsSiegel.neg_mul_inv_of_symplectic (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (hdet : P.det ≠ 0) (hsym : (-(Q * P⁻¹)).IsSymm) :
    GlobalTheory.IsSiegel (-(Q * P⁻¹)) := by
  refine ⟨hsym, ?_⟩
  set A : Matrix l l ℂ := fun a b => (s (.inl a) (.inl b) : ℂ) with hA
  set B : Matrix l l ℂ := fun a b => (s (.inl a) (.inr b) : ℂ) with hB
  set C : Matrix l l ℂ := fun a b => (s (.inr a) (.inl b) : ℂ) with hC
  set D : Matrix l l ℂ := fun a b => (s (.inr a) (.inr b) : ℂ) with hD
  have hPe : P = A - I • B := by ext a b; simp only [hP]; rfl
  have hQe : Q = C - I • D := by ext a b; simp only [hQ]; rfl
  have hsc : s.map (Complex.ofRealHom : ℝ →+* ℂ) = fromBlocks A B C D := by
    ext (a|a) (b|b) <;> rfl
  have hJ : (J l ℝ).map (Complex.ofRealHom : ℝ →+* ℂ) = J l ℂ := by
    ext (a|a) (b|b) <;> simp [J, Matrix.one_apply] <;> split_ifs <;> simp
  have hc : (fromBlocks A B C D)ᵀ * J l ℂ * fromBlocks A B C D = J l ℂ := by
    have h1 := congrArg (fun M => M.map (Complex.ofRealHom : ℝ →+* ℂ)) (SymplecticGroup.mem_iff'.mp hs)
    simp only [Matrix.map_mul, transpose_map, hJ, hsc] at h1
    exact h1
  rw [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hc
  obtain ⟨h11, h12, h21, h22⟩ := hc
  simp at h11 h12 h21 h22
  have star_real : ∀ X : Matrix l l ℂ, (∀ a b, star (X a b) = X a b) → Xᴴ = Xᵀ := by
    intro X hX; ext a b; simp [conjTranspose_apply, hX]
  have hAs : Aᴴ = Aᵀ := star_real A (fun a b => by simp [A])
  have hBs : Bᴴ = Bᵀ := star_real B (fun a b => by simp [B])
  have hCs : Cᴴ = Cᵀ := star_real C (fun a b => by simp [C])
  have hDs : Dᴴ = Dᵀ := star_real D (fun a b => by simp [D])
  have key : Pᴴ * Q - Qᴴ * P = -(2 * I) • (1 : Matrix l l ℂ) := by
    rw [hPe, hQe]
    simp only [conjTranspose_sub, conjTranspose_smul, hAs, hBs, hCs, hDs, Complex.star_def, conj_I,
      sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
    linear_combination (norm := (match_scalars <;> ring_nf <;> (try simp only [I_sq]) <;> ring_nf)) -h11 - h22 + I • h12 - I • h21
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  set τ := -(Q * P⁻¹) with hτ
  have hτP : τ * P = -Q := by rw [hτ, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  have hsymm : ∀ a b, τ b a = τ a b := fun a b => by
    have := congrFun (congrFun hsym a) b
    simpa [transpose_apply] using this
  set M : Matrix l l ℝ := τ.map im with hM
  set Mc : Matrix l l ℂ := M.map (Complex.ofRealHom : ℝ →+* ℂ) with hMc
  have hdiff : τ - τᴴ = (2 * I) • Mc := by
    ext a b
    simp only [Matrix.sub_apply, conjTranspose_apply, hsymm a b, Matrix.smul_apply, smul_eq_mul, Mc, M, map_apply,
      Complex.ofRealHom_eq_coe, Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  have hQP : Pᴴ * τᴴ = -Qᴴ := by rw [← conjTranspose_mul, hτP, conjTranspose_neg]
  have h2 : Pᴴ * Mc * P = 1 := by
    have e : Pᴴ * (τ - τᴴ) * P = (2 * I) • (1 : Matrix l l ℂ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hτP, hQP]
      rw [Matrix.mul_neg, Matrix.neg_mul]
      linear_combination (norm := (match_scalars <;> ring_nf <;> (try simp only [I_sq]) <;> ring_nf)) -key
    rw [hdiff, Matrix.mul_smul, Matrix.smul_mul] at e
    exact smul_right_injective _ (by simp [I_ne_zero] : (2 * I) ≠ 0) e
  have e1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hu, conjTranspose_one]
  have e2 : P * P⁻¹ = 1 := mul_nonsing_inv _ hu
  have hMcf : Mc = (P⁻¹)ᴴ * P⁻¹ := by
    calc Mc = ((P⁻¹)ᴴ * Pᴴ) * Mc * (P * P⁻¹) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * Mc * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * P⁻¹ := by rw [h2, Matrix.mul_one]
  have hinj : Function.Injective (P⁻¹).mulVec := by
    intro u v h
    have := congrArg P.mulVec h
    simpa [mulVec_mulVec, e2] using this
  have hpd : Mc.PosDef := hMcf ▸ PosDef.conjTranspose_mul_self _ hinj
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext a b
    simp [conjTranspose_apply, M, hsymm a b]
  · intro x hx
    set xc : l → ℂ := fun i => (x i : ℂ) with hxc
    have hxc0 : xc ≠ 0 := by
      intro h; apply hx; ext i
      have := congrFun h i
      simpa [xc] using this
    have e : star xc ⬝ᵥ Mc *ᵥ xc = ((star x ⬝ᵥ M *ᵥ x : ℝ) : ℂ) := by
      simp [dotProduct, mulVec, Mc, xc, Complex.ofReal_sum, Complex.ofReal_mul]
    have := hpd.dotProduct_mulVec_pos hxc0
    rw [e] at this
    exact zero_lt_real.mp this

end GlobalTheory
end

section

open MvPolynomial

noncomputable section

namespace GlobalTheory.Chow

theorem exists_mul_pow_mem_incidenceIdeal_of_generic {σ β K F : Type*} [Fintype σ] [CommRing K]
    [Field F] [Algebra K F]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → F} (hξ : ∀ g, aeval ξ g = 0 ↔ g ∈ p)
    {h : MvPolynomial (β × σ) (MvPolynomial σ K)}
    (hf : map (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom h ∈
      Ideal.span (Set.range (linForm ξ : β → _))) (j : σ) :
    ∃ m : ℕ, h * C (X j ^ m) ∈ incidenceIdeal (β := β) p := by
  let φ : MvPolynomial σ K →+* F := (aeval ξ : MvPolynomial σ K →ₐ[K] F).toRingHom
  have hφ : (fun j => φ (X j)) = ξ := by ext j; simp [φ]
  by_cases hj : ξ j = 0
  · exact ⟨1, Ideal.mul_mem_left _ _ (C_mem_incidenceIdeal (by
      rw [pow_one, ← hξ, aeval_X, hj]))⟩
  obtain ⟨m, g, hg⟩ := exists_pow_mul_sub_rename_mem (X : σ → MvPolynomial σ K) j h
  refine ⟨m, ?_⟩
  have h1 := map_mem_span_linForm φ hg
  rw [hφ, map_sub, map_mul, map_rename] at h1
  have h2 : rename Subtype.val (map φ g) ∈ Ideal.span (Set.range (linForm ξ : β → _)) := by
    have := Ideal.sub_mem _ (Ideal.mul_mem_right (map φ (C (X j ^ m))) _ hf) h1
    rwa [sub_sub_cancel] at this
  rw [← Set.image_univ, ← ker_linFormElim ξ (Ne.isUnit hj), RingHom.mem_ker,
    linFormElim_rename, ← RingHom.mem_ker, MvPolynomial.ker_map] at h2
  have hker : RingHom.ker φ = p := Ideal.ext fun g => hξ g
  rw [hker] at h2
  have h3 : rename Subtype.val g ∈ p.map (C : _ →+* MvPolynomial (β × σ) (MvPolynomial σ K)) := by
    rw [← Ideal.mem_comap (f := (rename Subtype.val : _ →ₐ[MvPolynomial σ K] _))]
    refine Ideal.map_le_iff_le_comap.2 (fun a ha => ?_) h2
    simpa [Ideal.mem_comap] using Ideal.mem_map_of_mem _ ha
  have := Ideal.add_mem _ (Ideal.mem_sup_right (S := p.map C) hg) (Ideal.mem_sup_left h3)
  rwa [sub_add_cancel] at this

theorem exists_field_generic_point {σ K : Type} [CommRing K] {p : Ideal (MvPolynomial σ K)}
    [p.IsPrime] (hp : ∃ j, X j ∉ p) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ξ : σ → F),
      (∀ g, aeval ξ g = 0 ↔ g ∈ p) ∧ ξ ≠ 0 :=
  ⟨FractionRing (MvPolynomial σ K ⧸ p), inferInstance, inferInstance, genericPoint p,
    aeval_genericPoint_eq_zero_iff p, genericPoint_ne_zero hp⟩

theorem eq_zero_of_mem_elimIdeal_of_forall_meets {K : Type} [Field K] {N : ℕ}
    {P : Ideal (MvPolynomial (Fin N) K)}
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0)
    {f : MvPolynomial (Unit × Fin N) K} (hf : f ∈ elimIdeal (β := Unit) P) : f = 0 := by
  apply map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K _).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro t
  obtain ⟨y, hy, hyP, hs⟩ := hP (fun j => t ((), j))
  have := aeval_eq_zero_of_mem_elimIdeal (β := Unit) hyP hy (t := t) (fun _ => hs) hf
  rw [map_zero, eval_map, ← aeval_def, this]

theorem exists_prime_saturation_generic_section (K L : Type) [Field K] [Field L] (N : ℕ)
    [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L]
    [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L]
    (P : Ideal (MvPolynomial (Fin N) K)) (hprime : P.IsPrime)
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0) :
    ∃ Q : Ideal (MvPolynomial (Fin N) L), Q.IsPrime ∧
      P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)} ≤ Q ∧
      ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈
        P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)} := by
  classical
  have hex : ∃ j, X j ∉ P := by
    obtain ⟨y, hy, hyP, -⟩ := hP 0
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
    exact ⟨j, fun h => hj (by simpa using hyP _ h)⟩
  obtain ⟨F, _, _, ξ, hξ, hne⟩ : ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ξ : Fin N → F),
      (∀ g, aeval ξ g = 0 ↔ g ∈ P) ∧ ξ ≠ 0 :=
    exists_field_generic_point hex
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hne
  have hq := isPrime_span_linForm (ι := Unit) ξ (Ne.isUnit hj₀) Set.univ
  rw [Set.image_univ] at hq
  set q : Ideal (MvPolynomial (Unit × Fin N) F) :=
    Ideal.span (Set.range (linForm ξ : Unit → _)) with hqdef
  obtain ⟨Ω, _, π, hπ⟩ : ∃ (Ω : Type) (_ : Field Ω) (π : MvPolynomial (Unit × Fin N) F →+* Ω),
      ∀ a, π a = 0 ↔ a ∈ q := by
    refine ⟨FractionRing (MvPolynomial (Unit × Fin N) F ⧸ q), inferInstance,
      (algebraMap (MvPolynomial (Unit × Fin N) F ⧸ q) _).comp (Ideal.Quotient.mk q), fun a => ?_⟩
    rw [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let ρ : MvPolynomial (Fin N) K →+* MvPolynomial (Unit × Fin N) K :=
    (rename (fun j => ((), j)) : _ →ₐ[K] _).toRingHom
  let θ : MvPolynomial (Fin N) K →+* Ω := π.comp ((map (algebraMap K F)).comp ρ)
  have hθ : Function.Injective θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : ρ a ∈ elimIdeal (β := Unit) P :=
      (mem_elimIdeal_iff_of_generic hξ hne).2 ((hπ _).1 ha)
    have h2 := eq_zero_of_mem_elimIdeal_of_forall_meets hP h1
    apply rename_injective (fun j : Fin N => ((), j)) (fun _ _ h => (Prod.ext_iff.1 h).2)
    rw [map_zero]
    exact h2
  let θL : L →+* Ω := IsFractionRing.lift hθ
  have hθL (a) : θL (algebraMap _ L a) = θ a := IsFractionRing.lift_algebraMap hθ a
  have hθK (a : K) : θL (algebraMap K L a) = π (C (algebraMap K F a)) := by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L, hθL]
    simp [θ, ρ]
  let ev : MvPolynomial (Fin N) L →+* Ω := eval₂Hom θL (fun j => π (C (ξ j)))
  let Ψ : MvPolynomial (Unit × Fin N) (MvPolynomial (Fin N) K) →+* MvPolynomial (Fin N) L :=
    eval₂Hom (map (algebraMap K L))
      (fun v => C (algebraMap (MvPolynomial (Fin N) K) L (X v.2)))
  let φ : MvPolynomial (Fin N) K →+* F := (aeval ξ : MvPolynomial (Fin N) K →ₐ[K] F).toRingHom
  have hcomp : ev.comp Ψ = π.comp (map φ) := by
    ext a
    · simp [ev, Ψ, φ, hθK]
    · simp [ev, Ψ, φ]
    · simp [ev, Ψ, φ, hθL, θ, ρ]
  have hcomp' (h) : ev (Ψ h) = π (map φ h) := DFunLike.congr_fun hcomp h
  have hΨC (a) : Ψ (C a) = map (algebraMap K L) a := by simp [Ψ]
  have hΨL : Ψ (genericForm (K := K) (σ := Fin N) ()) =
      ∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j := by

    rw [genericForm_eq, map_sum]
    exact Finset.sum_congr rfl fun j _ => by simp [Ψ, mul_comm]
  have hΨc (c : MvPolynomial (Fin N) K) : Ψ (map C (ρ c)) = C (algebraMap _ L c) := by
    have : Ψ.comp ((map C).comp ρ) = C.comp (algebraMap _ L) := by
      ext a
      · simp [Ψ, ρ, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin N) K) L]
      · simp [Ψ, ρ]
    exact DFunLike.congr_fun this c
  have hden (g : MvPolynomial (Fin N) L) : ∃ c : MvPolynomial (Fin N) K, c ≠ 0 ∧
      ∃ h, Ψ h = C (algebraMap _ L c) * g := by
    induction g using MvPolynomial.induction_on with
    | C a =>
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin N) K) a
      have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
      refine ⟨y, hy0, map C (ρ x), ?_⟩
      have : algebraMap _ L y ≠ 0 := by
        simpa using hy0
      rw [hΨc, ← C_mul, mul_div_cancel₀ _ this]
    | add f g hf hg =>
      obtain ⟨c, hc, h, hh⟩ := hf
      obtain ⟨d, hd, k, hk⟩ := hg
      refine ⟨c * d, mul_ne_zero hc hd, map C (ρ d) * h + map C (ρ c) * k, ?_⟩
      rw [map_add (f := _), map_mul, map_mul, hΨc, hΨc, hh, hk, map_mul, map_mul]
      ring
    | mul_X f v hf =>
      obtain ⟨c, hc, h, hh⟩ := hf
      refine ⟨c, hc, h * C (X v), ?_⟩
      rw [map_mul, hh, hΨC, map_X, mul_assoc]
  refine ⟨RingHom.ker ev, RingHom.ker_isPrime ev, ?_, ?_⟩
  · refine sup_le (Ideal.map_le_iff_le_comap.2 fun g hg => ?_) ?_
    · rw [Ideal.mem_comap, RingHom.mem_ker, ← hΨC, hcomp', map_C]
      have : φ g = 0 := (hξ g).2 hg
      rw [this, map_zero, map_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, ← hΨL,
        hcomp', hπ, genericForm, map_linForm]
      have hφ : (fun j => φ (X j)) = ξ := by ext j; simp [φ]
      rw [hφ]
      exact Ideal.subset_span ⟨(), rfl⟩
  · intro g hg j
    obtain ⟨c, hc, h, hh⟩ := hden g
    have h1 : map φ h ∈ q := by
      rw [← hπ, ← hcomp', hh, map_mul, (RingHom.mem_ker.1 hg), mul_zero]
    obtain ⟨m, hm⟩ := exists_mul_pow_mem_incidenceIdeal_of_generic hξ h1 j
    refine ⟨m, ?_⟩
    have hle : incidenceIdeal (β := Unit) P ≤ Ideal.comap Ψ
        (P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)}) := by
      refine incidenceIdeal_le.2 ⟨fun a ha => ?_, fun i => ?_⟩
      · rw [Ideal.mem_comap, hΨC]
        exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)
      · rw [Ideal.mem_comap, hΨL]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl)
    have h2 := hle hm
    rw [Ideal.mem_comap, map_mul, hh, hΨC, map_pow, map_X] at h2
    have hcL : algebraMap _ L c ≠ 0 := by simpa using hc
    have h3 := Ideal.mul_mem_left _ (C (algebraMap _ L c)⁻¹) h2
    convert h3 using 1
    rw [mul_assoc, ← mul_assoc (C _) (C _), ← C_mul, inv_mul_cancel₀ hcL, C_1, one_mul, mul_comm]

end GlobalTheory.Chow
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Topology Pointwise

namespace GlobalTheory.WhitHered.CellLoc

section Alg

variable {k : Type} [Field k] {N : ℕ}

end Alg

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N c : ℕ} {m : Fin c → ℕ}

theorem isClosed_parab (e : (Σ a, Fin (m a)) ≃ Fin N) : IsClosed (parab k e : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : (parab k e : Set (GL (Fin N) k)) = ⋂ i, ⋂ j, ⋂ _ : blk e j < blk e i, {g : GL (Fin N) k | g.val i j = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_parab, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

end Main

end GlobalTheory.WhitHered.CellLoc

end
end

section

open Matrix
open scoped Classical

namespace GlobalTheory

noncomputable def strictMonoEquivPowersetCard (a : ℕ) (n : Type*) [LinearOrder n] :
    {s : Fin a → n // StrictMono s} ≃ Set.powersetCard n a :=
  ({ toFun := fun s => OrderEmbedding.ofStrictMono s.1 s.2
     invFun := fun f => ⟨f, f.strictMono⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => by ext; rfl } : {s : Fin a → n // StrictMono s} ≃ (Fin a ↪o n)).trans
    Set.powersetCard.ofFinEmbEquiv

theorem subsetEnum_strictMonoEquivPowersetCard (a : ℕ) {n : Type*} [LinearOrder n]
    (s : {s : Fin a → n // StrictMono s}) :
    subsetEnum (strictMonoEquivPowersetCard a n s) = s.1 := by
  have h : Set.powersetCard.ofFinEmbEquiv.symm (strictMonoEquivPowersetCard a n s) =
      OrderEmbedding.ofStrictMono s.1 s.2 := Equiv.symm_apply_apply _ _
  exact congrArg (fun f : Fin a ↪o n => (f : Fin a → n)) h

theorem minorsMatrix_mem_unitaryGroup : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ),
    M ∈ Matrix.unitaryGroup (Fin N) ℂ →
    (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈
      Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by
  intro N a M hM
  set e := strictMonoEquivPowersetCard a (Fin N)
  have hC : (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} =>
      (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) =
      (compoundMatrix a Mᵀ).submatrix e e := by
    ext s s'
    have he : ∀ s, subsetEnum (e s) = s.1 := subsetEnum_strictMonoEquivPowersetCard a
    simp only [submatrix_apply, compoundMatrix, of_apply, he]
    rfl
  have hT : Mᵀ * (Mᵀ)ᴴ = 1 := by
    rw [mem_unitaryGroup_iff'] at hM
    have h1 : Mᵀ * (Mᵀ)ᴴ = (star M * M)ᵀ := by
      ext i j
      simp [Matrix.mul_apply, mul_comm]
    rw [h1, hM, transpose_one]
  rw [hC, mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_submatrix,
    submatrix_mul_equiv, ← compoundMatrix_conjTranspose, ← compoundMatrix_mul, hT,
    compoundMatrix_one, submatrix_one_equiv]

end GlobalTheory
end

section

open IsLocalRing GlobalTheory.Henselisation

theorem _root_.GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i j : EtNbhd R) (h : i ≤ j), IsLocalHom (EtNbhd.trans h) ∧ Function.Injective (EtNbhd.trans h) := by
  first | exact @GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective | exact GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective | (intros; apply GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective <;> assumption)
end

section

open IsLocalRing GlobalTheory.Henselisation

theorem _root_.GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (b : i.B), ∃ r : R, b - algebraMap R i.B r ∈ maximalIdeal i.B := by
  first | exact @GlobalTheory.Henselisation.EtNbhd.exists_sub_mem_maximalIdeal | exact GlobalTheory.Henselisation.EtNbhd.exists_sub_mem_maximalIdeal | (intros; apply GlobalTheory.Henselisation.EtNbhd.exists_sub_mem_maximalIdeal <;> assumption)
end

section

open IsLocalRing GlobalTheory.Henselisation

theorem _root_.GlobalTheory.T.maximalIdeal_pointedEtaleNeighbourhood_eq_map : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), maximalIdeal i.B = (maximalIdeal R).map (algebraMap R i.B) := by
  first | exact @GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map | exact GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map | (intros; apply GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map <;> assumption)
end

section

open IsLocalRing GlobalTheory.Henselisation

theorem _root_.GlobalTheory.T.flat_localRing_pointedEtaleNeighbourhood : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Module.Flat R i.B := by
  first | exact @GlobalTheory.Henselisation.EtNbhd.flat_B | exact GlobalTheory.Henselisation.EtNbhd.flat_B | (intros; apply GlobalTheory.Henselisation.EtNbhd.flat_B <;> assumption)
end

section

open Filter Topology


theorem _root_.GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by
  first | exact @GlobalTheory.LinSchurLatt.latt_open_compact_basis | exact GlobalTheory.LinSchurLatt.latt_open_compact_basis | (intros; apply GlobalTheory.LinSchurLatt.latt_open_compact_basis <;> assumption)
end

section

open Matrix Polynomial

theorem _root_.GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq : ∀ {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F) (e e' : Fin r → F), y.charpoly = y'.charpoly → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y' e').det → (GlobalTheory.LeviDesc.Krylov.krylov y e)⁻¹ * y * GlobalTheory.LeviDesc.Krylov.krylov y e = (GlobalTheory.LeviDesc.Krylov.krylov y' e')⁻¹ * y' * GlobalTheory.LeviDesc.Krylov.krylov y' e' := by
  first | exact @GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq | exact GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq | (intros; apply GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq <;> assumption)
end
