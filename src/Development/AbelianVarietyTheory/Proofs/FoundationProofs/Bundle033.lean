module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Mathlib.Algebra.DualNumber
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

@[expose] public section

section

open GlobalTheory.K5 Polynomial TrivSqZeroExt

noncomputable section
namespace GlobalTheory.K5.DlogUniq

section generic
variable {R : Type*} [CommRing R]

theorem aeval_dual {S : Type*} [CommRing S] [Algebra R S] (a m : S) (f : R[X]) :
    (aeval (inl a + inr m : DualNumber S) f).fst = aeval a f ∧
    (aeval (inl a + inr m : DualNumber S) f).snd = aeval a (derivative f) * m := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add (f := _), fst_add, snd_add, hf.1, hf.2, hg.1, hg.2, map_add (f := _), map_add (f := _), map_add (f := _), add_mul]
    exact ⟨rfl, rfl⟩
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, derivative_monomial, aeval_monomial]
    constructor
    · simp [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_pow]
    · simp [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_pow]
      ring

theorem exists_derivation (Φ : R[X]) (N : ℕ) (q : R) (I : Ideal R[X][X])
    (hI : I = Ideal.span {C Φ, X ^ N - C (C q)}) (S : Type*) [CommRing S] [Algebra R S]
    [Algebra (R[X][X] ⧸ I) S] [IsScalarTower R (R[X][X] ⧸ I) S] (mx my : S)
    (hx : algebraMap (R[X][X] ⧸ I) S (aeval (Ideal.Quotient.mk I (C X)) (derivative Φ)) * mx = 0)
    (hy : (N : S) * my = 0) :
    ∃ D : Derivation R (R[X][X] ⧸ I) S,
      D (Ideal.Quotient.mk I (C X)) = mx ∧ D (Ideal.Quotient.mk I X) = my := by
  let π : R[X][X] →+* S := (algebraMap (R[X][X] ⧸ I) S).comp (Ideal.Quotient.mk I)
  let ψ0 : R[X][X] →+* DualNumber S :=
    eval₂RingHom (aeval (inl (π (C X)) + inr mx : DualNumber S) : R[X] →ₐ[R] DualNumber S).toRingHom
      (inl (π X) + inr my)
  have hC : ∀ f : R[X], ψ0 (C f) = aeval (inl (π (C X)) + inr mx : DualNumber S) f := by
    intro f; simp [ψ0]
  have hX : ψ0 X = inl (π X) + inr my := by simp [ψ0]
  have hπC : ∀ f : R[X], aeval (π (C X)) f = π (C f) := by
    intro f
    have : (aeval (π (C X)) : R[X] →ₐ[R] S).toRingHom = π.comp C := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply]
        exact IsScalarTower.algebraMap_apply R (R[X][X] ⧸ I) S a
      · simp
    exact congrArg (fun g => g f) this
  have hπC' : ∀ f : R[X], aeval (π (C X)) f =
      algebraMap (R[X][X] ⧸ I) S (aeval (Ideal.Quotient.mk I (C X)) f) := by
    intro f
    exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R (R[X][X] ⧸ I) S) (Ideal.Quotient.mk I (C X)) f)
  have hfst : ∀ f, (ψ0 f).fst = π f := by
    intro f
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp ψ0 = π := by
      apply Polynomial.ringHom_ext
      · intro a
        show (ψ0 (C a)).fst = _
        rw [hC, (aeval_dual _ _ _).1, hπC]
      · show (ψ0 X).fst = _
        rw [hX]; simp
    exact congrArg (fun g => g f) this
  have hπI : ∀ f ∈ I, π f = 0 := by
    intro f hf
    show algebraMap (R[X][X] ⧸ I) S (Ideal.Quotient.mk I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  have hker : ∀ f ∈ I, ψ0 f = 0 := by
    have : I ≤ RingHom.ker ψ0 := by
      have h1 : C Φ ∈ I := hI ▸ Ideal.subset_span (by simp)
      have h2 : X ^ N - C (C q) ∈ I := hI ▸ Ideal.subset_span (by simp)
      refine hI.le.trans (Ideal.span_le.2 ?_)
      rintro f (rfl | rfl)
      · show ψ0 _ = 0
        ext
        · rw [hfst, hπI _ h1]; rfl
        · rw [hC, (aeval_dual _ _ _).2, hπC']; exact hx
      · show ψ0 _ = 0
        ext
        · rw [hfst, hπI _ h2]; rfl
        · rw [map_sub, map_pow, hX, hC, aeval_C, snd_sub, snd_pow, TrivSqZeroExt.algebraMap_eq_inl']
          simp only [snd_add, snd_inl, snd_inr, zero_add, sub_zero, snd_zero, smul_eq_mul, nsmul_eq_mul]
          rw [mul_left_comm, hy, mul_zero]
    exact fun f hf => this hf
  let ψ : (R[X][X] ⧸ I) →+* DualNumber S := Ideal.Quotient.lift I ψ0 hker
  have hψ : ∀ z, (ψ z).fst = algebraMap (R[X][X] ⧸ I) S z := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact hfst f
  have hleib : ∀ a b, (ψ (a * b)).snd = a • (ψ b).snd + b • (ψ a).snd := by
    intro a b
    rw [map_mul, DualNumber.snd_mul, hψ, hψ, Algebra.smul_def, Algebra.smul_def, mul_comm (ψ a).snd]
  have halg : ∀ c : R, (ψ (algebraMap R _ c)).snd = 0 := by
    intro c
    show (ψ0 (C (C c))).snd = 0
    rw [hC, (aeval_dual _ _ _).2]; simp
  let L : (R[X][X] ⧸ I) →ₗ[R] S :=
    { toFun := fun z => (ψ z).snd
      map_add' := fun a b => by rw [RingHom.map_add ψ, snd_add]
      map_smul' := fun c z => by
        rw [Algebra.smul_def, hleib, halg, smul_zero, add_zero, RingHom.id_apply, algebraMap_smul] }
  refine ⟨Derivation.mk' L hleib, ?_, ?_⟩
  · show (ψ0 (C X)).snd = mx
    rw [hC]; simp
  · show (ψ0 X).snd = my
    rw [hX]; simp

end generic

variable (p : ℕ) [Fact p.Prime]

theorem natCast_pow_quot {A : Type*} [CommRing A] (k l : ℕ) :
    ((k ^ l : ℕ) : A ⧸ Ideal.span {(k : A) ^ l}) * 1 = 0 := by
  rw [mul_one, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(k : A) ^ l})),
    Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.mem_span_singleton_self _

theorem aeval_xn (n : ℕ) (f : (O0 p)[X]) :
    aeval (xn p n) f = Ideal.Quotient.mk (towerIdeal p n) (C f) := by
  have : (aeval (xn p n) : (O0 p)[X] →ₐ[O0 p] On p n).toRingHom =
      (Ideal.Quotient.mk (towerIdeal p n)).comp C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply]
      rfl
    · simp [xn]
  exact congrArg (fun g => g f) this

theorem aeval_xn_cyclotomic (n : ℕ) : aeval (xn p n) (cyclotomic (p ^ n) (O0 p)) = 0 := by
  rw [aeval_xn, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

theorem isUnit_xn (m : ℕ) : IsUnit (xn p (m + 1)) := by
  have h := congrArg (aeval (xn p (m + 1))) (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  rw [map_mul, aeval_xn_cyclotomic, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
  exact IsUnit.of_pow_eq_one (sub_eq_zero.1 h.symm) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

theorem isUnit_yn (n : ℕ) : IsUnit (yn p n) := by
  have hq : IsUnit (qO p) := by
    refine IsUnit.map _ (IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_)
    rw [HahnSeries.single_mul_single]; simp
  have h : yn p n ^ (p ^ n) = Ideal.Quotient.mk (towerIdeal p n) (C (C (qO p))) := by
    rw [yn, ← map_pow, Ideal.Quotient.eq]
    exact Ideal.subset_span (by simp)
  have h2 : IsUnit (yn p n ^ (p ^ n)) := h ▸ ((hq.map _).map _).map _
  exact (isUnit_pow_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).1 h2

theorem derivative_cyclotomic_mul (m : ℕ) :
    aeval (xn p (m + 1)) (derivative (cyclotomic (p ^ (m + 1)) (O0 p))) * (xn p (m + 1) ^ p ^ m - 1) =
      (p : On p (m + 1)) ^ (m + 1) * xn p (m + 1) ^ (p ^ (m + 1) - 1) := by
  have h := congrArg (fun f => aeval (xn p (m + 1)) (derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  simp only [derivative_mul, map_add (f := _), map_mul, aeval_xn_cyclotomic, zero_mul, add_zero] at h
  simpa [derivative_X_pow] using h

end GlobalTheory.K5.DlogUniq
end
end

section

noncomputable section

namespace GlobalTheory.K5.Dense

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isClosed_eval_mem {K : Type*} [Field K] [Algebra K Ω] [Algebra.IsIntegral K Ω]
    (x : Ω) (s : Set Ω) : IsClosed {σ : Ω ≃ₐ[K] Ω | σ x ∈ s} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)), ?_,
    (stabilizer_isOpen_of_isIntegral x).preimage (by fun_prop), ?_⟩
  · intro τ hτ
    have h : σ.symm (τ x) = x := hτ
    have h' : τ x = σ x := by rw [← σ.symm_apply_eq.1 h]
    simpa [h'] using hσ
  · simp

theorem exists_of_seq (h : IsClo p Ω) (P : ℕ → Ω → Set Ω)
    (hP : ∀ n, ∃ σ : Gal p Ω, ∀ m ≤ n, ∀ x, σ x ∈ P m x) :
    ∃ σ : Gal p Ω, ∀ n x, σ x ∈ P n x := by
  classical
  let K := FractionRing (O0 p)
  letI : Algebra K Ω := (IsFractionRing.lift h.inj).toAlgebra
  have hK : ∀ a : O0 p, algebraMap K Ω (algebraMap (O0 p) K a) = algebraMap (O0 p) Ω a :=
    fun a => IsFractionRing.lift_algebraMap h.inj a
  haveI : IsScalarTower (O0 p) K Ω := IsScalarTower.of_algebraMap_eq (fun a => (hK a).symm)
  haveI : IsAlgClosed Ω := h.clo
  haveI : Algebra.IsAlgebraic (O0 p) Ω := h.alg
  haveI : Algebra.IsAlgebraic K Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) K)
  haveI : IsAlgClosure K Ω := ⟨h.clo, inferInstance⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap h.inj
  haveI : CharZero K := RingHom.charZero (algebraMap K Ω)
  haveI : IsGalois K Ω := {}
  have hfix : ∀ σ : Gal p Ω, ∀ y : K, σ (algebraMap K Ω y) = algebraMap K Ω y := by
    intro σ y
    have e : ((σ : Ω →+* Ω).comp (algebraMap K Ω)) = algebraMap K Ω := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (O0 p))
      ext a
      simp only [RingHom.comp_apply, hK]
      exact σ.commutes a
    exact congrArg (fun f : K →+* Ω => f y) e
  let φ : Gal p Ω → (Ω ≃ₐ[K] Ω) := fun σ => AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (hfix σ)
  have hφ : ∀ σ x, φ σ x = σ x := fun _ _ => rfl
  let G : ℕ → Set (Ω ≃ₐ[K] Ω) := fun n => {τ | ∀ m ≤ n, ∀ x, τ x ∈ P m x}
  have hcl : ∀ n, IsClosed (G n) := fun n => by
    have e : G n = ⋂ m, ⋂ (_ : m ≤ n), ⋂ x, {τ : Ω ≃ₐ[K] Ω | τ x ∈ P m x} := by
      ext τ; simp [G]
    rw [e]
    exact isClosed_iInter fun m => isClosed_iInter fun _ => isClosed_iInter fun x =>
      isClosed_eval_mem x _
  have hdec : ∀ n, G (n + 1) ⊆ G n := fun n τ hτ m hm x => hτ m (hm.trans n.le_succ) x
  have hne : ∀ n, (G n).Nonempty := fun n => by
    obtain ⟨σ, hσ⟩ := hP n
    exact ⟨φ σ, fun m hm x => by rw [hφ]; exact hσ m hm x⟩
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed G hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hτ
  exact ⟨τ.restrictScalars (O0 p), fun n x => hτ n n le_rfl x⟩

theorem exists_finset_orbit (h : IsClo p Ω) (x : Ω) : ∃ R : Finset Ω, ∀ σ : Gal p Ω, σ x ∈ R := by
  classical
  obtain ⟨P, hP0, hPx⟩ := h.alg.isAlgebraic x
  refine ⟨(P.aroots Ω).toFinset, fun σ => ?_⟩
  rw [Multiset.mem_toFinset, mem_aroots']
  refine ⟨(Polynomial.map_ne_zero_iff h.inj).2 hP0, ?_⟩
  have e := Polynomial.aeval_algHom_apply (σ : Ω →ₐ[O0 p] Ω) x P
  simp only [AlgEquiv.coe_algHom] at e
  rw [e, hPx, map_zero]

theorem isAlgZp_zeta (T : Tower p Ω) (n : ℕ) : IsAlgZp (p := p) (T.ζ n) := by
  refine ⟨X ^ (p ^ n) - C 1, X_pow_sub_C_ne_zero (pow_pos hp.out.pos n) 1, ?_⟩
  simp [(T.prim n).pow_eq_one]

theorem qq_pow_sub (T : Tower p Ω) {n m : ℕ} (h : n ≤ m) : T.qq m ^ p ^ (m - n) = T.qq n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]
  clear h
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, T.qpow, ih]

theorem ggeo_apply {g : Gal p Ω} (hg : g ∈ Ggeo (p := p) Ω) {x : Ω} (hx : IsAlgZp (p := p) x) : g x = x := hg x hx

theorem tau_pow_qq (T : Tower p Ω) {τ : Gal p Ω} (hτ : τ ∈ Ggeo (p := p) Ω)
    (hτq : ∀ n, τ (T.qq n) = T.ζ n * T.qq n) (n s : ℕ) :
    (τ ^ s) (T.qq n) = T.ζ n ^ s * T.qq n := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, AlgEquiv.mul_apply, hτq, map_mul, ih,
      ggeo_apply ((Ggeo (p := p) Ω).pow_mem hτ s) (isAlgZp_zeta T n), pow_succ]
    ring

theorem dense_tau_pow_mul (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (Ω : Type) [Field Ω]
    [Algebra (O0 p) Ω] (hΩ : IsClo p Ω) (T : Tower p Ω) (τ : Gal p Ω) (hτ : τ ∈ Ggeo (p := p) Ω)
    (hτq : ∀ n, τ (T.qq n) = T.ζ n * T.qq n) :
    ∀ g ∈ Ggeo (p := p) Ω, ∀ S : Finset Ω, ∃ s : ℕ, ∃ h ∈ Ggeo (p := p) Ω ⊓ ⨅ n, Gn T n,
      ∀ x ∈ S, (τ ^ s * h) x = g x := by
  classical
  intro g hg S
  have hs : ∀ n, ∃ s : ℕ, (τ ^ s) (T.qq n) = g (T.qq n) := by
    intro n
    have hq0 := Basic.qq_ne_zero T n
    have hqp : T.qq n ^ p ^ n ≠ 0 := pow_ne_zero _ hq0
    have e : (g (T.qq n) / T.qq n) ^ (p ^ n) = 1 := by
      rw [div_pow, ← map_pow, Basic.qq_pow, AlgEquiv.commutes, ← Basic.qq_pow T n, div_self hqp]
    obtain ⟨i, -, hi⟩ := (T.prim n).eq_pow_of_pow_eq_one e
    exact ⟨i, by rw [tau_pow_qq T hτ hτq, hi, div_mul_cancel₀ _ hq0]⟩
  choose s hs using hs
  let σ : ℕ → Gal p Ω := fun n => (τ ^ s n)⁻¹ * g
  have hσG : ∀ n, σ n ∈ Ggeo (p := p) Ω := fun n =>
    (Ggeo (p := p) Ω).mul_mem ((Ggeo (p := p) Ω).inv_mem ((Ggeo (p := p) Ω).pow_mem hτ _)) hg
  have hσq : ∀ n, σ n (T.qq n) = T.qq n := by
    intro n
    show ((τ ^ s n)⁻¹ * g) (T.qq n) = T.qq n
    rw [AlgEquiv.mul_apply, ← hs n, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  choose R hR using fun x => exists_finset_orbit hΩ x
  let F : ℕ → ((x : S) → ↥(R x.1)) := fun n x => ⟨σ n x, hR x.1 (σ n)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber F
  have hinf : (F ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  obtain ⟨n₁, hn₁⟩ := hinf.nonempty
  have hS : ∀ m ∈ F ⁻¹' {y}, ∀ x ∈ S, σ m x = σ n₁ x := by
    intro m hm x hx
    have e : F m = F n₁ := (Set.mem_preimage.1 hm).trans (Set.mem_preimage.1 hn₁).symm
    exact congrArg Subtype.val (congrFun e ⟨x, hx⟩)
  let P : ℕ → Ω → Set Ω := fun n x =>
    {z | (IsAlgZp (p := p) x → z = x) ∧ (x ∈ S → z = σ n₁ x) ∧ (x = T.qq n → z = x)}
  have hP : ∀ n, ∃ ρ : Gal p Ω, ∀ m ≤ n, ∀ x, ρ x ∈ P m x := by
    intro n
    obtain ⟨m, hm, hnm⟩ := hinf.exists_gt n
    refine ⟨σ m, fun m' hm' x => ⟨fun hx => ggeo_apply (hσG m) hx, fun hx => hS m hm x hx, ?_⟩⟩
    rintro rfl
    rw [← qq_pow_sub T (hm'.trans hnm.le), map_pow, hσq m]
  obtain ⟨z, hz⟩ := exists_of_seq hΩ P hP
  refine ⟨s n₁, z, ?_, fun x hx => ?_⟩
  · refine Subgroup.mem_inf.2 ⟨fun x hx => (hz 0 x).1 hx, Subgroup.mem_iInf.2 fun n => ?_⟩
    exact (Basic.mem_gn T n z).2 ⟨(hz 0 _).1 (isAlgZp_zeta T n), (hz n _).2.2 rfl⟩
  · rw [AlgEquiv.mul_apply, (hz 0 x).2.1 hx]
    show (τ ^ s n₁) (((τ ^ s n₁)⁻¹ * g) x) = g x
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

end GlobalTheory.K5.Dense
end
end

section

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.DerExt

theorem exists_extend_of_formallySmooth {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallySmooth R S] [Algebra ℤ R] (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ S S, ∀ r, D' (algebraMap R S r) = algebraMap R S (D r) := by
  let g : R →+* TrivSqZeroExt S S :=
    { toFun := fun r ↦ TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r))
      map_one' := by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_one,
            map_one, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_one,
            Derivation.map_one_eq_zero, map_zero, zero_add]
      map_mul' := fun a b ↦ by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_mul,
            map_mul, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul,
            TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, Derivation.leibniz,
            smul_eq_mul, map_add, map_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, zero_add, add_zero]
          ring
      map_zero' := by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_zero,
            map_zero, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero,
            map_zero, zero_add]
      map_add' := fun a b ↦ by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, map_add (f := _), add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, map_add (f := _), zero_add] }
  have hg : ∀ r, (g r).fst = algebraMap R S r ∧ (g r).snd = algebraMap R S (D r) := fun r ↦ by
    constructor
    · change (TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r)) :
        TrivSqZeroExt S S).fst = _
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · change (TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r)) :
        TrivSqZeroExt S S).snd = _
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  obtain ⟨l, h1, h2⟩ : ∃ l : S →+* TrivSqZeroExt S S, (∀ s, (l s).fst = s) ∧ ∀ r, l (algebraMap R S r) = g r := by
    letI : Algebra R (TrivSqZeroExt S S) := g.toAlgebra
    let π : TrivSqZeroExt S S →ₐ[R] S :=
      { (TrivSqZeroExt.fstHom S S S).toRingHom with commutes' := fun r ↦ (hg r).1 }
    have hs : Function.Surjective π := fun s ↦ ⟨TrivSqZeroExt.inl s, rfl⟩
    have hk : IsNilpotent (RingHom.ker (π : TrivSqZeroExt S S →+* S)) := by
      refine ⟨2, ?_⟩
      rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      rw [RingHom.mem_ker] at hx hy
      change x.fst = 0 at hx
      change y.fst = 0 at hy
      rw [Ideal.mem_bot]
      ext
      · simp [hx]
      · simp [TrivSqZeroExt.snd_mul, hx, hy]
    let l := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) π hs hk
    exact ⟨l, fun s ↦ AlgHom.congr_fun (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id R S) π hs hk) s,
      fun r ↦ l.commutes r⟩
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun s ↦ (l s).snd, map_zero' := by simp, map_add' := fun x y ↦ by rw [map_add (f := _)]; rfl }) fun a b ↦ ?_,
    fun r ↦ ?_⟩
  · change (l (a * b)).snd = a • (l b).snd + b • (l a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, h1, h1]
    simp [mul_comm]
  · change (l _).snd = _
    rw [h2, (hg r).2]

theorem derivation_extend : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ D : Derivation ℤ (O0 p) (O0 p),
    ∃ E : Derivation ℤ Ω Ω, ∀ x, E (algebraMap (O0 p) Ω x) = algebraMap (O0 p) Ω (D x) := by
  intro p _ Ω _ _ h D
  haveI : IsDomain (O0 p) := h.inj.isDomain _
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  let K := FractionRing (O0 p)
  letI : Algebra K Ω := (IsFractionRing.lift h.inj).toAlgebra
  haveI : IsScalarTower (O0 p) K Ω := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change _ = IsFractionRing.lift h.inj (algebraMap (O0 p) K x)
    rw [IsFractionRing.lift_algebraMap]
  haveI : Algebra.IsAlgebraic (O0 p) Ω := h.alg
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) K)
  haveI : Algebra.IsSeparable K Ω := Algebra.IsSeparable.of_integral K Ω
  haveI : Algebra.FormallyEtale K Ω := Algebra.FormallyEtale.of_isSeparable K Ω
  haveI : Algebra.FormallySmooth (O0 p) K := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors (O0 p))
  haveI : Algebra.FormallySmooth (O0 p) Ω := Algebra.FormallySmooth.comp (O0 p) K Ω
  exact exists_extend_of_formallySmooth D

end GlobalTheory.K5.DerExt
end
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem levelOne_form_one_add_expDecay :
    ∀ d : ℤ, 4 ≤ d → Even d → ∃ e : ℍ → ℂ, IsMF ⊤ d e ∧
      (fun τ : ℍ => e τ - 1) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  intro d hd hev
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ d)
  have hk : 3 ≤ k := by omega
  have hk2 : Even k := by simpa [Int.even_coe_nat] using hev
  let f : ModularForm 𝒮ℒ (k : ℤ) := ModularForm.E hk
  refine ⟨f, isMF_coe_top f, ?_⟩
  have h0 : valueAtInfty (f : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  have h := exp_decay_sub_atImInfty one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  rw [h0] at h
  simpa using h

end GlobalTheory
end
