module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

section

private theorem int_of_rat {K : Type} [Field K] [CharZero K] (r : ℚ)
    (h : IsIntegral ℤ (r : K)) : ∃ a : ℤ, (a : ℚ) = r := by
  have h1 : IsIntegral ℤ r := by
    have h2 : IsIntegral ℤ (algebraMap ℚ K r) := by simpa using h
    exact (isIntegral_algebraMap_iff ).mp h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact ⟨a, by simpa using ha⟩

theorem UpperTheory.discriminant_mul_integral_mem :
    ∀ (K : Type) [Field K] [CharZero K] (σ : K →+* K) (w y : K) (t n : ℤ), w + σ w = (t : K) → w * σ w = (n : K) → IsIntegral ℤ y → y ∈ IntermediateField.adjoin ℚ {w} → ∃ a b : ℤ, ((t ^ 2 - 4 * n : ℤ) : K) * y = (a : K) + (b : K) * w := by
  intro K _ _ σ w y t n ht hn hy hmem
  have hsq : w * w = (t : K) * w - (n : K) := by linear_combination w * ht - hn
  have hw : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X,
        eq_intCast, eq_intCast]
      linear_combination hsq
  have hwQ : IsIntegral ℚ w := hw.tower_top
  have hmem' : y ∈ Algebra.adjoin ℚ {w} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hwQ.isAlgebraic]
    exact hmem
  have hrep : ∀ z ∈ Algebra.adjoin ℚ {w}, ∃ p q : ℚ, z = (p : K) + (q : K) * w := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
    | algebraMap r => exact ⟨r, 0, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨p, q, rfl⟩ := hx
      obtain ⟨r, s, rfl⟩ := hz
      exact ⟨p + r, q + s, by push_cast; ring⟩
    | mul x z _ _ hx hz =>
      obtain ⟨p, q, rfl⟩ := hx
      obtain ⟨r, s, rfl⟩ := hz
      exact ⟨p * r - q * s * n, p * s + q * r + q * s * t, by
        push_cast; linear_combination (q : K) * (s : K) * hsq⟩
  obtain ⟨p, q, hpq⟩ := hrep y hmem'
  have hσ : ∀ z : K, IsIntegral ℤ z → IsIntegral ℤ (z + σ z) := fun z hz =>
    hz.add (hz.map σ.toIntAlgHom)
  have hσw : σ w = (t : K) - w := by linear_combination ht
  have hσy : σ y = (p : K) + (q : K) * ((t : K) - w) := by
    rw [hpq, map_add (f := _), map_mul, map_ratCast, map_ratCast, hσw]
  have hA : y + σ y = ((2 * p + q * t : ℚ) : K) := by
    rw [hσy, hpq]; push_cast; ring
  have hB : w * y + σ (w * y) = ((p * t + q * (t ^ 2 - 2 * n) : ℚ) : K) := by
    rw [map_mul, hσy, hσw, hpq]; push_cast; linear_combination 2 * (q : K) * hsq
  obtain ⟨A, hA'⟩ := int_of_rat _ (hA ▸ hσ y hy)
  obtain ⟨B, hB'⟩ := int_of_rat _ (hB ▸ hσ _ (hw.mul hy))
  have hAK : (A : K) = 2 * p + q * t := by exact_mod_cast congrArg (Rat.cast : ℚ → K) hA'
  have hBK : (B : K) = p * t + q * (t ^ 2 - 2 * n) := by
    exact_mod_cast congrArg (Rat.cast : ℚ → K) hB'
  refine ⟨(t ^ 2 - 2 * n) * A - t * B, 2 * B - t * A, ?_⟩
  push_cast
  rw [hAK, hBK, hpq]
  ring
end

section

theorem UpperTheory.Reformulated.B.Qi48.exists_psi :
    ∀ (L T : Type) [inst : Field L] [IsAlgClosed L] [inst_2 : CommRing T]
    [inst_3 : Algebra L T] [Algebra.FiniteType L T] (m : Ideal T),
    m.IsMaximal → ∃ (ψ : T →ₐ[L] L), ∀ (x : T), (ψ : T → L) x = (0 : L) ↔ x ∈ m := by
  intro L T _ _ _ _ _ m hm
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite L (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing L (T ⧸ m)
  have hb : Function.Bijective (Algebra.ofId L (T ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : L ≃ₐ[L] (T ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId L (T ⧸ m)) hb
  refine ⟨(e.symm : (T ⧸ m) →ₐ[L] L).comp (Ideal.Quotient.mkₐ L m), fun x => ?_⟩
  change e.symm (Ideal.Quotient.mk m x) = 0 ↔ x ∈ m
  rw [map_eq_zero_iff e.symm e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
end

section

theorem UpperTheory.Reformulated.B.Qh66.ring_sec :
    ∀ (Ω C : Type) [inst : Field Ω] [IsAlgClosed Ω]
    [inst_2 : CommRing C] [Nontrivial C] (φ : Ω →+* C), φ.FiniteType → ∃ (ρ : C →+* Ω), ρ.comp φ = RingHom.id Ω := by
  intro Ω C _ _ _ _ φ hφ
  letI : Algebra Ω C := φ.toAlgebra
  haveI : Algebra.FiniteType Ω C := hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite Ω (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing Ω (C ⧸ m)
  let f : (C ⧸ m) →ₐ[Ω] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(f.comp (Ideal.Quotient.mkₐ Ω m)).toRingHom, ?_⟩
  ext x
  exact (f.comp (Ideal.Quotient.mkₐ Ω m)).commutes x
end

section

theorem UpperTheory.Reformulated.B.Qi4.extendPt :
    ∀ (O Λ T K : Type) [inst : CommRing O] [inst_1 : CommRing Λ] [inst_2 : CommRing T]
    [inst_3 : Field K] [IsAlgClosed K] [inst_5 : Algebra O Λ] [inst_6 : Algebra O T] [inst_7 : Algebra Λ T]
    [IsScalarTower O Λ T] [inst_9 : Algebra O K] [Algebra.IsIntegral Λ T] (P : Ideal T) (y : Λ →ₐ[O] K),
    Ideal.comap (Algebra.algebraMap Λ T) P ≤ RingHom.ker y →
      ∃ (x : T →ₐ[O] K),
        P ≤ RingHom.ker x ∧ ∀ (a : Λ), (x : T → K) ((Algebra.algebraMap Λ T : Λ → T) a) = (y : Λ → K) a := by
  intro O Λ T K _ _ _ _ _ _ _ _ _ _ _ P y hP
  haveI hprime : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  obtain ⟨Q, hPQ, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker y) P hP
  change Q.comap (algebraMap Λ T) = RingHom.ker y at hQc
  have hker : ∀ a ∈ Q.comap (algebraMap Λ T), (y : Λ →+* K) a = 0 := by
    intro a ha
    rw [hQc] at ha
    exact ha
  let ybar : (Λ ⧸ Q.comap (algebraMap Λ T)) →+* K := Ideal.Quotient.lift _ (y : Λ →+* K) hker
  have hinj : Function.Injective ybar := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, hQc]
    exact ha
  letI : Algebra (Λ ⧸ Q.comap (algebraMap Λ T)) K := ybar.toAlgebra
  haveI : FaithfulSMul (Λ ⧸ Q.comap (algebraMap Λ T)) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : FaithfulSMul (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (Λ ⧸ Q.comap (algebraMap Λ T)) K :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI hint : Algebra.IsIntegral (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    Algebra.IsIntegral.quotient
  haveI : Algebra.IsAlgebraic (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let z : (T ⧸ Q) →ₐ[Λ ⧸ Q.comap (algebraMap Λ T)] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hz : ∀ a : Λ, z (Ideal.Quotient.mk Q (algebraMap Λ T a)) = y a := fun a =>
    z.commutes (Ideal.Quotient.mk _ a)
  refine ⟨{ (z : (T ⧸ Q) →+* K).comp (Ideal.Quotient.mk Q) with commutes' := fun o => ?_ }, ?_, hz⟩
  · have h := hz (algebraMap O Λ o)
    rw [← IsScalarTower.algebraMap_apply, y.commutes] at h
    exact h
  · intro t ht
    have h0 : Ideal.Quotient.mk Q t = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hPQ ht)
    show z (Ideal.Quotient.mk Q t) = 0
    rw [h0, map_zero]
end

section

theorem UpperTheory.Reformulated.B.RingHomExtensionOfIntegral.exists_ringHom_extend_of_isIntegral.{u_1, u_2, u_3} :
    ∀ {R : Type u_1} {S : Type u_2} {K : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Field K]
      [IsAlgClosed K] [inst_4 : Algebra R S] [Algebra.IsIntegral R S],
      Function.Injective (⇑(Algebra.algebraMap R S) : R → S) →
        ∀ (f : R →+* K), ∃ (g : S →+* K), ∀ (r : R), (g : S → K) ((Algebra.algebraMap R S : R → S) r) = (f : R → K) r := by
  intro R S K _ _ _ _ _ _ hinj f
  have hP : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hle : Ideal.comap (algebraMap R S) (⊥ : Ideal S) ≤ RingHom.ker f := by
    intro a ha
    have h0 : algebraMap R S a = 0 := by simpa using ha
    have : a = 0 := hinj (by rw [map_zero]; exact h0)
    simp [this]
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker f) ⊥ hle
  have hlies : Q.LiesOver (RingHom.ker f) := (Ideal.liesOver_iff _ _).2 hQc.symm
  letI : Algebra (R ⧸ RingHom.ker f) K := (RingHom.kerLift f).toAlgebra
  have hK : Module.IsTorsionFree (R ⧸ RingHom.ker f) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective f)
  have hS : Module.IsTorsionFree (R ⧸ RingHom.ker f) (S ⧸ Q) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.2
      ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h2 : Ideal.Quotient.mk Q (algebraMap R S r) = 0 := hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at h2
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hQc]
    exact h2
  have hint : Algebra.IsIntegral (R ⧸ RingHom.ker f) (S ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker f)
  have halg : Algebra.IsAlgebraic (R ⧸ RingHom.ker f) (S ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let φ : (S ⧸ Q) →ₐ[R ⧸ RingHom.ker f] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk Q), fun r => ?_⟩
  have h1 : φ (algebraMap (R ⧸ RingHom.ker f) (S ⧸ Q) (Ideal.Quotient.mk _ r)) =
      algebraMap (R ⧸ RingHom.ker f) K (Ideal.Quotient.mk _ r) := φ.commutes _
  exact h1
end

section

theorem UpperTheory.Reformulated.B.Qe16.ext_integral :
    ∀ {B S K : Type} [inst : CommRing B] [inst_1 : CommRing S]
    [inst_2 : Field K] [IsAlgClosed K] [inst_4 : Algebra B S] [Algebra.IsIntegral B S],
    Function.Injective (⇑(Algebra.algebraMap B S) : B → S) →
      ∀ (φ : B →+* K), ∃ (Φ : S →+* K), ∀ (b : B), (Φ : S → K) ((Algebra.algebraMap B S : B → S) b) = (φ : B → K) b := by
  intro B S K _ _ _ _ _ _ hinj φ
  haveI hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker φ) ⊥ (by
      rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le)
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (B ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (B ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  haveI : Algebra.IsIntegral (B ⧸ RingHom.ker φ) (S ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := B)
  haveI : FaithfulSMul (B ⧸ RingHom.ker φ) (S ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (B ⧸ RingHom.ker φ) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (B ⧸ RingHom.ker φ) K :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Nontrivial (B ⧸ RingHom.ker φ) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  haveI : Algebra.IsAlgebraic (B ⧸ RingHom.ker φ) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let f : (S ⧸ Q) →ₐ[B ⧸ RingHom.ker φ] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk Q), fun b => ?_⟩
  exact (f.commutes (Ideal.Quotient.mk _ b)).trans (RingHom.kerLift_mk φ b)
end

section

theorem UpperTheory.Reformulated.B.IntegralExtensionAlgClosed.exists_ringHom_extension_of_integral :
    ∀ (R S K : Type) [inst : CommRing R] [inst_1 : CommRing S]
    [inst_2 : Algebra R S] [Algebra.IsIntegral R S] [inst_4 : Field K] [IsAlgClosed K],
    Function.Injective (⇑(Algebra.algebraMap R S) : R → S) →
      ∀ (b : R →+* K), ∃ (Φ : S →+* K), Φ.comp (Algebra.algebraMap R S) = b := by
  intro R S K _ _ _ _ _ _ hinj b
  haveI hp : (RingHom.ker b).IsPrime := RingHom.ker_isPrime b
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker b) ⊥ (by
      intro x hx
      have hx0 : algebraMap R S x = 0 := by simpa using hx
      have : x = 0 := hinj (by simpa using hx0)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker b) := ⟨hQp.symm⟩
  letI : Algebra (R ⧸ RingHom.ker b) K := (RingHom.kerLift b).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker b) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective b)
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker b) (S ⧸ Q) := inferInstance
  haveI : FaithfulSMul (R ⧸ RingHom.ker b) (S ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker b) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker b) K :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker b) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let ψ : (S ⧸ Q) →ₐ[R ⧸ RingHom.ker b] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext x
  exact ψ.commutes (Ideal.Quotient.mk (RingHom.ker b) x)
end

section

noncomputable def UpperTheory.Reformulated.B.Qe26.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.Qe26.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.Qe26.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.Qe26.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.Qe26.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.Qe26.IsIrrSub r ⊤

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe26.tr :
    {k : Type} → [inst : Field k] → {n : ℕ} → GL (Fin n) k → k :=
    fun {k : Type} [Field k] {n : ℕ} (g : GL (Fin n) k) ↦ (↑g : Matrix (Fin n) (Fin n) k).trace

private theorem UpperTheory.Reformulated.B.Qe26.subalgebra_eq_top {k V : Type} [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (S : Subalgebra k (Module.End k V))
    (h : ∀ W : Submodule k V, (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) → W = ⊥ ∨ W = ⊤) :
    S = ⊤ := by
  have hsimple : IsSimpleModule S V := by
    rw [isSimpleModule_iff]
    refine ⟨fun p ↦ ?_⟩
    rcases h (p.restrictScalars k) (fun s hs v hv ↦ p.smul_mem ⟨s, hs⟩ hv) with h1 | h1
    · left
      simpa using h1
    · right
      simpa using h1
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) k
  have hfin : Module.Finite (Module.End S V) V :=
    Module.Finite.of_restrictScalars_finite k _ _
  rw [eq_top_iff]
  intro T _
  let T' : Module.End (Module.End S V) V :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun c v ↦ by
        obtain ⟨a, rfl⟩ := hb.2 c
        simp }
  obtain ⟨s, hs⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := S) (M := V) T'
  have : T = s.1 := by
    ext v
    exact (LinearMap.congr_fun hs v).symm
  rw [this]
  exact s.2

private theorem UpperTheory.Reformulated.B.Qe26.lift_surjective {k : Type} [Field k] [IsAlgClosed k] {H : Type}
    [Group H] {n : ℕ} (R : H →* GL (Fin n) k) (hR : UpperTheory.Reformulated.B.Qe26.IsIrr R) :
    Function.Surjective (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R)) := by
  obtain ⟨h0, -, h1⟩ := hR
  set L := MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) with hL
  have hnt : Nontrivial (Fin n → k) := (Submodule.nontrivial_iff k).1 ⟨⟨_, _, h0⟩⟩
  have htop := UpperTheory.Reformulated.B.Qe26.subalgebra_eq_top
    (((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp L).range) (by
      intro W hW
      refine h1 W le_top (fun g v hv ↦ ?_)
      have := hW _ ⟨MonoidAlgebra.single g 1, rfl⟩ v hv
      simpa [hL] using this)
  intro M
  have hM : Matrix.toLinAlgEquiv' M ∈
      ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp L).range := by
    rw [htop]; trivial
  obtain ⟨x, hx⟩ := hM
  exact ⟨x, (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective hx⟩

theorem UpperTheory.Reformulated.B.Qe26.kerLe :
    ∀ (k : Type) [inst : Field k] [IsAlgClosed k] (H : Type) [inst_2 : Group H] (n : ℕ) (R : H →* GL (Fin n) k),
      UpperTheory.Reformulated.B.Qe26.IsIrr R →
        ∀ (x₀ : GL (Fin n) k) (B : Type) [inst_3 : Ring B] [inst_4 : Algebra k B] [Module.Finite k B] (φ : H →* B)
          (f : B →ₗ[k] k),
          (∀ (h : H), UpperTheory.Reformulated.B.Qe26.tr (x₀ * (R : H → GL (Fin n) k) h) = (f : B → k) ((φ : H → B) h)) →
            n ^ (2 : ℕ) ≤ Module.finrank k ↥(Algebra.adjoin k (Set.range (⇑φ : H → B))) ∧
              ∀ (x : MonoidAlgebra k H),
                ((MonoidAlgebra.lift k B H : (H →* B) → MonoidAlgebra k H →ₐ[k] B) φ : MonoidAlgebra k H → B) x = (0 : B) →
                  ((MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H :
                            (H →* Matrix (Fin n) (Fin n) k) → MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k)
                          ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) :
                        MonoidAlgebra k H → Matrix (Fin n) (Fin n) k)
                      x =
                    (0 : Matrix (Fin n) (Fin n) k) := by
  intro k _ _ H _ n R hR x₀ B _ _ _ φ f hf
  have hsurj := UpperTheory.Reformulated.B.Qe26.lift_surjective R hR
  set L := MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) with hL
  set Φ := MonoidAlgebra.lift k B H φ with hΦ
  have htr : ∀ y, ((x₀ : Matrix (Fin n) (Fin n) k) * L y).trace = f (Φ y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [mul_add, ha, hb]
    | single g c =>
      have := hf g
      simp only [UpperTheory.Reformulated.B.Qe26.tr, Units.val_mul] at this
      simp [hL, hΦ, ← this]
  have hker : ∀ x, Φ x = 0 → L x = 0 := by
    intro x hx
    rw [Matrix.ext_iff_trace_mul_left]
    intro M
    obtain ⟨y, hy⟩ := hsurj ((↑x₀⁻¹ : Matrix (Fin n) (Fin n) k) * M)
    have := htr (y * x)
    rw [map_mul, map_mul, hx, hy, mul_zero, map_zero, ← mul_assoc, Units.mul_inv_cancel_left] at this
    simpa using this
  refine ⟨?_, hker⟩
  have hle : LinearMap.ker Φ.toLinearMap ≤ LinearMap.ker L.toLinearMap := fun x hx ↦ hker x hx
  have hrange : LinearMap.range Φ.toLinearMap ≤
      Subalgebra.toSubmodule (Algebra.adjoin k (Set.range φ)) := by
    rintro _ ⟨y, rfl⟩
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add]; exact add_mem ha hb
    | single g c =>
      have : Φ.toLinearMap (MonoidAlgebra.single g c) = c • φ g := by simp [hΦ]
      rw [this]
      exact Submodule.smul_mem _ _ (Algebra.subset_adjoin ⟨g, rfl⟩)
  let ψ : LinearMap.range Φ.toLinearMap →ₗ[k] Matrix (Fin n) (Fin n) k :=
    ((LinearMap.ker Φ.toLinearMap).liftQ L.toLinearMap hle).comp
      Φ.toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hψ : Function.Surjective ψ := by
    intro M
    obtain ⟨y, rfl⟩ := hsurj M
    exact ⟨Φ.toLinearMap.quotKerEquivRange (Submodule.Quotient.mk y), by simp [ψ]⟩
  calc n ^ 2 = Module.finrank k (Matrix (Fin n) (Fin n) k) := by
        simp [Module.finrank_matrix, sq]
    _ ≤ Module.finrank k (LinearMap.range Φ.toLinearMap) :=
        LinearMap.finrank_le_finrank_of_surjective hψ
    _ ≤ Module.finrank k (Subalgebra.toSubmodule (Algebra.adjoin k (Set.range φ))) :=
        Submodule.finrank_mono hrange
    _ = _ := rfl
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi42.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi42.GQ :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Gal(UpperTheory.Reformulated.B.Qi42.Om l/ℚ_[l])

theorem UpperTheory.Reformulated.B.Qi42.open_fix :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] (H : Subgroup (UpperTheory.Reformulated.B.Qi42.GQ v)),
      IsOpen (↑H : Set (UpperTheory.Reformulated.B.Qi42.GQ v)) → (IntermediateField.fixedField H).fixingSubgroup = H := by
  intro v inst H hH
  haveI : IsGalois ℚ_[v] (PadicAlgCl v) := IsAlgClosure.isGalois ℚ_[v] (PadicAlgCl v)
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
end
