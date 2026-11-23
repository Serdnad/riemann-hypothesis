module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle046
public import Formalism.UnipotentAdelicQuotients.Bundle002
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rat_idempotent_blockDiagPart_kills_span : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ e : Matrix ι ι ℚ, e * e = e ∧ (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ blk e a = 0 := by
  first | exact @GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero | exact GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero | (intros; apply GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rat_linear_param_blockDiag_kernel : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ ∀ ε : Matrix ι ι ℂ, 1 + ε ∈ Γ → e.map (algebraMap ℚ ℂ) * ε * (1 - e.map (algebraMap ℚ ℂ)) = ε → linExt c ε = ε := by
  first | exact @GlobalTheory.ClassFin.exists_linExt_corner_proj | exact GlobalTheory.ClassFin.exists_linExt_corner_proj | (intros; apply GlobalTheory.ClassFin.exists_linExt_corner_proj <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension : ∀ (F : Type) [Field F] [NumberField F] (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), δ ≠ 0 → (locNorm F δ S).index ≠ 0 ∧ 2 ^ (tFin F δ S + tReal F δ) ≤ (locNorm F δ S).index := by
  first | exact @GlobalTheory.QNorm.two_pow_le_index_locNorm | exact GlobalTheory.QNorm.two_pow_le_index_locNorm | (intros; apply GlobalTheory.QNorm.two_pow_le_index_locNorm <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.rat_component_mem_ratPolysVanishingOnMatrixSet : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, AddMonoidAlgebra.coeff f' m = l (AddMonoidAlgebra.coeff f m)) → f' ∈ vanI Γ := by
  first | exact @GlobalTheory.ClassFin.component_mem_vanI | exact GlobalTheory.ClassFin.component_mem_vanI | (intros; apply GlobalTheory.ClassFin.component_mem_vanI <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.TvAdjust

theorem exists_split (b : ℕ) (N : ℕ) (hN : 0 < N) :
    ∃ A B e : ℕ, N = A * B ∧ A ∣ b ^ e ∧ B.Coprime b := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hg : N.Coprime b
    · exact ⟨1, N, 0, by simp, by simp, hg⟩
    · obtain ⟨M, hM⟩ := Nat.gcd_dvd_left N b
      have hg0 : 0 < N.gcd b := Nat.gcd_pos_of_pos_left _ hN
      have hg1 : 1 < N.gcd b := by
        rcases Nat.lt_or_ge 1 (N.gcd b) with h | h
        · exact h
        · exact absurd (show N.gcd b = 1 by omega) hg
      have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have hlt : M < N := by nlinarith
      obtain ⟨A, B, e, h1, h2, h3⟩ := ih M hlt hM0
      refine ⟨N.gcd b * A, B, e + 1, by rw [mul_assoc, ← h1]; exact hM, ?_, h3⟩
      rw [pow_succ']
      exact mul_dvd_mul (Nat.gcd_dvd_right N b) h2

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • (M *ᵥ v) ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem
  | exact _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem
  | (apply _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem ..)

theorem tv_mul_mulVec {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
    (x v : Fin n → R) (t : R) (q : ℤ) :
    tv σ G x (q * t) *ᵥ v = v + q • ((tv σ G x t - 1) *ᵥ v) := by
  have : tv σ G x (q * t) = 1 + q • (tv σ G x t - 1) := by
    ext a b
    simp [tv, mul_assoc]
  rw [this, add_mulVec, one_mulVec, smul_mulVec]

theorem exists_tv_adjust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (t : E) (b : ℕ), 0 < b → t + c t = 0 → ∃ (t' : E) (k e : ℕ), t' + c t' = 0 ∧ k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (tv (c : E →+* E) G x t' *ᵥ v - tv (c : E →+* E) G x t *ᵥ v) = b • w) ∧ b ^ e • (tv (c : E →+* E) G x t' *ᵥ v) ∈ L ∧ b ^ e • (tv (c : E →+* E) G x (-t') *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G _ _ L hfg hL x t b _ ht
  obtain ⟨N, hN0, hN⟩ := exists_nsmul_mulVec_mem L hfg hL (tv (c : E →+* E) G x t - 1)
  obtain ⟨A, B, e, hAB, ⟨r, hr⟩, hB⟩ := exists_split b N hN0
  have hBA : B.Coprime (b * A) := by
    refine Nat.Coprime.mul_right hB ?_
    exact Nat.Coprime.coprime_dvd_right ⟨r, hr⟩ (hB.pow_right e)
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hBA
  push_cast at huw
  refine ⟨((u * B : ℤ) : E) * t, B, e, ?_, hB, fun v hv => ?_⟩
  · rw [map_mul, map_intCast, ← mul_add, ht, mul_zero]
  have hz := hN v hv
  have h1 : tv (c : E →+* E) G x t *ᵥ v = v + (tv (c : E →+* E) G x t - 1) *ᵥ v := by
    rw [sub_mulVec, one_mulVec]; abel
  have key : ∀ s : ℤ, b ^ e • (tv (c : E →+* E) G x (((s * B : ℤ) : E) * t) *ᵥ v) ∈ L := by
    intro s
    rw [tv_mul_mulVec, smul_add]
    refine L.add_mem (nsmul_mem hv _) ?_
    have := zsmul_mem hz (s * r)
    convert this using 1
    rw [hr, hAB, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  refine ⟨⟨(-w) • N • ((tv (c : E →+* E) G x t - 1) *ᵥ v), zsmul_mem hz _, ?_⟩, key u, ?_⟩
  · rw [tv_mul_mulVec]
    generalize tv (c : E →+* E) G x t *ᵥ v = y at h1 ⊢
    generalize (tv (c : E →+* E) G x t - 1) *ᵥ v = z at h1 ⊢
    subst h1
    have : v + (u * B) • z - (v + z) = (u * B - 1) • z := by
      rw [sub_smul, one_smul]; abel
    rw [this, hAB, ← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul,
      smul_smul]
    congr 1
    push_cast
    linear_combination (B : ℤ) * huw
  · have := key (-u)
    convert this using 4
    push_cast
    ring

end GlobalTheory.TvAdjust
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_unit_not_localKummerNorm_of_not_pow : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (ζ δ : F) (v : HeightOneSpectrum (𝓞 F)), p.Prime → IsPrimitiveRoot ζ p → (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ) → ∃ c : (v.adicCompletion F)ˣ, c ∉ kNorm p (RingHom.id (v.adicCompletion F)) (algebraMap F (v.adicCompletion F) δ) := by
  first | exact @GlobalTheory.CNorm.exists_local_nonnorm | exact GlobalTheory.CNorm.exists_local_nonnorm | (intros; apply GlobalTheory.CNorm.exists_local_nonnorm <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.LocusOpenCompact

theorem continuous_aeval_comp {F A X σ : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace X] (f : X → σ → A)
    (hf : ∀ i, Continuous fun x => f x i) (P : MvPolynomial σ F) :
    Continuous fun x => MvPolynomial.aeval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hf i)

theorem isClosed_zeroLocusGL {F : Type} [Field F] {n : ℕ}
    (S : Set (MvPolynomial (Fin n × Fin n) F)) (A : Type) [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    IsClosed (HeckeCharacterZeroLocus.zeroLocusGL S A) := by
  have e : HeckeCharacterZeroLocus.zeroLocusGL S A = ⋂ P ∈ S, {g : GL (Fin n) A | MvPolynomial.aeval
      (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0} := by
    ext g; simp only [HeckeCharacterZeroLocus.zeroLocusGL, Set.mem_iInter]; rfl
  rw [e]
  refine isClosed_biInter fun P _ => isClosed_eq ?_ continuous_const
  have hv : Continuous fun g : GL (Fin n) A => (g : Matrix (Fin n) (Fin n) A) :=
    Units.continuous_val
  exact continuous_aeval_comp (X := GL (Fin n) A)
    (fun g (ij : Fin n × Fin n) => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2)
    (fun ij => hv.matrix_elem ij.1 ij.2) P

theorem exists_isOpen_isCompact : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S), ∃ U : Subgroup (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) ∧ IsCompact (U : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) := by
  intro F _ _ n S hS
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  obtain ⟨U, hUo, hUc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact F n
  refine ⟨U.subgroupOf _, hUo.preimage continuous_subtype_val, ?_⟩
  exact (isClosed_zeroLocusGL S (FiniteAdeleRing (𝓞 F) F)).isClosedEmbedding_subtypeVal.isCompact_preimage hUc

end GlobalTheory.LocusOpenCompact
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.IdealSum

theorem tsum_ideal_eq_sum_classes {R : Type} [CommRing R] (m b : Ideal R) [Fintype (R ⧸ m)]
    (hbm : b ⊔ m = ⊤) (s : R ⧸ m → R) (hsb : ∀ r, s r ∈ b)
    (hs : ∀ r, Ideal.Quotient.mk m (s r) = r) (ψ g : R → ℂ)
    (hψ : ∀ a b, a - b ∈ m → ψ a = ψ b) (hg : Summable fun α : b => ψ α * g α) :
    ∑' α : b, ψ α * g α = ∑ r : R ⧸ m, ψ (s r) * ∑' β : ↥(b * m), g ((β : R) + s r) := by
  have hco : IsCoprime b m := Ideal.isCoprime_iff_sup_eq.2 hbm
  have hl : ∀ x ∈ b * m, x ∈ b := fun x hx => (Ideal.mul_le_inf hx).1
  have hr : ∀ x ∈ b * m, x ∈ m := fun x hx => (Ideal.mul_le_inf hx).2
  obtain ⟨φ, hval⟩ : ∃ φ : (R ⧸ m) × ↥(b * m) → b, ∀ p, (φ p).1 = p.2.1 + s p.1 :=
    ⟨fun p => ⟨p.2.1 + s p.1, b.add_mem (hl _ p.2.2) (hsb _)⟩, fun _ => rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨r, β⟩ ⟨r', β'⟩ h
      have h1 : (β : R) + s r = β' + s r' := by
        have h0 := congrArg Subtype.val h
        rwa [hval, hval] at h0
      have h2 := congrArg (Ideal.Quotient.mk m) h1
      have hβ : Ideal.Quotient.mk m (β : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hr _ β.2)
      have hβ' : Ideal.Quotient.mk m (β' : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hr _ β'.2)
      rw [map_add (f := _), map_add (f := _), hs, hs, hβ, hβ', zero_add, zero_add] at h2
      subst h2
      rw [Subtype.ext (add_right_cancel h1)]
    · rintro ⟨a, ha⟩
      have hmem : a - s (Ideal.Quotient.mk m a) ∈ b * m := by
        rw [Ideal.mul_eq_inf_of_isCoprime hco]
        exact Ideal.mem_inf.2 ⟨b.sub_mem ha (hsb _), Ideal.Quotient.eq.1 (hs _).symm⟩
      refine ⟨(Ideal.Quotient.mk m a, ⟨a - s (Ideal.Quotient.mk m a), hmem⟩), Subtype.ext ?_⟩
      rw [hval]
      exact sub_add_cancel _ _
  have h1 : ∑' p, ψ (φ p) * g (φ p) = ∑' α : b, ψ α * g α :=
    (Equiv.ofBijective φ hφ).tsum_eq (fun α : b => ψ α * g α)
  have h2 : Summable fun p => ψ (φ p) * g (φ p) := hg.comp_injective hφ.1
  have h3 : ∑' p, ψ (φ p) * g (φ p) = ∑' r, ∑' β, ψ (φ (r, β)) * g (φ (r, β)) :=
    h2.tsum_prod
  rw [← h1, h3, tsum_fintype]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun β => ?_
  rw [hval]
  rw [hψ ((β : R) + s r) (s r) (by rw [add_sub_cancel_right]; exact hr _ β.2)]

theorem finite_support_dilate (K : Type) [Field K] [NumberField K] (f : mixedSpace K → ℂ)
    (hf : HasCompactSupport f) (t : ℝ) (ht : 0 < t) :
    {α : 𝓞 K | f (t • mixedEmbedding K (α : K)) ≠ 0}.Finite := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : mixedSpace K)).1
    hf.isCompact.isBounded
  let I := FractionalIdeal.mk0 K (1 : (Ideal (𝓞 K))⁰)
  have hd : DiscreteTopology (idealLattice K I).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (idealLattice K I))
  have hfin : (Metric.closedBall (0 : mixedSpace K) (r / t) ∩
      (idealLattice K I : Set (mixedSpace K))).Finite :=
    Metric.finite_isBounded_inter_isClosed
      (isDiscrete_iff_discreteTopology.2 hd)
      Metric.isBounded_closedBall
      (((idealLattice K I).toAddSubgroup).isClosed_of_discreteTopology)
  have hinj : Function.Injective fun α : 𝓞 K => mixedEmbedding K (α : K) :=
    (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective
  refine (hfin.preimage hinj.injOn).subset fun α hα => ⟨?_, ?_⟩
  · have := hr (subset_tsupport f hα)
    rw [mem_closedBall_zero_iff, _root_.norm_smul, Real.norm_of_nonneg ht.le] at this
    rw [mem_closedBall_zero_iff, le_div_iff₀ ht, mul_comm]
    exact this
  · refine (mem_idealLattice K I).2 ⟨(α : K), ?_, rfl⟩
    simp [I]

theorem tsum_idealLattice (K : Type) [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰)
    (F : mixedSpace K → ℂ) :
    ∑' l : idealLattice K (FractionalIdeal.mk0 K J), F l =
      ∑' β : ↥(J.1), F (mixedEmbedding K ((β : 𝓞 K) : K)) := by
  let φ : ↥(J.1) → idealLattice K (FractionalIdeal.mk0 K J) := fun β =>
    ⟨mixedEmbedding K ((β : 𝓞 K) : K), (mem_idealLattice K _).2 ⟨((β : 𝓞 K) : K), by
      rw [FractionalIdeal.coe_mk0]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ β.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      exact Subtype.ext (RingOfIntegers.coe_injective
        (mixedEmbedding_injective K (congrArg Subtype.val h)))
    · rintro ⟨l, hl⟩
      obtain ⟨y, hy, rfl⟩ := (mem_idealLattice K _).1 hl
      rw [FractionalIdeal.coe_mk0] at hy
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      exact ⟨⟨x, hx⟩, rfl⟩
  exact ((Equiv.ofBijective φ hφ).tsum_eq (fun l => F l)).symm

theorem ideal_sum_periodic_dilate : ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (ψ : 𝓞 K → ℂ) (f : mixedSpace K → ℂ), m ≠ ⊥ → (∀ a b, a - b ∈ m → ψ a = ψ b) → ContDiff ℝ ∞ f → HasCompactSupport f → ∃ κ : ℂ, ∀ b : Ideal (𝓞 K), b ≠ ⊥ → b ⊔ m = ⊤ → ∀ A : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖∑' α : b, ψ α * f (t • mixedEmbedding K ((α : 𝓞 K) : K)) - κ / (((Ideal.absNorm b : ℝ) * t ^ Module.finrank ℚ K : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  intro K _ _ m ψ f hm hψ hf hfc
  haveI : Finite (𝓞 K ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm
  haveI : Fintype (𝓞 K ⧸ m) := Fintype.ofFinite _
  set D : ℝ := 2⁻¹ ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)| with hD
  refine ⟨(∑ r : 𝓞 K ⧸ m, ψ (Quotient.out r)) * (∫ x, f x) /
    (((Ideal.absNorm m : ℝ) * D : ℝ) : ℂ), fun b hb hbm A => ?_⟩
  have hrep : ∀ r : 𝓞 K ⧸ m, ∃ x ∈ b, Ideal.Quotient.mk m x = r := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (hbm ▸ Submodule.mem_top : a ∈ b ⊔ m)
    exact ⟨x, hx, by rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hy, add_zero]⟩
  choose s hsb hs using hrep
  let J : (Ideal (𝓞 K))⁰ := ⟨b * m, mem_nonZeroDivisors_iff_ne_zero.2 (mul_ne_zero hb hm)⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.lattice_sum_dilate_haar_asymptotic (mixedSpace K) volume
    (idealLattice K (FractionalIdeal.mk0 K J)) f hf hfc A
  refine ⟨(∑ r : 𝓞 K ⧸ m, ‖ψ (s r)‖) * C, fun t ht ht1 => ?_⟩
  have hsum : Summable fun α : b => ψ α * f (t • mixedEmbedding K ((α : 𝓞 K) : K)) := by
    refine summable_of_hasFiniteSupport ?_
    refine ((finite_support_dilate K f hfc t ht).preimage
      (Subtype.val_injective (p := fun x => x ∈ b)).injOn).subset fun α hα => ?_
    exact right_ne_zero_of_mul hα
  rw [tsum_ideal_eq_sum_classes m b hbm s hsb hs ψ
    (fun α => f (t • mixedEmbedding K (α : K))) hψ hsum]
  have hout : ∀ r : 𝓞 K ⧸ m, ψ (Quotient.out r) = ψ (s r) := fun r =>
    hψ _ _ (Ideal.Quotient.eq.1 ((Ideal.Quotient.mk_out r).trans (hs r).symm))
  have hcov : ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) volume =
      (Ideal.absNorm b : ℝ) * ((Ideal.absNorm m : ℝ) * D) := by
    rw [covolume_idealLattice, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, hD]
    simp only [J, map_mul]
    push_cast
    ring
  have key : (∑ r : 𝓞 K ⧸ m, ψ (Quotient.out r)) * (∫ x, f x) /
      (((Ideal.absNorm m : ℝ) * D : ℝ) : ℂ) /
      (((Ideal.absNorm b : ℝ) * t ^ Module.finrank ℚ K : ℝ) : ℂ) =
      ∑ r : 𝓞 K ⧸ m, ψ (s r) * ((∫ x, f x) /
        ((ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) volume *
          t ^ Module.finrank ℝ (mixedSpace K) : ℝ) : ℂ)) := by
    rw [← Finset.sum_mul, hcov, mixedEmbedding.finrank, div_div, mul_div_assoc]
    simp only [hout]
    congr 2
    push_cast
    ring
  rw [key, ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun r _ => ?_
  rw [← mul_sub, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := hC (mixedEmbedding K (s r : K)) t ht ht1
  rw [tsum_idealLattice K J (fun l => f (t • (l + mixedEmbedding K (s r : K))))] at h
  have hβ : ∀ β : ↥(b * m), mixedEmbedding K (((β : 𝓞 K) + s r : 𝓞 K) : K) =
      mixedEmbedding K ((β : 𝓞 K) : K) + mixedEmbedding K (s r : K) := fun β => by
    rw [← map_add (f := _)]
    rfl
  simp only [hβ]
  exact h

end GlobalTheory.IdealSum
end
