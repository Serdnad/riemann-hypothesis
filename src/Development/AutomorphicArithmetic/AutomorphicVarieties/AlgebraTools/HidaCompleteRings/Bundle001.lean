module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

section

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

variable {O R K : Type*} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K]

def Sep (Y : Set (R →ₐ[O] K)) : Prop := ∀ f : R, (∀ y ∈ Y, y f = 0) → f = 0

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
end

section

open IsLocalRing

private theorem map_mem_smul_top {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : Module.End R N) {x : N} (hx : x ∈ J • (⊤ : Submodule R N)) :
    f x ∈ J • (⊤ : Submodule R N) := by
  have h1 : f x ∈ (J • (⊤ : Submodule R N)).map f := Submodule.mem_map_of_mem hx
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

private theorem pow_mem_pow_smul_top {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : Module.End R N) (hf : ∀ x, f x ∈ J • (⊤ : Submodule R N)) (k : ℕ) :
    ∀ x, (f ^ k) x ∈ J ^ k • (⊤ : Submodule R N) := by
  induction k with
  | zero =>
    intro x
    simp
  | succ k ih =>
    intro x
    rw [pow_succ' f k, Module.End.mul_apply, pow_succ J k, Submodule.mul_smul]
    have h1 : f ((f ^ k) x) ∈ (J ^ k • (⊤ : Submodule R N)).map f :=
      Submodule.mem_map_of_mem (ih x)
    rw [Submodule.map_smul''] at h1
    refine Submodule.smul_mono le_rfl ?_ h1
    rintro _ ⟨z, _, rfl⟩
    exact hf z

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar :
    ∀ (R N T ι : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup N] [Module R N] [Module.Finite R N] [CommRing T] (ρ : T →+* Module.End R N) (I : Ideal T) (u : ι → T) (e : T), (∀ μ ∈ I, ∀ x, ρ μ x ∈ maximalIdeal R • (⊤ : Submodule R N)) → IsIdempotentElem e → (∀ i, ∃ n : ℕ, u i ^ n * e ∈ I) → 1 - e ∈ I ⊔ Ideal.span (Set.range u) → ∀ x, ρ e x = x ↔ ∀ (i : ι) (k : ℕ), ∃ n : ℕ, (ρ (u i) ^ n) x ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := by
  intro R N T ι _ _ _ _ _ _ _ ρ I u e hI he hu hspan x
  have hP : ∀ (k : ℕ) (t : T) {z : N}, z ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) →
      ρ t z ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) :=
    fun k t z hz => map_mem_smul_top _ (ρ t) hz
  constructor
  · intro hx i k
    obtain ⟨n, hn⟩ := hu i
    have hek : ∀ j : ℕ, ρ (e ^ j) x = x := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, map_mul, Module.End.mul_apply, hx, ih]
    refine ⟨n * k, ?_⟩
    have hmem := pow_mem_pow_smul_top (maximalIdeal R) (ρ (u i ^ n * e)) (hI _ hn) k x
    have heq : (ρ (u i) ^ (n * k)) x = (ρ (u i ^ n * e) ^ k) x := by
      rw [← map_pow, ← map_pow, mul_pow, ← pow_mul, map_mul, Module.End.mul_apply, hek k]
    rw [heq]
    exact hmem
  · intro h
    obtain ⟨y, hy⟩ : ∃ y, y = ρ (1 - e) x := ⟨_, rfl⟩
    have hyk : ∀ k : ℕ, y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := by
      intro k
      let S : Ideal T :=
        { carrier := {t | ρ t y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)}
          add_mem' := fun {a b} ha hb => by
            show ρ (a + b) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_add (f := _), LinearMap.add_apply]
            exact add_mem ha hb
          zero_mem' := by
            show ρ 0 y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_zero, LinearMap.zero_apply]
            exact zero_mem _
          smul_mem' := fun c t ht => by
            show ρ (c * t) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_mul, Module.End.mul_apply]
            exact hP k c ht }
      have hrad : I ⊔ Ideal.span (Set.range u) ≤ S.radical := by
        refine sup_le (fun μ hμ => Ideal.mem_radical_iff.mpr ⟨k, ?_⟩) (Ideal.span_le.mpr ?_)
        · show ρ (μ ^ k) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
          rw [map_pow]
          exact pow_mem_pow_smul_top _ (ρ μ) (hI μ hμ) k y
        · rintro _ ⟨i, rfl⟩
          obtain ⟨n, hn⟩ := h i k
          refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
          show ρ (u i ^ n) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
          have hc : ρ (u i ^ n) y = ρ (1 - e) ((ρ (u i) ^ n) x) := by
            rw [hy, ← map_pow, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
              ← map_mul, mul_comm]
          rw [hc]
          exact hP k _ hn
      obtain ⟨K, hK⟩ := Ideal.mem_radical_iff.mp (hrad hspan)
      have hKy : ρ ((1 - e) ^ K) y = y := by
        rw [hy, ← Module.End.mul_apply, ← map_mul, ← pow_succ, he.one_sub.pow_succ_eq]
      have hK' : ρ ((1 - e) ^ K) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := hK
      rwa [hKy] at hK'
    have hy0 : y = 0 := IsHausdorff.haus inferInstance y (fun k => SModEq.zero.mpr (hyk k))
    rw [hy, map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hy0
    exact hy0.symm
end

section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.invMem :
    ∀ (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] (S : Subalgebra Λ (Module.End Λ M)) (u : (Module.End Λ M)ˣ), (u : Module.End Λ M) ∈ S → ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ∈ S := by
  intro Λ M _ _ _ _ S u hu
  obtain ⟨p, hp, hpv⟩ :=
    LinearMap.exists_monic_and_aeval_eq_zero Λ ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M)
  have key : ∀ n i, i ≤ n → (u : Module.End Λ M) ^ n *
      ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ i = (u : Module.End Λ M) ^ (n - i) := by
    intro n i hi
    have h1 : (u : Module.End Λ M) ^ i * ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ i = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv]
    rw [← pow_sub_mul_pow (u : Module.End Λ M) hi, mul_assoc, h1, mul_one]
  rw [Polynomial.aeval_eq_sum_range] at hpv
  cases h : p.natDegree with
  | zero =>
    have hc : p.coeff 0 = 1 := by rw [← h]; exact hp.coeff_natDegree
    rw [h, Finset.sum_range_one, hc, one_smul, pow_zero] at hpv
    have hz : ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) = 0 := by
      rw [← mul_one ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M), hpv, mul_zero]
    rw [hz]
    exact S.zero_mem
  | succ n =>
    have hc : p.coeff (n + 1) = 1 := by rw [← h]; exact hp.coeff_natDegree
    rw [h, Finset.sum_range_succ, hc, one_smul] at hpv
    have hmul := congrArg (fun w => (u : Module.End Λ M) ^ n * w) hpv
    rw [mul_add, Finset.mul_sum, mul_zero] at hmul
    have hlast : (u : Module.End Λ M) ^ n *
        ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ (n + 1) =
        ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) := by
      rw [pow_succ, ← mul_assoc, key n n le_rfl, Nat.sub_self, pow_zero, one_mul]
    rw [hlast] at hmul
    have hterm : ∀ i ∈ Finset.range (n + 1), (u : Module.End Λ M) ^ n *
        (p.coeff i • ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ i) =
        p.coeff i • (u : Module.End Λ M) ^ (n - i) := by
      intro i hi
      rw [mul_smul_comm, key n i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    rw [Finset.sum_congr rfl hterm] at hmul
    rw [eq_neg_of_add_eq_zero_right hmul]
    exact S.neg_mem (S.sum_mem fun i _ => S.smul_mem (S.pow_mem hu _) _)
end

section

noncomputable section

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section Alg

variable {k G V N : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup N] [Module k N]

abbrev Into (ρ : Representation k G V) (Y : Submodule k V) (σ : Representation k G N) : Type :=
  {f : N →ₗ[k] V // (∀ g v, f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y}

def copies (ρ : Representation k G V) (Y : Submodule k V) (σ : Representation k G N) : Submodule k V :=
  ⨆ f : Into ρ Y σ, LinearMap.range f.1

end Alg

section Mass

variable {G : Type} [Group G]

end Mass

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
end
end

section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finMax :
    ∀ (Λ T : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing T] [Algebra Λ T] [Module.Finite Λ T], Finite (MaximalSpectrum T) ∧ (∀ m : Ideal T, m.IsMaximal → m.comap (algebraMap Λ T) = maximalIdeal Λ ∧ (Finite (ResidueField Λ) → Finite (T ⧸ m))) ∧ ∃ n : ℕ, (⊥ : Ideal T).jacobson ^ n ≤ (maximalIdeal Λ).map (algebraMap Λ T) ∧ (maximalIdeal Λ).map (algebraMap Λ T) ≤ (⊥ : Ideal T).jacobson := by
  intro Λ T _ _ _ _ _
  let I : Ideal T := (maximalIdeal Λ).map (algebraMap Λ T)
  have h1 : Module.Finite Λ (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ Λ I).toLinearMap Ideal.Quotient.mk_surjective
  have h2 : Module.Finite (Λ ⧸ maximalIdeal Λ) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  have h0 : IsArtinianRing (Λ ⧸ maximalIdeal Λ) := by
    letI := Ideal.Quotient.field (maximalIdeal Λ)
    infer_instance
  have h3 : IsArtinianRing (T ⧸ I) := IsArtinianRing.of_finite (Λ ⧸ maximalIdeal Λ) (T ⧸ I)
  have hcomap : ∀ m : Ideal T, m.IsMaximal → m.comap (algebraMap Λ T) = maximalIdeal Λ := by
    intro m hm
    haveI := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Λ) m
    exact IsLocalRing.eq_maximalIdeal this
  have hIm : ∀ m : Ideal T, m.IsMaximal → I ≤ m := fun m hm =>
    Ideal.map_le_iff_le_comap.2 (hcomap m hm).ge
  have hker : RingHom.ker (Ideal.Quotient.mk I) = I := Ideal.mk_ker
  refine ⟨?_, ?_, ?_⟩
  · let f : MaximalSpectrum (T ⧸ I) → MaximalSpectrum T := fun p =>
      ⟨p.asIdeal.comap (Ideal.Quotient.mk I),
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
    apply Finite.of_surjective f
    intro m
    have hcm : (m.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = m.asIdeal := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        hker]
      exact sup_eq_left.2 (hIm _ m.isMaximal)
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective m.isMaximal with h | h
    · exfalso
      apply m.isMaximal.ne_top
      rw [← hcm, h, Ideal.comap_top]
    · exact ⟨⟨_, h⟩, MaximalSpectrum.ext hcm⟩
  · intro m hm
    refine ⟨hcomap m hm, fun hk => ?_⟩
    haveI : Finite (Λ ⧸ maximalIdeal Λ) := hk
    haveI : Finite (T ⧸ I) := Module.finite_of_finite (Λ ⧸ maximalIdeal Λ)
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective (hIm m hm))
  · obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T ⧸ I)
    refine ⟨n, ?_, ?_⟩
    · have hJ : (⊥ : Ideal T).jacobson.map (Ideal.Quotient.mk I) ≤ (⊥ : Ideal (T ⧸ I)).jacobson := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_jacobson_bot]
        intro y
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [← map_mul, ← map_one (Ideal.Quotient.mk I), ← map_add (f := _)]
        exact (Ideal.mem_jacobson_bot.1 hx y).map _
      intro x hx
      have hx' : Ideal.Quotient.mk I x ∈ ((⊥ : Ideal (T ⧸ I)).jacobson) ^ n := by
        apply Ideal.pow_right_mono hJ n
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hx
      rw [hn] at hx'
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hx'
    · rw [Ideal.jacobson]
      refine le_sInf ?_
      rintro m ⟨-, hm⟩
      exact hIm m hm
end
