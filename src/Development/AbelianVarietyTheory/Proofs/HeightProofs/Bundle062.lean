module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle016
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsXiOKEvenRamified
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle058
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain

namespace GlobalTheory.RayDescent

theorem dvd_intNorm_sub_one (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (n : ℕ)
    (a : 𝓞 E) (h : (n : 𝓞 E) ∣ a - 1) : (n : 𝓞 K) ∣ Algebra.intNorm (𝓞 K) (𝓞 E) a - 1 := by
  classical
  obtain ⟨c, hc⟩ := h
  have ha : a = 1 + n * c := by rw [← hc]; ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha]
  let F := AlgebraicClosure E
  let r : (E →ₐ[K] F) → (𝓞 E →+* 𝓞 F) := fun σ => RingOfIntegers.mapRingHom (σ : E →+* F)
  have hd : (n : 𝓞 F) ∣ (∏ σ : E →ₐ[K] F, r σ a) - 1 := by
    have : ∀ s : Finset (E →ₐ[K] F), (n : 𝓞 F) ∣ (∏ σ ∈ s, r σ a) - 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert σ s hσ ih =>
        rw [Finset.prod_insert hσ]
        obtain ⟨d, hd⟩ := ih
        refine ⟨r σ a * d + r σ c, ?_⟩
        have h1 : r σ a = 1 + n * r σ c := by rw [ha]; simp
        have h2 : ∏ σ ∈ s, r σ a = 1 + n * d := by rw [← hd]; ring
        rw [h2, h1]; ring
    exact this _
  obtain ⟨d, hd⟩ := hd
  set N := Algebra.intNorm (𝓞 K) (𝓞 E) a with hN
  have hNK : (N : K) = Algebra.norm K (a : E) := Algebra.algebraMap_intNorm (L := E) a
  have hprod : algebraMap K F (N : K) = 1 + n * (d : F) := by
    rw [hNK, Algebra.norm_eq_prod_embeddings K F]
    have := congrArg (algebraMap (𝓞 F) F) hd
    rw [map_sub, map_prod, map_one, map_mul, map_natCast] at this
    rw [← this]
    simp [r]
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
  have hy : algebraMap K F (((N : K) - 1) / n) = d := by
    rw [map_div₀, map_sub, hprod, map_one, map_natCast]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hnF]
  have hint : IsIntegral ℤ (((N : K) - 1) / n) := by
    rw [← isIntegral_algebraMap_iff (B := F), hy]
    exact d.isIntegral_coe
  obtain ⟨y, hy'⟩ : ∃ y : 𝓞 K, (y : K) = ((N : K) - 1) / n := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨y, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 K) K (N - 1) = algebraMap (𝓞 K) K (n * y)
  rw [map_sub, map_mul, map_one, map_natCast]
  change (N : K) - 1 = n * (y : K)
  rw [hy', mul_div_cancel₀ _ hnK]

theorem containsRayField_comp (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Field L] [NumberField L]
    (φ : K →+* E) (ψ : E →+* L) (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField ψ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (ψ.comp φ) n := by
  intro P hP
  obtain ⟨f, α, h1, h2, h3⟩ := h P hP
  letI : Algebra K E := φ.toAlgebra
  letI : Algebra E L := ψ.toAlgebra
  have hq : P.asIdeal.comap (RingOfIntegers.mapRingHom ψ) = P.asIdeal.under (𝓞 E) := rfl
  have hp : P.asIdeal.comap (RingOfIntegers.mapRingHom (ψ.comp φ)) = (P.asIdeal.under (𝓞 E)).under (𝓞 K) := by
    ext x
    rfl
  rw [hq] at h1 h2
  rw [hp]
  haveI := P.isMaximal
  set q := P.asIdeal.under (𝓞 E)
  set p := q.under (𝓞 K)
  haveI : q.IsMaximal := inferInstance
  haveI : p.IsMaximal := inferInstance
  have hrel : Ideal.relNorm (𝓞 K) q = p ^ q.inertiaDeg (𝓞 K) := Ideal.relNorm_eq_pow_of_isMaximal q p
  refine ⟨q.inertiaDeg (𝓞 K) * f, Algebra.intNorm (𝓞 K) (𝓞 E) α, ?_, ?_, dvd_intNorm_sub_one K E n α h3⟩
  · rw [h1, pow_mul, ← map_pow Ideal.absNorm p, ← hrel, Ideal.absNorm_relNorm]
  · rw [pow_mul, ← hrel, ← map_pow, h2, Ideal.relNorm_singleton]

end GlobalTheory.RayDescent
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.RayNorm

open NumberField IsDedekindDomain GlobalTheory.NT
open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem heckeIdeal_prime_pow (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 K)) (f : ℕ) :
    heckeIdeal L χ (𝔮.asIdeal ^ f) = heckeVal L χ 𝔮 ^ f := by
  unfold heckeIdeal
  rw [finprod_eq_single _ 𝔮]
  · rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot)
      (HeightOneSpectrum.associates_irreducible 𝔮), Associates.count_self
      (HeightOneSpectrum.associates_irreducible 𝔮), mul_one]
  · intro 𝔭 h𝔭
    have hne : Associates.mk 𝔭.asIdeal ≠ Associates.mk 𝔮.asIdeal := by
      intro h
      apply h𝔭
      rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq] at h
      exact HeightOneSpectrum.ext h
    rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot)
      (HeightOneSpectrum.associates_irreducible 𝔭), Associates.count_eq_zero_of_ne
      (HeightOneSpectrum.associates_irreducible 𝔭) (HeightOneSpectrum.associates_irreducible 𝔮) hne,
      mul_zero, pow_zero]


omit [NumberField K] [NumberField L] in
theorem pow_smul_sub_mem (P : Ideal (𝓞 L)) {σ : L ≃ₐ[K] L} {q : ℕ} (h : ∀ x : 𝓞 L, σ • x - x ^ q ∈ P) (k : ℕ)
    (x : 𝓞 L) : σ ^ k • x - x ^ q ^ k ∈ P := by
  have h' : ∀ y : 𝓞 L, Ideal.Quotient.mk P (σ • y) = Ideal.Quotient.mk P y ^ q := fun y => by
    rw [← map_pow, Ideal.Quotient.eq]
    exact h y
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Ideal.Quotient.eq] at ih ⊢
    rw [pow_succ' σ k, mul_smul, h', ih, ← map_pow, ← pow_mul, ← pow_succ]

theorem exists_frob_pow_eq_one [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (hu : UnramIn L 𝔭)
    (P : HeightOneSpectrum (𝓞 L)) [hPo : P.asIdeal.LiesOver 𝔭.asIdeal] {f : ℕ}
    (hf : Ideal.absNorm P.asIdeal = Ideal.absNorm 𝔭.asIdeal ^ f) :
    ∃ σ : L ≃ₐ[K] L, IsFrob L 𝔭 σ ∧ σ ^ f = 1 := by
  unfold UnramIn at hu
  have hq : Nat.card (𝓞 K ⧸ P.asIdeal.under (𝓞 K)) = Ideal.absNorm 𝔭.asIdeal := by
    rw [← hPo.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (𝓞 L ⧸ P.asIdeal) :=
    (Ideal.absNorm_ne_zero_iff _).mp (fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P.asIdeal
  have hσ' : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P.asIdeal := fun x => by
    have h1 := hσ x
    rw [hq] at h1
    exact h1
  refine ⟨σ, ⟨P.asIdeal, P.isPrime, hPo, hσ'⟩, ?_⟩
  have hfix : ∀ x : 𝓞 L, σ ^ f • x - x ∈ P.asIdeal := fun x => by
    have h1 := pow_smul_sub_mem P.asIdeal hσ' f x
    have h2 : x ^ Ideal.absNorm 𝔭.asIdeal ^ f - x ∈ P.asIdeal := by
      let _ := Ideal.Quotient.field P.asIdeal
      have _ := Fintype.ofFinite (𝓞 L ⧸ P.asIdeal)
      rw [← hf, ← Ideal.Quotient.eq, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, FiniteField.pow_card]
    have h3 := P.asIdeal.add_mem h1 h2
    rw [sub_add_sub_cancel] at h3
    exact h3
  apply hu
  exact ⟨P.asIdeal, P.isPrime, hPo, hfix⟩

theorem exists_gen_of_ray {𝔮 I : Ideal (𝓞 K)}
    (h : ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α}) :
    ∃ π : 𝓞 K, I = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  obtain ⟨α, β, hr, hI⟩ := h
  unfold RayPair at hr
  obtain ⟨-, hβ, -, hβc, hαβ, -⟩ := hr
  have hα : α ∈ I * Ideal.span {β} := by
    rw [hI]
    exact Ideal.mem_span_singleton_self α
  obtain ⟨π, -, hπ⟩ := Submodule.mem_mul_span_singleton.mp hα
  have hb0 : Ideal.span {β} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hβ
  refine ⟨π, ?_, ?_⟩
  · apply mul_right_cancel₀ hb0
    rw [hI, Ideal.span_singleton_mul_span_singleton, hπ]
  · have hq : β * (π - 1) ∈ 𝔮 := by
      have e : β * (π - 1) = α - β := by
        rw [← hπ]
        ring
      rw [e]
      exact hαβ
    have h1 : (1 : 𝓞 K) ∈ Ideal.span {β} ⊔ 𝔮 := by
      rw [Ideal.isCoprime_iff_sup_eq.mp hβc]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e2 : π - 1 = c * (β * (π - 1)) + (π - 1) * z := by
      calc π - 1 = (π - 1) * (c * β + z) := by rw [hyz, mul_one]
        _ = c * (β * (π - 1)) + (π - 1) * z := by ring
    rw [e2]
    exact 𝔮.add_mem (𝔮.mul_mem_left c hq) (𝔮.mul_mem_left (π - 1) hz)

private theorem pow_residue_degree_eq_one_of_isFrobenius [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (hu : UnramIn L 𝔭)
    (Q : Ideal (𝓞 L)) [hQ : Q.IsPrime] [hQo : Q.LiesOver 𝔭.asIdeal] {f : ℕ}
    (hQf : Ideal.absNorm Q = Ideal.absNorm 𝔭.asIdeal ^ f) (τ : L ≃ₐ[K] L)
    (hτ : ∀ x : 𝓞 L, τ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q) : τ ^ f = 1 := by
  unfold UnramIn at hu
  have hN0 : Ideal.absNorm Q ≠ 0 := by
    rw [hQf]
    exact pow_ne_zero f (fun h0 => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  have hQ0 : Q ≠ ⊥ := fun h0 => hN0 (Ideal.absNorm_eq_zero_iff.mpr h0)
  have hfin : Finite (𝓞 L ⧸ Q) := (Ideal.absNorm_ne_zero_iff _).mp hN0
  haveI : Q.IsMaximal := hQ.isMaximal hQ0
  have hfix : ∀ x : 𝓞 L, τ ^ f • x - x ∈ Q := fun x => by
    have h1 := pow_smul_sub_mem Q hτ f x
    have h2 : x ^ Ideal.absNorm 𝔭.asIdeal ^ f - x ∈ Q := by
      let _ := Ideal.Quotient.field Q
      have _ := Fintype.ofFinite (𝓞 L ⧸ Q)
      rw [← hQf, ← Ideal.Quotient.eq, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, FiniteField.pow_card]
    have h3 := Q.add_mem h1 h2
    rw [sub_add_sub_cancel] at h3
    exact h3
  exact hu _ ⟨Q, hQ, hQo, hfix⟩

theorem containsRayField_of_ray [IsGalois K L] (n : ℕ)
    (hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} → UnramIn L 𝔭)
    (hart : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I (Ideal.span {(n : 𝓞 K)}) →
      (∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) →
        ∃ α β : 𝓞 K, RayPair (Ideal.span {(n : 𝓞 K)}) α β ∧ I * Ideal.span {β} = Ideal.span {α}) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap K L) n := by
  intro 𝔓 h𝔓
  haveI := 𝔓.isPrime
  have hN : ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 K) ∈
      𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap K L)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap K L)) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hN
    have h2 := congrArg (algebraMap (𝓞 K) K) hN
    rw [map_natCast, map_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h2
    exact 𝔓.ne_bot h2
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨_, inferInstance, hne⟩
  haveI : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := ⟨rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f, f = 𝔓.asIdeal.inertiaDeg (𝓞 K) := ⟨_, rfl⟩
  have hf : Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal ^ f := by
    rw [hfdef, Ideal.absNorm_pow_inertiaDeg]
  have hn𝔭 : ((n : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro h
    apply h𝔓
    have h' : (RingOfIntegers.mapRingHom (algebraMap K L)) (n : 𝓞 K) ∈ 𝔓.asIdeal := h
    rwa [map_natCast] at h'
  have hu : UnramIn L 𝔭 := hun 𝔭 (fun h => hn𝔭 (Ideal.dvd_span_singleton.mp h))
  have hcop1 : IsCoprime 𝔭.asIdeal (Ideal.span {(n : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne2
    have e := (𝔭.isMaximal).eq_of_le hne2 le_sup_left
    have h2 : (n : 𝓞 K) ∈ 𝔭.asIdeal ⊔ Ideal.span {(n : 𝓞 K)} :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← e] at h2
    exact hn𝔭 h2
  have hI0 : 𝔭.asIdeal ^ f ≠ ⊥ := pow_ne_zero f 𝔭.ne_bot
  have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ (𝔭.asIdeal ^ f) = 1 := by
    intro χ
    rw [heckeIdeal_prime_pow]
    obtain ⟨σ0, hσ0, -⟩ := exists_frob_pow_eq_one 𝔭 hu 𝔓 hf
    have hc : (∀ σ : L ≃ₐ[K] L, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ :=
      ⟨fun σ hσ => by rw [hu σ hσ, map_one], ⟨σ0, hσ0⟩⟩
    unfold heckeVal
    rw [dite_eq_left hc]
    obtain ⟨Q, hQp, hQo, hQ⟩ := hc.2.choose_spec
    have hQf : Ideal.absNorm Q = Ideal.absNorm 𝔭.asIdeal ^ f := by
      rw [hfdef, Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal 𝔓.asIdeal Q (L ≃ₐ[K] L),
        Ideal.absNorm_pow_inertiaDeg]
    have hτ := pow_residue_degree_eq_one_of_isFrobenius 𝔭 hu Q hQf _ hQ
    have hχτ : χ hc.2.choose ^ f = 1 := by rw [← map_pow, hτ, map_one]
    rw [← Units.val_pow_eq_pow_val, hχτ, Units.val_one]
  obtain ⟨α, β, hr, hI⟩ := hart (𝔭.asIdeal ^ f) hI0 hcop1.pow_left hχ
  obtain ⟨π, hπ, hπ1⟩ := exists_gen_of_ray ⟨α, β, hr, hI⟩
  exact ⟨f, π, hf, hπ, Ideal.mem_span_singleton.mp hπ1⟩

end GlobalTheory.FieldSize.RayNorm

end
end

section

noncomputable section

namespace GlobalTheory.TwistFieldCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.L2.Theta
open GlobalTheory.FinalJoin
open scoped TensorProduct

variable {D : D7}

theorem cF_eq (a : D.host.E) : GlobalTheory.Member.cF D a = D.host.conj a := by
  apply D.host.φ₀.injective
  rw [GlobalTheory.XiCounterexample.conj_emb]
  exact (D.host.conjE_apply D.host.φ₀ a).symm

end GlobalTheory.TwistFieldCompare
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteIdeles_normOne_eq_div_conj_of_congOne : ∀ (D : D7), (∀ x : (AfE D)ˣ, NormOne x → ∃ y, x = y / cjFin D y) ∧ (∀ y : (AfE D)ˣ, cjFin D y = y → ∃ a : Af D.host.F, (y : AfE D) = a ⊗ₜ 1) ∧ ∀ (p N : ℕ) (x : (AfE D)ˣ), p.Prime → p ≠ 2 → p ∣ N → 0 < N → NormOne x → CongOne N x → ∃ y, IntUnit y ∧ CongOne p y ∧ x = y / cjFin D y := by
  first | exact @GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence | exact GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence | (intros; apply GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

theorem _root_.GlobalTheory.T.re_trace_hermitianOrthonormalBasis_mul_eq_ite : ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length), (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.pB_orthonormal | exact GlobalTheory.TypeSum.CasBasis.pB_orthonormal | (intros; apply GlobalTheory.TypeSum.CasBasis.pB_orthonormal <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace


theorem _root_.GlobalTheory.T.indefinite_unitary_lie_orthonormal_bases_props : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε ∧ (kB ε i)ᴴ = -kB ε i ∧ hs (kB ε i) ≤ 1) ∧ ∀ b, pB ε b ∈ lieSet ε ∧ (pB ε b)ᴴ = pB ε b := by
  first | exact @GlobalTheory.TypeSum.CasBasis.bases_mem_lie | exact GlobalTheory.TypeSum.CasBasis.bases_mem_lie | (intros; apply GlobalTheory.TypeSum.CasBasis.bases_mem_lie <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace


theorem _root_.GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε) ∧ ∀ b, pB ε b ∈ lieSet ε := by
  first | exact @GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet | exact GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet | (intros; apply GlobalTheory.TypeSum.CasBasis.bases_mem_lieSet <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

theorem _root_.GlobalTheory.T.re_trace_skewHermitian_mul_hermitianOrthonormalBasis : ∀ (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length), (trace (kB ε i * pB ε b)).re = 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB | exact GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB | (intros; apply GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

theorem _root_.GlobalTheory.T.skewHermitianOrthonormalBasis_trace_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length), (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal | exact GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal | (intros; apply GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace


theorem _root_.GlobalTheory.T.words_on_weighted_casimir_eigenvectors_bounded_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → (∀ i, kB ε i ∈ lieSet ε) → (∀ b, pB ε b ∈ lieSet ε) → ∀ χ : ℂ, (∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v)) → (∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖) → ∀ T : List (List (Mx n)), Words (lieSet ε) T → ∃ (s : ℕ) (C : ℝ), ∀ m ∈ T, ∀ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) → (∀ i, onePlusCas σ (kB ε) (e i) = (μ i : ℂ) • e i) → ∀ z : Fin q → ℂ, ‖∑ j, ((((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) • Dw σ m (e j)‖ ^ 2 ≤ C * ∑ j, ‖z j‖ ^ 2 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.frame_bounded | exact GlobalTheory.TypeSum.CasBasis.frame_bounded | (intros; apply GlobalTheory.TypeSum.CasBasis.frame_bounded <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier


theorem _root_.GlobalTheory.T.exists_orthogonal_projection_polynomial_compact_unitary : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (p : KG ε → ℂ), Continuous p → ∃ p' ∈ GlobalTheory.KFourier.polyV ε d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d, ∫ k, star (q k) * (p k - p' k) ∂(muK ε) = 0 := by
  first | exact @GlobalTheory.KFourier.exists_orthProj_polyV | exact GlobalTheory.KFourier.exists_orthProj_polyV | (intros; apply GlobalTheory.KFourier.exists_orthProj_polyV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) → ∀ (M : ℕ) (u : List (Mx n)), (∀ Y ∈ u, inK ε Y) → ∃ C : ℝ, ∀ (d : ℕ) (p : KG ε → ℂ), p ∈ polyV ε d → ∀ y ∈ UJset ε, ‖∫ k, ((fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] p) k * F u (y * toMK k) ∂(muK ε)‖ ≤ C * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖p k‖ ^ 2 ∂(muK ε)) := by
  first | exact @GlobalTheory.KFourier.CasimirMove.casimir_pow_bound | exact GlobalTheory.KFourier.CasimirMove.casimir_pow_bound | (intros; apply GlobalTheory.KFourier.CasimirMove.casimir_pow_bound <;> assumption)
end
