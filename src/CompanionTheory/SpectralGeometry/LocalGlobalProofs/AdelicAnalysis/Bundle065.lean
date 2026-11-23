module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle048
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle064
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.DenSum

variable {F : Type} [Field F] [NumberField F]

noncomputable def dI (b : F) : Ideal (𝓞 F) :=
  Submodule.comap (LinearMap.toSpanSingleton (𝓞 F) F b) (1 : Submodule (𝓞 F) F)

theorem den_eq (b : F) : den b = Ideal.absNorm (dI b) := rfl

theorem mem_dI {b : F} {x : 𝓞 F} : x ∈ dI b ↔ ∃ t : 𝓞 F, (t : F) = (x : F) * b := by
  simp only [dI, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one,
    Algebra.smul_def]

theorem dI_add (b : F) (r : 𝓞 F) : dI (b + (r : F)) = dI b := by
  ext x
  rw [mem_dI, mem_dI]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t - x * r, by push_cast; linear_combination ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t + x * r, by push_cast; linear_combination ht⟩

theorem dI_ne_bot (b : F) : dI b ≠ ⊥ := by
  intro h
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) b
  have hmem : (s : 𝓞 F) ∈ dI b := mem_dI.mpr ⟨a, by rw [mul_comm]; exact hs.symm⟩
  rw [h, Ideal.mem_bot] at hmem
  exact nonZeroDivisors.coe_ne_zero s hmem

theorem fibre_bound (N : ℕ) (hN : 0 < N) (s : Set F)
    (hs : ∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b')
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Finite {b : s // dI (b : F) = I} ∧
      Nat.card {b : s // dI (b : F) = I} ≤ N ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I := by
  classical
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ, a = Ideal.absNorm I := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by rw [ha_def, Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  have haI : (a : 𝓞 F) ∈ I := by rw [ha_def]; exact Ideal.absNorm_mem I
  obtain ⟨C, hC⟩ : I ∣ Ideal.span {(a : 𝓞 F)} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem I).mpr haI)
  have hspan_ne : Ideal.span {(a : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast ha0
  have hC0 : C ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hC
    exact hspan_ne hC
  have hex : ∀ b : {b : s // dI (b : F) = I}, ∃ t : 𝓞 F, (t : F) = (a : F) * ((b : s) : F) := by
    rintro ⟨b, hb⟩
    have hm : (a : 𝓞 F) ∈ dI (b : F) := by rw [hb]; exact haI
    obtain ⟨t, ht⟩ := mem_dI.mp hm
    exact ⟨t, by rw [ht]; push_cast; rfl⟩
  choose t ht using hex
  have htC : ∀ b, t b ∈ C := by
    intro b
    have hle : Ideal.span {t b} * I ≤ I * C := by
      rw [← hC, Ideal.span_singleton_mul_le_iff]
      intro z hz
      have hz' : z ∈ dI ((b : s) : F) := by rw [b.2]; exact hz
      obtain ⟨u, hu⟩ := mem_dI.mp hz'
      rw [Ideal.mem_span_singleton']
      refine ⟨u, ?_⟩
      apply IsFractionRing.injective (𝓞 F) F
      have hu' : algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F z * ((b : s) : F) := hu
      have ht' : algebraMap (𝓞 F) F (t b) = (a : F) * ((b : s) : F) := ht b
      rw [map_mul, map_mul, map_natCast, hu', ht']
      ring
    have hdvd : I * C ∣ I * Ideal.span {t b} := by
      rw [mul_comm I (Ideal.span _)]
      exact Ideal.dvd_iff_le.mpr hle
    have h2 := (mul_dvd_mul_iff_left hI).mp hdvd
    exact (Ideal.span_singleton_le_iff_mem C).mp (Ideal.dvd_iff_le.mp h2)
  let H : AddSubgroup (𝓞 F) := (Ideal.span {((a * N : ℕ) : 𝓞 F)}).toAddSubgroup
  let K : AddSubgroup (𝓞 F) := C.toAddSubgroup
  have haC : (a : 𝓞 F) ∈ C := by
    have h1 : (a : 𝓞 F) ∈ I * C := by rw [← hC]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : C * I ≤ C) (by rwa [mul_comm] at h1)
  have hHK : H ≤ K := by
    intro x hx
    have hle : Ideal.span {((a * N : ℕ) : 𝓞 F)} ≤ C := by
      rw [Ideal.span_singleton_le_iff_mem]
      push_cast
      exact C.mul_mem_right _ haC
    exact hle hx
  let Φ : {b : s // dI (b : F) = I} → K ⧸ H.addSubgroupOf K := fun b => QuotientAddGroup.mk ⟨t b, htC b⟩
  have hΦ : Function.Injective Φ := by
    intro b b' hbb
    have hmem := QuotientAddGroup.eq.mp hbb
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    have hr' : r * ((a * N : ℕ) : 𝓞 F) = -t b + t b' := by simpa using hr
    have h1 := congrArg (algebraMap (𝓞 F) F) hr'
    have htb : algebraMap (𝓞 F) F (t b) = (a : F) * ((b.1 : s) : F) := ht b
    have htb' : algebraMap (𝓞 F) F (t b') = (a : F) * ((b'.1 : s) : F) := ht b'
    simp only [map_mul, map_add (f := _), map_neg, map_natCast, Nat.cast_mul, htb, htb'] at h1
    have hrF : algebraMap (𝓞 F) F r = (r : F) := rfl
    rw [hrF] at h1
    have ha' : (a : F) ≠ 0 := by exact_mod_cast ha0
    have key : ((b'.1 : s) : F) - ((b.1 : s) : F) = (N : F) * (r : F) := by
      apply mul_left_cancel₀ ha'
      linear_combination -h1
    have := hs _ b'.1.2 _ b.1.2 ⟨r, key⟩
    exact Subtype.ext (Subtype.ext this.symm)
  have hnormNat : ∀ m : ℕ, Ideal.absNorm (Ideal.span {(m : 𝓞 F)}) = m ^ Module.finrank ℤ (𝓞 F) := by
    intro m
    rw [Ideal.absNorm_span_singleton]
    have hm : (m : 𝓞 F) = algebraMap ℤ (𝓞 F) (m : ℤ) := by simp
    rw [hm, Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  have hrel : H.relIndex K = N ^ Module.finrank ℤ (𝓞 F) * a := by
    have h1 := AddSubgroup.relIndex_mul_index hHK
    have hKi : K.index = Ideal.absNorm C := by rw [Ideal.absNorm_apply]; rfl
    have hHi : H.index = (a * N) ^ Module.finrank ℤ (𝓞 F) := by
      have h3 : H.index = Ideal.absNorm (Ideal.span {((a * N : ℕ) : 𝓞 F)}) := by rw [Ideal.absNorm_apply]; rfl
      rw [h3, hnormNat]
    have hmul : Ideal.absNorm (Ideal.span {(a : 𝓞 F)}) = a * Ideal.absNorm C := by rw [hC, map_mul, ha_def]
    have hC0' : Ideal.absNorm C ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    rw [hKi, hHi] at h1
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hC0')
    rw [h1, mul_pow, ← hnormNat a, hmul]
    ring
  haveI hfinQ : Finite (K ⧸ H.addSubgroupOf K) := Nat.finite_of_card_ne_zero (by
    show H.relIndex K ≠ 0
    rw [hrel]
    exact Nat.mul_ne_zero (pow_ne_zero _ hN.ne') ha0)
  refine ⟨Finite.of_injective Φ hΦ, ?_⟩
  calc Nat.card {b : s // dI (b : F) = I} ≤ Nat.card (K ⧸ H.addSubgroupOf K) := Nat.card_le_card_of_injective Φ hΦ
    _ = N ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I := by
      show H.relIndex K = _
      rw [hrel, ha_def]

theorem summable_den :
    ∀ (F : Type) [Field F] [NumberField F], ∀ M : ℕ, 3 ≤ M → ∀ N : ℕ, 0 < N → (∀ (b : F) (r : 𝓞 F), den (b + (r : F)) = den b) ∧ (∀ b : F, 0 < den b) ∧ ∀ s : Set F, (∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b') → Summable fun b : s => ((den (b : F) : ℝ) ^ M)⁻¹ := by
  intro F _ _ M hM N hN
  refine ⟨fun b r => by rw [den_eq, den_eq, dI_add], fun b => ?_, fun s hs => ?_⟩
  · rw [den_eq]
    exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact dI_ne_bot b)
  · have hsum2 := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 2 (by norm_num)).1
    have hfin : ∀ I : Ideal (𝓞 F), Finite {b : s // dI (b : F) = I} := by
      intro I
      by_cases hI : I = ⊥
      · subst hI
        haveI : IsEmpty {b : s // dI (b : F) = ⊥} := ⟨fun b => dI_ne_bot _ b.2⟩
        infer_instance
      · exact (fibre_bound N hN s hs I hI).1
    let f : s → ℝ := fun b => ((den (b : F) : ℝ) ^ M)⁻¹
    show Summable f
    rw [← (Equiv.sigmaFiberEquiv (fun b : s => dI (b : F))).summable_iff]
    refine (summable_sigma_of_nonneg (fun _ => by simp only [Function.comp, f]; positivity)).mpr ⟨fun I => ?_, ?_⟩
    · haveI := hfin I
      exact Summable.of_finite
    · refine Summable.of_nonneg_of_le (fun I => tsum_nonneg (fun _ => by simp only [Function.comp, f]; positivity)) (fun I => ?_)
        (hsum2.mul_left ((N : ℝ) ^ Module.finrank ℤ (𝓞 F)))
      by_cases hI : I = ⊥
      · subst hI
        haveI : IsEmpty {b : s // dI (b : F) = ⊥} := ⟨fun b => dI_ne_bot _ b.2⟩
        rw [tsum_empty]
        positivity
      · have hterm : ∀ y : {b : s // dI (b : F) = I},
            (f ∘ ⇑(Equiv.sigmaFiberEquiv fun b : s => dI (b : F))) ⟨I, y⟩ = ((Ideal.absNorm I : ℝ) ^ M)⁻¹ := by
          rintro ⟨b, hb⟩
          simp [f, den_eq, hb]
        rw [tsum_congr hterm, tsum_const, nsmul_eq_mul]
        have hc := (fibre_bound N hN s hs I hI).2
        have hn1 : (1 : ℝ) ≤ Ideal.absNorm I := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
        calc (Nat.card {b : s // dI (b : F) = I} : ℝ) * ((Ideal.absNorm I : ℝ) ^ M)⁻¹
            ≤ ((N : ℝ) ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I) * ((Ideal.absNorm I : ℝ) ^ M)⁻¹ := by
              gcongr
              exact_mod_cast hc
          _ ≤ (N : ℝ) ^ Module.finrank ℤ (𝓞 F) * (Ideal.absNorm I : ℝ) ^ (-(2:ℝ)) := by
              rw [Real.rpow_neg (by positivity), mul_assoc]
              gcongr
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              have ha : (0:ℝ) < Ideal.absNorm I := by linarith
              have hM1 : (Ideal.absNorm I : ℝ) ^ M = (Ideal.absNorm I : ℝ) * (Ideal.absNorm I : ℝ) ^ (M - 1) := by
                rw [← pow_succ']
                congr 1
                omega
              rw [hM1, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
              exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hn1 (by omega))

end GlobalTheory.CompanionTheory.SW.DenSum
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.exists_fibre_family_block_one_eq_map_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ m', IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J), Measurable s → (∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y) → (∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C') → ∃ B : Set (HermR R σ (n + 1)), IsOpen B ∧ hermOf R σ _ hT' ∈ B ∧ (∀ S ∈ B, IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1)) (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B)) (coordHerm R σ b lam (n + 1)) B fib ∧ fib (hermOf R σ _ hT') = c ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibre_family_near_block | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibre_family_near_block | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibre_family_near_block <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.witt_extension_rational_to_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : Fin n → Fin M → E) (Y : Fin n → Fin M → AF F ⊗[F] E), (gramE σ J X).det ≠ 0 → gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) → ∃ h : HA (AF F) σ J, actW (AF F) σ J h (ratTup (AF F) X) = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.TransA.trans_adelic | exact GlobalTheory.CompanionTheory.SW.TransA.trans_adelic | (intros; apply GlobalTheory.CompanionTheory.SW.TransA.trans_adelic <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.ThetaGauss

theorem continuous_gaussQ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (hom : IsHomeomorph e)
    (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) :
    Continuous (gaussQ e b Pm) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, -, -, -, hco, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  have hxw : ∀ w p, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w p := by
    intro w p
    have h := (hco d b).continuous
    exact (continuous_apply w).comp (hom.continuous.comp ((continuous_apply p.2).comp
      (h.comp ((continuous_apply p.1).comp (continuous_apply 0)))))
  have hxw' : ∀ w, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w := fun w =>
    continuous_pi (hxw w)
  unfold gaussQ
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
  exact (hxw' w).dotProduct (Continuous.matrix_mulVec continuous_const (hxw' w))

theorem lintegral_thetaMeas_gauss : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (a : ℕ), 0 < a → ∀ β : F, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (gaussQ e b Pm (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : Fin M × Fin d → F | ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂(prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b B hB ρ e hom hρ Pm μ 𝓕 hμ h𝓕 a ha β
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨hR, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  haveI := hBor 1 M
  have hA := GlobalTheory.T.measurable_finite_level_lattice_set F E σ hσ d M b a
  have hproj : Continuous (projInf : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    (GlobalTheory.T.adelic_tuple_projections F E σ hσ d b 1 M).1
  have hG : Continuous fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
      ENNReal.ofReal (gaussQ e b Pm (projInf X)) :=
    ENNReal.continuous_ofReal.comp ((continuous_gaussQ σ hσ b e hom Pm).comp hproj)
  rw [← lintegral_indicator hA]
  rw [GlobalTheory.T.theta_integral_over_coordinates F E σ hσ M J hJ d b μ 𝓕 hμ h𝓕
    {x | (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}
    {X | gramE σ J X = fun _ _ => algebraMap F E β}
    (fun x => (GlobalTheory.T.coordinate_bijection_trace_form F E σ hσ M J hJ d b).2.2 B hB β x) _
    (hG.measurable.indicator hA)]
  refine lintegral_congr fun ω => tsum_congr fun x => ?_
  obtain ⟨hinf, hfin⟩ := GlobalTheory.T.infinite_component_coordinates_action F E σ hσ M J hJ d b ρ e hρ ω x.1
  have hmem := GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b a (projFin (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))))
  rw [hfin] at hmem
  have hgauss : gaussQ e b Pm (projInf (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1)))) =
      Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x.1 j)) ⬝ᵥ
        (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x.1 j)))) := by
    simp only [gaussQ, hinf]
  by_cases hx : ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x.1 j)) i) v ∈
      v.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (by exact hmem.2 hx), Set.indicator_of_mem (by exact hx), hgauss]
  · rw [Set.indicator_of_notMem, Set.indicator_of_notMem]
    all_goals first | exact hx | exact fun h => hx (hmem.1 h)

end GlobalTheory.CompanionTheory.SW.BB.ThetaGauss
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adele_ring_cocompact_discrete_number_field : ∀ (F : Type) [Field F] [NumberField F], (∃ C : Set (AdeleRing (𝓞 F) F), IsCompact C ∧ ∀ y, ∃ l : F, y - algebraMap F (AdeleRing (𝓞 F) F) l ∈ C) ∧ (∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C → {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite) ∧ NoncompactSpace (AdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact | exact GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact | (intros; apply GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact <;> assumption)
end
