module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import ReciprocityTheory.SemistableReduction.Bundle018
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle026
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.PowMulMem

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem alg_mem (L : LocE F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ L.O := by
  rw [L.O_def]
  exact isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := a)

theorem exists_pow_mul_mem [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) (e : E) : ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * e ∈ L.O := by
  apply GlobalTheory.PowSmulMemLattice.exists_pow_mul_mem_O <;> assumption

theorem exists_pow_smul_mem [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E)
    {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ} {Λ : Submodule L.O (Fin n → E)}
    (hΛ : GlobalTheory.HL.IsLat L Λ) (v : Fin n → E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) • v ∈ Λ := by
  have hO : ∀ (x : E), x ∈ L.O → ∀ w ∈ Λ, x • w ∈ Λ := fun x hx w hw =>
    Λ.smul_mem (⟨x, hx⟩ : L.O) hw
  have hp : ∀ k : ℕ, algebraMap F E ((ϖ : F) ^ k) ∈ L.O := fun k => by
    rw [map_pow]; exact L.O.pow_mem (alg_mem L ϖ) k
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, hO _ (hp 0) _ hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · have := hO _ (hp b) _ ha
      rwa [smul_smul, ← map_mul, ← pow_add, add_comm b a] at this
    · have := hO _ (hp a) _ hb
      rwa [smul_smul, ← map_mul, ← pow_add] at this
  | smul e x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := exists_pow_mul_mem L hϖ e
    refine ⟨a + b, ?_⟩
    have := hO _ hb _ ha
    have h : algebraMap F E ((ϖ : F) ^ (a + b)) • e • x
        = (algebraMap F E ((ϖ : F) ^ b) * e) • algebraMap F E ((ϖ : F) ^ a) • x := by
      rw [smul_smul, smul_smul, pow_add, map_mul]
      congr 1
      ring
    rw [h]
    exact this

end GlobalTheory.PowMulMem
end

section

namespace GlobalTheory.FiniteSumFlagMeasures

open NumberField

theorem main {K : Type} [Field K] [NumberField K] {b : ℕ}
    (B : Submodule (NumberField.RingOfIntegers K) (Fin b → K))
    (hB : Submodule.span K (↑B : Set (Fin b → K)) = ⊤) (v : Fin b → K) :
    ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ B := by
  apply ReciprocityTheory.MultiplicativeHeights.sc_scale <;> assumption

end GlobalTheory.FiniteSumFlagMeasures
end

section

namespace GlobalTheory.SaturatedSublattice

open NumberField

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤ → ∀ (v : Fin n → E), ∃ (D : NumberField.RingOfIntegers E), D ≠ (0 : NumberField.RingOfIntegers E) ∧ D • v ∈ Λ := by
  apply ReciprocityTheory.MultiplicativeHeights.sc_scale <;> assumption

end GlobalTheory.SaturatedSublattice
end

section

namespace GlobalTheory.DenominatorTheorem

open NumberField

theorem main_theorem : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (G : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    Submodule.span E (↑G : Set (Fin n → E)) = ⊤ → ∀ (y : Fin n → E),
    ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ G := by
  apply ReciprocityTheory.MultiplicativeHeights.sc_scale <;> assumption

end GlobalTheory.DenominatorTheorem
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal NNReal

namespace GlobalTheory.FibreScaling

variable {P Q : ℕ}

theorem qf_continuous : Continuous (qf : Sp P Q → ℝ) := by
  unfold qf
  fun_prop

theorem qf_real_smul (r : ℝ) (x : Sp P Q) : qf (r • x) = r ^ 2 * qf x := by
  simp only [qf, Pi.smul_apply, Complex.real_smul, map_mul, Complex.normSq_ofReal, mul_sub,
    Finset.mul_sum, sq]

theorem finrank_sp : Module.finrank ℝ (Sp P Q) = 2 * (P + Q) := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

theorem map_dx_smul {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (P + Q)) • (dx P Q).map (fun y => Real.sqrt t • y) = dx P Q := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hm : AEMeasurable (fun y : Sp P Q => Real.sqrt t • y) (volume : Measure (Sp P Q)) :=
    (continuous_const_smul _).aemeasurable
  have h := Measure.map_addHaar_smul (volume : Measure (Sp P Q)) hs
  rw [finrank_sp, pow_mul, Real.sq_sqrt ht.le, abs_of_pos (by positivity)] at h
  rw [dx, Measure.map_smul _ hm, h, smul_comm, smul_smul (ENNReal.ofReal _),
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
    one_smul]

theorem lintegral_inv_mul {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ≥0∞) :
    ∫⁻ b, g (t⁻¹ * b) = ENNReal.ofReal t * ∫⁻ b, g b := by
  have h := (Homeomorph.mulLeft₀ t⁻¹ (inv_ne_zero ht.ne')).measurableEmbedding.lintegral_map
    (μ := volume) g
  rw [Homeomorph.coe_mulLeft₀, Real.map_volume_mul_left (inv_ne_zero ht.ne'), inv_inv,
    abs_of_pos ht, lintegral_smul_measure, smul_eq_mul] at h
  exact h.symm

theorem isDxDq_scale {fib : ℝ → Measure (Sp P Q)} (h : IsDxDq fib) {t : ℝ} (ht : 0 < t) :
    IsDxDq fun b => ENNReal.ofReal (t ^ (P + Q) / t) •
      (fib (t⁻¹ * b)).map (fun y => Real.sqrt t • y) := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hc : Continuous (fun y : Sp P Q => Real.sqrt t • y) := continuous_const_smul _
  have hm := hc.measurable
  have hpre : (fun y : Sp P Q => Real.sqrt t • y) ⁻¹' {x : Sp P Q | x ≠ 0} = {x | x ≠ 0} :=
    Set.ext fun x => by simp [hs]
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hsu hts => ?_⟩
  · have hS : MeasurableSet (qf ⁻¹' {id b} ∩ {x : Sp P Q | x ≠ 0})ᶜ :=
      ((qf_continuous.measurable (measurableSet_singleton _)).inter isOpen_ne.measurableSet).compl
    have h0 : ((fib (t⁻¹ * b)).map (fun y => Real.sqrt t • y))
        (qf ⁻¹' {id b} ∩ {x : Sp P Q | x ≠ 0})ᶜ = 0 := by
      rw [Measure.map_apply hm hS]
      convert h.1 (t⁻¹ * b) using 2
      rw [Set.preimage_compl, Set.preimage_inter, hpre]
      congr 2
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, id, qf_real_smul, Real.sq_sqrt ht.le]
      exact (eq_inv_mul_iff_mul_eq₀ ht.ne').symm
    rw [Measure.smul_apply, h0, smul_zero]
  · simp only [lintegral_smul_measure, lintegral_map hφ hm, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_inv_mul ht fun b => ∫⁻ y, φ (Real.sqrt t • y) ∂(fib b),
      ← h.2.1 (fun x => φ (Real.sqrt t • x)) (hφ.comp hm), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ ht.ne']
    conv_lhs => rw [← map_dx_smul ht]
    rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      Measure.restrict_map hm isOpen_ne.measurableSet, lintegral_map hφ hm, hpre]
  · have hs' : HasCompactSupport (φ ∘ fun y : Sp P Q => Real.sqrt t • y) :=
      hsu.comp_homeomorph (Homeomorph.smulOfNeZero (Real.sqrt t) hs)
    have ht' : tsupport (φ ∘ fun y : Sp P Q => Real.sqrt t • y) ⊆ {x | x ≠ 0} := by
      rw [← hpre]
      exact (tsupport_comp_subset_preimage φ hc).trans (Set.preimage_mono hts)
    obtain ⟨h1, h2⟩ := h.2.2 _ (hφ.comp hc) hs' ht'
    refine ⟨fun b _ => ?_, ?_⟩
    · exact ((integrable_map_measure hφ.aestronglyMeasurable hm.aemeasurable).2
        (h1 _ trivial)).smul_measure ENNReal.ofReal_ne_top
    · simp only [integral_smul_measure, integral_map hm.aemeasurable hφ.aestronglyMeasurable]
      exact (((continuousOn_univ.1 h2).comp (continuous_const_mul t⁻¹)).const_smul
        (ENNReal.ofReal (t ^ (P + Q) / t)).toReal).continuousOn

theorem lintegral_fibre_scale : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β t : ℝ), IsDxDq fib →
    β ≠ 0 → 0 < t → ∀ φ : Sp P Q → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ y ∂(fib (t * β)) =
        ENNReal.ofReal (t ^ (P + Q) / t) * ∫⁻ y, φ (Real.sqrt t • y) ∂(fib β) := by
  intro P Q fib β t h hβ ht φ hφ
  have hO : (qf : Sp P Q → ℝ) ⁻¹' {t * β} ⊆ {x | x ≠ 0} := by
    rintro x hx rfl
    exact mul_ne_zero ht.ne' hβ (by simpa [qf] using hx.symm)
  have e := GlobalTheory.IsFibreFamily_eq_at (dx P Q) qf {x | x ≠ 0} {x | x ≠ 0} {x | x ≠ 0} Set.univ
    Set.univ fib _ (t * β) qf_continuous.measurable isOpen_ne subset_rfl subset_rfl hO isOpen_univ
    isOpen_univ trivial trivial h (isDxDq_scale h ht)
  rw [e, lintegral_smul_measure, smul_eq_mul, inv_mul_cancel_left₀ ht.ne',
    lintegral_map hφ (continuous_const_smul _).measurable]

end GlobalTheory.FibreScaling
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.pairing_conj_inverseAdjoint_close_to_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (Z Zi M Mi M' : Matrix (Fin n) (Fin n) E) (t e : E), t ∈ L.O → L.cj t = t → Zi * Z = 1 → (∀ i j, e * Z i j ∈ L.O) → (∀ i j, e * Zi i j ∈ L.O) → Mi * M = 1 → M * Mi = 1 → (∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o) → cT L M * Z * M' = Z → ∀ i j, ∃ o ∈ L.O, e * e * (M' - 1) i j = t * o := by
  first | exact @GlobalTheory.Sloc.CloseConj.main | exact GlobalTheory.Sloc.CloseConj.main | (intros; apply GlobalTheory.Sloc.CloseConj.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FiniteModuleOrder

theorem exists_card_eq_pow (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) :
    ∀ (D : Type) [AddCommGroup D] [Module R D] [Finite D], Nat.card D = n →
      ∃ i : ℕ, Nat.card D = Nat.card (R ⧸ IsLocalRing.maximalIdeal R) ^ i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D _ _ _ hn
    rcases subsingleton_or_nontrivial D with h | h
    · exact ⟨0, by simp⟩
    have hfin : Finite (Submodule R D) := Finite.of_injective _ SetLike.coe_injective
    obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R D)).resolve_left bot_ne_top
    have hs : IsSimpleModule R (D ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
    have hI' : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
    subst hI'
    have hc := Submodule.card_eq_card_quotient_mul_card M
    have hnt : Nontrivial (D ⧸ M) := IsSimpleModule.nontrivial R _
    have hf : Finite (D ⧸ M) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective M)
    have h2 : 1 < Nat.card (D ⧸ M) := Finite.one_lt_card
    have hpos : 0 < Nat.card M := Nat.card_pos
    obtain ⟨i, hi⟩ := ih (Nat.card M) (by rw [← hn, hc]; nlinarith) M rfl
    exact ⟨i + 1, by rw [hc, hi, Nat.card_congr e.toEquiv, pow_succ]⟩

theorem card_eq_pow_and_index_ge : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D], (∃ i : ℕ, Nat.card D = resQ ϖ ^ i) ∧ ∀ I : Submodule L.O D, I ≠ ⊤ → resQ ϖ * Nat.card I ≤ Nat.card D := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  have key : ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D],
      ∃ i : ℕ, Nat.card D = resQ ϖ ^ i := by
    intro D _ _ _
    let : Module 𝒪[F] D := Module.compHom D i
    rw [resQ, ← hϖ.maximalIdeal_eq]
    exact exists_card_eq_pow 𝒪[F] _ D rfl
  intro D _ _ _
  refine ⟨key D, fun I hI => ?_⟩
  have hnt : Nontrivial (D ⧸ I) := Submodule.Quotient.nontrivial_iff.2 hI
  have hf : Finite (D ⧸ I) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective I)
  have h2 : 1 < Nat.card (D ⧸ I) := Finite.one_lt_card
  obtain ⟨j, hj⟩ := key (D ⧸ I)
  have hj0 : j ≠ 0 := by rintro rfl; rw [pow_zero] at hj; omega
  rw [Submodule.card_eq_card_quotient_mul_card I, hj, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_self_pow hj0 _)

end GlobalTheory.FiniteModuleOrder
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramVal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem zpow_mul_unit_mem_iff {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ) (u : (𝒪[F])ˣ) :
    (ϖ : F) ^ k * ((u : 𝒪[F]) : F) ∈ 𝒪[F] ↔ 0 ≤ k := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  constructor
  · intro h
    by_contra hk
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one (ϖ ^ n * ⟨_, h⟩ * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])) ?_)
    apply Subtype.ext
    have hu : ((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have h1 : (ϖ : F) * (ϖ : F) ^ n * (ϖ : F) ^ (-((n : ℤ) + 1)) = 1 := by
      rw [zpow_neg, zpow_add_one₀ h0, zpow_natCast]
      field_simp
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_one]
    linear_combination (((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F)) * h1 + hu
  · intro hk
    lift k to ℕ using hk
    rw [zpow_natCast]
    exact Subring.mul_mem _ (Subring.pow_mem _ ϖ.2 k) (u : 𝒪[F]).2

variable [IsNonarchimedeanLocalField F]

theorem vE_zpow_mul_unit (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ)
    (u : (𝒪[F])ˣ) : vE L ϖ (algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))) = k := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hset : {m : ℤ | ∃ y ∈ L.O, algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))
      = algebraMap F E ((ϖ : F) ^ m) * y} = Set.Iic k := by
    ext m
    have hsplit : (ϖ : F) ^ k * ((u : 𝒪[F]) : F)
        = (ϖ : F) ^ m * ((ϖ : F) ^ (k - m) * ((u : 𝒪[F]) : F)) := by
      rw [← mul_assoc, ← zpow_add₀ h0]; congr 2; ring
    have hun : IsUnit (algebraMap F E ((ϖ : F) ^ m)) :=
      (IsUnit.mk0 _ (zpow_ne_zero m h0)).map _
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [hsplit, map_mul, ← sub_nonneg, ← zpow_mul_unit_mem_iff hϖ (k - m) u,
      ← GlobalTheory.UnramOrder.algebraMap_mem_iff L]
    constructor
    · rintro ⟨y, hy, h⟩
      rw [hun.mul_left_cancel h]; exact hy
    · intro h; exact ⟨_, h, rfl⟩
  rw [vE, hset, csSup_Iic]

theorem exists_eq_zpow_mul_unit {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : F} (hx : x ≠ 0) :
    ∃ (k : ℤ) (u : (𝒪[F])ˣ), x = (ϖ : F) ^ k * ((u : 𝒪[F]) : F) := by
  obtain ⟨k, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hx
  refine ⟨k, u, ?_⟩
  rw [h, mul_comm]; rfl

theorem vE_valuation : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → (∀ x y : F, x ≠ 0 → y ≠ 0 → vE L ϖ (algebraMap F E (x * y)) = vE L ϖ (algebraMap F E x) + vE L ϖ (algebraMap F E y)) ∧ vE L ϖ (algebraMap F E (ϖ : F)) = 1 ∧ (∀ x : F, x ≠ 0 → (0 ≤ vE L ϖ (algebraMap F E x) ↔ x ∈ 𝒪[F])) ∧ (∀ x : F, x ≠ 0 → ∃ u : (𝒪[F])ˣ, x = (ϖ : F) ^ (vE L ϖ (algebraMap F E x)) * ((u : 𝒪[F]) : F)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨fun x y hx hy => ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    obtain ⟨l, v, rfl⟩ := exists_eq_zpow_mul_unit hϖ hy
    have : (ϖ : F) ^ k * ((u : 𝒪[F]) : F) * ((ϖ : F) ^ l * ((v : 𝒪[F]) : F))
        = (ϖ : F) ^ (k + l) * (((u * v : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
      rw [zpow_add₀ h0, Units.val_mul, Subring.coe_mul]; ring
    rw [this, vE_zpow_mul_unit L hϖ, vE_zpow_mul_unit L hϖ, vE_zpow_mul_unit L hϖ]
  · simpa using vE_zpow_mul_unit L hϖ 1 1
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    rw [vE_zpow_mul_unit L hϖ, zpow_mul_unit_mem_iff hϖ]
  · obtain ⟨k, u, rfl⟩ := exists_eq_zpow_mul_unit hϖ hx
    exact ⟨u, by rw [vE_zpow_mul_unit L hϖ]⟩

end GlobalTheory.UnramVal
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbTransport

open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
private lemma exists_smul_eq_orbit_out {G α : Type} [Group G] [MulAction G α] (y : α) :
    ∃ g : G, g • y = (Quotient.mk (orbitRel G α) y).out := by
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G α) y
  exact ⟨g, hg⟩

open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
private lemma card_stabilizer_smul_eq' {G α : Type} [Group G] [MulAction G α] (g : G) (a : α) :
    ENat.card (stabilizer G (g • a)) = ENat.card (stabilizer G a) :=
  (ENat.card_congr (stabilizerEquivStabilizer (g := g) rfl).toEquiv).symm


open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
theorem _root_.GlobalTheory.Mass.OrbTransport.main : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → _root_.GlobalTheory.Mass.orbSum G X (fun x => N (f x)) = _root_.GlobalTheory.Mass.orbSum G' Y N := by
  intro G G' α β _ _ _ _ φ f X Y N hX hY hf hequiv hN
  have hcard : ∀ x ∈ X, ENat.card (stabilizer G' (f x)) = ENat.card (stabilizer G x) := by
    intro x hx
    refine (ENat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun g => ?_)).symm
    simp only [mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← hequiv g x hx]
    exact ⟨fun h => by rw [h], fun h => hf.injOn (hX g x hx) hx h⟩
  have hout : ∀ q : {q : orbitRel.Quotient G α // q.out ∈ X},
      (Quotient.mk (orbitRel G' β) (f q.1.out)).out ∈ Y := by
    intro q
    obtain ⟨g, hg⟩ := exists_smul_eq_orbit_out (G := G') (f q.1.out)
    rw [← hg]
    exact hY g _ (hf.mapsTo q.2)
  let F : {q : orbitRel.Quotient G α // q.out ∈ X} → {q : orbitRel.Quotient G' β // q.out ∈ Y} :=
    fun q => ⟨Quotient.mk _ (f q.1.out), hout q⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ h
      obtain ⟨g', hg'⟩ := Quotient.exact (congrArg Subtype.val h)
      apply Subtype.ext
      show q₁ = q₂
      rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
      apply Quotient.sound
      refine ⟨φ.symm g', ?_⟩
      apply hf.injOn (hX _ _ h₂) h₁
      rw [hequiv _ _ h₂, MulEquiv.apply_symm_apply]
      exact hg'
    · rintro ⟨q', hq'⟩
      obtain ⟨x, hx, hfx⟩ := hf.surjOn hq'
      obtain ⟨g, hg⟩ := exists_smul_eq_orbit_out (G := G) x
      have hmem : (Quotient.mk (orbitRel G α) x).out ∈ X := by rw [← hg]; exact hX g x hx
      refine ⟨⟨Quotient.mk _ x, hmem⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (f (Quotient.mk (orbitRel G α) x).out) = q'
      rw [← Quotient.out_eq q', ← hg, hequiv g x hx, hfx]
      exact Quotient.sound ⟨φ g, rfl⟩
  unfold _root_.GlobalTheory.Mass.orbSum
  rw [← (Equiv.ofBijective F hF).tsum_eq]
  congr 1
  funext q
  obtain ⟨g', hg'⟩ := exists_smul_eq_orbit_out (G := G') (f q.1.out)
  show _ = (ENat.card (stabilizer G' (Quotient.mk (orbitRel G' β) (f q.1.out)).out) : ℝ≥0∞)⁻¹ *
    N (Quotient.mk (orbitRel G' β) (f q.1.out)).out
  rw [← hg', card_stabilizer_smul_eq', hN, hcard _ q.2]

end GlobalTheory.Mass.OrbTransport
end

section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

theorem _root_.GlobalTheory.T.indexMeasureIntegral_eq_mean_over_representatives : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ) (R : Finset W), B ≤ A → (∀ w, ∀ b ∈ B, φ (w + b) = φ w) → (∀ w, w ∉ A → φ w = 0) → (∀ w ∈ R, w ∈ A) → (∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) → Fine A φ B ∧ (R.card : ℕ) = B.relIndex A ∧ cint A φ = (∑ w ∈ R, φ w) / (R.card : ℂ) := by
  first | exact @GlobalTheory.IdxInt.cint_eq_mean_reps | exact GlobalTheory.IdxInt.cint_eq_mean_reps | (intros; apply GlobalTheory.IdxInt.cint_eq_mean_reps <;> assumption)
end

section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

theorem _root_.GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound : ∀ {W : Type} [AddCommGroup W] (A : AddSubgroup W), (∀ φ ψ : W → ℂ, Nice A φ → Nice A ψ → Nice A (φ + ψ) ∧ cint A (φ + ψ) = cint A φ + cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖cint A φ‖ ≤ (cint A ψ).re)) ∧ (∀ (c : ℂ) (φ : W → ℂ), Nice A φ → Nice A (fun w => c * φ w) ∧ cint A (fun w => c * φ w) = c * cint A φ) ∧ (∀ P : W → Prop, 0 ≤ (cint A (ind P)).re ∧ (cint A (ind P)).im = 0) ∧ ∀ (ι : Type) (s : Finset ι) (φ : ι → W → ℂ), (∀ i ∈ s, Nice A (φ i)) → Nice A (fun w => ∑ i ∈ s, φ i w) ∧ cint A (fun w => ∑ i ∈ s, φ i w) = ∑ i ∈ s, cint A (φ i) := by
  first | exact @GlobalTheory.IdxInt.Lin.main | exact GlobalTheory.IdxInt.Lin.main | (intros; apply GlobalTheory.IdxInt.Lin.main <;> assumption)
end
