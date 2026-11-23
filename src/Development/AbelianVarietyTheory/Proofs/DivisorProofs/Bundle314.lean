module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle224
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle238
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle225
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle001
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle226
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open scoped NumberField

theorem _root_.GlobalTheory.T.card_killed_by_ideal_mod_int_eq_absNorm_pow : ∀ (K : Type) [Field K] [NumberField K] (M : Type) [AddCommGroup M] [Module (𝓞 K) M], Module.Free ℤ M → Module.Finite ℤ M → ∀ (r : ℕ), Module.finrank ℤ M = r * Module.finrank ℚ K → ∀ (𝔟 : Ideal (𝓞 K)) (c : ℕ), 0 < c → (c : 𝓞 K) ∈ 𝔟 → Nat.card {x : M ⧸ (Ideal.span {(c : 𝓞 K)} • (⊤ : Submodule (𝓞 K) M)) // ∀ a ∈ 𝔟, a • x = 0} = Ideal.absNorm 𝔟 ^ r := by
  first | (exact @GlobalTheory.TorsQuotCount.card_killed_eq) | (exact GlobalTheory.TorsQuotCount.card_killed_eq) | (intros; apply GlobalTheory.TorsQuotCount.card_killed_eq <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem _root_.GlobalTheory.T.card_divisors_le_absNorm_numberField : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ s : Finset (Ideal (𝓞 F)), (∀ J ∈ s, I ≤ J) → s.card ≤ Ideal.absNorm I := by
  first | exact @GlobalTheory.card_le_absNorm_of_forall_le | exact GlobalTheory.card_le_absNorm_of_forall_le | (intros; apply GlobalTheory.card_le_absNorm_of_forall_le <;> assumption)
end

section

set_option autoImplicit false
open NumberField

namespace GlobalTheory.PicDom

theorem exists_int_mem_span {B : Type} [CommRing B] [IsDomain B] [Algebra.IsIntegral ℤ B] {d : B} (hd : d ≠ 0) :
    ∃ a : ℤ, a ≠ 0 ∧ (a : B) ∈ Ideal.span {d} := by
  have h := Ideal.comap_ne_bot_of_integral_mem hd (Ideal.mem_span_singleton_self d)
    (Algebra.IsIntegral.isIntegral (R := ℤ) d)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨a, ha0, by simpa using ha⟩

theorem isOfFinOrder_of_not_charZero (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (hc : ¬ CharZero B) (M : CommRing.Pic B) : IsOfFinOrder M := by
  have hp : ringChar B ≠ 0 := by
    intro h
    apply hc
    have : CharP B 0 := h ▸ ringChar.charP B
    exact CharP.charP_to_charZero B
  have hfin : Finite B := Module.finite_of_fg_torsion B fun x =>
    ⟨⟨(ringChar B : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, by
      change ((ringChar B : ℤ)) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, ringChar.Nat.cast_ringChar, zero_mul]⟩
  exact isOfFinOrder_of_finite M

variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]

theorem finiteDimensional_of_isFractionRing (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [CharZero K] :
    FiniteDimensional ℚ K := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
  have key : ∀ y : B, algebraMap B K y ∈
      Submodule.span ℚ (algebraMap B K '' (s : Set B)) := fun y => by
    have hy : y ∈ Submodule.span ℤ (s : Set B) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx => rw [map_zsmul]; exact zsmul_mem hx a
  classical
  refine Module.finite_def.2 ⟨s.image (algebraMap B K), ?_⟩
  rw [Finset.coe_image, eq_top_iff]
  intro x _
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨a, ha0, ha⟩ := exists_int_mem_span hd0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
  have hdK : algebraMap B K d ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha0
  have : algebraMap B K b / algebraMap B K d =
      ((a : ℚ)⁻¹) • algebraMap B K (c * b) := by
    rw [Rat.smul_def, map_mul, Rat.cast_inv, Rat.cast_intCast]
    have h2 : (a : K) = algebraMap B K c * algebraMap B K d := by
      rw [← map_mul, hc, map_intCast]
    have hcK : algebraMap B K c ≠ 0 := by
      intro h; apply haK; rw [h2, h, zero_mul]
    rw [h2]
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ (key _)

end GlobalTheory.PicDom

namespace GlobalTheory.PicDom

variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]

theorem isOfFinOrder_of_numberField (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [NumberField K]
    (M : CommRing.Pic B) : IsOfFinOrder M := by
  let φ : B →+* 𝓞 K :=
    { toFun := fun b => ⟨algebraMap B K b, (Algebra.IsIntegral.isIntegral (R := ℤ) b).algebraMap⟩
      map_zero' := by ext; simp only [RingOfIntegers.map_mk, map_zero]
      map_one' := by ext; simp only [RingOfIntegers.map_mk, map_one]
      map_add' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_add (f := _)]; rfl
      map_mul' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_mul]; rfl }
  have hφ : ∀ b, ((φ b : 𝓞 K) : K) = algebraMap B K b := fun b => rfl
  have hinj : Function.Injective φ := fun x y h => IsFractionRing.injective B K (by
    rw [← hφ, ← hφ, h])

  have hmul : ∀ ω : 𝓞 K, ∃ a : ℤ, a ≠ 0 ∧ (a : 𝓞 K) * ω ∈ φ.range := fun ω => by
    obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := B) (ω : K)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    obtain ⟨a, ha0, ha⟩ := exists_int_mem_span hd0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    have hdK : algebraMap B K d ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]
    refine ⟨a, ha0, c * b, ?_⟩
    apply RingOfIntegers.ext
    rw [hφ, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_intCast, ← RingOfIntegers.coe_eq_algebraMap, ← hbd]
    have h2 : (a : K) = algebraMap B K c * algebraMap B K d := by
      rw [← map_mul, hc, map_intCast]
    rw [h2, mul_assoc]
    congr 1
    exact (mul_div_cancel₀ _ hdK).symm
  classical
  choose a ha0 ha using hmul
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℤ) (M := 𝓞 K)
  set N : ℤ := ∏ ω ∈ t, a ω
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun ω _ => ha0 ω
  have hNmem : ∀ x : 𝓞 K, (N : 𝓞 K) * x ∈ φ.range := fun x => by
    have hx : x ∈ Submodule.span ℤ (t : Set (𝓞 K)) := ht ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem ω hω =>
      show ((∏ ω ∈ t, a ω : ℤ) : 𝓞 K) * ω ∈ φ.range
      rw [← Finset.mul_prod_erase t a (Finset.mem_coe.1 hω), Int.cast_mul, mul_comm (a ω : 𝓞 K), mul_assoc]
      exact mul_mem (intCast_mem _ _) (ha ω)
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact zsmul_mem hx k
  have hn0 : N.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hN0
  have hcond : ∀ x : 𝓞 K, ((N.natAbs : ℕ) : 𝓞 K) * x ∈ φ.range := fun x => by
    rcases Int.natAbs_eq N with h | h
    · have := hNmem x
      rwa [h, Int.cast_natCast] at this
    · have := neg_mem (hNmem x)
      rwa [h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this
  haveI : Finite (CommRing.Pic (𝓞 K)) := Finite.of_equiv _ (ClassGroup.equivPic (𝓞 K)).toEquiv
  exact GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B (𝓞 K) φ N.natAbs hinj hn0 hcond M (isOfFinOrder_of_finite _)

theorem isOfFinOrder_of_charZero (M : CommRing.Pic B) : IsOfFinOrder M := by
  haveI : CharZero (FractionRing B) := IsFractionRing.charZero_of_isFractionRing B
  haveI : FiniteDimensional ℚ (FractionRing B) := finiteDimensional_of_isFractionRing B (FractionRing B)
  haveI : NumberField (FractionRing B) := ⟨⟩
  exact isOfFinOrder_of_numberField B (FractionRing B) M

end GlobalTheory.PicDom

theorem GlobalTheory.pic_isOfFinOrder_of_finite_int : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (M : CommRing.Pic B), IsOfFinOrder M := by
  intro B _ _ _ M
  by_cases hc : CharZero B
  · exact GlobalTheory.PicDom.isOfFinOrder_of_charZero B M
  · exact GlobalTheory.PicDom.isOfFinOrder_of_not_charZero B hc M
end

section

open NumberField

theorem _root_.GlobalTheory.T.trace_ringOfIntegers_action_lattice_eq : ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] [Algebra (𝓞 F) O] (La : Type) [AddCommGroup La] [Module O La] [Module.Free ℤ La] [Module.Finite ℤ La] (k : ℕ), Module.finrank ℤ La = k * Module.finrank ℚ F → ∀ c : 𝓞 F, ((LinearMap.trace ℤ La (DistribSMul.toAddMonoidHom La (algebraMap (𝓞 F) O c)).toIntLinearMap : ℤ) : ℂ) = (k : ℂ) * ∑ τ : F →+* ℂ, τ (c : F) := by
  first | exact @GlobalTheory.LatticeTrace.trace_lattice_eq | exact GlobalTheory.LatticeTrace.trace_lattice_eq | (intros; apply GlobalTheory.LatticeTrace.trace_lattice_eq <;> assumption)
end

section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.EmbConj

open GlobalTheory.PadicComplexHost

variable {p : ℕ} [Fact p.Prime]

theorem injective_of_comp {Λ : Type} [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] (φ : Λ →+* PadicAlgCl p)
    (h : φ.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p)) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
  change Ideal.comap (algebraMap ℤ_[p] Λ) (RingHom.ker φ) = ⊥
  rw [RingHom.comap_ker, h, ← RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p), RingHom.coe_comp]
  exact (algebraMap ℚ_[p] (PadicAlgCl p)).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

theorem exists_algEquiv {Λ : Type} [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (φ₀ φ₁ : Λ →+* PadicAlgCl p)
    (h₀ : φ₀.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p))
    (h₁ : φ₁.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p)) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x, σ (φ₀ x) = φ₁ x := by
  have tf : ∀ φ : Λ →+* PadicAlgCl p, Function.Injective φ →
      letI := φ.toAlgebra
      Module.IsTorsionFree Λ (PadicAlgCl p) := fun φ hφ => by
    letI := φ.toAlgebra
    haveI : FaithfulSMul Λ (PadicAlgCl p) := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
    infer_instance
  have alg : letI := φ₀.toAlgebra
      Algebra.IsAlgebraic Λ (PadicAlgCl p) := by
    letI := φ₀.toAlgebra
    haveI : IsScalarTower ℤ_[p] Λ (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq' h₀.symm
    haveI : Algebra.IsAlgebraic ℤ_[p] (PadicAlgCl p) := ⟨fun x =>
      (IsFractionRing.isAlgebraic_iff ℤ_[p] ℚ_[p] (PadicAlgCl p)).2
        (Algebra.IsAlgebraic.isAlgebraic x)⟩
    exact Algebra.IsAlgebraic.extendScalars (R := ℤ_[p]) (FaithfulSMul.algebraMap_injective _ _)
  obtain ⟨g, hg⟩ : ∃ g : PadicAlgCl p →+* PadicAlgCl p, ∀ x, g (φ₀ x) = φ₁ x := by
    let f := @IsAlgClosed.lift (PadicAlgCl p) _ _ Λ _ _ (PadicAlgCl p) _ _ φ₀.toAlgebra
      φ₁.toAlgebra (tf φ₀ (injective_of_comp φ₀ h₀)) (tf φ₁ (injective_of_comp φ₁ h₁)) alg
    exact ⟨@AlgHom.toRingHom _ _ _ _ _ _ φ₀.toAlgebra φ₁.toAlgebra f,
      fun x => @AlgHom.commutes _ _ _ _ _ _ φ₀.toAlgebra φ₁.toAlgebra f x⟩
  have hq : g.comp (algebraMap ℚ_[p] (PadicAlgCl p)) = algebraMap ℚ_[p] (PadicAlgCl p) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    ext a
    exact (congrArg g (RingHom.congr_fun h₀ a).symm).trans
      ((hg _).trans (RingHom.congr_fun h₁ a))
  let g' : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p := { g with commutes' := RingHom.congr_fun hq }
  exact ⟨AlgEquiv.ofBijective g' (Algebra.IsAlgebraic.algHom_bijective g'), hg⟩

end GlobalTheory.EmbConj
end

section

open scoped TensorProduct
open Function

theorem _root_.GlobalTheory.T.exists_localRing_quotients_coprime_iInf_eq_bot : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A], ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal A), (∀ i, IsLocalRing (A ⧸ I i)) ∧ Pairwise (IsCoprime on I) ∧ ⨅ i, I i = ⊥ := by
  first | (exact @GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt) | (exact GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt) | (intros; apply GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt  <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one : ∀ (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (S : Submonoid B), (0 : B) ∉ S → ∀ x y : B, y ≠ 0 →
    (∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → y ∈ Q → Disjoint (S : Set B) (Q : Set B) →
      ∃ t ∉ Q, y ∣ t * x) → ∃ u ∈ S, y ∣ u * x := by
  first | (exact @GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one) | (exact GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one) | (intros; apply GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals : ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C, (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  first | exact @GlobalTheory.iInf_sup_pow_eq_of_compatible | exact GlobalTheory.iInf_sup_pow_eq_of_compatible | (intros; apply GlobalTheory.iInf_sup_pow_eq_of_compatible <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.isAdicComplete_of_le_maximalIdeal' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (I : Ideal R), I ≤ maximalIdeal R → IsAdicComplete I R := by
  first | exact @GlobalTheory.isAdicComplete_of_le_maximalIdeal | exact GlobalTheory.isAdicComplete_of_le_maximalIdeal | (intros; apply GlobalTheory.isAdicComplete_of_le_maximalIdeal <;> assumption)
end

section

open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin.Extend

def filt {σ R : Type} [CommRing R] (I : Ideal R) (k : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {F | ∀ α, MvPowerSeries.coeff α F ∈ I ^ (k - α.degree)}
  add_mem' {F G} hF hG α := by simpa using Ideal.add_mem _ (hF α) (hG α)
  zero_mem' α := by simp
  smul_mem' c F hF α := by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Ideal.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have : p.2.degree ≤ α.degree := by rw [← h, map_add (f := _)]; omega
    exact Ideal.pow_le_pow_right (by omega) (hF p.2)

theorem mem_filt {σ R : Type} [CommRing R] (I : Ideal R) (k : ℕ) (F : MvPowerSeries σ R) :
    F ∈ filt I k ↔ ∀ α, MvPowerSeries.coeff α F ∈ I ^ (k - α.degree) := Iff.rfl

theorem eq_zero_of_forall_mem_filt {σ R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (F : MvPowerSeries σ R) (h : ∀ k, F ∈ filt I k) : F = 0 := by
  ext α
  rw [map_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun m => ?_
  have := h (m + α.degree) α
  rw [Nat.add_sub_cancel] at this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact this

end GlobalTheory.FormalOrigin.Extend
end

section

open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.PowerSeriesComplete

theorem isAdicComplete_map_C : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R))
      (MvPowerSeries (Fin n) R) := by
  intro R _ _ I hI n
  have hfg : I.FG := IsNoetherian.noetherian I
  have hC : (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) = algebraMap R (MvPowerSeries (Fin n) R) := rfl
  have hP : IsPrecomplete I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isPrecomplete_pi (M := R) (Fin n →₀ ℕ) hfg
  have hH : IsHausdorff I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isHausdorff_pi (M := R) (Fin n →₀ ℕ) hfg
  rw [hC]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 hH
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 hP }

end GlobalTheory.PowerSeriesComplete
end

section


theorem _root_.GlobalTheory.T.adicCompletion_map_injective_and_invariants : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by
  first | exact @GlobalTheory.adicCompletion_map_invariants | exact GlobalTheory.adicCompletion_map_invariants | (intros; apply GlobalTheory.adicCompletion_map_invariants <;> assumption)
end
