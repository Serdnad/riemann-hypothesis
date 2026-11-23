module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Tactic.Continuity
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure CotInd (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) : Prop where
  mem : ∀ k, x k ∈ maximalIdeal R
  indep : ∀ a : κ → R, ∑ k, a k * x k ∈ maximalIdeal R ^ 2 → ∀ k, a k ∈ maximalIdeal R

theorem cotInd_iff (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) :
    CotInd R x ↔ ∃ h : ∀ k, x k ∈ maximalIdeal R,
      LinearIndependent (ResidueField R)
        (fun k => ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)) := by
  have key : ∀ (h : ∀ k, x k ∈ maximalIdeal R) (a : κ → R),
      (∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R) = 0) ↔
        ∑ k, a k * x k ∈ maximalIdeal R ^ 2 := by
    intro h a
    have h1 : ∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)
        = (maximalIdeal R).toCotangent (∑ k, a k • (⟨x k, h k⟩ : maximalIdeal R)) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      exact algebraMap_smul (ResidueField R) (a k) _
    rw [h1, Ideal.toCotangent_eq_zero]
    simp
  constructor
  · rintro ⟨h, hi⟩
    refine ⟨h, Fintype.linearIndependent_iff.2 fun g hg k => ?_⟩
    choose a ha using fun k => residue_surjective (g k)
    rw [← ha k, residue_eq_zero_iff]
    refine hi a ((key h a).1 ?_) k
    simpa [ha] using hg
  · rintro ⟨h, hi⟩
    refine ⟨h, fun a ha k => ?_⟩
    have := Fintype.linearIndependent_iff.1 hi (fun k => residue R (a k)) ((key h a).2 ha) k
    exact (residue_eq_zero_iff _).1 this

theorem CotInd.comp {R : Type} [CommRing R] [IsLocalRing R] {κ ι : Type} [Fintype κ] [Fintype ι]
    {x : κ → R} (h : CotInd R x) (e : ι → κ) (he : Function.Injective e) : CotInd R (x ∘ e) := by
  obtain ⟨h1, h2⟩ := (cotInd_iff R x).1 h
  exact (cotInd_iff R _).2 ⟨fun i => h1 (e i), h2.comp e he⟩

end UpperTheory.V.AlgebraTools
end

section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.supportDim_le_of_finite :
    ∀ (L B : Type) [CommRing L] [IsNoetherianRing L] [CommRing B] [Algebra L B] (N : Type) [AddCommGroup N] [Module B N]
      [Module L N] [IsScalarTower L B N] [Module.Finite L N], Module.supportDim B N ≤ ringKrullDim L := by
  intro L B _ _ _ _ N _ _ _ _ _
  have hfin : Module.Finite B N := Module.Finite.of_restrictScalars_finite L B N
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  let f : B →ₐ[L] Module.End L N := Algebra.lsmul L L N
  have hf : ∀ b : B, b ∈ Module.annihilator B N → f b = 0 := by
    intro b hb
    ext n
    exact Module.mem_annihilator.mp hb n
  let g : (B ⧸ Module.annihilator B N) →ₐ[L] Module.End L N :=
    Ideal.Quotient.liftₐ (Module.annihilator B N) f hf
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).mpr ?_
    intro q hq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine Module.mem_annihilator.mpr (fun n => ?_)
    have h := LinearMap.congr_fun hq n
    exact h
  haveI : Algebra.IsIntegral L (B ⧸ Module.annihilator B N) :=
    ⟨fun q => (isIntegral_algHom_iff g hinj).mp (Algebra.IsIntegral.isIntegral _)⟩
  exact Order.krullDim_le_of_strictMono
    (fun P => (⟨Ideal.comap (algebraMap L (B ⧸ Module.annihilator B N)) P.asIdeal, inferInstance⟩ :
      PrimeSpectrum L))
    (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)
end

section

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field {A X : Type} [CommRing A] [IsLocalRing A] [AddCommGroup X] [Module A X] [IsSimpleModule A X] : Nonempty (X ≃ ResidueField A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A X)
  have : I = maximalIdeal A := IsLocalRing.eq_maximalIdeal hI
  subst this
  exact ⟨e.toEquiv⟩

private theorem UpperTheory.V.AlgebraTools.card_finite_length_module {A : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] {X : Type} [AddCommGroup X] [Module A X] (h : IsFiniteLength A X) :
    Finite X ∧ Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨Finite.of_subsingleton, ?_⟩
    rw [Module.length_eq_zero]
    simp [Nat.card_eq_one_iff_unique]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨hfin, hcard⟩ := ih
    obtain ⟨e⟩ := UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field (A := A) (X := M ⧸ N)
    have hq : Nat.card (M ⧸ N) = Nat.card (ResidueField A) := Nat.card_congr e
    have hNt : Module.length A N ≠ ⊤ := Module.length_ne_top_iff.mpr hN
    have hlen : Module.length A M = Module.length A N + 1 := by
      rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), Module.length_eq_one A (M ⧸ N)]
    have hc : Nat.card M = Nat.card (M ⧸ N) * Nat.card N :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
    have hq0 : Nat.card (ResidueField A) ≠ 0 := Nat.card_pos.ne'
    have hM : Nat.card M = Nat.card (ResidueField A) ^ ((Module.length A N).toNat + 1) := by
      rw [hc, hq, hcard, pow_succ, mul_comm]
    refine ⟨Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ hq0), ?_⟩
    rw [hM, hlen, ENat.toNat_add hNt ENat.one_ne_top]
    simp

theorem UpperTheory.V.AlgebraTools.card_eq_pow_length :
    ∀ {A X : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] [AddCommGroup X] [Module A X], (Finite X ↔ Module.length A X ≠ ⊤) ∧ (Finite X → Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat) := by
  intro A X _ _ _ _ _
  have key : Finite X → Module.length A X ≠ ⊤ := fun h => by
    haveI := h
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, isArtinian_of_finite⟩)
  refine ⟨⟨key, fun h => (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp h)).1⟩, fun h => ?_⟩
  exact (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp (key h))).2
end

section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.mem_support_baseChange :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
      (Q : PrimeSpectrum B), Q ∈ Module.support B (TensorProduct R B M) ↔
        PrimeSpectrum.comap (algebraMap R B) Q ∈ Module.support R M := by
  intro R B _ _ _ M _ _ _ Q
  let p := PrimeSpectrum.comap (algebraMap R B) Q
  let φ := Ideal.ResidueField.mapₐ p.asIdeal Q.asIdeal (Algebra.ofId R B) rfl
  letI : Algebra p.asIdeal.ResidueField Q.asIdeal.ResidueField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField Q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B Q.asIdeal.ResidueField
      Q.asIdeal.ResidueField M).nontrivial_congr,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField
      Q.asIdeal.ResidueField Q.asIdeal.ResidueField M).nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right _ _
end

section

open IsLocalRing

private theorem UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero {K : Type} [Field K] (V : ValuationSubring K)
    {ι : Type} [Fintype ι] [Nonempty ι] (w : ι → K) (hw : w ≠ 0) :
    ∃ c, w c ≠ 0 ∧ ∀ j, w j / w c ∈ V := by
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun j => V.valuation (w j))
    Finset.univ_nonempty
  have hwc : w c ≠ 0 := by
    intro h0
    apply hw
    funext j
    have hj := hc j (Finset.mem_univ j)
    rw [h0, map_zero] at hj
    exact (Valuation.zero_iff _).mp (le_antisymm hj zero_le')
  refine ⟨c, hwc, fun j => ?_⟩
  rw [← V.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hc j (Finset.mem_univ j)) zero_le'

theorem UpperTheory.V.AlgebraTools.exists_kernel_vector :
    ∀ (K : Type) [Field K] (V : ValuationSubring K) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (z : Matrix ι ι K) (m : ι → K), z.mulVec m = 0 → z.det = 0 →
      ∃ (c : ι) (l : ι → K), l c = 1 ∧ (∀ j, l j ∈ V) ∧ z.mulVec l = 0 ∧ ∀ j, m j = l j * m c := by
  intro K _ V ι _ _ _ z m hm hdet
  have key : ∀ w : ι → K, z.mulVec w = 0 → ∀ c, w c ≠ 0 →
      z.mulVec (fun j => w j / w c) = 0 := by
    intro w hw c _
    have e : (fun j => w j / w c) = (w c)⁻¹ • w := by
      funext j
      simp [div_eq_inv_mul]
    rw [e, Matrix.mulVec_smul, hw, smul_zero]
  by_cases h0 : m = 0
  · obtain ⟨w, hw, hzw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    obtain ⟨c, hc, hV⟩ := UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero V w hw
    exact ⟨c, fun j => w j / w c, div_self hc, hV, key w hzw c hc, fun j => by simp [h0]⟩
  · obtain ⟨c, hc, hV⟩ := UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero V m h0
    exact ⟨c, fun j => m j / m c, div_self hc, hV, key m hm c hc,
      fun j => (div_mul_cancel₀ _ hc).symm⟩
end
