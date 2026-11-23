module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open Matrix NumberField IsDedekindDomain

noncomputable section

namespace PI.SelfDualLoc.W

open PI.SelfDualLoc

def hvec {E : Type} [Field E] {n m : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) : (Fin n → E) →ₗ[E] (Fin m → E) where
  toFun y := fun i => hform σ J (x i) y
  map_add' y y' := by ext i; simp [hform_add_right]
  map_smul' c y := by ext i; simp [hform_smul_right]

theorem hvec_apply {E : Type} [Field E] {n m : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (y : Fin n → E) (i : Fin m) :
    hvec σ J x y i = hform σ J (x i) y := rfl

theorem spanTop_of (hN : Nondeg) : SpanTop := by
  intro F E _ _ _ _ _ n σ J Lb T hfin hdual hT
  by_contra hne
  have hlt : Module.finrank E (Submodule.span E (Lb : Set (Fin n → E))) < n := by
    have h := Submodule.finrank_lt hne
    rwa [Module.finrank_fin_fun] at h
  let b := Module.finBasis E (Submodule.span E (Lb : Set (Fin n → E)))
  let x : Fin (Module.finrank E (Submodule.span E (Lb : Set (Fin n → E)))) → Fin n → E :=
    fun i => (b i : Fin n → E)
  have hker : LinearMap.ker (hvec (σ : E →+* E) J x) ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker (hvec (σ : E →+* E) J x)
    rw [hbot, finrank_bot, add_zero, Module.finrank_fin_fun] at h1
    have h2 := Submodule.finrank_le (LinearMap.range (hvec (σ : E →+* E) J x))
    rw [Module.finrank_fin_fun] at h2
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  apply hy0
  refine hN F E n σ J Lb T hfin hdual hT y fun z hz => ?_
  have hzV : z ∈ Submodule.span E (Lb : Set (Fin n → E)) := Submodule.subset_span hz
  have hz' : z = ∑ i, (b.repr ⟨z, hzV⟩ i) • x i := by
    have h := congrArg Subtype.val (b.sum_repr ⟨z, hzV⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm
  rw [hz', hform_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hform_smul_left]
  have hi : hform (σ : E →+* E) J (x i) y = 0 := by
    rw [← hvec_apply]
    exact congrFun (LinearMap.mem_ker.mp hy) i
  rw [hi, mul_zero]

theorem dualBasis : DualBasis := by
  intro F E _ _ _ _ _ n σ J x _ hnd
  have hinj : Function.Injective (hvec (σ : E →+* E) J x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hnd y fun i => by rw [← hvec_apply, hy]; rfl
  let e := LinearEquiv.ofInjectiveEndo (hvec (σ : E →+* E) J x) hinj
  have he : ∀ v, e v = hvec (σ : E →+* E) J x v := fun v => rfl
  refine ⟨fun j => e.symm (Pi.single j 1), fun i j => ?_, fun w => ⟨fun j => e w j, ?_⟩⟩
  · rw [← hvec_apply, ← he, LinearEquiv.apply_symm_apply, Pi.single_apply]
  · apply e.injective

    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]

end PI.SelfDualLoc.W
end
end

section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

noncomputable section

namespace PI.SelfDualLoc.W.ND

open PI.SelfDualLoc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

lemma mem_intOE_iff (x : E) : x ∈ intOE E ↔ ∃ a : 𝓞 E, (a : E) = x := by
  unfold intOE
  exact RingHom.mem_range

lemma coe_mem_intOE (a : 𝓞 E) : (a : E) ∈ intOE E :=
  (mem_intOE_iff _).2 ⟨a, rfl⟩

lemma exists_den (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ z ∈ L, ∀ j, (d : E) * z j ∈ intOE E := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 E)⁰
    (S.biUnion fun s => Finset.univ.image fun j => s j)
  refine ⟨(b : 𝓞 E), nonZeroDivisors.ne_zero b.2, ?_⟩
  have hgen : ∀ s ∈ S, ∀ j, ((b : 𝓞 E) : E) * s j ∈ intOE E := by
    intro s hs j
    obtain ⟨a, ha⟩ := hb (s j)
      (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
    refine (mem_intOE_iff _).2 ⟨a, ?_⟩
    rw [show ((b : 𝓞 E) : E) * s j = b • s j from by rw [Submonoid.smul_def, Algebra.smul_def]]
    exact ha
  intro z hz
  rw [← hS] at hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero =>
    intro j
    simp only [Pi.zero_apply, mul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro j
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx j) (hy j)
  | smul a x _ hx =>
    intro j
    have e : ((b : 𝓞 E) : E) * (a • x) j = (a : E) * (((b : 𝓞 E) : E) * x j) := by
      change ((b : 𝓞 E) : E) * ((a : E) * x j) = _
      ring
    rw [e]
    exact mul_mem (coe_mem_intOE a) (hx j)

lemma exists_not_mem_intOE : ∃ t : E, t ∉ intOE E := by
  refine ⟨(2 : E)⁻¹, fun h => ?_⟩
  obtain ⟨a, ha⟩ := (mem_intOE_iff _).1 h
  have h1 : IsIntegral ℤ ((2 : E)⁻¹) := ha ▸ RingOfIntegers.isIntegral_coe a
  have h2 : algebraMap ℚ E ((2 : ℚ)⁻¹) = (2 : E)⁻¹ := by simp
  rw [← h2] at h1
  have h3 : IsIntegral ℤ ((2 : ℚ)⁻¹) := (isIntegral_algebraMap_iff ).1 h1
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have h4 : (2 : ℚ) * (z : ℚ) = 1 := by
    rw [show (z : ℚ) = (2 : ℚ)⁻¹ by simpa using hz]
    norm_num
  have h5 : (2 : ℤ) * z = 1 := by exact_mod_cast h4
  omega

lemma hform_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end PI.SelfDualLoc.W.ND

namespace PI.SelfDualLoc.W

open PI.SelfDualLoc ND

theorem nondeg : Nondeg := by
  intro F E _ _ _ _ _ n σ J Lb T hfin hT hT0 y hy
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨d, hd0, hd⟩ := exists_den Lb (Module.Finite.iff_fg.1 hfin)
  obtain ⟨t, ht⟩ := exists_not_mem_intOE (E := E)
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hT' : (T : E) ≠ 0 := by exact_mod_cast hT0
  have hmem : (T : E) • ((t / ((d : E) * (T : E) * y j)) • y) ∈ Lb := by
    apply hT
    intro x hx
    rw [hform_smul_right, hy x hx, mul_zero]
    exact zero_mem _
  have := hd _ hmem j
  apply ht
  convert this using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end PI.SelfDualLoc.W
end
end

section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.SelfDualLoc.W

theorem selfDualLoc_of_dirs (hF : FwdDir) (hB : BwdDir) : PI.SelfDualLoc := by
  intro F E _ _ _ _ _ n σ J v Lb T hfin hint hdual hT y
  exact ⟨fun hy z hz => hF F E n σ J v Lb hint y hy z hz,
    fun h => hB F E n σ J v Lb T hfin hint hdual hT y h⟩

end PI.SelfDualLoc.W
end
end
