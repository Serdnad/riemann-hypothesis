module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
public import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

theorem exists_mul_mem_tens (E : Place (algebraMap ℂ K)) (w : K ⊗[ℂ] κ') :
    ∃ d ∈ E.ring, d ≠ 0 ∧ (d ⊗ₜ[ℂ] (1 : κ')) * w ∈ tens (κ' := κ') (placeAlg E) := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, one_ne_zero, by simpa using zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := E.ring) x
    have hb0 : (b : K) ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
    have he : x * (b : K) = (a : K) := by
      rw [← e]
      exact div_mul_cancel₀ _ hb0
    refine ⟨b, b.2, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, he]
    exact tmul_mem a.2 y
  | add u v hu hv =>
    obtain ⟨d₁, hd₁, hd₁0, h₁⟩ := hu
    obtain ⟨d₂, hd₂, hd₂0, h₂⟩ := hv
    refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, mul_ne_zero hd₁0 hd₂0, ?_⟩
    have e : ((d₁ * d₂) ⊗ₜ[ℂ] (1 : κ')) * (u + v) =
        (d₂ ⊗ₜ[ℂ] (1 : κ')) * ((d₁ ⊗ₜ[ℂ] (1 : κ')) * u) +
          (d₁ ⊗ₜ[ℂ] (1 : κ')) * ((d₂ ⊗ₜ[ℂ] (1 : κ')) * v) := by
      rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm d₂ d₁, mul_add]
    rw [e]
    exact add_mem (mul_mem (tmul_mem hd₂ 1) h₁) (mul_mem (tmul_mem hd₁ 1) h₂)

theorem isLocModel_locAt : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ E 𝔭 _ hO
  obtain ⟨O', hO'⟩ := hO
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ L
  have hc : ∀ a : ℂ, algebraMap ℂ L a ∈ locAt (L := L) 𝔭 := fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L]
    exact (toQ (L := L) 𝔭 (algebraMap ℂ (tens (κ' := κ') (placeAlg E)) a)).2
  refine
    { const_mem := hc
      isLocalRing := isLocalRing_locAt 𝔭 hinj
      essFiniteType := ?_
      frac := ?_ }
  · have e : (algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc =
        (toQ (L := L) 𝔭).comp (algebraMap ℂ (tens (κ' := κ') (placeAlg E))) := by
      ext a
      simp only [RingHom.codRestrict_apply, RingHom.comp_apply, coe_toQ]
      exact IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L a
    rw [e]

    letI : Algebra ℂ O' := ((algebraMap ℂ κ').codRestrict O' hO'.const_mem).toAlgebra
    haveI : IsScalarTower ℂ O' κ' := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.EssFiniteType ℂ O' := hO'.essFiniteType
    haveI : IsFractionRing O' κ' := IsFractionRing.of_field O' κ' fun f => by
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hO'.frac f
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩
    haveI : Algebra.EssFiniteType O' κ' :=
      Algebra.EssFiniteType.of_isLocalization κ' (nonZeroDivisors O')
    haveI : Algebra.EssFiniteType ℂ κ' := Algebra.EssFiniteType.comp ℂ O' κ'

    haveI : Algebra.EssFiniteType ℂ (placeAlg E) := by
      let φ : E.ring →+* placeAlg E :=
        { toFun := fun x => ⟨x.1, x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hφ : φ.FiniteType := RingHom.FiniteType.of_surjective φ fun y => ⟨⟨y.1, y.2⟩, rfl⟩
      have e : φ.comp ((algebraMap ℂ K).codRestrict E.ring E.const_mem) =
          algebraMap ℂ (placeAlg E) := RingHom.ext fun _ => rfl
      have h := RingHom.EssFiniteType.comp E.essFiniteType hφ.essFiniteType
      rw [e] at h
      exact RingHom.essFiniteType_algebraMap.1 h
    haveI : Algebra.EssFiniteType (placeAlg E) (placeAlg E ⊗[ℂ] κ') :=
      Algebra.EssFiniteType.baseChange ℂ κ' (placeAlg E)
    haveI : Algebra.EssFiniteType ℂ (placeAlg E ⊗[ℂ] κ') :=
      Algebra.EssFiniteType.comp ℂ (placeAlg E) (placeAlg E ⊗[ℂ] κ')
    haveI : Algebra.EssFiniteType ℂ (tens (κ' := κ') (placeAlg E)) :=
      Algebra.EssFiniteType.of_surjective (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom
        (tensEquiv (κ' := κ') (placeAlg E)).surjective
    have h1 : (algebraMap ℂ (tens (κ' := κ') (placeAlg E))).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.2 inferInstance

    letI : Algebra (tens (κ' := κ') (placeAlg E)) (locAt (L := L) 𝔭) := (toQ (L := L) 𝔭).toAlgebra
    haveI : IsLocalization 𝔭.primeCompl (locAt (L := L) 𝔭) :=
      { map_units := fun s => isUnit_toQ 𝔭 hinj s.2
        surj := fun x => by
          obtain ⟨a, s, hs, hx⟩ := exists_mul_toQ 𝔭 x
          exact ⟨(a, ⟨s, hs⟩), hx⟩
        exists_of_eq := fun {x y} h => ⟨1, by
          simp only [OneMemClass.coe_one, one_mul]
          exact Subtype.ext (hinj (congrArg Subtype.val h))⟩ }
    haveI : Algebra.EssFiniteType (tens (κ' := κ') (placeAlg E)) (locAt (L := L) 𝔭) :=
      Algebra.EssFiniteType.of_isLocalization (locAt (L := L) 𝔭) 𝔭.primeCompl
    have h2 : (toQ (L := L) 𝔭).EssFiniteType := RingHom.essFiniteType_algebraMap.2 this
    exact RingHom.EssFiniteType.comp h1 h2
  · intro f
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') f
    have hv0 : algebraMap (K ⊗[ℂ] κ') L v ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hv
    obtain ⟨d₁, hd₁, hd₁0, h₁⟩ := exists_mul_mem_tens (κ' := κ') E u
    obtain ⟨d₂, hd₂, hd₂0, h₂⟩ := exists_mul_mem_tens (κ' := κ') E v
    set D : K ⊗[ℂ] κ' := (d₁ * d₂) ⊗ₜ[ℂ] (1 : κ') with hD
    have hD1 : D = (d₂ ⊗ₜ[ℂ] (1 : κ')) * (d₁ ⊗ₜ[ℂ] (1 : κ')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm d₂ d₁]
    have hD2 : D = (d₁ ⊗ₜ[ℂ] (1 : κ')) * (d₂ ⊗ₜ[ℂ] (1 : κ')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hu : D * u ∈ tens (κ' := κ') (placeAlg E) := by
      rw [hD1, mul_assoc]; exact mul_mem (tmul_mem hd₂ 1) h₁
    have hv' : D * v ∈ tens (κ' := κ') (placeAlg E) := by
      rw [hD2, mul_assoc]; exact mul_mem (tmul_mem hd₁ 1) h₂
    have hDu : IsUnit D := by
      refine IsUnit.of_mul_eq_one ((d₁ * d₂)⁻¹ ⊗ₜ[ℂ] (1 : κ')) ?_
      rw [hD, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        mul_inv_cancel₀ (mul_ne_zero hd₁0 hd₂0)]
      rfl
    have hD0 : algebraMap (K ⊗[ℂ] κ') L D ≠ 0 := (hDu.map _).ne_zero
    refine ⟨_, (toQ (L := L) 𝔭 ⟨D * u, hu⟩).2, _, (toQ (L := L) 𝔭 ⟨D * v, hv'⟩).2, ?_, ?_⟩
    · show algebraMap (K ⊗[ℂ] κ') L (D * v) ≠ 0
      rw [map_mul]; exact mul_ne_zero hD0 hv0
    · show _ * algebraMap (K ⊗[ℂ] κ') L (D * v) = algebraMap (K ⊗[ℂ] κ') L (D * u)
      rw [map_mul, map_mul]
      field_simp

end GlobalTheory.GraphLocal
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

theorem ne_zero_of_ord_pos {K : Type} [Field K] [Algebra ℂ K] (E : Place (algebraMap ℂ K)) {e : K}
    (he : 0 < E.ord e) : e ≠ 0 := by
  rintro rfl
  simp [Place.ord] at he

theorem graphIdeal_ne_top_of_hom {K κ κ' F : Type} [Field K] [Field κ] [Field κ'] [Field F]
    [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (h1 : ∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a)
    (h2 : ∀ a, algebraMap ℂ K a ∈ R) (h4 : E.Contains R)
    (α : E.ring →+* F) (β : κ' →+* F) (hα : ∀ r : R, α ⟨r, h4 _ r.2⟩ = β (ρ (π r)))
    (hpos : ∀ x : E.ring, 0 < E.ord (x : K) → α x = 0) :
    graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  letI : Algebra ℂ F := (β.comp (algebraMap ℂ κ')).toAlgebra
  let j : placeAlg E →+* E.ring :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let α' : placeAlg E →ₐ[ℂ] F :=
    { α.comp j with
      commutes' := fun a => by
        have := hα ⟨algebraMap ℂ K a, h2 a⟩
        rw [h1, ρ.commutes] at this
        exact this }
  let β' : κ' →ₐ[ℂ] F := { β with commutes' := fun _ => rfl }
  let Φ := Algebra.TensorProduct.lift α' β' (fun _ _ => Commute.all _ _)
  let Ψ : tens (κ' := κ') (placeAlg E) →+* F :=
    (Φ.comp (tensEquiv (κ' := κ') (placeAlg E)).symm.toAlgHom).toRingHom
  have hΨ : ∀ w, Ψ (tensEquiv (placeAlg E) w) = Φ w := fun w => by
    simp [Ψ]
  intro htop
  have hle : graphIdeal (κ' := κ') E R π ρ ≤ RingHom.ker Ψ := by
    rw [graphIdeal, Ideal.span_le]
    rintro b (⟨e, he, hb⟩ | ⟨a, hb⟩)
    · have hmem : e ∈ E.ring := (E.ord_nonneg_iff (ne_zero_of_ord_pos E he)).1 he.le
      have hb' : b = tensEquiv (κ' := κ') (placeAlg E) (⟨e, hmem⟩ ⊗ₜ 1) :=
        Subtype.ext (by rw [hb]; rfl)
      rw [SetLike.mem_coe, RingHom.mem_ker, hb', hΨ]
      simp only [Φ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact hpos ⟨e, hmem⟩ he
    · have hb' : b = tensEquiv (κ' := κ') (placeAlg E)
          (⟨a, h4 _ a.2⟩ ⊗ₜ 1 - 1 ⊗ₜ ρ (π a)) :=
        Subtype.ext (by rw [hb, coe_tensEquiv, map_sub]; rfl)
      rw [SetLike.mem_coe, RingHom.mem_ker, hb', hΨ]
      simp only [Φ, map_sub, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul]
      rw [sub_eq_zero]
      exact hα a
  have h1mem : (1 : tens (κ' := κ') (placeAlg E)) ∈ graphIdeal (κ' := κ') E R π ρ :=
    htop ▸ Submodule.mem_top
  exact one_ne_zero ((RingHom.mem_ker).1 (hle h1mem) |>.symm.trans (map_one Ψ)).symm

end GlobalTheory.GraphLocal

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

theorem graphIdeal_ne_top : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K)),
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  intro K κ κ' _ _ _ _ _ _ R π ρ E h1 h2 h3 h4 h5
  let kE := IsLocalRing.ResidueField E.ring
  let inc : R →+* E.ring := R.subtype.codRestrict E.ring (fun r => h4 _ r.2)
  let g : R →+* kE := (IsLocalRing.residue E.ring).comp inc
  have hnu : ∀ x : E.ring, (x : K) ≠ 0 →
      (0 < E.ord x ↔ x ∈ IsLocalRing.maximalIdeal E.ring) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hpos hu
      have := E.ord_eq_zero hu
      omega
    · intro hnu'
      have h0 : 0 ≤ E.ord x := (E.ord_nonneg_iff hx).2 x.2
      rcases h0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hnu'
        have hinv : (x : K)⁻¹ ∈ E.ring :=
          (E.ord_nonneg_iff (inv_ne_zero hx)).1 (by rw [E.ord_inv, ← h]; simp)
        exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hx))
  have hker : ∀ r : R, π r = 0 ↔ g r = 0 := by
    intro r
    by_cases hr : (r : K) = 0
    · have : r = 0 := Subtype.ext hr
      subst this
      simp
    · rw [h5 r hr, show g r = IsLocalRing.residue E.ring (inc r) from rfl,
        IsLocalRing.residue_eq_zero_iff]
      exact hnu (inc r) hr
  have hsurj : Function.Surjective π.rangeRestrict := π.rangeRestrict_surjective
  let φ₀ : π.range →+* kE := π.rangeRestrict.liftOfSurjective hsurj
    ⟨g, fun r hr => by
      rw [RingHom.mem_ker] at hr ⊢
      exact (hker r).1 (congrArg Subtype.val hr)⟩
  have hφ₀ : ∀ r, φ₀ (π.rangeRestrict r) = g r := fun r =>
    RingHom.liftOfSurjective_comp_apply _ hsurj _ r
  have hinj : Function.Injective φ₀ := (injective_iff_map_eq_zero φ₀).2 fun s hs => by
    obtain ⟨r, rfl⟩ := hsurj s
    rw [hφ₀] at hs
    exact Subtype.ext ((hker r).2 hs)
  haveI : IsFractionRing π.range κ := IsFractionRing.of_field π.range κ fun z => by
    obtain ⟨a, b, hb, e⟩ := h3 z
    refine ⟨π.rangeRestrict a, π.rangeRestrict b, ?_⟩
    show z = π a / π b
    rw [eq_div_iff hb, e]
  let ι : κ →+* kE := IsFractionRing.lift hinj
  have hι : ∀ r, ι (π r) = g r := fun r => by
    rw [← hφ₀]
    exact IsFractionRing.lift_algebraMap hinj (π.rangeRestrict r)
  letI : Algebra κ kE := ι.toAlgebra
  letI : Algebra κ κ' := ρ.toRingHom.toAlgebra
  haveI : Nontrivial (kE ⊗[κ] κ') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain κ kE κ'
      ι.injective ρ.toRingHom.injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (kE ⊗[κ] κ')
  letI : Field (kE ⊗[κ] κ' ⧸ M) := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  let α : E.ring →+* (kE ⊗[κ] κ' ⧸ M) :=
    q.comp (Algebra.TensorProduct.includeLeftRingHom.comp (IsLocalRing.residue E.ring))
  let β : κ' →+* (kE ⊗[κ] κ' ⧸ M) :=
    q.comp (Algebra.TensorProduct.includeRight (R := κ) (A := kE)).toRingHom
  refine graphIdeal_ne_top_of_hom R π ρ E h1 h2 h4 α β (fun r => ?_) (fun x hx => ?_)
  · show q (IsLocalRing.residue E.ring (inc r) ⊗ₜ 1) = q (1 ⊗ₜ ρ (π r))
    congr 1
    rw [show IsLocalRing.residue E.ring (inc r) = g r from rfl, ← hι,
      show ι (π r) = π r • (1 : kE) by rw [Algebra.smul_def, mul_one]; rfl,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  · show q (IsLocalRing.residue E.ring x ⊗ₜ 1) = 0
    rw [(IsLocalRing.residue_eq_zero_iff x).2 ((hnu x (ne_zero_of_ord_pos E hx)).1 hx),
      TensorProduct.zero_tmul, map_zero]

end GlobalTheory.GraphLocal
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

theorem exists_isUnit_mul_zpow_tmul :
    ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  Function.Injective (algebraMap (K ⊗[ℂ] κ') L) → Irreducible t →
  ∀ g : K, g ≠ 0 → ∃ q : locAt (L := L) 𝔭, IsUnit q ∧
    algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.ord g := by
  intro K κ' L _ _ _ _ _ _ E 𝔭 _ t _ ht g hg
  set n := E.ord g
  have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  set u : K := g * (t : K) ^ (-n) with hu_def
  have hu0 : u ≠ 0 := mul_ne_zero hg (zpow_ne_zero _ ht0)
  have hord : E.ord u = 0 := by
    rw [hu_def, E.ord_mul hg (zpow_ne_zero _ ht0), E.ord_zpow, E.ord_irreducible ht]
    ring
  have hu : u ∈ E.ring := (E.ord_nonneg_iff hu0).1 hord.ge
  have hui : u⁻¹ ∈ E.ring := (E.ord_nonneg_iff (inv_ne_zero hu0)).1 (by rw [E.ord_inv, hord]; simp)
  let b : tens (κ' := κ') (placeAlg E) := ⟨u ⊗ₜ 1, tmul_mem (mem_placeAlg.2 hu) 1⟩
  let b' : tens (κ' := κ') (placeAlg E) := ⟨u⁻¹ ⊗ₜ 1, tmul_mem (mem_placeAlg.2 hui) 1⟩
  have hbb : b * b' = 1 := by
    apply Subtype.ext
    change (u ⊗ₜ[ℂ] (1 : κ')) * (u⁻¹ ⊗ₜ 1) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hu0, one_mul]
    rfl
  refine ⟨toQ (L := L) 𝔭 b, (IsUnit.of_mul_eq_one (b := b') hbb).map _, ?_⟩
  let φ : K →+* L := (algebraMap (K ⊗[ℂ] κ') L).comp Algebra.TensorProduct.includeLeftRingHom
  have hφ (x : K) : φ x = algebraMap (K ⊗[ℂ] κ') L (x ⊗ₜ 1) := rfl
  have hg' : g = u * (t : K) ^ n := by
    rw [hu_def, mul_assoc, ← zpow_add₀ ht0, neg_add_cancel, zpow_zero, mul_one]
  rw [coe_toQ, ← hφ, ← hφ, ← hφ, ← map_zpow₀, ← map_mul, ← hg']

end GlobalTheory.GraphLocal
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

namespace GlobalTheory.GraphLocal

theorem sum_notMem_of_ne_zero : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  graphIdeal E R π ρ ≤ 𝔭 → E.Contains R →
  ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i → ∑ i, ρ (π (a i)) * b i ≠ 0 → w ∉ 𝔭 := by
  intro K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ hle hR l a b w hw hc
  let g : Fin l → tens (κ' := κ') (placeAlg E) := fun i =>
    ⟨(a i : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π (a i)),
      sub_mem (tmul_mem (hR _ (a i).2) 1) (tmul_mem (one_mem (placeAlg E)) _)⟩
  let bb : Fin l → tens (κ' := κ') (placeAlg E) := fun i =>
    ⟨1 ⊗ₜ b i, tmul_mem (one_mem (placeAlg E)) _⟩
  let u : tens (κ' := κ') (placeAlg E) :=
    ⟨1 ⊗ₜ (∑ i, ρ (π (a i)) * b i), tmul_mem (one_mem (placeAlg E)) _⟩
  let v : tens (κ' := κ') (placeAlg E) :=
    ⟨1 ⊗ₜ (∑ i, ρ (π (a i)) * b i)⁻¹, tmul_mem (one_mem (placeAlg E)) _⟩
  have hg : ∀ i, g i ∈ graphIdeal E R π ρ := fun i => Ideal.subset_span (Or.inr ⟨a i, rfl⟩)
  have hsum : w - u = ∑ i, g i * bb i := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, hw, AddSubmonoidClass.coe_finsetSum]
    simp only [g, bb, u, Subalgebra.coe_mul, sub_mul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, Finset.sum_sub_distrib, TensorProduct.tmul_sum]
  have huv : u * v = 1 := by
    apply Subtype.ext
    simp only [u, v, Subalgebra.coe_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_inv_cancel₀ hc, Subalgebra.coe_one, Algebra.TensorProduct.one_def]
  have hu : u ∉ 𝔭 := fun h => one_notMem 𝔭 (huv ▸ 𝔭.mul_mem_right v h)
  intro hwp
  have hd : w - u ∈ 𝔭 :=
    hle (hsum ▸ Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hg i))
  exact hu (by simpa using 𝔭.sub_mem hwp hd)

end GlobalTheory.GraphLocal
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

noncomputable section

namespace GlobalTheory.DblScal

namespace SplitSurj

theorem dbl_incM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) : dbl (incM F J) = incM F (dbl J) := by
  ext (i | i) (j | j) <;> simp [dbl, incM]

theorem dbl_skew {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i j, σ (J j i) = -J i j) :
    ∀ i j, σ (dbl J j i) = -dbl J i j := by
  rintro (i | i) (j | j) <;> simp [dbl, hJ]

theorem isUnit_det_dbl_map {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    (t : E →ₐ[F] K) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (hJ : J.det ≠ 0) : IsUnit ((dbl J).map t).det := by
  have h1 : (J.map t).det ≠ 0 := by
    rw [show J.map t = (t : E →+* K).mapMatrix J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 hJ
  rw [dbl, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero t), Matrix.det_fromBlocks_zero₂₁]
  refine isUnit_iff_ne_zero.2 (mul_ne_zero h1 ?_)
  rw [show ((-J).map t) = -(J.map t) by ext i j; simp, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1

end SplitSurj

open SplitSurj in
theorem locMatD_surjOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 → (∀ i j, σ (J j i) = -J i j) →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.SurjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) Set.univ := by
  intro F E _ _ _ _ _ σ h d J hdet hJ v t c A _
  have hK := isUnit_det_dbl_map t J hdet
  have skew := dbl_skew σ J hJ
  let A' : GL (Fin d ⊕ Fin d) (Fv F v) := dsum c * A * (dsum c)⁻¹
  let G : GL (Fin d ⊕ Fin d) (AE F E) := GlobalTheory.LeviIdx.adelicGL h t (dbl J) hK A'
  have hu : G ∈ UG (cA σ) (dbl (incM F J)) := by
    show (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ * dbl (incM F J) *
      (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F J)
    rw [dbl_incM]
    exact GlobalTheory.LeviIdx.adelicGL_unitary h t (dbl J) hK skew A'
  refine ⟨⟨G, hu⟩, GlobalTheory.LeviIdx.adelicGL_at h t (dbl J) hK A', ?_⟩
  change (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) G * dsum c = A
  rw [GlobalTheory.LeviIdx.adelicGL_map_piW]
  show (dsum c)⁻¹ * (dsum c * A * (dsum c)⁻¹) * dsum c = A
  group

end GlobalTheory.DblScal

end
end
