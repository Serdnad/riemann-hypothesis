module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle016
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle012
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
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u



theorem SemilocalLengthSum.proof (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFiniteRank.Statement.{u}) (h3 : DegZeroLocalRing.Statement.{u})
    (h4 : FiniteAlgebraLengthSum.Statement.{u}) (h5 : SemilocalMaxIdeals.Statement.{u}) :
    SemilocalLengthSum.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW d hd α hα β hβ
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  refine ⟨hfin, ?_⟩
  have := (h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1
  have := (h3 F K (fun k => ι' (j k)) (contractPrime j P') (isMultiProjPrime_contractPrime j ι' hP')
    W hW hPW).1.2
  obtain ⟨𝔪, h𝔪, hinj, hcov, hloc⟩ := h5 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  let : Fintype (fibrePrimes j P' W) := hfin.fintype
  let alg : ∀ W' : fibrePrimes j P' W,
      Algebra (degZeroLoc P' (fibrePrimes j P' W)) (degZeroLoc P' {W'.1}) :=
    fun W' => degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
  rw [h4 _ _ _ 𝔪 h𝔪 hinj hcov (fun W' => degZeroLoc P' {W'.1}) (fun W' => (hloc W').1) α,
    Finset.sum_filter, Finset.sum_subtype hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]
  refine Finset.sum_congr rfl fun W' _ => ?_
  obtain ⟨hW'p, -, hW'c⟩ := W'.2
  have := hW'p.isPrime
  have hb : algebraMap _ (degZeroLoc P' {W'.1}) (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W)) α) = β W'.1 :=
    Subtype.ext (hβ W'.1 W'.2).symm
  rw [hb, (hloc W').2, ← hd W'.1 hW'p hW'c]
  split_ifs with haW'
  · rfl
  rw [Ring.ord_of_isUnit, zero_mul]
  have hne : ∀ g, g ∉ contractPrime j P' → algebraMap (MRing ι' F ⧸ P')
      (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' (rename (blockIncl j ι') g)) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  have hhP : h ∉ contractPrime j P' := fun hm => hhW (hPW hm)
  refine IsUnit.of_mul_eq_one ⟨_, div_mem_degZeroLoc P' {W'.1} (isMultiHomog_rename j ι' hh)
    (isMultiHomog_rename j ι' ha) haP (fun W'' hW'' => (Set.mem_singleton_iff.mp hW'') ▸ haW')⟩ ?_
  apply Subtype.ext
  change (β W'.1 : FractionRing (MRing ι' F ⧸ P')) * _ = 1
  rw [hβ W'.1 W'.2, hα, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
  have := hne h hhP
  have := hne a haP
  field_simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem FibreNonempty.proof (h1 : SemilocalFiniteRank.Statement.{u})
    (h2 : DegZeroLocalRing.Statement.{u}) : FibreNonempty.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hn hc W hW hWn hle
  have := hP'.isPrime
  by_contra hem
  rw [Set.not_nonempty_iff_eq_empty] at hem
  obtain ⟨hfin, -, -⟩ := h1 F K K' j ι' P' hP' n hn hc W hW hWn hle
  have := hfin
  have hnone : ∀ W' ∈ fibrePrimes j P' W, False := fun W' hW' => by
    rw [hem] at hW'
    exact hW'

  have hB : IsField (degZeroLoc P' (fibrePrimes j P' W)) := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro x hx
    obtain ⟨b, f, g, hf, hg, hgP, -, hxfg⟩ := DegZeroLocQuot.proof F K' ι' P' (fibrePrimes j P' W)
      (fun W' hW' => (hnone W' hW').elim) x.1 x.2
    have hfP : f ∉ P' := by
      intro hfP
      apply hx
      apply Subtype.ext
      rw [hxfg, Ideal.Quotient.eq_zero_iff_mem.mpr hfP, map_zero, zero_div]
      rfl
    refine ⟨⟨_, div_mem_degZeroLoc P' (fibrePrimes j P' W) hg hf hfP
      (fun W' hW' => (hnone W' hW').elim)⟩, ?_⟩
    have hne : ∀ a : MRing ι' F, a ∉ P' →
        algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' a) ≠ 0 :=
      fun a ha => by
        rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
        exact ha
    apply Subtype.ext
    change x.1 * _ = 1
    rw [hxfg, div_mul_div_comm, mul_comm (algebraMap _ _ (Ideal.Quotient.mk P' f))]
    exact div_self (mul_ne_zero (hne g hgP) (hne f hfP))

  have hinj : Function.Injective (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W))) := by
    intro x y hxy
    have := congrArg (fun z : degZeroLoc P' (fibrePrimes j P' W) =>
      (z : FractionRing (MRing ι' F ⧸ P'))) hxy
    simp only [degZeroLoc.algebraMap_contract_coe] at this
    exact Subtype.ext ((contractFracMap j P').toRingHom.injective this)
  have : Algebra.IsIntegral (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W)) := Algebra.IsIntegral.of_finite _ _
  have hA := isField_of_isIntegral_of_isField hinj hB
  have hdim := (h2 F K (fun k => ι' (j k)) (contractPrime j P')
    (isMultiProjPrime_contractPrime j ι' hP') W hW hle).2 n hc hWn
  rw [ringKrullDim_eq_zero_of_isField hA] at hdim
  exact zero_ne_one hdim

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem SemilocalResidueLength.proof (hRes : DegZeroLocResidue.Statement.{u})
    (hFR : SemilocalFiniteRank.Statement.{u}) (hLoc : DegZeroLocLocalize.Statement.{u}) :
    SemilocalResidueLength.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW
  have := hP'.isPrime
  intro W' hW'
  have := hW'.1.isPrime
  haveI hfin := (hFR F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1
  have h𝒲 := FibreFinite.proof F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  obtain ⟨-, hPW', hc⟩ := id hW'
  subst hc
  obtain ⟨ρO, hρOv, hρOk, hρOr⟩ := hRes F K' ι' P' W' hPW'
  obtain ⟨ρA, hρAv, -, hρAr⟩ := hRes F K (fun k => ι' (j k)) (contractPrime j P') _ hPW
  have hLE := map_homFracDegZero_le j ι' W'
  have hBO := degZeroLoc_anti P' (Set.singleton_subset_iff.mpr hW')
  let L := (homFracDegZero (contractPrime j W')).map (contractFracMap j W')
  let M := IntermediateField.extendScalars hLE
  let τ : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) →+* M :=
    (ρO.comp (Subalgebra.inclusion hBO).toRingHom).codRestrict M (fun b => (hρOr _).mpr ⟨_, rfl⟩)
  let σ : degZeroLoc (contractPrime j P') {contractPrime j W'} →+* L :=
    ((contractFracMap j W').toRingHom.comp ρA).codRestrict L
      (fun a => ⟨ρA a, (hρAr _).mpr ⟨a, rfl⟩, rfl⟩)
  have hσs : Function.Surjective σ := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨a, rfl⟩ := (hρAr w).mp hw
    exact ⟨a, rfl⟩
  letI : Algebra (degZeroLoc (contractPrime j P') {contractPrime j W'}) L := σ.toAlgebra
  letI : Algebra (degZeroLoc (contractPrime j P') {contractPrime j W'}) M :=
    ((algebraMap L M).comp σ).toAlgebra
  haveI : IsScalarTower (degZeroLoc (contractPrime j P') {contractPrime j W'}) L M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hcomp : ∀ a : degZeroLoc (contractPrime j P') {contractPrime j W'}, τ (algebraMap _ _ a) = algebraMap _ M a := by
    intro a
    obtain ⟨b, f, g, hf, hg, -, hgW, hx⟩ := DegZeroLocQuot.proof F K (fun k => ι' (j k))
      (contractPrime j P') {contractPrime j W'} (fun V hV => by rw [hV]; infer_instance) a.1 a.2
    apply Subtype.ext
    show ρO ⟨contractFracMap j P' a, _⟩ = contractFracMap j W' (ρA a)
    rw [hρAv a b f g hf hg (hgW _ rfl) hx, map_div₀, contractFracMap_algebraMap,
      contractFracMap_algebraMap]
    apply hρOv _ _ _ _ (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hg) (hgW _ rfl)
    show contractFracMap j P' a = _
    rw [hx, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
  let τA : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) →ₐ[degZeroLoc (contractPrime j P') {contractPrime j W'}] M :=
    { τ with commutes' := hcomp }

  have hmem : ∀ l : L, algebraMap L M l ∈ τ.rangeS := by
    intro l
    obtain ⟨a, rfl⟩ := hσs l
    exact ⟨_, hcomp a⟩
  let R : Subalgebra L M := { τ.rangeS with algebraMap_mem' := hmem }
  have hsurj : Function.Surjective τ := by
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := (hρOr z).mp hz
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hys⟩ := hLoc F K' ι' P' hP' _ h𝒲
      (fun V hV => ⟨hV.1, hV.2.1⟩) W' hW' y.1 y.2
    have hs0 : τ ⟨s, hs⟩ ≠ 0 := by
      intro h0
      have h1 : ρO ⟨s, hBO hs⟩ * ρO ⟨t, ht⟩ = 1 := by
        rw [← map_mul, ← map_one ρO]
        exact congrArg ρO (Subtype.ext hst)
      rw [show ρO ⟨s, hBO hs⟩ = 0 from congrArg Subtype.val h0, zero_mul] at h1
      exact zero_ne_one h1
    have hint : IsIntegral L (τ ⟨s, hs⟩) :=
      ((Algebra.IsIntegral.isIntegral (R := degZeroLoc (contractPrime j P') {contractPrime j W'})
        (⟨s, hs⟩ : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')))).map τA).tower_top
    obtain ⟨c, hc⟩ := hint.inv_mem (A := R) ⟨⟨s, hs⟩, rfl⟩
    have hbys : τ ⟨b, hb⟩ = ⟨ρO y, hz⟩ * τ ⟨s, hs⟩ := by
      apply Subtype.ext
      show ρO ⟨b, hBO hb⟩ = ρO y * ρO ⟨s, hBO hs⟩
      rw [← map_mul]
      exact congrArg ρO (Subtype.ext hys.symm)
    refine ⟨⟨b, hb⟩ * c, ?_⟩
    rw [map_mul, hc, hbys, mul_inv_cancel_right₀ hs0]
  refine ⟨RingHom.ker τ, fun x => ?_, ?_⟩
  · rw [RingHom.mem_ker, ← ZeroMemClass.coe_eq_zero]
    exact hρOk ⟨x, hBO x.2⟩
  · let e : (degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) ⧸ RingHom.ker τ) ≃ₐ[degZeroLoc (contractPrime j P') {contractPrime j W'}] M :=
      AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hsurj) (fun a => by
        rw [← Ideal.Quotient.mk_algebraMap, RingHom.quotientKerEquivOfSurjective_apply_mk]
        exact hcomp a)
    haveI : Module.Finite (degZeroLoc (contractPrime j P') {contractPrime j W'}) M :=
      Module.Finite.of_surjective τA.toLinearMap hsurj
    haveI : Module.Finite L M :=
      Module.Finite.of_restrictScalars_finite (degZeroLoc (contractPrime j P') {contractPrime j W'}) L M
    refine e.toLinearEquiv.length_eq.trans ?_
    refine (Module.length_eq_of_surjective (S := degZeroLoc (contractPrime j P') {contractPrime j W'}) (R := L) (M := M) hσs).trans ?_
    rw [Module.length_eq_finrank L M, relDeg,
      IntermediateField.relfinrank_eq_finrank_of_le hLE]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
