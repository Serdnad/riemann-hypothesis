module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle005
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle023
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
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle022

@[expose] public section

section

open scoped Matrix
open Formalism.UG

namespace GlobalTheory.WittTransitivity

variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)

theorem hform_sub_left (x y z : Fin M → A) :
    hform c J (x - y) z = hform c J x z - hform c J y z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (x y z : Fin M → A) :
    hform c J x (y - z) = hform c J x y - hform c J x z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_smul_left (a : A) (x z : Fin M → A) :
    hform c J (a • x) z = c a * hform c J x z := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_right (a : A) (x z : Fin M → A) :
    hform c J x (a • z) = a * hform c J x z := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem conj_hform (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j) (x y : Fin M → A) :
    c (hform c J x y) = hform c J y x := by

  simp only [Formalism.UG.hform, map_sum, map_mul, hc, hJ]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem hform_eq_sum (x y : Fin M → A) :
    hform c J x y = ∑ j, hform c J x (Pi.single j 1) * y j := by
  have key : ∀ j, hform c J x (Pi.single j 1) = ∑ i, c (x i) * J i j := by
    intro j
    simp [Formalism.UG.hform, Pi.single_apply]
  simp_rw [key]
  simp only [Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm

theorem exists_mem_UJ (hdet : IsUnit J.det) (g : Matrix (Fin M) (Fin M) A)
    (hg : ∀ y z, hform c J (g *ᵥ y) (g *ᵥ z) = hform c J y z) :
    ∃ G ∈ UJ c J, (G : Matrix (Fin M) (Fin M) A) = g := by
  apply PI.VolStabSW.OrbR.mem_UJ_of <;> assumption

theorem exists_reflection (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j)
    (hdet : IsUnit J.det) (x x' : Fin M → A) (hx : hform c J x x = hform c J x' x')
    (hs : IsUnit (hform c J x x - hform c J x' x)) :
    ∃ g ∈ UJ c J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = x' := by
  set s := hform c J x x - hform c J x' x with hs_def
  obtain ⟨su, hsu⟩ := hs
  set b : A := ↑su⁻¹ with hb_def
  have hbs : b * s = 1 := by rw [hb_def, ← hsu, Units.inv_mul]
  have hcb : c b * c s = 1 := by rw [← map_mul, hbs, map_one]
  set v := x - x' with hv
  have hvv : hform c J v v = s + c s := by
    have hxx : c (hform c J x x) = hform c J x x := conj_hform c J hc hJ x x
    have e1 : c s = hform c J x x - hform c J x x' := by
      rw [hs_def, map_sub, hxx, conj_hform c J hc hJ]
    rw [hv, hform_sub_left, hform_sub_right, hform_sub_right, e1, hs_def, ← hx]
    ring
  set g : Matrix (Fin M) (Fin M) A :=
    1 - Matrix.of (fun k j => b * v k * hform c J v (Pi.single j 1)) with hg_def
  have hgy : ∀ y, g *ᵥ y = y - (b * hform c J v y) • v := by
    intro y
    rw [hform_eq_sum c J v y]
    ext k
    rw [hg_def, Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.of_apply]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpres : ∀ y z, hform c J (g *ᵥ y) (g *ᵥ z) = hform c J y z := by
    intro y z
    rw [hgy, hgy, hform_sub_left, hform_sub_right, hform_sub_right, hform_smul_left,
      hform_smul_left, hform_smul_right, hform_smul_right, map_mul,
      conj_hform c J hc hJ v y, hvv]
    linear_combination (hform c J y v * hform c J v z * c b) * hbs +
      (hform c J y v * hform c J v z * b) * hcb
  obtain ⟨G, hG, hGg⟩ := exists_mem_UJ c J hdet g hpres
  refine ⟨G, hG, ?_⟩
  have hvx : hform c J v x = s := by rw [hv, hform_sub_left, hs_def]
  rw [hGg, hgy, hvx, hbs, one_smul, hv, sub_sub_cancel]

theorem exists_norm_one (hc : ∀ a, c (c a) = a) (hf : ∀ a, c a = a → a ≠ 0 → IsUnit a)
    (h2 : IsUnit (2 : A)) (h3 : (3 : A) ≠ 0) (hθ : ∃ θ, IsUnit (θ - c θ))
    (b t : A) (hcb : c b = b) (hb : IsUnit b) :
    ∃ u : A, u * c u = 1 ∧ IsUnit (b - c u * t) := by
  have hN : ∀ a : A, a * c a ≠ 0 → IsUnit (a * c a) := by
    intro a ha
    exact hf _ (by rw [map_mul, hc, mul_comm]) ha
  by_cases h1 : (b - t) * c (b - t) = 0
  · by_cases h1' : (b + t) * c (b + t) = 0
    · rw [map_sub, hcb] at h1
      rw [map_add (f := _), hcb] at h1'
      have h4 : (2 * b) * (t + c t) = (2 * b) * 0 := by linear_combination h1' - h1
      have htc : t + c t = 0 := (h2.mul hb).mul_left_cancel h4
      have hct : c t = -t := by linear_combination htc
      rw [hct] at h1 h1'
      have h5 : (2 : A) * (b * b - t * t) = 2 * 0 := by linear_combination h1 + h1'
      have hb2 : b * b = t * t := sub_eq_zero.mp (h2.mul_left_cancel h5)
      have ht : IsUnit t := isUnit_of_mul_isUnit_left (by rw [← hb2]; exact hb.mul hb)
      have key : ∀ w : A, IsUnit (w * c w) → IsUnit (w - c w) → IsUnit (w + c w) →
          ∃ u : A, u * c u = 1 ∧ IsUnit (b - c u * t) := by
        intro w hw hm hp
        obtain ⟨e, he⟩ := isUnit_of_mul_isUnit_right hw
        have h0 : c (↑e⁻¹ : A) * w = 1 := by
          have h6 := congrArg c (Units.inv_mul e)
          rw [map_mul, he, hc, map_one] at h6
          exact h6
        refine ⟨w * ↑e⁻¹, ?_, ?_⟩
        · calc w * ↑e⁻¹ * c (w * ↑e⁻¹) = (↑e⁻¹ * c w) * (c ↑e⁻¹ * w) := by rw [map_mul]; ring
            _ = 1 := by rw [← he, Units.inv_mul, h0, one_mul]
        · have hprod : IsUnit ((w * b - c w * t) * (c w * b + w * t)) := by
            have e1 : (w * b - c w * t) * (c w * b + w * t) = b * t * (w - c w) * (w + c w) := by
              linear_combination (w * c w) * hb2
            rw [e1]
            exact ((hb.mul ht).mul hm).mul hp
          have e2 : b - c (w * ↑e⁻¹) * t = c ↑e⁻¹ * (w * b - c w * t) := by
            rw [map_mul]
            linear_combination (-b) * h0
          rw [e2]
          exact (isUnit_of_mul_isUnit_left (by rw [h0]; exact isUnit_one)).mul
            (isUnit_of_mul_isUnit_left hprod)
      obtain ⟨θ, hθu⟩ := hθ
      have hcδ : c (θ - c θ) = -(θ - c θ) := by rw [map_sub, hc]; ring
      by_cases hd : (1 + (θ - c θ)) * c (1 + (θ - c θ)) = 0
      · rw [map_add (f := _), map_one, hcδ] at hd
        apply key (2 + (θ - c θ))
        · have e : (2 + (θ - c θ)) * c (2 + (θ - c θ)) = 3 := by
            rw [map_add (f := _), map_ofNat, hcδ]
            linear_combination hd
          rw [e]
          exact hf 3 (map_ofNat c 3) h3
        · have e : 2 + (θ - c θ) - c (2 + (θ - c θ)) = 2 * (θ - c θ) := by
            rw [map_add (f := _), map_ofNat, hcδ]
            ring
          rw [e]
          exact h2.mul hθu
        · have e : 2 + (θ - c θ) + c (2 + (θ - c θ)) = 2 * 2 := by
            rw [map_add (f := _), map_ofNat, hcδ]
            ring
          rw [e]
          exact h2.mul h2
      · apply key (1 + (θ - c θ)) (hN _ hd)
        · have e : 1 + (θ - c θ) - c (1 + (θ - c θ)) = 2 * (θ - c θ) := by
            rw [map_add (f := _), map_one, hcδ]
            ring
          rw [e]
          exact h2.mul hθu
        · have e : 1 + (θ - c θ) + c (1 + (θ - c θ)) = 2 := by
            rw [map_add (f := _), map_one, hcδ]
            ring
          rw [e]
          exact h2
    · refine ⟨-1, by rw [map_neg, map_one]; ring, ?_⟩
      have e : b - c (-1) * t = b + t := by rw [map_neg, map_one]; ring
      rw [e]
      exact isUnit_of_mul_isUnit_left (hN _ h1')
  · refine ⟨1, by rw [map_one, one_mul], ?_⟩
    have e : b - c 1 * t = b - t := by rw [map_one, one_mul]
    rw [e]
    exact isUnit_of_mul_isUnit_left (hN _ h1)

theorem witt_transitive (A : Type) [CommRing A] (c : A →+* A) (hc : ∀ a, c (c a) = a)
    (hf : ∀ a, c a = a → a ≠ 0 → IsUnit a) (h2 : IsUnit (2 : A)) (h3 : (3 : A) ≠ 0)
    (hθ : ∃ θ, IsUnit (θ - c θ)) (M : ℕ) (J : Matrix (Fin M) (Fin M) A)
    (hJ : ∀ i j, c (J j i) = J i j) (hdet : IsUnit J.det) (x x' : Fin M → A)
    (hx : hform c J x x = hform c J x' x') (hb : IsUnit (hform c J x x)) :
    ∃ g ∈ UJ c J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = x' := by
  have hxx : c (hform c J x x) = hform c J x x := conj_hform c J hc hJ x x
  obtain ⟨u, hu, hut⟩ :=
    exists_norm_one c hc hf h2 h3 hθ (hform c J x x) (hform c J x' x) hxx hb
  have hux : hform c J x x = hform c J (u • x') (u • x') := by
    rw [hform_smul_left, hform_smul_right, ← hx]
    linear_combination (-(hform c J x x)) * hu
  obtain ⟨g1, hg1, hg1x⟩ := exists_reflection c J hc hJ hdet x (u • x') hux
    (by rw [hform_smul_left]; exact hut)
  obtain ⟨g2, hg2, hg2e⟩ := exists_mem_UJ c J hdet (c u • (1 : Matrix (Fin M) (Fin M) A))
    (by
      intro y z
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [hform_smul_left, hform_smul_right, hc]
      linear_combination (hform c J y z) * hu)
  refine ⟨g2 * g1, mul_mem hg2 hg1, ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg1x, hg2e]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
  rw [mul_comm, hu, one_smul]

end GlobalTheory.WittTransitivity
end

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular

theorem modularCharacter_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (hG : IsUnimodular G) (g : G) :
    Measure.modularCharacter g = 1 := by
  haveI := hG Measure.haar inferInstance
  change Measure.modularCharacterFun g = 1
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure G) g]
  have key : ∀ (μ' : Measure G) [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant],
      μ' = Measure.haar → Measure.haarScalarFactor μ' (Measure.haar : Measure G) = 1 := by
    intro μ' _ _ h
    subst h
    exact Measure.haarScalarFactor_self _
  exact key _ (map_mul_right_eq_self _ g)

theorem invariantMeasureClause : InvariantMeasureClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH uG uH
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space G H hH fun h => ?_
  rw [modularCharacter_eq_one uG, modularCharacter_eq_one uH]

end GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular
end

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

theorem _root_.GlobalTheory.T.existsUnique_haar_group_quotient_integral_formula : NormaliseGroupClause := by
  first | exact @GlobalTheory.normaliseGroupClause_holds | exact GlobalTheory.normaliseGroupClause_holds | (intros; apply GlobalTheory.normaliseGroupClause_holds <;> assumption)
end

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

theorem _root_.GlobalTheory.T.existsUnique_haar_subgroup_quotient_integral_formula : NormaliseSubgroupClause := by
  first | exact @GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause | exact GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause | (intros; apply GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal GlobalTheory.SelfDualLatticeCompare

namespace GlobalTheory.UnramConjUnit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.UnramConjUnit.conj_ne_id (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ¬ ∀ e, σ e = e := by
  intro hσ
  obtain ⟨-, hE, -, hconj⟩ := h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := hE.isComplex w
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  ext x
  simpa [hσ x] using (hconj w.embedding x).symm


open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.UnramConjUnit.exists_sub_conj_notMem (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) :
    ∃ (t d : 𝓞 E) (s : 𝓞 F), (d : E) = (t : E) - σ t ∧
      algebraMap F E (s : F) = (d : E) * d ∧ s ∉ v.asIdeal := by
  classical
  have hne := _root_.GlobalTheory.UnramConjUnit.conj_ne_id h
  obtain ⟨-, -, hrank, -⟩ := h
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ σ.bijective
  have hτ : ∀ x, τ x = σ x := fun _ => rfl
  have hτ1 : τ ≠ 1 := fun h1 => hne fun e => by rw [← hτ, h1]; rfl
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    refine le_antisymm (hrank ▸ AlgEquiv.card_le) ?_
    have h2 : ({1, τ} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair (Ne.symm hτ1)
    exact h2 ▸ Finset.card_le_univ _
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E
    (by rw [Nat.card_eq_fintype_card, hcard, hrank])
  have hG : ∀ g : E ≃ₐ[F] E, g = 1 ∨ g = τ := by
    intro g
    by_contra hg
    push_neg at hg
    have h3 : ({g, 1, τ} : Finset (E ≃ₐ[F] E)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hg.1, hg.2]), Finset.card_pair (Ne.symm hτ1)]
    have := h3 ▸ Finset.card_le_univ ({g, 1, τ} : Finset (E ≃ₐ[F] E))
    omega
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    rcases hG (τ * τ) with h2 | h2
    · exact congrArg (fun g : E ≃ₐ[F] E => g x) h2
    · exact absurd (mul_eq_right.mp h2) hτ1
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := 𝓞 E) v.asIdeal
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hPv.over, Ideal.under, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
  have he := hv ⟨P, hP, hPbot⟩ hPv
  have hin : τ ∉ Ideal.inertia (E ≃ₐ[F] E) P := by
    intro hmem
    have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)] at h1
    have h1' : Nat.card (Ideal.inertia (E ≃ₐ[F] E) P) = 1 := h1.trans he
    rw [Subgroup.card_eq_one] at h1'
    rw [h1', Subgroup.mem_bot] at hmem
    exact hτ1 hmem
  have hin' : ¬ ∀ x : 𝓞 E, τ • x - x ∈ P := fun hall => hin (AddSubgroup.mem_inertia.mpr hall)
  push_neg at hin'
  obtain ⟨x, hx⟩ := hin'
  set d : 𝓞 E := x - τ • x with hd_def
  have hd : d ∉ P := fun hd => hx (by rw [← neg_sub]; exact P.neg_mem hd)
  have hdE : (d : E) = x - σ x := rfl
  have hfix : ∀ g : E ≃ₐ[F] E, g ((d : E) * d) = (d : E) * d := by
    intro g
    rcases hG g with rfl | rfl
    · rfl
    · have : τ (d : E) = -(d : E) := by
        rw [hdE, map_sub, ← hτ, hττ, neg_sub]
      rw [map_mul, this, neg_mul_neg]
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
  have hcint : IsIntegral ℤ c := by
    have hi : IsIntegral ℤ (algebraMap F E c) := by
      rw [hc]
      exact ((d * d : 𝓞 E)).isIntegral_coe
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E)
      (algebraMap F E).injective).mp hi
  refine ⟨x, d, ⟨c, hcint⟩, hdE, hc, ?_⟩
  intro hs
  have hmem : algebraMap (𝓞 F) (𝓞 E) ⟨c, hcint⟩ ∈ P := by
    rw [hPv.over] at hs
    exact hs
  have heq : algebraMap (𝓞 F) (𝓞 E) ⟨c, hcint⟩ = d * d := by
    apply RingOfIntegers.ext
    change _ = (d : E) * d
    rw [← hc]
    rfl
  rw [heq] at hmem
  exact hd ((hP.mem_or_mem hmem).elim id id)


open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.UnramConjUnit.exists_sub_conj_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    ∀ v : HeightOneSpectrum (𝓞 F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v →
    ∃ θ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v, ∃ b ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v,
      (θ - _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ θ) * b = 1 := by
  intro F E _ _ _ _ _ σ h v hv
  obtain ⟨t, d, s, hd, hs, hsv⟩ := _root_.GlobalTheory.UnramConjUnit.exists_sub_conj_notMem h v hv
  have hu : Valued.v (algebraMap F (v.adicCompletion F) (s : F)) = 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [HeightOneSpectrum.adicCompletion.valued_coe]
    exact (HeightOneSpectrum.valuation_of_algebraMap v s).trans
      ((HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hsv)
  set u : v.adicCompletion F := algebraMap F (v.adicCompletion F) (s : F) with hu_def
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have huinv : u⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]
  have hintR : ∀ y : 𝓞 E, IsIntegral (v.adicCompletionIntegers F)
      ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (y : E)) := by
    intro y
    exact y.isIntegral_coe.map_of_comp_eq (Int.castRingHom _)
      (Algebra.TensorProduct.includeRight (R := F) (A := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (B := E)).toRingHom
      (RingHom.ext_int _ _)
  refine ⟨(1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E), hintR t,
    (u⁻¹ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E), ?_, ?_⟩
  · have hb : (u⁻¹ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E) =
        algebraMap (v.adicCompletionIntegers F) (TensorProduct F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) ⟨u⁻¹, huinv⟩ *
          ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E)) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
      rfl
    rw [hb]
    exact isIntegral_algebraMap.mul (hintR d)
  · have hsub : (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E) -
        _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E)) =
        (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E) := by
      simp [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hd, TensorProduct.tmul_sub]
    rw [hsub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hs, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    change (u * u⁻¹) ⊗ₜ[F] (1 : E) = 1
    rw [mul_inv_cancel₀ hu0]
    rfl

end GlobalTheory.UnramConjUnit
end

section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.exists_borelSection_unitary_orbit_quadric : ∀ (P Q : ℕ) (β : ℝ) (x₀ : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q), β ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x₀ = β → ∃ s : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → UpqT P Q, GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.IsSection β x₀ s := by
  first | exact @GlobalTheory.QuadricSection.exists_isSection | exact GlobalTheory.QuadricSection.exists_isSection | (intros; apply GlobalTheory.QuadricSection.exists_isSection <;> assumption)
end

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.jetsAreBoundedMeasureMoments_padicInt_matrix_change : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ κ' : Type) [Fintype κ] [Fintype κ'] (v : κ → V) (w : κ' → V) (c : κ' → κ → ℂ) (a : κ' → κ → ℤ_[q]) (G : V → ℂ), (∀ i j, ι (c i j) = zc (a i j)) → (∀ i, w i = ∑ j, c i j • v j) → MomInt ι v G → MomInt ι w G := by
  first | exact @GlobalTheory.MomN.momInt_push | exact GlobalTheory.MomN.momInt_push | (intros; apply GlobalTheory.MomN.momInt_push <;> assumption)
end

section

open GlobalTheory.MomN

theorem _root_.GlobalTheory.T.mahlerJetCoefficient_of_family_zero_off_embedding : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι'] (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ i, u (e i) = w i) → (∀ p, p ∉ Set.range e → u p = 0) → (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u G k = 0) ∧ (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → GlobalTheory.MomN.mahler u G k = GlobalTheory.MomN.mahler w G (fun i => k (e i))) := by
  first | exact @GlobalTheory.MomEmbed.mahler_embed | exact GlobalTheory.MomEmbed.mahler_embed | (intros; apply GlobalTheory.MomEmbed.mahler_embed <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) → haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩; (LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0) ∧ ord χ s = ord χ.primitiveCharacter s := by
  first | exact @GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter | exact GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter | (intros; apply GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter <;> assumption)
end
