module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle012
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle018
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestWeightVectorFindim
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.CasimirPowerScaledInsertDividedPower
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.CommutatorTripleProductLeibniz
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialPreservesDiagonalStable
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.EquivariantInjectiveOfCyclic
import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionRangeTrivial
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle009
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle017
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle011
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectionCommutesOperators
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle010
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle016
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralGeneratorsPreserveLattice
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MultidegreePartFinitelyGenerated
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle014
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightDifferenceLeEllOfRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle013
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def smulRightLinear {K L W : Type} [Field K] [AddCommGroup L] [Module K L] [AddCommGroup W] [Module K W]
    (ξ : L →ₗ[K] K) : W →ₗ[K] (L →ₗ[K] W) where
  toFun := fun m => ξ.smulRight m
  map_add' := fun m m' => by ext x; simp
  map_smul' := fun c m => by
    ext x
    simp only [LinearMap.smulRight_apply, RingHom.id_apply, LinearMap.smul_apply]
    exact smul_comm _ _ _

theorem isotypic_projector_trace_formula (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : IsotypicProjectorTraceFormula := by
  intro n K W _ _ _ _ _ E hE lam e he v0 hv0 hL P hP ι _ b m
  have hEL := restrictRepresentation_isRep E hE _ hL
  have hv0' := highest_vector_restrict E _ hL lam v0 (self_mem_cyclicSubmodule E v0) hv0
  have hcyc := cyclicSubmodule_restrict_eq_top E v0 hL
  have hPe := fun g => invariant_projection_equivariant D h2 (restrictRepresentation E _ hL) E hEL hE P hP g

  let Θ : W →ₗ[K] W := ∑ i, (LinearMap.applyₗ (b i)) ∘ₗ P ∘ₗ smulRightLinear (b.coord i)
  have hΘ : ∀ m, Θ m = ∑ i, P ((b.coord i).smulRight m) (b i) := by
    intro m
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]
    rfl
  have hle : (⨆ mu, isoSub E mu) ≤ LinearMap.eqLocus ((Fintype.card ι : K) • Θ) e := by
    refine iSup_le fun mu => ?_
    by_cases hmu : mu = lam
    · subst hmu
      refine Submodule.span_le.2 ?_
      rintro y ⟨u, hu, v, hv, rfl⟩
      have hy : u v ∈ isoSub E mu := Submodule.subset_span ⟨u, hu, v, hv, rfl⟩
      obtain ⟨φ, hφ, hφv⟩ := exists_equivariant_cyclic_to_hwv D h2 E hE mu v0 v hv0 hv hL
      obtain ⟨uL, _, huL⟩ := equivariant_lifts_monoid (restrictRepresentation E _ hL) E φ hφ hu
      have hm : u v = φ (uL ⟨v0, self_mem_cyclicSubmodule E v0⟩) := by rw [huL, hφv]
      obtain ⟨P0, hP0⟩ := invariant_projection_exists D h2 n K _ _ (homRepresentation_isRep _ _ hEL hEL)
      have hT : IsEquivariantMap (homRepresentation (restrictRepresentation E _ hL) (restrictRepresentation E _ hL)) (homRepresentation (restrictRepresentation E _ hL) E)
          (LinearMap.llcomp K _ _ W φ) := by
        intro a c g
        ext x
        simp only [LinearMap.llcomp_apply, homRepresentation_apply, map_sub]
        rw [hφ]
      change ((Fintype.card ι : K) • Θ) (u v) = e (u v)
      rw [he.1 _ hy, LinearMap.smul_apply, hΘ, hm, Finset.smul_sum]
      set l := uL ⟨v0, self_mem_cyclicSubmodule E v0⟩ with hl
      have hterm : ∀ i, (Fintype.card ι : K) • P ((b.coord i).smulRight (φ l)) (b i) = (b.repr l i) • φ (b i) := by
        intro i
        have h3 : (b.coord i).smulRight (φ l) = LinearMap.llcomp K _ _ W φ ((b.coord i).smulRight l) := by
          ext x; simp
        have h4 := equivariant_commutes_isotypic D h2 n K _ _ _ _ (homRepresentation_isRep _ _ hEL hEL) (homRepresentation_isRep _ _ hEL hE)
          (LinearMap.llcomp K _ _ W φ) hT P0 P hP0 hP ((b.coord i).smulRight l)
        have h5 := schur_invariant_projection_trace D h2 _ hEL mu _ hv0' hcyc P0 hP0 ((b.coord i).smulRight l)
        rw [Module.finrank_eq_card_basis b, LinearMap.trace_smulRight] at h5
        rw [h3, ← h4, LinearMap.llcomp_apply, ← map_smul, ← LinearMap.smul_apply, h5]
        simp [Module.Basis.coord_apply]
      rw [Finset.sum_congr rfl fun i _ => hterm i]
      conv_rhs => rw [← b.sum_repr l]

      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm
    · intro y hy
      have hWm : IsSubrepresentation E (isoSub E mu) := fun a c => isotypic_stable_under_gl_operator E mu a c
      have hEm := restrictRepresentation_isRep E hE _ hWm
      obtain ⟨P1, hP1⟩ := invariant_projection_exists D h2 n K _ _ (homRepresentation_isRep _ _ hEL hEm)
      have hT : IsEquivariantMap (homRepresentation (restrictRepresentation E _ hL) (restrictRepresentation E _ hWm)) (homRepresentation (restrictRepresentation E _ hL) E)
          (LinearMap.llcomp K _ _ W (isoSub E mu).subtype) := by
        intro a c g
        ext x
        simp
      have hzero : ∀ ξ : cyclicSubmodule E v0 →ₗ[K] K, P (ξ.smulRight y) = 0 := by
        intro ξ
        have h3 : ξ.smulRight y = LinearMap.llcomp K _ _ W (isoSub E mu).subtype
            (ξ.smulRight (⟨y, hy⟩ : isoSub E mu)) := by
          ext x; simp
        have h4 := equivariant_commutes_isotypic D h2 n K _ _ _ _ (homRepresentation_isRep _ _ hEL hEm) (homRepresentation_isRep _ _ hEL hE)
          (LinearMap.llcomp K _ _ W (isoSub E mu).subtype) hT P1 P hP1 hP (ξ.smulRight (⟨y, hy⟩ : isoSub E mu))
        have hmem : ∀ x, P (ξ.smulRight y) x ∈ isoSub E mu := by
          intro x
          rw [h3, ← h4]
          simp
        have hv00 : P (ξ.smulRight y) ⟨v0, self_mem_cyclicSubmodule E v0⟩ = 0 := by
          by_contra h0
          have h6 := highest_vector_mem_isotypic E lam _ (equivariant_image_highest_vector _ E _ (hPe _) lam _ hv0' h0)
          exact h0 ((he.1 _ h6).symm.trans (he.2 mu hmu _ (hmem _)))
        ext x
        exact equivariant_kills_cyclic_of_zero _ E _ (hPe _) _ hv00 x (by rw [hcyc]; trivial)
      change ((Fintype.card ι : K) • Θ) y = e y
      rw [he.2 mu hmu y hy, LinearMap.smul_apply, hΘ]
      simp [hzero]
  have hm : m ∈ (⨆ mu, isoSub E mu) := by rw [isotypic_submodules_span_top D h2 n K W E hE]; trivial
  have := hle hm
  change ((Fintype.card ι : K) • Θ) m = e m at this
  rw [LinearMap.smul_apply, hΘ] at this
  exact this

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem generated_weight_lemma_of_formulas (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (hV1 : ValuationsAdditive D) (hDP : DividedPowerFormulaCharZero) (hBin : BinomialFormulaCharZero) :
    ShaLengthVersionTwo D :=
  generated_weight_lemma_char_zero D hV1 (stable_subspace_complete_reducibility D h2) highest_weight_module_bounds polynomial_operators_gl_relations monomials_are_weight_vectors polynomial_locally_finite hDP hBin

end Formalism.MainNotions.G.GLWeightTheory
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem integral_formula_lattice_holds : AdmissibleDVRIntegralFormLatticesStable := by
  intro p n' O _ _ _ S0 hG
  have hV : ValuationProperties p O := valuation_properties_hold hG.prime S0
  have hchar := dvr_fraction_field_char_zero hG.prime S0
  exact ⟨hchar, fun n ι _ LL => ⟨fun S => integral_formula_stability_holds hG.prime hV n ι LL S,
    fun S => char_zero_stability_of_closure hG.prime hchar (fock_lattice_closure_holds hV) n ι LL S, fock_lattice_finite_spanning_holds hG.prime S0 hV n ι⟩⟩

theorem polynomial_isotypic_lattice_corollary (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D :=
  polynomial_isotypic_lattice_of_parts D (complete_reducibility_of_semisimple D h2) contravariant_orthogonality_holds highest_weight_dominant_holds (subrep_restriction_of_reducibility (complete_reducibility_of_semisimple D h2)) polynomial_representation_holds integral_formula_lattice_holds h13

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem degreeZeroWeightsBounded_ellOf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) :
    DegreeZeroWeightsBounded E (ellOf E (⊤ : Submodule K V)) := by
  intro ν hsum hne a
  have hsplit : ν a + ∑ i ∈ Finset.univ.erase a, ν i = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ a)]; exact hsum
  have hell : (0 : ℤ) ≤ (ellOf E (⊤ : Submodule K V) : ℤ) := by positivity
  rw [abs_le]
  constructor
  · by_cases h0 : 0 ≤ ν a
    · linarith
    · push_neg at h0
      obtain ⟨b, hb, hbpos⟩ : ∃ b ∈ Finset.univ.erase a, 0 < ν b := by
        by_contra hc
        push_neg at hc
        have := Finset.sum_nonpos hc
        linarith
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      have := weight_difference_le_ell_of_rep hE ν hne b a hba (by linarith)
      linarith
  · by_cases h0 : ν a ≤ 0
    · linarith
    · push_neg at h0
      obtain ⟨b, hb, hbneg⟩ : ∃ b ∈ Finset.univ.erase a, ν b < 0 := by
        by_contra hc
        push_neg at hc
        have := Finset.sum_nonneg hc
        linarith
      have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
      have := weight_difference_le_ell_of_rep hE ν hne a b hab (by linarith)
      linarith

private theorem degreeZeroWeightsBounded_linf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) :
    DegreeZeroWeightsBounded E (linf E (⊤ : Submodule K V)) := by
  intro ν hsum hne a
  have hmem : (ν a).natAbs ∈ {k | ∃ nu ∈ wtsOf E (⊤ : Submodule K V), (∑ b, nu b = 0) ∧
      ∃ b, k = (nu b).natAbs} :=
    ⟨ν, by simpa [wtsOf] using hne, hsum, a, rfl⟩
  have hbdd : BddAbove {k | ∃ nu ∈ wtsOf E (⊤ : Submodule K V), (∑ b, nu b = 0) ∧
      ∃ b, k = (nu b).natAbs} := by
    refine ⟨ellOf E (⊤ : Submodule K V), ?_⟩
    rintro k ⟨nu, hnu, hs, b, rfl⟩
    have hne' : weightSp E nu ≠ ⊥ := by simpa [wtsOf] using hnu
    have h := degreeZeroWeightsBounded_ellOf hE nu hs hne' b
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  have hle : (ν a).natAbs ≤ linf E (⊤ : Submodule K V) := by
    unfold linf
    exact le_csSup hbdd hmem
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hle

theorem linf_lemma_without_projector (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : InvariantDenominatorLinftyBound := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx
  haveI : CharZero (KK O) := dvr_fraction_field_charZero_prime S hG.prime
  rw [hMQ]
  exact invariant_projection_denominator_bound D h2 p O n V E hE M hM.1 Inv hInv _ _
    (fun c u hu0 hu => extremal_projector_properties hE c _ (degreeZeroWeightsBounded_linf hE) u hu0 hu)
    (fun c y hy => extremalProjector_denominator_bound S hG.prime hE hM.1 c _ y hy) x hx

theorem denominator_lemma_without_projector (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : InvariantProjectionDenominator := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx
  haveI : CharZero (KK O) := dvr_fraction_field_charZero_prime S hG.prime
  rw [hMQ]
  exact invariant_projection_denominator_bound D h2 p O n V E hE M hM.1 Inv hInv _ _
    (fun c u hu0 hu => extremal_projector_properties hE c _ (degreeZeroWeightsBounded_ellOf hE) u hu0 hu)
    (fun c y hy => extremalProjector_denominator_bound S hG.prime hE hM.1 c _ y hy) x hx

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section inv

variable {A : Type*} [CommRing A] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)

theorem laurentExpand_C (σ : Type*) (b : LaurentPolynomial A) :
    mul_Phi σ A (C b) = AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A) b := by
  simp [mul_Phi]

theorem laurentExpand_X (σ : Type*) (v : σ) :
    mul_Phi σ A (X v) = LaurentPolynomial.C (X v) := by
  simp [mul_Phi]

theorem mapRingHom_laurent_C {A' : Type*} [CommRing A'] (f : A →+* A') (a : A) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  ext k
  rw [AddMonoidAlgebra.coeff_mapRingHom, LaurentPolynomial.C_apply, LaurentPolynomial.C_apply]
  split_ifs <;> simp

private theorem mapRingHom_laurent_comp {A₁ B₁ D₁ : Type*} [CommRing A₁] [CommRing B₁] [CommRing D₁]
    (f : B₁ →+* D₁) (g : A₁ →+* B₁) (x : LaurentPolynomial A₁) :
    AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.mapRingHom ℤ g x) =
      AddMonoidAlgebra.mapRingHom ℤ (f.comp g) x := by
  ext k
  simp only [AddMonoidAlgebra.coeff_mapRingHom, RingHom.comp_apply]

theorem laurentExpand_substitution (M M' : Matrix (Fin n) (Fin n) A) (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_Phi (ι × Fin n) A (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) =
      AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M') (mul_Phi (ι × Fin n) A Q) := by
  have key : (mul_Phi (ι × Fin n) A).comp
      (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C)) =
      (AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M')).comp (mul_Phi (ι × Fin n) A) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      have hC : (matrixSubst LL S (RingHom.id A) M M').comp (C : A →+* MvPolynomial (ι × Fin n) A) = C :=
        RingHom.ext fun a => by simp only [RingHom.comp_apply, matrixSubst_C, RingHom.id_apply]
      simp only [RingHom.comp_apply, matrixSubst_C, RingHom.id_apply, laurentExpand_C, mapRingHom_laurent_comp, hC]
    · intro v
      simp only [RingHom.comp_apply, matrixSubst_X, laurentExpand_X, mapRingHom_laurent_C]
      split_ifs <;> simp [map_sum, laurentExpand_C, laurentExpand_X, mapRingHom_laurent_C, Matrix.map_apply]
  exact congrArg (fun f => f Q) key

theorem laurent_degrees_substitution_subset (M M' : Matrix (Fin n) (Fin n) A) (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_degs (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) ⊆
      mul_degs Q := by
  rw [mul_degs_eq (matrixSubst LL S (RingHom.id _) _ _ Q), laurentExpand_substitution]
  have key : (AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M')).comp (mul_Phi (ι × Fin n) A) =
      eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ ((matrixSubst LL S (RingHom.id A) M M').comp C))
        (fun v => LaurentPolynomial.C (matrixSubst LL S (RingHom.id A) M M' (X v))) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, laurentExpand_C, mapRingHom_laurent_comp, MvPolynomial.eval₂Hom_C]
    · intro v
      simp only [RingHom.comp_apply, laurentExpand_X, mapRingHom_laurent_C, MvPolynomial.eval₂Hom_X']
  have e := congrArg (fun f => f Q) key
  simp only [RingHom.comp_apply] at e
  rw [e]
  exact mul_Psi_support _ _ Q

theorem laurent_degrees_substitution_eq (M M' : Matrix (Fin n) (Fin n) A) (h : M * M' = 1)
    (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_degs (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) =
      mul_degs Q := by
  apply Finset.Subset.antisymm (laurent_degrees_substitution_subset LL S M M' Q)
  have h' : M' * M = 1 := by
    first
    | exact Matrix.mul_eq_one_comm.1 h
    | exact mul_eq_one_comm.1 h
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) h
    | exact Matrix.nonsing_inv_mul_cancel_of_mul_eq_one h
  have hQ : matrixSubst LL S (RingHom.id _) (M'.map LaurentPolynomial.C) (M.map LaurentPolynomial.C)
      (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) = Q := by
    rw [matrixSubst_comp, ← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _), matrixSubst_one,
      MvPolynomial.map_id]
  conv_lhs => rw [← hQ]
  exact laurent_degrees_substitution_subset LL S M' M _

end inv

private theorem genericMatrixBis_mul_genericMatrixInverse (R : Type) [Field R] (n : ℕ) : genericMatrixRootWeights R n * genericMatrixInverse R n = 1 := by
  have e : genericMatrixInverse R n = IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det •
      (genMat R n).adjugate.map (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) := by
    ext a b
    simp [genericMatrixInverse, Matrix.smul_apply]
  rw [e, genericMatrixRootWeights, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp [Matrix.smul_apply, Matrix.one_apply, hab]

private theorem map_C_genericMatrixBis_and_inverse_eq_gL_gLinv (R : Type) [Field R] (n : ℕ) :
    (genericMatrixRootWeights R n).map LaurentPolynomial.C = gL R n ∧ (genericMatrixInverse R n).map LaurentPolynomial.C = gLinv R n := by
  constructor <;> (ext a b; simp [genericMatrixRootWeights, genericMatrixInverse, gL, gLinv])

private theorem support_laurent_C_mul_T_of_ne_zero {B : Type*} [CommRing B] (h : B) (hh : h ≠ 0) (w : ℤ) :
    (LaurentPolynomial.C h * LaurentPolynomial.T w).coeff.support = {w} := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
  exact Finsupp.support_single_ne_zero _ hh

private theorem laurent_C_mul_T_eq_zero_iff {B : Type*} [CommRing B] (h : B) (w : ℤ) :
    LaurentPolynomial.C h * LaurentPolynomial.T w = 0 ↔ h = 0 := by
  constructor
  · intro e
    have := congrArg (fun p : LaurentPolynomial B => p.coeff w) e
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single] at this
    simpa using this
  · rintro rfl
    simp

theorem twist_exponents_are_weight_entries : TwistExponentsAreWeightEntries := by
  intro R _ ι _ LL n S j G
  classical
  let u : (GLLaurent R n)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  let D : Fin n → (GLLaurent R n)ˣ := fun a => if a = j then u else 1
  have hD : (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n)) =
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T 1 else 1) := by
    congr 1; funext a; by_cases h : a = j <;> simp [D, h, u]
  have hD' : (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n)) =
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T (-1) else 1) := by
    congr 1; funext a; by_cases h : a = j <;> simp [D, h, u]
  obtain ⟨hgL, hgLinv⟩ := map_C_genericMatrixBis_and_inverse_eq_gL_gLinv R n
  have hcoefL : (LaurentPolynomial.C).comp (coefficientMap R n) = coefL R n := rfl
  have hH : MvPolynomial.map LaurentPolynomial.C (genericTranslate LL S G) =
      matrixSubst LL S (coefL R n) (gLinv R n) (gL R n) G := by
    rw [genericTranslate, map_matrixSubst, hgL, hgLinv, hcoefL]
  have hT : twistSub LL S j G = matrixSubst LL S (RingHom.id _) (gL R n) (gLinv R n)
      (matrixSubst LL S (RingHom.id _) (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n))
        (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n))
        (MvPolynomial.map LaurentPolynomial.C (genericTranslate LL S G))) := by
    rw [hH, hD, hD', matrixSubst_comp, matrixSubst_comp, twistSub_eq_matrixSubst]
    simp only [twistMat, Matrix.mul_assoc]
  have hprod : ∀ w : Fin n → ℤ, (((∏ a, D a ^ w a) : (GLLaurent R n)ˣ) : GLLaurent R n) =
      LaurentPolynomial.T (w j) := by
    intro w
    rw [Finset.prod_eq_single j (fun a _ ha => by simp [D, ha]) (fun h => absurd (Finset.mem_univ j) h)]
    simp only [D, if_pos rfl]
    rcases w j with k | k
    · rw [Int.ofNat_eq_coe, zpow_natCast, Units.val_pow_eq_pow_val]
      simp only [u, LaurentPolynomial.T_pow, mul_one]
    · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      simp only [u, Units.inv_mk, LaurentPolynomial.T_pow]
      congr 1
      rw [Int.negSucc_eq]
      push_cast
      ring
  set H := genericTranslate LL S G with hHdef
  set P := matrixSubst LL S (RingHom.id _) (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n))
        (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n))
        (MvPolynomial.map LaurentPolynomial.C H) with hPdef
  have hcoef : ∀ m, P.coeff m = LaurentPolynomial.C (H.coeff m) * LaurentPolynomial.T (wtS LL S m j) := by
    intro m
    rw [hPdef]
    conv_lhs => rw [H.as_sum]

    simp only [map_sum, MvPolynomial.map_monomial,
    torus_acts_through_weight (GLLaurent R n) (GLLaurent R n) ι LL n S (RingHom.id _) D, RingHom.id_apply, hprod,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [MvPolynomial.notMem_support_iff.mp hm]
      simp
  have hsupp : P.support = H.support := by
    ext m
    rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, hcoef, Ne, laurent_C_mul_T_eq_zero_iff]
  show mul_degs (twistSub LL S j G) = _
  rw [hT, ← hgL, ← hgLinv, laurent_degrees_substitution_eq LL S (genericMatrixRootWeights R n) (genericMatrixInverse R n) (genericMatrixBis_mul_genericMatrixInverse R n)]
  rw [mul_degs, hsupp, ← Finset.biUnion_singleton]
  apply Finset.biUnion_congr rfl
  intro m hm
  rw [hcoef]
  exact support_laurent_C_mul_T_of_ne_zero _ (MvPolynomial.mem_support_iff.mp hm) _

end Formalism.MainNotions.G.GLWeightTheory
end
end
