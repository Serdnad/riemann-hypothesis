module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.UCls.KGrp
open scoped ENNReal TensorProduct

theorem GlobalTheory.UCls.exists_special_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ L : Submodule (𝓞 E) (Fin r → E)) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (S : Finset (Fin m)) (Γ : Fin m → Subgroup (GL (Fin r) E)) (Λi : Fin m → Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) → (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, (Λi i : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ ∀ γ, γ ∈ Γ i ↔ IsUStab G (Λi i) γ ∧ ∀ x ∈ Λi i, ∃ y ∈ Λi i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) → ∃ (γ : Fin m → GL (Fin r) E) (s : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), (∀ i ∈ S, (∀ u v, herm G ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) ∧ IsSA G (s i) ∧ ∀ δ : GL (Fin r) E, (δ : Matrix (Fin r) (Fin r) E).det = 1 → (∀ u v, herm G ((δ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → (δ ∈ (Γ i).map (MulAut.conj (γ i)⁻¹).toMonoidHom ↔ IsKM (IsCMField.complexConj E) G (L : Set (Fin r → E)) M ((s i)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) * s i))) ∧ ∀ i ∈ S, ∀ j ∈ S, SEquiv G (L : Set (Fin r → E)) M (s i) (s j) → UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) := by
  intro E _ _ _ r M m G Λ L g g0 S Γ Λi hM hΛ hg0 hL hLhat hg hT hΓ
  have hU : ∀ {γ : GL (Fin r) E}, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) → ∀ x y,
      herm G (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
        (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y := by
    intro γ hγ x y
    rw [← hγ, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]
  have hRA : ∀ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) →
      IsUA (IsCMField.complexConj E) G (ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E)) :=
    fun γ hγ => GlobalTheory.T.isInvertibleUnitaryAdelicMatrix_of_rational_unitary E r G _ (Matrix.isUnits_det_units γ).ne_zero hγ
  have hR1 : ∀ γ : GL (Fin r) E, ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) *
      ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 := fun γ => by
    rw [← ratM_mul, Units.mul_inv, ratM_one]
  have hR2 : ∀ γ : GL (Fin r) E, ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
      ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) = 1 := fun γ => by
    rw [← ratM_mul, Units.inv_mul, ratM_one]
  have hdet : ∀ γ : Matrix (Fin r) (Fin r) E, (ratM (maximalRealSubfield E) γ).det =
      (1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ γ.det := fun γ =>
    (RingHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[maximalRealSubfield E]
      RA (maximalRealSubfield E) E).toRingHom γ).symm
  have hex : ∀ i, ∃ (γ : GL (Fin r) E) (k : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), i ∈ S →
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧
      IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M k ∧
      IsSA G (ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i * k⁻¹ * g0⁻¹) := by
    intro i
    by_cases hi : i ∈ S
    swap
    · exact ⟨1, 1, fun h => absurd h hi⟩
    obtain ⟨u, hu, k, hk, hdg⟩ := hT i hi
    obtain ⟨γ, hγ, hγdet⟩ : ∃ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
        ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧ (0 < r → (γ : Matrix (Fin r) (Fin r) E).det = u) := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · exact ⟨1, fun x y => by simp, fun h => absurd h (by omega)⟩
      · obtain ⟨γ, h1, h2⟩ := GlobalTheory.T.exists_unitary_with_determinant E r G u hr hΛ.1 hΛ.2.1 hu
        exact ⟨γ, h1, fun _ => h2⟩
    refine ⟨γ, k, fun _ => ⟨hγ, hk, ?_, ?_⟩⟩
    · exact isUA_mul _ G (isUA_mul _ G (isUA_mul _ G (hRA _ (hU hγ)) (hg i)) (isUA_inv _ G hk.1))
        (isUA_inv _ G hg0)
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simp
      · have hγ1 : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det * u = 1 := by
          rw [← hγdet hr, ← det_mul, Units.inv_mul, det_one]
        have e1 : ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det : RA (maximalRealSubfield E) E) *
            ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ u) = 1 := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hγ1, Algebra.TensorProduct.one_def]
        have e2 := Ring.mul_inverse_cancel _ hg0.1
        have e3 := Ring.mul_inverse_cancel _ hk.1.1
        rw [det_mul, det_mul, det_mul, det_nonsing_inv, det_nonsing_inv, hdet, hdg]
        calc _ = (((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det : RA (maximalRealSubfield E) E) *
            ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ u)) *
            (g0.det * Ring.inverse g0.det) * (k.det * Ring.inverse k.det) := by ring
          _ = 1 := by rw [e1, e2, e3, one_mul, one_mul]
  choose γ k hγk using hex

  refine ⟨γ, fun i => ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
    (k i)⁻¹ * g0⁻¹, ?_, ?_⟩
  · intro i hi
    obtain ⟨hγU, hk, hsSA⟩ := hγk i hi
    refine ⟨hγU, hsSA, fun δ hδdet hδU => ?_⟩
    have hmap : δ ∈ (Γ i).map (MulAut.conj (γ i)⁻¹).toMonoidHom ↔ γ i * δ * (γ i)⁻¹ ∈ Γ i := by
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    obtain ⟨hΛi, hΓi⟩ := hΓ i hi
    have hgU : IsUnit (g i) := (Matrix.isUnit_iff_isUnit_det _).2 (hg i).1
    obtain ⟨Λ', hΛ'1, -, -, hΛ'hat⟩ := exists_lattice_latOf (maximalRealSubfield E) E r Λ hgU.unit
      hΛ.2.2.1 hΛ.2.2.2.1
    rw [IsUnit.unit_spec] at hΛ'1 hΛ'hat
    have hhat : (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) =
        (g i).mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set _) := by
      rw [hΛi, ← hΛ'1, hΛ'hat]
    have hrat : ∀ v, fv (maximalRealSubfield E) v ∈ hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) ↔
        v ∈ Λi i := fun v => by
      rw [← SetLike.mem_coe, hhat, ← SetLike.mem_coe (x := v), hΛi]; rfl
    have hβU : ∀ x y, herm G (((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
        (((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y := by
      intro x y
      simp only [Units.val_mul, ← mulVec_mulVec, hγU, hδU, hU hγU]
    have e0 : g0 * g0⁻¹ = 1 := mul_nonsing_inv g0 hg0.1
    have e0' : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
    have ek : k i * (k i)⁻¹ = 1 := mul_nonsing_inv _ hk.1.1
    have ek' : (k i)⁻¹ * k i = 1 := nonsing_inv_mul _ hk.1.1
    have eg : g i * (g i)⁻¹ = 1 := mul_nonsing_inv _ (hg i).1
    have eg' : (g i)⁻¹ * g i = 1 := nonsing_inv_mul _ (hg i).1
    have c0 : ∀ P, P * g0 * g0⁻¹ = P := fun P => by rw [Matrix.mul_assoc, e0, Matrix.mul_one]
    have c0' : ∀ P, P * g0⁻¹ * g0 = P := fun P => by rw [Matrix.mul_assoc, e0', Matrix.mul_one]
    have ck : ∀ P, P * k i * (k i)⁻¹ = P := fun P => by rw [Matrix.mul_assoc, ek, Matrix.mul_one]
    have ck' : ∀ P, P * (k i)⁻¹ * k i = P := fun P => by rw [Matrix.mul_assoc, ek', Matrix.mul_one]
    have cg : ∀ P, P * g i * (g i)⁻¹ = P := fun P => by rw [Matrix.mul_assoc, eg, Matrix.mul_one]
    have cg' : ∀ P, P * (g i)⁻¹ * g i = P := fun P => by rw [Matrix.mul_assoc, eg', Matrix.mul_one]
    have cR : ∀ P, P * ratM (maximalRealSubfield E) (γ i : Matrix (Fin r) (Fin r) E) *
        ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = P := fun P => by
      rw [Matrix.mul_assoc, hR1, Matrix.mul_one]
    have hXY : (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) =
        (g i * (k i)⁻¹ * g0⁻¹).mulVec '' (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) := by
      rw [hhat, ← isKM_image _ G _ M (_root_.GlobalTheory.UCls.KGrp.isKM_inv _ G _ M hk), Set.image_image, hLhat, Set.image_image]
      simp only [mulVec_mulVec, c0']
    have hsinv : (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)⁻¹ = g0 * k i * (g i)⁻¹ * ratM (maximalRealSubfield E) (γ i : Matrix (Fin r) (Fin r) E) := by
      refine Matrix.inv_eq_left_inv ?_
      simp only [← Matrix.mul_assoc, cR, cg', ck, e0]
    have hconj := hatKM_conj (X := (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set _))
      (Y := (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E))) M
      (A := g i * (k i)⁻¹ * g0⁻¹) (A' := g0 * k i * (g i)⁻¹)
      (P := ratM (maximalRealSubfield E) ((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))
      (by simp only [← Matrix.mul_assoc, c0', ck', eg]) (by simp only [← Matrix.mul_assoc, cg', ck, e0]) hXY
    have hPeq : g0 * k i * (g i)⁻¹ * ratM (maximalRealSubfield E)
        ((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (g i * (k i)⁻¹ * g0⁻¹) =
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) *
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹) := by
      rw [hsinv, Units.val_mul, Units.val_mul, ratM_mul, ratM_mul]
      simp only [Matrix.mul_assoc]
    rw [hPeq] at hconj
    have hsUA := hsSA.1
    have hKUA : IsUA (IsCMField.complexConj E) G ((ratM (maximalRealSubfield E)
        (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i * (k i)⁻¹ * g0⁻¹)⁻¹ *
        ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) *
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)) :=
      isUA_mul _ G (isUA_mul _ G (isUA_inv _ G hsUA) (hRA δ hδU)) hsUA
    have hL5 := GlobalTheory.T.lattice_congruence_iff_completion (maximalRealSubfield E) E r (Λi i) M (γ i * δ * (γ i)⁻¹) hM hrat
    rw [hmap, hΓi]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨hKUA, hconj.1 (hL5.1 ⟨h1, h2⟩)⟩
    · intro hK
      obtain ⟨h1, h2⟩ := hL5.2 (hconj.2 hK.2)
      exact ⟨⟨hβU, h1⟩, h2⟩

  · intro i hi j hj hSE
    obtain ⟨δ, hδ, κ, hκ, -, hsj⟩ := hSE
    simp only at hsj
    obtain ⟨hγiU, hki, -⟩ := hγk i hi
    obtain ⟨hγjU, hkj, -⟩ := hγk j hj
    have e0' : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
    have ekj : k j * (k j)⁻¹ = 1 := mul_nonsing_inv _ hkj.1.1
    have egj : g j * (g j)⁻¹ = 1 := mul_nonsing_inv _ (hg j).1
    refine ⟨(γ j : Matrix (Fin r) (Fin r) E) * δ * (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E), ?_,
      (k i)⁻¹ * (g0⁻¹ * κ * g0) * k j, ?_, ?_⟩
    · rw [ratM_mul, ratM_mul]
      exact isUA_mul _ G (isUA_mul _ G (hRA _ hγjU) hδ.1) (hRA _ (hU hγiU))
    · exact _root_.GlobalTheory.UCls.KGrp.isKM_mul _ G _ M (_root_.GlobalTheory.UCls.KGrp.isKM_mul _ G _ M (_root_.GlobalTheory.UCls.KGrp.isKM_inv _ G _ M hki) (isKM_conj _ G _ _ M hg0 hLhat hκ)) hkj
    · have hdj : g j = ratM (maximalRealSubfield E) (γ j : Matrix (Fin r) (Fin r) E) *
          (ratM (maximalRealSubfield E) (((γ j)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g j *
            (k j)⁻¹ * g0⁻¹) * g0 * k j := by
        simp only [← Matrix.mul_assoc, hR1 (γ j), Matrix.one_mul]
        rw [Matrix.mul_assoc (g j * (k j)⁻¹), e0', Matrix.mul_one, Matrix.mul_assoc, nonsing_inv_mul _ hkj.1.1,
          Matrix.mul_one]
      rw [hdj, hsj, ratM_mul, ratM_mul]
      simp only [Matrix.mul_assoc]
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem exists_nontriv_family : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite N.hom → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → i ≠ 1 → ∃ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB ∧ IsAdditive M ∧ Triv (ev M (fst A T ≫ q) (snd A T)) ∧ ¬ Triv M := by
  intro K _ _ A A' N _ _ _ i q hA hA' hi hq hNf hqf hqfl hqs hker hi1
  have hmono : Mono i := hker.mono_fst_of_mono
  have hcomm : IsCommMonObj A := hA.comm
  have : IsCommMonObj N := AbelianSubgroupFinite.isCommMonObj_of_mono i
  have hN1 : 𝟙 N ≠ (1 : N ⟶ N) := by
    intro h
    apply hi1
    rw [← Category.id_comp i, h, MonObj.one_comp]
  obtain ⟨T, χ, hχ, hne⟩ := GlobalTheory.T.exists_nontrivial_character_finite_comm_group K N hNf hN1
  obtain ⟨M, e, hM, he⟩ := GlobalTheory.T.exists_descended_lineBundle_equivariantGenerator _ A A' N T i q χ hi hq hqf hqfl hqs hker hχ
  exact ⟨T, M, hM, GlobalTheory.T.characterLineBundle_additive_of_equivariantGenerator K A A' N T i q χ M e hA hA' hi hq hqf hqfl hqs hker hχ hM he,
    GlobalTheory.T.cechTrivial_pullback_of_isPullbackGenerator _ _ _ M e he.1, fun h => hne (GlobalTheory.T.character_eq_one_of_descended_lineBundle_trivial K A A' N T i q χ M e hA hq hker hM he h)⟩

end GlobalTheory.CharKer
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.additive_lineBundle_descends_along_isogeny_torsor : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q → Triv (ev P (fst N B ≫ i) (snd N B)) → ∃ P₀ : LB (A' ⊗ B).left, P₀.IsLB ∧ LBIso (ev P₀ (fst A B ≫ q) (snd A B)) P := by
  first | exact @GlobalTheory.PoincareDescent.descend_torsor | exact GlobalTheory.PoincareDescent.descend_torsor | (intros; apply GlobalTheory.PoincareDescent.descend_torsor <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormOrdFinite

theorem exists_isFrame_genericPoint {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    [IsIntegral X] (p : X ⟶ Sp k) [LocallyOfFiniteType p] (n : ℕ)
    (hn : topologicalKrullDim X = n) :
    ∃ (U : X.Opens) (ω : FormsOn p n U), genericPoint X ∈ U ∧ IsFrame ω := by
  obtain ⟨V, hV, hgV, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X) (U := ⊤) trivial
  haveI : Nonempty V := ⟨⟨_, hgV⟩⟩
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).toAlgebra
  have h1 : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).FiniteType :=
    (p.finiteType_appLE (isAffineOpen_top _) hV _).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  haveI : Algebra.FiniteType k Γ(X, V) := h1
  have hd : ringKrullDim Γ(X, V) = n := by
    have h2 := GlobalTheory.OpenDim.topologicalKrullDim_open k p V ⟨_, hgV⟩
    rw [hn] at h2
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← h2]
    exact (topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec).symm
  obtain ⟨s, hs, hsm⟩ := GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
    (K := k) (A := Γ(X, V)) hd
  have hloc := hV.isLocalization_basicOpen s
  have h₁ : (algebraMap k (Localization.Away s)).IsStandardSmoothOfRelativeDimension n :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2 hsm
  have h₂ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
      Γ(X, X.basicOpen s)).toRingEquiv h₁
  have e : ((IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
      Γ(X, X.basicOpen s)).toRingEquiv.toRingHom.comp (algebraMap k (Localization.Away s))) =
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (X.basicOpen s) := by
    rw [← resG_comp_algX p (X.basicOpen_le s)]
    ext a
    simp [IsScalarTower.algebraMap_apply k Γ(X, V) (Localization.Away s)]
    rfl
  rw [e] at h₂
  obtain ⟨ω, hω⟩ := GlobalTheory.TopForm.exists_isFreeGen h₂
  have hne : X.basicOpen s ≠ ⊥ := fun h => hs ((AlgebraicGeometry.basicOpen_eq_bot_iff s).1 h)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  exact ⟨X.basicOpen s, ω, gen_mem hx, hV.basicOpen s, hω⟩

theorem finite_setOf_formOrd_ne_zero : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ η : RatForms p n, η ≠ 0 → {z : X | ∃ E : DivOver p, E.IsAt z ∧ (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η ≠ 0}.Finite := by
  intro k _ _ X _ _ _ p n hp hn η hη
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  obtain ⟨U, ω, hU, hω⟩ := exists_isFrame_genericPoint p n hn
  have hgen := isFreeGen_formOf hU hω
  have h0 : formOf U hU ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨c, hc⟩ := hgen.2 η
  replace hc : c • formOf U hU ω = η := hc
  have hc0 : c ≠ 0 := fun h => hη (by rw [← hc, h, zero_smul])
  obtain ⟨W, hW, hWu⟩ := (unitAt_genericPoint hc0).exists_nhds
  let B : Closeds X := ⟨((U ⊓ W : X.Opens) : Set X)ᶜ, (U ⊓ W).isOpen.isClosed_compl⟩
  have hB : B ≠ ⊤ := fun h => by
    have hm : genericPoint X ∈ (B : Set X) := by rw [h]; trivial
    exact hm ⟨hU, hW⟩
  refine (GlobalTheory.T.finite_codim_one_points_closed X B hB).subset ?_
  rintro z ⟨E, hE, hne⟩
  refine ⟨hE.coheight_eq_one, fun hz => hne ?_⟩
  obtain ⟨hzU, hzW⟩ := hz
  obtain ⟨a, ha, e⟩ := hWu z hzW
  have hord : E.ord (Units.mk0 c hc0) = 0 :=
    E.ord_eq_zero (u := hE.equiv a) (ha.map hE.equiv) e
  have h1 := E.formOrd_smul hn h0 (Units.mk0 c hc0)
  rw [Units.val_mk0, hc, hord, DivOver.formOrd_formOf_eq_zero hzU hE hω] at h1
  change E.formOrd η = 0
  simpa using h1

end GlobalTheory.FormOrdFinite
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ : X → ℚ) (η : RatForms p n) (x : X) (m : ℕ) (g : X.functionFieldˣ), η ≠ 0 → 0 < m → IsLogEqn p Γ η x m g → (LcAt p n Γ x ↔ ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g) := by
  first | exact @GlobalTheory.PairStep.lcAt_iff_of_isLogEqn | exact GlobalTheory.PairStep.lcAt_iff_of_isLogEqn | (intros; apply GlobalTheory.PairStep.lcAt_iff_of_isLogEqn <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem isLogEqn_changeForm_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (η η' : RatForms p n) (x : X) (m mD l : ℕ)
    (gG fD g a F : X.functionFieldˣ) (A : CartierDiv X) (δ t : ℚ), η' ≠ 0 → η = (F : X.functionField) • η' →
    0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) → A.IsEqn x a →
    ∃ (m₂ : ℕ) (g₂ : X.functionFieldˣ), 0 < m₂ ∧
      IsLogEqn p (Δ + (1 - δ) • D + t • qWeil (CartierDiv.principal g + l • A) 1) η' x m₂ g₂ ∧
      ∀ E : DivOver p, discrep E η' m₂ g₂ = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η' + E.ord F - E.ord gG / m
        - (1 - δ) * (E.ord fD / mD) - t * E.ord (g * a ^ l) := by
  intro X _ _ p _ n hn Δ D η η' x m mD l gG fD g a F A δ t hη' hηF hm hmD hg hD hA
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'

  set gG' : X.functionFieldˣ := gG * F ^ (-(m : ℤ)) with hgG'
  have hord (E : DivOver p) : (E.ord gG' : ℚ) = E.ord gG - m * E.ord F := by
    rw [hgG', E.ord_mul, divOver_ord_zpow]
    push_cast
    ring
  have h1 : IsLogEqn p Δ η' x m gG' := by
    intro z hz E hE
    have e := hg z hz E hE
    rw [hηF, E.formOrd_smul hn hη' F] at e
    rw [hord, ← e]
    push_cast
    ring
  have hd1 (E : DivOver p) : discrep E η' m gG' = E.formOrd η' + E.ord F - E.ord gG / m := by
    rw [discrep, hord]
    field_simp
    ring

  obtain ⟨m₁, g₁, hm₁, h2, hd2⟩ := isLogEqn_add_smul X p n Δ D η' x m mD gG' fD (1 - δ) hm hmD h1 hD

  have hB : (CartierDiv.principal g + l • A).IsEqn x (g * a ^ l) :=
    (CartierDiv.isEqn_principal g x).add (hA.nsmul l)
  obtain ⟨V, hxV, hV⟩ := hB.exists_nhds
  have hD' : ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z →
      qWeil (CartierDiv.principal g + l • A) 1 z = (E.ord (g * a ^ l) : ℚ) / (1 : ℕ) := by
    intro z hz E hE
    rw [qWeil, (hV z (hz.mem_open V.isOpen hxV)).mult_eq, ← hE.ord_eq]
  obtain ⟨m₂, g₂, hm₂, h3, hd3⟩ := isLogEqn_add_smul X p n (Δ + (1 - δ) • D)
    (qWeil (CartierDiv.principal g + l • A) 1) η' x m₁ 1 g₁ (g * a ^ l) t hm₁ Nat.one_pos h2 hD'
  refine ⟨m₂, g₂, hm₂, h3, fun E => ?_⟩
  rw [hd3, hd2, hd1]
  unfold DivOver.formOrd
  push_cast
  ring

end GlobalTheory.PairStep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ D : X → ℚ) (η : RatForms p n) (x : X) (m m' : ℕ) (g f : X.functionFieldˣ) (c : ℚ), 0 < m → 0 < m' → IsLogEqn p Γ η x m g → (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m') → ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + c • D) η x m'' g'' ∧ ∀ E : DivOver p, discrep E η m'' g'' = discrep E η m g - c * ((E.ord f : ℚ) / m') := by
  first | exact @GlobalTheory.PairStep.isLogEqn_add_smul | exact GlobalTheory.PairStep.isLogEqn_add_smul | (intros; apply GlobalTheory.PairStep.isLogEqn_add_smul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ : X → ℚ) (x z : X), z ⤳ x → (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) := by
  first | exact @GlobalTheory.Discrepancy.kltAt_lcAt_generisation | exact GlobalTheory.Discrepancy.kltAt_lcAt_generisation | (intros; apply GlobalTheory.Discrepancy.kltAt_lcAt_generisation <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.regular_at_normal_point_of_divisors : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) → ∀ f : X.functionField, (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → f ∈ E.ring) → RegAt y f := by
  first | exact @GlobalTheory.Discrepancy.regAt_of_isIntegrallyClosed_stalk | exact GlobalTheory.Discrepancy.regAt_of_isIntegrallyClosed_stalk | (intros; apply GlobalTheory.Discrepancy.regAt_of_isIntegrallyClosed_stalk <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

theorem _root_.GlobalTheory.T.primeDivisorOver_ord_eq_sum_adaptedMonomial : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [GlobalTheory.IsNormalScheme Y] {q : Y ⟶ Sp k} (E : DivOver q) (y : Y), E.Through y →
    ∀ {ι : Type} [Fintype ι] (w : ι → Y) (u : ι → Y.functionFieldˣ), Function.Injective w →
    (∀ j, w j ⤳ y) → (∀ j, Order.coheight (w j) = 1) →
    (∀ j, Scheme.ord (u j : Y.functionField) (w j) = 1) →
    (∀ j v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0) →
    ∀ φ : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j, v ≠ w j) → Scheme.ord (φ : Y.functionField) v = 0) →
      E.ord φ = ∑ j, Scheme.ord (φ : Y.functionField) (w j) * E.ord (u j) := by
  first | exact @GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial | exact GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial | (intros; apply GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial <;> assumption)
end
