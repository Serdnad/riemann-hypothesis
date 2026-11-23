module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle001
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.MvPolynomial.Localization

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericFibreDrop.proof : GenericFibreDrop.Statement := by
  intro O _ _ _ F _ _ _ n P P' f hP hP'C hfP hP'
  let A := MvPolynomial (Fin n) O
  let T := MvPolynomial (Fin n) F
  let M : Submonoid A := (nonZeroDivisors O).map (C : O →+* A)
  have hφ : (algebraMap A T) = MvPolynomial.map (algebraMap O F) := rfl
  have : IsLocalization M T := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hP'p : P'.IsPrime := hP'.1.1
  have hPP' : P ≤ P' := le_sup_left.trans hP'.1.2
  have hfP' : f ∈ P' := hP'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hdisj' : Disjoint (M : Set A) (P' : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨o, ho, rfl⟩ hmem
    have h1 : o ∈ P'.comap (C : O →+* A) := hmem
    rw [hP'C, Ideal.mem_bot] at h1
    exact nonZeroDivisors.ne_zero ho h1
  have hdisj : Disjoint (M : Set A) (P : Set A) :=
    Set.disjoint_of_subset_right hPP' hdisj'

  let I : Ideal T := P.map (algebraMap A T)
  let I' : Ideal T := P'.map (algebraMap A T)
  have hI : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T P hP hdisj
  have hI' : I'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T P' hP'p hdisj'
  have hII' : I ≤ I' := Ideal.map_mono hPP'

  let Q : Ideal (A ⧸ P) := P'.map (Ideal.Quotient.mk P)
  have hQ : Q.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hQne : Q ≠ ⊥ := by
    intro h
    have h1 : Ideal.Quotient.mk P f ∈ Q := Ideal.mem_map_of_mem _ hfP'
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact hfP h1
  have hQ1 : Q.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hP') ?_
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hQne)
    simpa using this

  let M' : Submonoid (A ⧸ P) := Algebra.algebraMapSubmonoid (A ⧸ P) M
  have hQdisj : Disjoint (M' : Set (A ⧸ P)) (Q : Set (A ⧸ P)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have h1 : Ideal.Quotient.mk P a ∈ Q := hmem
    rw [Ideal.mem_quotient_iff_mem hPP'] at h1
    exact Set.disjoint_left.1 hdisj' ha h1
  have hh := IsLocalization.height_map_of_disjoint (S := T ⧸ I) M' Q hQdisj
  have hmap : Q.map (algebraMap (A ⧸ P) (T ⧸ I)) = I'.map (Ideal.Quotient.mk I) := by
    simp only [Q, I', Ideal.map_map]
    rfl
  rw [hmap, hQ1] at hh
  have _ : (I'.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

  have key := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F)
    (I'.map (Ideal.Quotient.mk I))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hII')] at key
  show ringKrullDim (T ⧸ I) = ringKrullDim (T ⧸ I') + 1
  rw [← key, add_comm]
  rfl

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section NumberField

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def parPrime (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : Ideal (MvPolynomial (Par e n) (𝓞 K)) :=
  Ideal.map C v.asIdeal

instance parPrime_isPrime (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : (parPrime e n v).IsPrime := by
  have h : parPrime e n v = RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk v.asIdeal) :
      MvPolynomial (Par e n) (𝓞 K) →+* MvPolynomial (Par e n) (𝓞 K ⧸ v.asIdeal)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
    rfl
  rw [h]
  exact RingHom.ker_isPrime _

abbrev ParDVR (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  Localization.AtPrime (parPrime e n v)

instance parDVR_isDomain (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : IsDomain (ParDVR e n v) :=
  IsLocalization.isDomain_of_atPrime _ (parPrime e n v)

def parY (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : Par e n → ParDVR e n v :=
  fun p => algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (X p)

def modelR (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    Ideal (MvPolynomial (Fin n) (ParDVR e n v)) :=
  (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))

abbrev SecB (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  SecAlg (modelR e I v) (parY e n v)

abbrev ParFrac (K : Type*) [Field K] [NumberField K] (e n : ℕ) : Type _ :=
  FractionRing (MvPolynomial (Par e n) (𝓞 K))

def parToFrac (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : ParDVR e n v →+* ParFrac K e n :=
  IsLocalization.lift (M := (parPrime e n v).primeCompl) (g := algebraMap _ (ParFrac K e n))
    fun s => IsUnit.mk0 _ fun h => (s.2 : (s : MvPolynomial (Par e n) (𝓞 K)) ∉ parPrime e n v)
      (by rw [(IsFractionRing.injective _ (ParFrac K e n)) (h.trans (map_zero _).symm)]
          exact Ideal.zero_mem _)

theorem intToFrac_injective (K : Type*) [Field K] [NumberField K] (e n : ℕ) :
    Function.Injective ((algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp C) := by
  simp only [RingHom.coe_comp]
  exact (IsFractionRing.injective _ _).comp (MvPolynomial.C_injective _ _)

def kToFrac (K : Type*) [Field K] [NumberField K] (e n : ℕ) : K →+* ParFrac K e n :=
  IsFractionRing.lift (intToFrac_injective K e n)

def parYF (K : Type*) [Field K] [NumberField K] (e n : ℕ) : Par e n → ParFrac K e n :=
  fun p => algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (X p)

def idealF (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) :
    Ideal (MvPolynomial (Fin n) (ParFrac K e n)) :=
  I.map (MvPolynomial.map (kToFrac K e n))

def specComps (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    Set (Ideal (MvPolynomial (Fin n) (𝓞 K))) :=
  relComps (integralModel I ⊔ Ideal.map C v.asIdeal)

def secIdealOf (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) : Ideal (SecB e I v) :=
  (W.map (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))).map (Ideal.Quotient.mk _)

def vertDeg (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  ∑ᶠ W ∈ vertComps I u v,
    GroundTheory.Heights₂.Heights.localMult
      (integralModel I ⊔ Ideal.span {linForm u}) W * chowDegree (reduceMod v W) (e + 1)

end NumberField

def ParDVRIsDVR.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    IsDiscreteValuationRing (ParDVR e n v)

def ParAlgIndep.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ),
    letI := (kToFrac K e n).toAlgebra
    AlgebraicIndependent K (parYF K e n)

def GaussDVR.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (g : MvPolynomial (Par e n) (𝓞 K)), g ≠ 0 →
      gaussNorm v (g.map (algebraMap (𝓞 K) K)) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (Ring.ord (ParDVR e n v) (algebraMap _ _ g)).toNat = 1

def PrimitiveScale.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (σ : Type)
    (f : MvPolynomial σ K), f ≠ 0 →
      ∃ (c : K) (g : MvPolynomial σ (𝓞 K)), c ≠ 0 ∧ g.map (algebraMap (𝓞 K) K) = C c * f ∧
        ∃ m, g.coeff m ∉ v.asIdeal

def SecBFinite.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → Module.Finite (ParDVR e n v) (SecB e I v)

def SecBTorsionFree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∀ (r : ParDVR e n v) (b : SecB e I v), r ≠ 0 → r • b = 0 → b = 0

def SecBGeneric.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∃ φ : SecB e I v →+* SecAlg (idealF e I) (parYF K e n),
        (∀ j, φ (secCoord _ _ j) = secCoord _ _ j) ∧
        (∀ r : ParDVR e n v, φ (algebraMap _ _ r) = algebraMap _ _ (parToFrac e n v r)) ∧
        letI := φ.toAlgebra
        IsLocalization (Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)))
          (SecAlg (idealF e I) (parYF K e n))

def SecBLinInj.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      Function.Injective fun b : SecB e I v =>
        secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) * b

def SpecMax.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f →
      (∀ W ∈ specComps I v, (secIdealOf e I v W).IsMaximal) ∧
        ∀ 𝔫 : Ideal (SecB e I v), 𝔫.IsMaximal → ∃! W, W ∈ specComps I v ∧ secIdealOf e I v W = 𝔫


open Classical in
def SpecLength.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      ∀ 𝔫 : MaximalSpectrum (SecB e I v), ∀ W ∈ specComps I v, secIdealOf e I v W = 𝔫.asIdeal →
        Ring.ord (Localization.AtPrime 𝔫.asIdeal)
            (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
              (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)))) =
          (letI : Decidable (linForm u ∈ W) := Classical.propDecidable _
           if linForm u ∈ W then
             (GroundTheory.Heights₂.Heights.localMult
               (integralModel I ⊔ Ideal.span {linForm u}) W : ℕ∞) else 0)

def SpecResidue.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      Module.length (ParDVR e n v) (SecB e I v ⧸ secIdealOf e I v W) = chowDegree (reduceMod v W) (e + 1)

def VertSpec.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      vertComps I u v = {W | W ∈ specComps I v ∧ linForm u ∈ W}

def NormIdentity.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) →
    linForm (fun j => (u j : K)) ∉ I → (∃ m, g.coeff m ∉ v.asIdeal) →
      ∃ w : (ParDVR e n v)ˣ,
        algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename Sum.inl (specFirst g u)) =
          w * Algebra.norm (ParDVR e n v)
            (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)))

def OrdEq.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) →
    linForm (fun j => (u j : K)) ∉ I → (∃ m, g.coeff m ∉ v.asIdeal) →
      Ring.ord (ParDVR e n v)
          (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename Sum.inl (specFirst g u))) =
        vertDeg e I u v

def VertTermEq.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
      GroundTheory.Heights₂.Heights.vertTermAt I (e + 1) u v =
        vertDeg e I u v * Real.log (Ideal.absNorm v.asIdeal)

def GaussEq.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) →
    linForm (fun j => (u j : K)) ∉ I → (∃ m, g.coeff m ∉ v.asIdeal) →
      gaussNorm v (specFirst (g.map (algebraMap (𝓞 K) K)) fun j => (u j : K)) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ vertDeg e I u v = 1 ∧
        gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial TensorProduct

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

section Basis

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

def polyTensorAlgEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₐ[R] MvPolynomial (Fin n) A :=
  (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R) A).trans
    ((algebraTensorAlgEquiv R A).restrictScalars R)

theorem polyTensorAlgEquiv_tmul (p : MvPolynomial (Fin n) R) (a : A) :
    polyTensorAlgEquiv R A n (p ⊗ₜ a) = a • MvPolynomial.map (algebraMap R A) p := by
  simp [polyTensorAlgEquiv]

def polyTensorEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₗ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A where
  toFun := polyTensorAlgEquiv R A n
  invFun := (polyTensorAlgEquiv R A n).symm
  map_add' := map_add _
  left_inv := (polyTensorAlgEquiv R A n).symm_apply_apply
  right_inv := (polyTensorAlgEquiv R A n).apply_symm_apply
  map_smul' q t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p a =>
      rw [smul_tmul', smul_eq_mul, polyTensorAlgEquiv_tmul, polyTensorAlgEquiv_tmul, RingHom.id_apply,
        Algebra.smul_def q, MvPolynomial.algebraMap_def, map_mul, mul_smul_comm]
    | add s t hs ht =>
      rw [smul_add, map_add (f := _), map_add (f := _), hs, ht, smul_add]

def polyBasis {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) :
    Module.Basis ι (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
  (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map (polyTensorEquiv R A n)

theorem polyBasis_apply {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) (i : ι) :
    polyBasis b n i = C (b i) := by
  simp [polyBasis, polyTensorEquiv, Algebra.TensorProduct.basis_apply, polyTensorAlgEquiv_tmul,
    smul_eq_C_mul]

end Basis

theorem normForm_eq_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (x : Fin n → A) :
    normForm A x = (∑ j, (X j : MvPolynomial (Fin n) R) • (Algebra.leftMulMatrix b (x j)).map C).det := by
  let bP := polyBasis b n
  let M : Fin n → Matrix ι ι R := fun j => Algebra.leftMulMatrix b (x j)
  have hM : ∀ j k, x j * b k = ∑ i, M j i k • b i := fun j k => by
    simp only [M, Algebra.leftMulMatrix_eq_repr_mul]
    exact (b.sum_repr (x j * b k)).symm
  have key : ∀ (q : MvPolynomial (Fin n) R) (a : A),
      q • (C a : MvPolynomial (Fin n) A) = MvPolynomial.map (algebraMap R A) q * C a := fun q a => by
    rw [Algebra.smul_def, MvPolynomial.algebraMap_def]
  have hmat : Algebra.leftMulMatrix bP (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) =
      ∑ j, (X j : MvPolynomial (Fin n) R) • (M j).map C := by
    refine Matrix.ext fun i k => ?_
    rw [Algebra.leftMulMatrix_eq_repr_mul, polyBasis_apply]
    have hsum : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k) =
        ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by
      calc (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k)
          = ∑ j, ∑ i', (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_

            rw [mul_assoc, ← C_mul, hM j k, map_sum, Finset.mul_sum]
        _ = ∑ i', ∑ j, (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := Finset.sum_comm
        _ = ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by
            refine Finset.sum_congr rfl fun i' _ => ?_

            rw [polyBasis_apply, key, map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_mul, map_X, map_C, Algebra.smul_def, C_mul, mul_assoc]
    rw [hsum, bP.repr_sum_self, Matrix.sum_apply]
    simp [Matrix.map_apply]
  rw [normForm, Algebra.norm_eq_matrix_det bP, hmat]

theorem NormFormEval.proof : NormFormEval.Statement := by
  intro R A _ _ _ _ _ n x u
  classical
  let b := Module.Free.chooseBasis R A
  let M : Fin n → Matrix (Module.Free.ChooseBasisIndex R A) (Module.Free.ChooseBasisIndex R A) R :=
    fun j => Algebra.leftMulMatrix b (x j)
  rw [normForm_eq_det b, RingHom.map_det]
  have hev : (MvPolynomial.eval u).mapMatrix (∑ j, (X j : MvPolynomial (Fin n) R) • (M j).map C) =
      Algebra.leftMulMatrix b (∑ j, algebraMap R A (u j) * x j) := by
    ext i k

    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, eval_X, eval_C, M]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul]
  rw [hev, ← Algebra.norm_eq_matrix_det b]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

theorem IncidenceNull.proof : IncidenceNull.Statement := by
  intro F _ n k I f hf
  have hvan : ∀ j : Fin n, rename Sum.inr f * X (Sum.inl j) ∈
      MvPolynomial.vanishingIdeal F
        (MvPolynomial.zeroLocus (AlgebraicClosure F) (incIdeal I k)) := by
    intro j z hz
    have hI : ∀ g ∈ I, aeval (z ∘ Sum.inl) g = 0 := by
      intro g hg
      have hmem : rename Sum.inl g ∈ incIdeal I k :=
        Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg)
      have h := hz _ hmem
      rwa [aeval_rename] at h
    have hlin : ∀ i : Fin k, ∑ j, (z ∘ Sum.inr) (i, j) * (z ∘ Sum.inl) j = 0 := by
      intro i
      have hmem : (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) :
          MvPolynomial (Fin n ⊕ (Fin k × Fin n)) F) ∈ incIdeal I k :=
        Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
      have h := hz _ hmem
      simpa using h
    rw [map_mul, aeval_rename, aeval_X]
    by_cases hx : z ∘ Sum.inl = 0
    · have h0 : z (Sum.inl j) = 0 := congrFun hx j
      rw [h0, mul_zero]
    · have hu : z ∘ Sum.inr ∈ incidence I k := ⟨z ∘ Sum.inl, hx, hI, hlin⟩
      rw [(hf.2 f).2 dvd_rfl _ hu, zero_mul]
  have hrad : ∀ j : Fin n, ∃ m, (rename Sum.inr f * X (Sum.inl j)) ^ m ∈ incIdeal I k := by
    intro j
    have h := hvan j
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at h
    exact h
  choose m hm using hrad
  exact ⟨Finset.univ.sup m, fun j =>
    Ideal.pow_mem_of_pow_mem _ (hm j) (Finset.le_sup (Finset.mem_univ j))⟩

end GroundTheory.Heights₂.Heights.Vertical
end
