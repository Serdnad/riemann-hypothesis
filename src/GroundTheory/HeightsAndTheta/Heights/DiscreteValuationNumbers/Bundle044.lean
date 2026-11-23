module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle032
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull FlagPair midDeg midVar)

def FlagPairJoinRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (EF E'F : ChartBundle O (mseg (joinCoord x z)) N V),
    IsPull O x z E EF → IsPull O x z E' E'F → ∀ φ : FlagPair O (joinCoord x z) EF E'F,
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord w z))) N V,
      IsPull O x (joinCoord w z) E EB → IsPull O x (joinCoord w z) E' E'B →
    ∃ ψ : FlagPair O (joinCoord x (joinCoord w z)) EB E'B,
      ψ.Vs = φ.Vs ∧ ψ.gen = φ.gen ∧ ψ.gen' = φ.gen' ∧
      ψ.deg = (fun i => midDeg (K₂ := K₂) (φ.deg i)) ∧
      ψ.deg' = (fun i => midDeg (K₂ := K₂) (φ.deg' i)) ∧
      ψ.f = (fun i => rename (midVar ι₂) (φ.f i)) ∧ ψ.g = (fun i => rename (midVar ι₂) (φ.g i))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField midDeg midVar)

def PairNumberJoinRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x (joinCoord w z))) d →
    fnField O (joinCoord x (joinCoord w z)) = fnField O (joinCoord x z) →
    ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim ι₂ ι')))
      (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι ι')),
      IsFieldIntersection I → IsFieldIntersection I₁ →
    ∀ (n : ℕ) (a a' : Fin n → K ⊕ K' → ℤ)
      (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
      (∀ i, IsVertDiv O (mcIdeal O (joinCoord x z)) (a i - a' i) (f i) (g i)) →
    ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I₁ (mcIdeal O (joinCoord x z)) d a a' f g H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (mcIdeal O (joinCoord x (joinCoord w z))) d
          (fun i => midDeg (K₂ := K₂) (a i)) (fun i => midDeg (K₂ := K₂) (a' i))
          (fun i => rename (midVar ι₂) (f i)) (fun i => rename (midVar ι₂) (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)

noncomputable section

theorem ConeTrdegFnField.trdeg_eq_of_le_of_isAlgebraic {O B : Type} [CommRing O] [IsDomain O] [CommRing B]
    [IsDomain B] [Algebra O B] (hinj : Function.Injective (algebraMap O B)) {S T : Subalgebra O B}
    (hST : S ≤ T) (halg : ∀ t ∈ T, IsAlgebraic S t) : Algebra.trdeg O S = Algebra.trdeg O T := by
  let _ : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  have _ : IsScalarTower O S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : FaithfulSMul O S :=
    (faithfulSMul_iff_algebraMap_injective O S).2 fun a b h => hinj (congrArg Subtype.val h)
  have _ : FaithfulSMul S T :=
    (faithfulSMul_iff_algebraMap_injective S T).2 (Subalgebra.inclusion_injective hST)
  let f : T →ₐ[S] B := { T.val.toRingHom with commutes' := fun _ => rfl }
  have _ : Algebra.IsAlgebraic S T :=
    ⟨fun t => (isAlgebraic_algHom_iff f Subtype.val_injective).1 (halg t t.2)⟩
  have h := trdeg_add_eq O S (A := T)
  rw [trdeg_eq_zero (R := S) (A := T), add_zero] at h
  exact h

section Cone

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem ConeTrdegFnField.mem_fnField_of_mem_adjoin (y : (Σ k, ι k) → Ω) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (fnField O y : Set Ω)) : a ∈ fnField O y := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hx
  | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

def ConeTrdegFnField.coneMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    MvPolynomial K (Algebra.adjoin O (fnField O y : Set Ω)) →ₐ[O] MvPolynomial K Ω :=
  ((aeval fun k => C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars O).comp
    (MvPolynomial.mapAlgHom (Algebra.adjoin O (fnField O y : Set Ω)).val)

theorem ConeTrdegFnField.coneMap_C (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (a : Algebra.adjoin O (fnField O y : Set Ω)) :
    ConeTrdegFnField.coneMap y c (C a) = C (a : Ω) := by
  simp [ConeTrdegFnField.coneMap]

theorem ConeTrdegFnField.coneMap_X (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) :
    ConeTrdegFnField.coneMap (O := O) y c (X k) = C (y ⟨k, c k⟩) * X k := by
  simp [ConeTrdegFnField.coneMap]

theorem ConeTrdegFnField.mcMap_X (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) :
    mcMap O y (X p) = C (y p) * X p.1 := by
  simp [mcMap]

theorem ConeTrdegFnField.coneMap_injective (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Function.Injective (ConeTrdegFnField.coneMap (O := O) y c) := by
  let ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩) * X k
  let ψ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩)⁻¹ * X k
  have hinv : ψ'.comp ψ = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [ψ, ψ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc k), map_one, one_mul]
  have hψ : Function.Injective ψ := Function.LeftInverse.injective (g := ψ') fun p => by
    rw [← AlgHom.comp_apply, hinv, AlgHom.id_apply]
  exact hψ.comp (MvPolynomial.map_injective _ Subtype.val_injective)

end Cone

theorem ConeTrdegFnField.proof : ConeTrdegFnField.Statement := by
  intro O _ _ Ω _ _ hinj K _ ι _ y hy
  choose c hc using hy
  set F₀ := Algebra.adjoin O (fnField O y : Set Ω)
  have hF : ∀ w ∈ fnField O y, w ∈ F₀ := fun w hw => Algebra.subset_adjoin hw
  have hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ F₀ := fun p =>
    hF _ (Subfield.subset_closure (Or.inr ⟨⟨p.1, (p.2, c p.1)⟩, rfl⟩))

  let ρ : MRingOver O ι →ₐ[O] MvPolynomial K F₀ := aeval fun p => C (⟨_, hu p⟩ : F₀) * X p.1
  have hfac : mcMap O y = (ConeTrdegFnField.coneMap (O := O) y c).comp ρ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [ConeTrdegFnField.mcMap_X, AlgHom.comp_apply, aeval_X, map_mul, ConeTrdegFnField.coneMap_C,
      ConeTrdegFnField.coneMap_X, ← mul_assoc, ← map_mul]
    simp only [div_mul_cancel₀ _ (hc p.1)]
  set R := (mcMap O y).range
  have hle : R ≤ (ConeTrdegFnField.coneMap (O := O) y c).range := by
    show (mcMap O y).range ≤ _
    rw [hfac]; exact AlgHom.range_comp_le_range _ _
  have hXR : ∀ p : Σ k, ι k, (C (y p) * X p.1 : MvPolynomial K Ω) ∈ R := fun p =>
    ⟨X p, ConeTrdegFnField.mcMap_X y p⟩

  have halgC : ∀ w ∈ fnField O y, IsAlgebraic R (C w : MvPolynomial K Ω) := by
    intro w hw
    induction hw using Subfield.closure_induction with
    | mem x hx =>
      rcases hx with ⟨r, rfl⟩ | ⟨q, rfl⟩
      · have e : (C (algebraMap O Ω r) : MvPolynomial K Ω) = algebraMap O (MvPolynomial K Ω) r := by
          rw [MvPolynomial.algebraMap_apply]
        rw [e]
        exact isAlgebraic_algebraMap (⟨_, R.algebraMap_mem r⟩ : R)
      · dsimp only
        by_cases h0 : y ⟨q.1, q.2.2⟩ = 0
        · rw [h0, div_zero, map_zero]; exact isAlgebraic_zero
        · refine IsAlgebraic.of_mul (y := C (y ⟨q.1, q.2.2⟩) * X q.1)
            (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (C_ne_zero.2 h0) (X_ne_zero _)))
            (isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.2⟩⟩ : R)) ?_
          have e : (C (y ⟨q.1, q.2.2⟩) * X q.1 : MvPolynomial K Ω) * C (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) =
              C (y ⟨q.1, q.2.1⟩) * X q.1 := by
            rw [mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ h0]
          rw [e]
          exact isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.1⟩⟩ : R)
    | one => rw [map_one]; exact isAlgebraic_one
    | add x z _ _ hx hz => rw [map_add (f := _)]; exact hx.add hz
    | neg x _ hx => rw [map_neg]; exact hx.neg
    | inv x _ hx =>
      by_cases h0 : x = 0
      · rw [h0, inv_zero, map_zero]; exact isAlgebraic_zero
      · refine IsAlgebraic.of_mul (y := C x) (mem_nonZeroDivisors_of_ne_zero (C_ne_zero.2 h0)) hx ?_
        rw [← map_mul, mul_inv_cancel₀ h0, map_one]; exact isAlgebraic_one
    | mul x z _ _ hx hz => rw [map_mul]; exact hx.mul hz
  have halg : ∀ t ∈ (ConeTrdegFnField.coneMap (O := O) y c).range, IsAlgebraic R t := by
    rintro _ ⟨q, rfl⟩
    change IsAlgebraic R (ConeTrdegFnField.coneMap (O := O) y c q)
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [ConeTrdegFnField.coneMap_C]
      exact halgC a (ConeTrdegFnField.mem_fnField_of_mem_adjoin y a.2)
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p k hp =>
      rw [map_mul, ConeTrdegFnField.coneMap_X]
      exact hp.mul (isAlgebraic_algebraMap (⟨_, hXR ⟨k, c k⟩⟩ : R))
  have hinjP : Function.Injective (algebraMap O (MvPolynomial K Ω)) := by
    rw [IsScalarTower.algebraMap_eq O Ω (MvPolynomial K Ω)]
    exact (C_injective K Ω).comp hinj
  have h1 : Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) = Algebra.trdeg O R :=
    (Ideal.quotientKerEquivRange (mcMap O y)).trdeg_eq
  have h2 : Algebra.trdeg O (ConeTrdegFnField.coneMap (O := O) y c).range = Algebra.trdeg O (MvPolynomial K F₀) :=
    (AlgEquiv.ofInjective (ConeTrdegFnField.coneMap (O := O) y c)
      (ConeTrdegFnField.coneMap_injective y c hc)).trdeg_eq.symm
  have _ : FaithfulSMul O F₀ :=
    (faithfulSMul_iff_algebraMap_injective O F₀).2 fun a b h => hinj (congrArg Subtype.val h)
  have _ : FaithfulSMul F₀ (MvPolynomial K F₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (C_injective K _)
  have h3 : Algebra.trdeg O (MvPolynomial K F₀) = Algebra.trdeg O F₀ + Fintype.card K := by
    rw [← trdeg_add_eq O F₀ (A := MvPolynomial K F₀), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype]
  rw [h1, ConeTrdegFnField.trdeg_eq_of_le_of_isAlgebraic hinjP hle halg, h2, h3]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord)

theorem FlagModelCommonModel.proof (hModel : JoinTwoModels.Statement)
    (hPull : JoinPullbackAlt.Statement) (hVert : JoinVerticalDivisor.Statement)
    (hLeft : FlagModelJoinLeftAlt.Statement) (hRight : FlagModelJoinRightAlt.Statement) :
    FlagModelCommonModel.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hW hE F₁ F₂
  obtain ⟨hZ, hfn⟩ := hModel O Ω K ι x d hW F₁.K' F₁.ι' F₁.z F₂.K' F₂.ι' F₂.z F₁.model F₁.birat
    F₂.model F₂.birat
  obtain ⟨EB, E'B, hp, hp', hsame⟩ :=
    hPull O Ω K ι x (F₁.K' ⊕ F₂.K') (Sum.elim F₁.ι' F₂.ι') (joinCoord F₁.z F₂.z) N V E E' hE
  obtain ⟨φ₁, h₁⟩ := hLeft O Ω K ι x d N V E E' hW hE F₁ F₂.K' F₂.ι' F₂.z hZ hfn EB E'B hp hp'
  obtain ⟨φ₂, h₂⟩ := hRight O Ω K ι x d N V E E' hW hE F₂ F₁.K' F₁.ι' F₁.z hZ hfn EB E'B hp hp'
  refine ⟨F₁.K' ⊕ F₂.K', inferInstance, Sum.elim F₁.ι' F₂.ι', inferInstance, joinCoord F₁.z F₂.z, EB, E'B,
    φ₁, φ₂, hZ, hfn, hp, hp', hsame, fun b f g hv => hVert O Ω K ι x _ _ _ b f g hv, ?_⟩
  intro I I₁ I₂ hI hI₁ hI₂ G r y y' f g hv c Q hc hG hQ
  exact ⟨h₁ I I₁ hI hI₁ G r y y' f g hv c Q hc hG hQ, h₂ I I₂ hI hI₂ G r y y' f g hv c Q hc hG hQ⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

def homLocRing (P W : Ideal (MRing ι R)) [P.IsPrime] : Subring (FractionRing (MRing ι R ⧸ P)) :=
  Subring.closure {z | ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧
    z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g)}

end Objects

section Lemmas

def HomLocRingLocal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (hP : IsMultiProjPrime P) (c : K → ℕ) (x : MRing ι O),
    IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.isPrime
      IsLocalRing (homLocRing P W) ∧ IsNoetherianRing (homLocRing P W) ∧
        ringKrullDim (homLocRing P W) = 1

def DivCycleHomLoc.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (hP : IsMultiProjPrime P) (c : K → ℕ) (x : MRing ι O),
    IsMultiHomog x c → x ∉ P →
    ∀ (W : Ideal (MRing ι O)) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes), IsRelevant W →
    ∀ g : MRing ι O, IsMultiHomog g c → g ∉ W →
      haveI := hP.isPrime
      ∀ hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
            homLocRing P W,
      haveI : W.IsPrime := hW.1.1
      multAt (P ⊔ Ideal.span {x}) W =
        Module.length (homLocRing P W) (homLocRing P W ⧸ Ideal.span {(⟨_, hz⟩ : homLocRing P W)})

def FiniteBirationalLength.Statement : Prop :=
  ∀ (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [Module.Finite A B], ringKrullDim A = 1 →
    Function.Injective (algebraMap A B) → Module.finrank A B = 1 → ∀ z : A, z ≠ 0 →
      Finite {𝔫 : Ideal B // 𝔫.IsMaximal} ∧
      Module.length A (A ⧸ Ideal.span {z}) =
        ∑ᶠ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
          (haveI := 𝔫.2.isPrime
           Module.length (Localization.AtPrime 𝔫.1)
             (Localization.AtPrime 𝔫.1 ⧸
               Ideal.span {algebraMap B (Localization.AtPrime 𝔫.1) (algebraMap A B z)})) *
            (𝔫.1.inertiaDeg A : ℕ∞)

def BlowUpFibreSemilocal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
    ∀ g : MRing ι O, IsMultiHomog g c → g ∉ W →
      haveI := hP.multiProj.isPrime
      ∀ hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
            homLocRing P W,
      ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (homLocRing P W) B),
        Module.Finite (homLocRing P W) B ∧ Function.Injective (algebraMap (homLocRing P W) B) ∧
        Module.finrank (homLocRing P W) B = 1 ∧
        ∃ e : {𝔫 : Ideal B // 𝔫.IsMaximal} ≃ {W' : Ideal (MRing (extIdx ι J) O) //
            W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
              W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W},
          ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
            (haveI := 𝔫.2.isPrime
             Module.length (Localization.AtPrime 𝔫.1)
               (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {(algebraMap B (Localization.AtPrime 𝔫.1)
                 (algebraMap (homLocRing P W) B ⟨_, hz⟩))})) =
              ((divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1).toNat : ℕ∞) ∧
            𝔫.1.inertiaDeg (homLocRing P W) = specialRelDeg (e 𝔫).1

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

theorem PolynomialDimensionInequality.full : PolynomialDimensionInequality.Statement.{u} :=
  PolynomialDimensionInequality.proof PolynomialPrimeOverZeroHeight.proof.{u}

theorem DimensionInequalityOneGenerator.full : DimensionInequalityOneGenerator.Statement.{u, v} :=
  DimensionInequalityOneGenerator.proof PolynomialDimensionInequality.full.{u}
    QuotientHeightAddOne.proof.{u}

theorem DimensionInequality.full : DimensionInequality.Statement.{u, v} :=
  DimensionInequality.proof DimensionInequalityOneGenerator.full.{u, v}
    DimensionInequalityOneGenerator.full.{v, v}

theorem ReesAlgebraDim.full : ReesAlgebraDim.Statement.{u} :=
  ReesAlgebraDim.proof DimensionInequality.full.{u, u}

theorem BlowUpModel.full : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof ReesAlgebraDim.full.{u}

end GroundTheory.Heights₂.Heights.NumbersDVR
end
