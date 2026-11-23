module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle002
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def SmoothPullbackHasLocalAmbientEmbedding : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X Y A : Scheme.{u})
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pA : A ⟶ Spec (CommRingCat.of k)) [IsAffine A] [Smooth pA]
    [LocallyOfFiniteType pA] [QuasiCompact pA]
    (i : X ⟶ A) [IsClosedImmersion i], i ≫ pA = pX →
    ∀ (M c : ℕ) (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M))) [IsClosedImmersion ρ],
      ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin M)) = pA →
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u} (Fin M))) ρ c →
    ∀ (r : ℕ) (h : Y ⟶ X) [SmoothOfRelativeDimension r h], h ≫ pX = pY →
    ∀ y : Y,
      ∃ (V : Y.Opens) (_ : y ∈ V) (_ : IsAffineOpen V)
        (A' : Scheme.{u}) (pA' : A' ⟶ Spec (CommRingCat.of k)),
        IsAffine A' ∧ Smooth pA' ∧ LocallyOfFiniteType pA' ∧ QuasiCompact pA' ∧
        ∃ g : A' ⟶ A, Smooth g ∧ g ≫ pA = pA' ∧
          ∃ j : V.toScheme ⟶ A', IsClosedImmersion j ∧
            IsPullback j (V.ι ≫ h) g i ∧
            ∃ N₀ : ℕ, r ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
              ∃ σ : A' ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin (M + N))),
                IsClosedImmersion σ ∧
                σ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin (M + N))) = pA' ∧
                HasSmoothCoordCodim
                  (affineSpaceIndexedByToSpec k (ULift.{u} (Fin (M + N)))) σ (c + (N - r))

end FunctorialResolution.EmbeddedResolution

end
end

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def AffineEmbedsIntoAffineSpace : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p],
    ∃ (n : ℕ) (e : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))),
      AlgebraicGeometry.IsClosedImmersion e ∧ NonzeroOnComponents e.ker ∧
        e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) = p

def NilIsStrictNormalCrossingsOnAffineSpace : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u} (Fin n))).IdealSheafData)

def AffineSpaceIsSmooth : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))

def ClosedEmbeddingsRelatedByAutomorphism : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p] (n m : ℕ)
    (e₁ : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n)))
    [AlgebraicGeometry.IsClosedImmersion e₁]
    (e₂ : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m)))
    [AlgebraicGeometry.IsClosedImmersion e₂],
    e₁ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) = p →
    e₂ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin m)) = p →
    ∃ Φ : affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ≅
            affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)),
      Φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) =
          affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) ∧
        AffineSpace.homOfVector p (coordVectorInl n m e₁) ≫ Φ.hom =
          AffineSpace.homOfVector p (coordVectorInr n m e₂)

abbrev AffineResolutionRule : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], SequenceOfBlowups Y

def IsCompatibleWithOpenImmersions (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    [AlgebraicGeometry.IsReduced V] [AlgebraicGeometry.IsAffine V]
    (φ : V ⟶ Y) [AlgebraicGeometry.IsOpenImmersion φ],
    φ ≫ pY = pV → IsPullbackBlowupSequence φ (R k V pV) (R k Y pY)

def IsCompatibleWithEtaleCovers (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y W : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pW : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType pW] [AlgebraicGeometry.QuasiCompact pW]
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.IsAffine W]
    (φ : W ⟶ Y) [AlgebraicGeometry.Etale φ],
    φ ≫ pY = pW → (∀ y : ↥Y, ∃ w : ↥W, φ.base w = y) →
    IsStrictPullbackBlowupSeq φ (R k W pW) (R k Y pY)

def IsCompatibleWithFieldBaseChange (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (K : Type u) [Field K] [CharZero K] [Algebra k K]
    [AlgebraicGeometry.IsReduced (baseChange p K)]
    [AlgebraicGeometry.IsAffine (baseChange p K)],
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (R K (baseChange p K) (baseChangeToSpec p K)) (R k Y p)

def IsInducedByAffineRule (R : AffineResolutionRule.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (B : SequenceOfBlowups Y) : Prop :=
  ∀ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.IsAffine W]
    (φ : W ⟶ Y) [AlgebraicGeometry.Etale φ],
    φ ≫ p = q → (∀ y : ↥Y, ∃ w : ↥W, φ.base w = y) → IsStrictPullbackBlowupSeq φ (R k W q) B

def ExistsGluedBlowupSequence (R : AffineResolutionRule.{u}) : Prop :=
  IsCompatibleWithEtaleCovers R →
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y],
    ∃ B : SequenceOfBlowups Y, (∀ i, i < B.length → B.center i ≠ ⊤) ∧ IsInducedByAffineRule R k Y p B

def InducedRuleCompatibleWithFieldExtension (R : AffineResolutionRule.{u}) : Prop :=
  IsCompatibleWithOpenImmersions R → IsCompatibleWithFieldBaseChange R →
  ∀ F : ResolutionRule.{u},
    (∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X],
      IsInducedByAffineRule R k X f (F k X f)) →
    IsCompatibleWithFieldExtension F

end FunctorialResolution.EmbeddedResolution
end
end

section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem iso_hom_comp_projectionToBase {X' : Scheme.{u}} {s' s'' : SequenceOfBlowups X'}
    (ε : ∀ i : ℕ, i ≤ s'.length → (s'.schemeAt i ≅ s''.schemeAt i))
    (h0 : (ε 0 (Nat.zero_le _)).hom ≫ s''.isoZero.hom = s'.isoZero.hom)
    (hst : ∀ i : ℕ, ∀ hi : i < s'.length,
      (ε (i + 1) hi).hom ≫ s''.transitionMapSucc i = s'.transitionMapSucc i ≫ (ε i hi.le).hom) :
    ∀ i : ℕ, ∀ hi : i ≤ s'.length, (ε i hi).hom ≫ s''.projectionToBase i = s'.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [s''.projectionToBase_zero, s'.projectionToBase_zero]
    exact h0
  | succ n ih =>
    intro hi
    rw [s''.projectionToBase_succ n, s'.projectionToBase_succ n, ← Category.assoc,
      hst n hi, Category.assoc, ih (Nat.le_of_succ_le hi)]

private def pullbackProjectionToBaseIsoOfEq {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) :
    Limits.pullback φ (s.projectionToBase a) ≅ Limits.pullback φ (s.projectionToBase b) :=
  eqToIso (by rw [h])

private theorem pullbackIsoOfEq_hom_fst {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    {a b : ℕ} (h : a = b) :
    (pullbackProjectionToBaseIsoOfEq φ s h).hom ≫ Limits.pullback.fst φ (s.projectionToBase b)
      = Limits.pullback.fst φ (s.projectionToBase a) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]

private theorem pullbackIsoOfEq_hom_comp_pullbackTransitionMap {X X' : Scheme.{u}} (φ : X' ⟶ X)
    (s : SequenceOfBlowups X) {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b') :
    (pullbackProjectionToBaseIsoOfEq φ s hb).hom ≫ s.pullbackTransitionMap φ hab'
      = s.pullbackTransitionMap φ hab ≫ (pullbackProjectionToBaseIsoOfEq φ s ha).hom := by
  subst ha
  subst hb
  have hpr : hab = hab' := rfl
  subst hpr
  simp [pullbackProjectionToBaseIsoOfEq]

private theorem comap_pullbackIsoOfEq {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X) {a b : ℕ}
    (h : a = b) {W : Scheme.{u}} (g : W ⟶ Limits.pullback φ (s.projectionToBase a)) :
    (s.center b).comap (g ≫ (pullbackProjectionToBaseIsoOfEq φ s h).hom ≫ Limits.pullback.snd φ (s.projectionToBase b))
      = (s.center a).comap (g ≫ Limits.pullback.snd φ (s.projectionToBase a)) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]

private theorem strictMono_enumeration_le {n m L : ℕ} {r q : ℕ → ℕ} {P : ℕ → Prop}
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    ∀ i, i < n → i < m → r i ≤ q i := by
  have main : ∀ k i : ℕ, i < k → i < n → i < m → r i ≤ q i := by
    intro k
    induction k with
    | zero => intro i hik; exact absurd hik (Nat.not_lt_zero i)
    | succ k ih =>
      intro i hik hin him
      by_contra hcon
      push Not at hcon
      have hqL : q i < L := hq1 i him
      obtain ⟨j, hjn, hj⟩ := (hr4 (q i) hqL).mp ((hq4 (q i) hqL).mpr ⟨i, him, rfl⟩)
      have hji : j < i := by
        by_contra hc
        push Not at hc
        rcases Nat.eq_or_lt_of_le hc with h' | h'
        · rw [← h'] at hj
          omega
        · have hlt := hr2 i j hjn.le h'
          omega
      have h1 : r j ≤ q j := ih j (by omega) (by omega) (by omega)
      have h2 : q j < q i := hq2 j i him.le hji
      omega
  intro i hin him
  exact main (i + 1) i (Nat.lt_succ_self i) hin him

private theorem strictMono_enumeration_unique {n m L : ℕ} {r q : ℕ → ℕ} {P : ℕ → Prop}
    (hr1 : ∀ i, i < n → r i < L)
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hrn : r n = L)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hqm : q m = L)
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    n = m ∧ ∀ i, i ≤ n → r i = q i := by
  have le1 := strictMono_enumeration_le hr2 hq1 hq2 hr4 hq4
  have le2 := strictMono_enumeration_le hq2 hr1 hr2 hq4 hr4
  have heq : ∀ i, i < n → i < m → r i = q i := fun i h1 h2 =>
    le_antisymm (le1 i h1 h2) (le2 i h2 h1)
  have hnm : n = m := by
    rcases lt_trichotomy n m with hlt | heqnm | hgt
    · exfalso
      have hqn : q n < L := hq1 n hlt
      obtain ⟨j, hjn, hj⟩ := (hr4 (q n) hqn).mp ((hq4 (q n) hqn).mpr ⟨n, hlt, rfl⟩)
      have ha : r j = q j := heq j hjn (hjn.trans hlt)
      have hb : q j < q n := hq2 j n hlt.le hjn
      omega
    · exact heqnm
    · exfalso
      have hrm : r m < L := hr1 m hgt
      obtain ⟨j, hjm, hj⟩ := (hq4 (r m) hrm).mp ((hr4 (r m) hrm).mpr ⟨m, hgt, rfl⟩)
      have ha : r j = q j := heq j (hjm.trans hgt) hjm
      have hb : r j < r m := hr2 j m hgt.le hjm
      omega
  refine ⟨hnm, ?_⟩
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with h | h
  · rw [h, hrn, hnm, hqm]
  · exact heq i h (by omega)

namespace IsPullbackBlowupSequence

theorem of_isomorphic {X X' : Scheme.{u}} {φ : X' ⟶ X} {s : SequenceOfBlowups X} {s' s'' : SequenceOfBlowups X'}
    (h : IsPullbackBlowupSequence φ s' s) (e : s'.Isomorphic s'') : IsPullbackBlowupSequence φ s'' s := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨hlen, ε, h0, hst, hc⟩ := e
  have hcl : ∀ i : ℕ, i ≤ s''.length → i ≤ s'.length := fun i hi => le_of_le_of_eq hi hlen.symm
  have hcl' : ∀ i : ℕ, i < s''.length → i < s'.length := fun i hi => lt_of_lt_of_eq hi hlen.symm
  have hproj := iso_hom_comp_projectionToBase ε h0 hst
  refine ⟨r, fun i hi => (ε i (hcl i hi)).symm ≪≫ E i (hcl i hi),
    fun i hi => hr1 i (hcl' i hi), fun i j hj hij => hr2 i j (hcl j hj) hij,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hlen]; exact hr3
  · intro i hi
    rw [hr4 i hi, hlen]
  · intro i hi
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hfst i (hcl i hi)]
    rw [← hproj i (hcl i hi)]
    simp
  · intro i hi hr
    have h1 := hstepE i (hcl' i hi) hr
    have h2 := hst i (hcl' i hi)
    have key : s''.transitionMapSucc i ≫ (ε i (hcl i hi.le)).inv
        = (ε (i + 1) (hcl' i hi)).inv ≫ s'.transitionMapSucc i := by
      rw [← Iso.cancel_iso_hom_left (ε (i + 1) (hcl' i hi)), ← Category.assoc, h2]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, key, Category.assoc, h1, Category.assoc]
  · intro i hi
    have h1 := hcen i (hcl' i hi)
    have h2 := hc i (hcl' i hi)
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [Scheme.IdealSheafData.comap_comp, ← h1, ← h2, ← Scheme.IdealSheafData.comap_comp,
      Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

theorem isomorphic {X X' : Scheme.{u}} {φ : X' ⟶ X} {s : SequenceOfBlowups X} {s' s'' : SequenceOfBlowups X'}
    (h : IsPullbackBlowupSequence φ s' s) (h' : IsPullbackBlowupSequence φ s'' s) : s'.Isomorphic s'' := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨q, G, hq1, hq2, hq3, hq4, gfst, gstep, gcen⟩ := h'
  obtain ⟨hnm, hall⟩ := strictMono_enumeration_unique hr1 hr2 hr3 hr4 hq1 hq2 hq3 hq4
  refine ⟨hnm, fun i hi => E i hi ≪≫ pullbackProjectionToBaseIsoOfEq φ s (hall i hi) ≪≫
    (G i (le_of_le_of_eq hi hnm)).symm, ?_, ?_, ?_⟩
  · have hG0 : (G 0 (le_of_le_of_eq (Nat.zero_le _) hnm)).inv ≫ s''.projectionToBase 0
        = Limits.pullback.fst φ (s.projectionToBase (q 0)) := by
      rw [← gfst 0 (le_of_le_of_eq (Nat.zero_le _) hnm)]
      simp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← s''.projectionToBase_zero, hG0, pullbackIsoOfEq_hom_fst, hfst 0 (Nat.zero_le _),
      s'.projectionToBase_zero]
  · intro i hi
    have hr : r i ≤ r (i + 1) := (hr2 i (i + 1) hi (Nat.lt_succ_self i)).le
    have hq' : q i ≤ q (i + 1) :=
      (hq2 i (i + 1) (le_of_le_of_eq hi hnm) (Nat.lt_succ_self i)).le
    have h1 := hstepE i hi hr
    have h2 := gstep i (lt_of_lt_of_eq hi hnm) hq'
    have hGinv : (G (i + 1) (le_of_le_of_eq hi hnm)).inv ≫ s''.transitionMapSucc i
        = s.pullbackTransitionMap φ hq' ≫ (G i (le_of_le_of_eq (Nat.le_of_succ_le hi) hnm)).inv := by
      rw [← Iso.cancel_iso_hom_left (G (i + 1) (le_of_le_of_eq hi hnm)), ← Category.assoc,
        Iso.hom_inv_id, Category.id_comp, ← Category.assoc, ← h2]
      simp
    have htrans := pullbackIsoOfEq_hom_comp_pullbackTransitionMap φ s (hall i (Nat.le_of_succ_le hi))
      (hall (i + 1) hi) hr hq'
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hGinv]
    rw [reassoc_of% h1, reassoc_of% htrans]
  · intro i hi
    have h1 := hcen i hi
    have h2 := gcen i (lt_of_lt_of_eq hi hnm)
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [h2, h1, ← Scheme.IdealSheafData.comap_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact comap_pullbackIsoOfEq φ s (hall i (Nat.le_of_succ_le hi)) _

end IsPullbackBlowupSequence

end FunctorialResolution.EmbeddedResolution
end
end

section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem map_eq_ker {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : X ⟶ Y) :
    I.map f = (I.subschemeι ≫ f).ker := rfl

private theorem comap_eq_ker_pullback_fst {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.comap f = (pullback.fst f I.subschemeι).ker := rfl

theorem comap_map_eq_map_comap_of_isPullback {W X X' W' : Scheme.{u}} {f : W ⟶ X} {g : X' ⟶ X}
    {g' : W' ⟶ W} {f' : W' ⟶ X'} (H : IsPullback g' f' f g)
    [QuasiCompact f] [AlgebraicGeometry.Flat g] (I : W.IdealSheafData) :
    (I.map f).comap g = (I.comap g').map f' := by
  have hqc : QuasiCompact (I.subschemeι ≫ f) := inferInstance
  have S : IsPullback (pullback.snd g' I.subschemeι) (pullback.fst g' I.subschemeι ≫ f')
      (I.subschemeι ≫ f) g := (IsPullback.of_hasPullback g' I.subschemeι).flip.paste_vert H
  have hqc' : QuasiCompact (pullback.fst g' I.subschemeι ≫ f') := quasiCompact_of_isPullback S
  have h1 := ker_eq_comap_ker_of_isPullback_of_flat S
  rw [map_eq_ker, ← h1, Scheme.Hom.ker_comp, comap_eq_ker_pullback_fst]

theorem comap_map_eq_self_of_isPullback {W X Q : Scheme.{u}} (γ : W ⟶ X)
    [QuasiCompact γ] [AlgebraicGeometry.Flat γ] {p q : Q ⟶ W} (H : IsPullback p q γ γ)
    (I : W.IdealSheafData) (hI : I.comap p = I.comap q) :
    (I.map γ).comap γ = I := by
  have key := comap_map_eq_map_comap_of_isPullback H I
  rw [hI] at key
  rw [key]
  obtain ⟨s, hsq⟩ : ∃ s : W ⟶ Q, s ≫ q = 𝟙 W :=
    ⟨H.lift (𝟙 W) (𝟙 W) rfl, H.lift_snd _ _ _⟩
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_map_comap I q)
  have h1 := Scheme.IdealSheafData.comap_map_le (I.comap q) q
  have h2 : (((I.comap q).map q).comap q).comap s ≤ ((I.comap q).comap s) :=
    Scheme.IdealSheafData.comap_mono s h1
  rwa [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hsq,
    Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id] at h2

end FunctorialResolution.EmbeddedResolution
end
