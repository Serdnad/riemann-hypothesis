module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Mathlib.RingTheory.Length
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem

@[expose] public section

section

open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.existsO :
    ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) [NeZero n], ∃ O : Subalgebra ℤ_[l] (PadicAlgCl l),
      IsDiscreteValuationRing O ∧ Module.Finite ℤ_[l] O ∧ HasEnoughRootsOfUnity O n := by
  intro l _ n _
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n
  have hζi : IsIntegral ℤ_[l] ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] {ζ}
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨(integralClosure ℤ_[l] K).map f, ?_, ?_, ?_⟩
  · exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  · exact Module.Finite.equiv e.toLinearEquiv
  · have hz : ζ ∈ K := IntermediateField.mem_adjoin_simple_self _ _
    have hmem : ζ ∈ (integralClosure ℤ_[l] K).map f :=
      ⟨⟨ζ, hz⟩, (isIntegral_algHom_iff f hf).1 hζi, rfl⟩
    refine ⟨⟨⟨ζ, hmem⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩
    exact IsPrimitiveRoot.of_map_of_injective (f := ((integralClosure ℤ_[l] K).map f).val) hζ Subtype.val_injective
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_ker_eq_coker {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
    (f : A →ₗ[R] A) (hfin : Module.length R A ≠ ⊤) :
    Module.length R (A ⧸ LinearMap.range f) = Module.length R (LinearMap.ker f) := by
  have h1 := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h2 := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [(f.quotKerEquivRange).length_eq] at h2
  have h3 : Module.length R (LinearMap.range f) ≠ ⊤ := by
    intro h
    rw [h, top_add] at h1
    exact hfin h1
  rw [h1, add_comm] at h2
  exact (WithTop.add_right_inj h3).1 h2

private theorem len_sup_ne_top {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
    (S T : Submodule R A) (hS : Module.length R S ≠ ⊤) (hT : Module.length R T ≠ ⊤) :
    Module.length R (S ⊔ T : Submodule R A) ≠ ⊤ := by
  have h := Module.length_le_of_surjective (S.subtype.coprod T.subtype).rangeRestrict
    (LinearMap.surjective_rangeRestrict _)
  rw [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype,
    Module.length_prod] at h
  exact ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hS, hT⟩) h

private theorem len_map_le {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (a : R)
    (F : Submodule R N) (hF : Module.length R F ≠ ⊤) :
    Module.length R (F.map (LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))).mkQ) ≤
      Module.length R (LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) := by
  set P := LinearMap.range (a • (LinearMap.id : N →ₗ[R] N)) with hP
  let g : F →ₗ[R] F.map P.mkQ := P.mkQ.submoduleMap F
  have hg : Function.Surjective g := LinearMap.submoduleMap_surjective _ _
  have hle : LinearMap.range (a • (LinearMap.id : F →ₗ[R] F)) ≤ LinearMap.ker g := by
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext ?_
    show P.mkQ (a • (x : N)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hg' : Function.Surjective (Submodule.liftQ _ g hle) := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  refine (Module.length_le_of_surjective _ hg').trans ?_
  rw [len_ker_eq_coker _ hF]
  refine Module.length_le_of_injective
    (F.subtype.restrict (p := LinearMap.ker (a • (LinearMap.id : F →ₗ[R] F)))
      (q := LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) ?_) ?_
  · intro x hx
    exact congrArg Subtype.val hx
  · intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

theorem UpperTheory.V.Base.lenCokerLe :
    ∀ (R N : Type) [CommRing R] [AddCommGroup N] [Module R N], (∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) → ∀ a : R,
      Module.length R (N ⧸ LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))) ≤ Module.length R (LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) := by
  intro R N _ _ _ hN a
  by_contra hlt
  rw [not_le] at hlt
  set P := LinearMap.range (a • (LinearMap.id : N →ₗ[R] N)) with hP
  set K := LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N)) with hK
  have key : ∀ k : ℕ, ∃ F : Submodule R N, Module.length R F ≠ ⊤ ∧
      (k : ℕ∞) ≤ Module.length R (F.map P.mkQ) := by
    intro k
    induction k with
    | zero => exact ⟨⊥, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨F, hF, hk⟩ := ih
      have h1 : Module.length R (F.map P.mkQ) ≤ Module.length R K := len_map_le a F hF
      have h2 : F.map P.mkQ ≠ ⊤ := by
        intro h
        rw [h, Module.length_top] at h1
        exact absurd hlt (not_lt.2 h1)
      obtain ⟨y, hy⟩ : ∃ y, y ∉ F.map P.mkQ := by
        by_contra hh
        exact h2 (eq_top_iff.2 fun y _ => by_contra fun h => hh ⟨y, h⟩)
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P y
      refine ⟨F ⊔ Submodule.span R {x}, len_sup_ne_top _ _ hF (hN x), ?_⟩
      have h3 : F.map P.mkQ < (F ⊔ Submodule.span R {x}).map P.mkQ := by
        refine lt_of_le_of_ne (Submodule.map_mono le_sup_left) fun h => hy ?_
        rw [h]
        exact Submodule.mem_map_of_mem (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      have h4 : Order.height (F.map P.mkQ) < ⊤ := by
        rw [← Module.length_submodule]
        exact lt_of_le_of_lt h1 (lt_of_lt_of_le hlt le_top)
      have h5 := Order.height_strictMono h3 h4
      rw [← Module.length_submodule, ← Module.length_submodule] at h5
      rw [Nat.cast_succ]
      exact Order.add_one_le_of_lt (lt_of_le_of_lt hk h5)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (lt_of_lt_of_le hlt le_top).ne
  obtain ⟨F, hF, hk⟩ := key (n + 1)
  have h := hk.trans (len_map_le a F hF)
  rw [← hK, ← hn] at h
  exact absurd (Nat.cast_le.1 h) (by omega)
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_le_of_exact {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : LinearMap.ker g ≤ LinearMap.range f) :
    Module.length R B ≤ Module.length R C + Module.length R A := by
  have e := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  rw [e, add_comm]
  refine add_le_add (Module.length_le_of_injective _ (Submodule.subtype_injective _)) ?_
  exact (Module.length_le_of_injective _ (Submodule.inclusion_injective h)).trans
    (Module.length_le_of_surjective _ f.surjective_rangeRestrict)

theorem UpperTheory.V.Base.lenComp :
    ∀ (R N : Type) [CommRing R] [AddCommGroup N] [Module R N] (a b : Module.End R N),
      Module.length R (LinearMap.ker (a * b)) ≤ Module.length R (LinearMap.ker a) + Module.length R (LinearMap.ker b) ∧
      Module.length R (N ⧸ LinearMap.range (a * b)) ≤ Module.length R (N ⧸ LinearMap.range a) + Module.length R (N ⧸ LinearMap.range b) := by
  intro R N _ _ _ a b
  constructor
  · have h1 : LinearMap.ker b ≤ LinearMap.ker (a * b) := fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [Module.End.mul_apply, hx, map_zero]
    have h2 : ∀ x ∈ LinearMap.ker (a * b), b x ∈ LinearMap.ker a := fun x hx => hx
    refine length_le_of_exact (Submodule.inclusion h1) (LinearMap.restrict b h2) fun x hx => ?_
    exact ⟨⟨x.1, congrArg Subtype.val hx⟩, rfl⟩
  · have h1 : LinearMap.range b ≤ (LinearMap.range (a * b)).comap a := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    have h2 : LinearMap.range (a * b) ≤ (LinearMap.range a).comap LinearMap.id := by
      rintro _ ⟨y, rfl⟩
      exact ⟨b y, rfl⟩
    refine length_le_of_exact (Submodule.mapQ _ _ a h1) (Submodule.mapQ _ _ LinearMap.id h2) fun x hx => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [Submodule.mapQ_apply, hy]
    rfl
end
