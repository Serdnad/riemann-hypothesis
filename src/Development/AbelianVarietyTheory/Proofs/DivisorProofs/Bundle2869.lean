module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Tactic.ENatToNat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle009
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.AffDesc

open TensorProduct

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem isoPushout_desc_tmul {R0 A B : Type} [CommRing R0] [CommRing A] [CommRing B] [Algebra R0 A]
    [Algebra R0 B] {D : CommRingCat.{0}} (u : CommRingCat.of A ⟶ D) (v : CommRingCat.of B ⟶ D)
    (w : CommRingCat.ofHom (algebraMap R0 A) ≫ u = CommRingCat.ofHom (algebraMap R0 B) ≫ v) (a : A) (b : B) :
    ((CommRingCat.isPushout_tensorProduct R0 A B).isoPushout.hom ≫ pushout.desc u v w).hom (a ⊗ₜ b) =
      u.hom a * v.hom b := by
  have e : a ⊗ₜ[R0] b = Algebra.TensorProduct.includeLeftRingHom a *
      Algebra.TensorProduct.includeRight.toRingHom b := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, map_mul]
  have h1 := congrArg (fun φ => φ.hom a)
    ((CommRingCat.isPushout_tensorProduct R0 A B).inl_isoPushout_hom =≫ pushout.desc u v w)
  have h2 := congrArg (fun φ => φ.hom b)
    ((CommRingCat.isPushout_tensorProduct R0 A B).inr_isoPushout_hom =≫ pushout.desc u v w)
  simp only [Category.assoc, pushout.inl_desc, pushout.inr_desc, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom] at h1 h2
  rw [← h1, ← h2]
  rfl

theorem appLE_apply_appLE {X Y Y' Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (h : f ≫ g = f' ≫ g') (U : Z.Opens) (V : Y.Opens) (V' : Y'.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e₁' : V' ≤ g' ⁻¹ᵁ U) (e₂' : W ≤ f' ⁻¹ᵁ V') (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (f'.appLE V' W e₂').hom ((g'.appLE U V' e₁').hom x) := by
  have a := Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂
  have b := Scheme.Hom.appLE_comp_appLE f' g' U V' W e₁' e₂'
  have c := appLE_eq_of_eq h U W (by rw [Scheme.Hom.comp_preimage]; exact le_trans e₂ (Scheme.Hom.preimage_mono f e₁))
    (by rw [Scheme.Hom.comp_preimage]; exact le_trans e₂' (Scheme.Hom.preimage_mono f' e₁'))
  exact congrArg (fun φ => CommRingCat.Hom.hom φ x) (a.trans (c.trans b.symm))

theorem appTop_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) : f.appTop = f.appLE ⊤ ⊤ le_top :=
  Scheme.Hom.app_eq_appLE f

end GlobalTheory.Mum.AffDesc

namespace GlobalTheory.Mum.AffDesc
open TensorProduct

theorem mem_range_app_of_flat : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y → (∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom) → ∀ V : Y.Opens, IsAffineOpen V → ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  intro R _ S Y Z π y p q hπ hy H r h1 h2 hP hx V hV f hf
  classical
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  haveI : QuasiSeparatedSpace S := (quasiSeparated_iff_quasiSeparatedSpace π).1 inferInstance
  haveI : CompactSpace (pullback π π : Scheme) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst π π ≫ π)
  have hUY1 : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hUY2 : pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) = r ⁻¹ᵁ ⊤ ⊓ (pullback.fst p p ≫ p) ⁻¹ᵁ V := by
    simp [Scheme.Hom.comp_preimage]
  have i1 := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H.flip (US := ⊤) (UX := ⊤) (UT := V)
    le_top le_top hUY1 (isAffineOpen_top _) hV isCompact_univ isQuasiSeparated_univ
  have m2 := mono_pushoutSection_of_isCompact_of_flat_right hP (US := ⊤) (UX := ⊤) (UT := V)
    le_top le_top hUY2 (isAffineOpen_top _) hV isCompact_univ
  letI aB : Algebra Γ(Sp R, ⊤) Γ(S, ⊤) := (π.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI aA : Algebra Γ(Sp R, ⊤) Γ(Y, V) := (y.appLE ⊤ V le_top).hom.toAlgebra
  letI aC : Algebra Γ(Sp R, ⊤) Γ(pullback π π, ⊤) := ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top).hom.toAlgebra
  haveI : Module.Flat Γ(Sp R, ⊤) Γ(Y, V) := y.flat_appLE (isAffineOpen_top _) hV le_top
  let ΦB := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(S, ⊤) Γ(Y, V)).isoPushout.hom ≫
    pushoutSection H.flip (US := ⊤) (UX := ⊤) (UT := V) le_top le_top hUY1
  let ΦC := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(pullback π π, ⊤) Γ(Y, V)).isoPushout.hom ≫
    pushoutSection hP (US := ⊤) (UX := ⊤) (UT := V) le_top le_top hUY2
  have hB : Function.Surjective ΦB.hom := by
    have : IsIso ΦB := by dsimp only [ΦB]; infer_instance
    exact (ConcreteCategory.bijective_of_isIso ΦB).2
  have hC : Function.Injective ΦC.hom := by
    have : Mono ΦC := by dsimp only [ΦC]; infer_instance
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback ΦC).1 this
  have fB : ∀ (b : Γ(S, ⊤)) (a : Γ(Y, V)), ΦB.hom (b ⊗ₜ a) =
      (q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b * (p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a :=
    fun b a => isoPushout_desc_tmul _ _ _ b a
  have fC : ∀ (c : Γ(pullback π π, ⊤)) (a : Γ(Y, V)), ΦC.hom (c ⊗ₜ a) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom c *
        ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun c a => isoPushout_desc_tmul _ _ _ c a
  have k1 : ∀ x, (pullback.fst π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) x) =
      ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top) x := fun x =>
    congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.Hom.appLE_comp_appLE (pullback.fst π π) π ⊤ ⊤ ⊤ le_top le_top)
  have k2 : ∀ x, (pullback.snd π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) x) =
      ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top) x := fun x =>
    (congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.Hom.appLE_comp_appLE (pullback.snd π π) π ⊤ ⊤ ⊤ le_top le_top)).trans
      (congrArg (fun φ => CommRingCat.Hom.hom φ x) (appLE_eq_of_eq (pullback.condition (f := π) (g := π)).symm _ _ _ _))
  let d : Γ(S, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(pullback π π, ⊤) :=
    { toFun := fun x => (pullback.fst π π).appLE ⊤ ⊤ le_top x - (pullback.snd π π).appLE ⊤ ⊤ le_top x
      map_add' := fun x x' => by simp only [map_add (f := _)]; abel
      map_smul' := fun c x => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, k1, k2, RingHom.id_apply]
        ring }
  have hex : Function.Exact (Algebra.linearMap Γ(Sp R, ⊤) Γ(S, ⊤)) d := by
    intro x
    constructor
    · intro h0
      have e0 : (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x := by
        rw [appTop_eq_appLE, appTop_eq_appLE]; exact sub_eq_zero.1 h0
      obtain ⟨c, hc⟩ := hx x e0
      refine ⟨c, ?_⟩
      rw [appTop_eq_appLE] at hc
      exact hc
    · rintro ⟨c, rfl⟩
      show (pullback.fst π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) c) -
        (pullback.snd π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) c) = 0
      rw [k1, k2, sub_self]
  have hex' := Module.Flat.rTensor_exact Γ(Y, V) hex
  have hEq : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have c1 : ∀ b, ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom ((q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom ((pullback.fst π π).appLE ⊤ ⊤ le_top b) :=
    fun b => by
      rw [Scheme.Hom.app_eq_appLE]
      exact appLE_apply_appLE (pullback.fst p p) q r (pullback.fst π π) h1.symm ⊤ (p ⁻¹ᵁ V) ⊤
        (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp) le_rfl le_top (by simp) b
  have c2 : ∀ b, ((pullback.snd p p).appLE _ _ hEq.ge).hom ((q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom ((pullback.snd π π).appLE ⊤ ⊤ le_top b) :=
    fun b => appLE_apply_appLE (pullback.snd p p) q r (pullback.snd π π) h2.symm ⊤ (p ⁻¹ᵁ V) ⊤
      (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp) hEq.ge le_top (by simp) b
  have c3 : ∀ a, ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a) =
      ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun a => by
      rw [Scheme.Hom.app_eq_appLE]
      exact congrArg (fun φ => CommRingCat.Hom.hom φ a)
        (Scheme.Hom.appLE_comp_appLE (pullback.fst p p) p V (p ⁻¹ᵁ V) (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) le_rfl le_rfl)
  have c4 : ∀ a, ((pullback.snd p p).appLE _ _ hEq.ge).hom ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a) =
      ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun a => (congrArg (fun φ => CommRingCat.Hom.hom φ a)
      (Scheme.Hom.appLE_comp_appLE (pullback.snd p p) p V (p ⁻¹ᵁ V) (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) le_rfl hEq.ge)).trans
      (congrArg (fun φ => CommRingCat.Hom.hom φ a) (appLE_eq_of_eq (pullback.condition (f := p) (g := p)).symm V
        (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) _ _))
  have key : ∀ t, ΦC.hom (d.rTensor Γ(Y, V) t) = ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom (ΦB.hom t) -
      ((pullback.snd p p).appLE _ _ hEq.ge).hom (ΦB.hom t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
      rw [LinearMap.rTensor_tmul, fC, fB, map_mul, map_mul, c1, c2, c3, c4]
      change (r.appLE _ _ _).hom ((pullback.fst π π).appLE ⊤ ⊤ le_top b - (pullback.snd π π).appLE ⊤ ⊤ le_top b) * _ = _
      rw [map_sub, sub_mul]
    | add t t' ht ht' =>
      rw [map_add (f := _), map_add (f := _), ht, ht', map_add (f := _), map_add (f := _), map_add (f := _)]
      abel
  obtain ⟨t, rfl⟩ := hB f
  have hz : d.rTensor Γ(Y, V) t = 0 := hC (by rw [key, map_zero, hf hEq, sub_self])
  obtain ⟨s, rfl⟩ := (hex' t).1 hz
  clear hf hz key
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c a =>
    rw [LinearMap.rTensor_tmul, fB]
    refine ⟨(y.appLE ⊤ V le_top).hom c * a, ?_⟩
    rw [map_mul, Scheme.Hom.app_eq_appLE]
    congr 1
    exact appLE_apply_appLE p y q π H.w ⊤ V ⊤ (p ⁻¹ᵁ V) le_top le_rfl le_top (by simp) c
  | add s s' hs hs' =>
    obtain ⟨u, hu⟩ := hs
    obtain ⟨u', hu'⟩ := hs'
    exact ⟨u + u', by rw [map_add (f := _), hu, hu', map_add (f := _), map_add (f := _)]⟩

end GlobalTheory.Mum.AffDesc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FlatMul

variable {T : Scheme.{0}}

theorem whiskerRight_pb {H V : Over T} (q : V ⟶ H) (Y : Over T) :
    IsPullback (pullback.fst V.hom Y.hom) (q ▷ Y).left q.left (pullback.fst H.hom Y.hom) := by
  refine (IsPullback.of_right (h₁₁ := (q ▷ Y).left) (v₁₁ := pullback.fst V.hom Y.hom)
    (h₂₁ := q.left) (v₁₂ := pullback.fst H.hom Y.hom) ?_ (Over.whiskerRight_left_fst q)
    (IsPullback.of_hasPullback H.hom Y.hom).flip).flip
  rw [Over.whiskerRight_left_snd, Over.w]
  exact (IsPullback.of_hasPullback V.hom Y.hom).flip

theorem whiskerLeft_pb (X : Over T) {A B : Over T} (q : A ⟶ B) :
    IsPullback (snd X A).left (X ◁ q).left q.left (snd X B).left := by
  have : IsPullback (snd X A) (X ◁ q) q (snd X B) := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst X B) s.fst)
      (fun s => by simp) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
    · ext1
      · simp
      · simp [s.condition]
    · ext1
      · simp [← h₂]
      · simp [← h₁]
  exact this.map (Over.forget T)

theorem isIso_shear (H : Over T) [GrpObj H] : IsIso (lift μ[H] (snd H H)) := by
  refine ⟨⟨lift (fst H H * (snd H H)⁻¹) (snd H H), ?_, ?_⟩⟩
  · have hμ : μ[H] = fst H H * snd H H := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    apply hom_ext
    · rw [Category.assoc, lift_fst, comp_mul, lift_fst, GrpObj.comp_inv, lift_snd, hμ, mul_inv_cancel_right,
        Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]
  · have hμ : μ[H] = fst H H * snd H H := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    apply hom_ext
    · rw [Category.assoc, lift_fst, hμ, comp_mul, lift_fst, lift_snd, inv_mul_cancel_right, Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]

theorem flat_mu (H : Over T) [GrpObj H] (hH : Flat H.hom) : Flat μ[H].left := by
  have e : μ[H] = lift μ[H] (snd H H) ≫ fst H H := by rw [lift_fst]
  have := isIso_shear H
  have : IsIso (lift μ[H] (snd H H)).left := (Over.forget T).map_isIso (lift μ[H] (snd H H))
  have hfst : Flat (fst H H).left := by
    have h1 : (fst H H).left = pullback.fst H.hom H.hom := by simp
    rw [h1]
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback H.hom H.hom).flip hH
  rw [e, Over.comp_left]
  infer_instance

theorem main : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Flat H.hom →
    Flat ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  intro T H V _ e he hH
  have h1 : Flat (e ▷ V).left := MorphismProperty.of_isPullback (whiskerRight_pb e V)
    (inferInstance : Flat e.left)
  have h2 : Flat (H ◁ e).left := MorphismProperty.of_isPullback (whiskerLeft_pb H e)
    (inferInstance : Flat e.left)
  have h3 := flat_mu H hH
  have k : (fst V V ≫ e) * (snd V V ≫ e) = ((e ▷ V) ≫ (H ◁ e)) ≫ μ[H] := by
    rw [Hom.mul_def]
    congr 1
    apply hom_ext <;> simp
  rw [k, Over.comp_left, Over.comp_left]
  infer_instance

end GlobalTheory.Mum.FlatMul
end

section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.FlagCls

theorem isNormalScheme_of_isPreimmersion_of_flat {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem isNormalScheme_of_isPullback_fractionField : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (N G : Scheme.{0}) (g : N ⟶ Sp R) (j : G ⟶ N) (s : G ⟶ Sp K), IsPullback j s g (spMap (algebraMap R K)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G := by
  intro R K _ _ _ _ _ N G g j s hp hN
  have hb : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hbf : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) hp.flip hb
  have : Flat j := MorphismProperty.of_isPullback (P := @Flat) hp.flip hbf
  exact isNormalScheme_of_isPreimmersion_of_flat j hN

end GlobalTheory.FlagCls
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isImmersion_of_forall_affine_surjective_appLE : ∀ (Y Z : Scheme.{0}) (φ : Y ⟶ Z), (∀ y : Y, ∃ (U : Z.Opens) (W : Y.Opens) (h : W ≤ φ ⁻¹ᵁ U), IsAffineOpen U ∧ φ y ∈ U ∧ φ ⁻¹ᵁ U ≤ W ∧ IsAffineOpen W ∧ Function.Surjective (φ.appLE U W h).hom) → IsImmersion φ := by
  intro Y Z φ H
  have H' : ∀ y : Y, ∃ U : Z.Opens, φ y ∈ U ∧ IsClosedImmersion (φ ∣_ U) := by
    intro y
    obtain ⟨U, W, h, hU, hy, hW, hWa, hs⟩ := H y
    obtain rfl : W = φ ⁻¹ᵁ U := le_antisymm h hW
    refine ⟨U, hy, ?_⟩
    have : IsAffine U := hU
    have : IsAffine (φ ⁻¹ᵁ U) := hWa
    rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (Arrow.isoMk hWa.isoSpec hU.isoSpec (Scheme.Opens.toSpecΓ_naturality φ _) :
        Arrow.mk (φ ∣_ U) ≅ Arrow.mk (Spec.map (φ.app U)))]
    rw [Scheme.Hom.app_eq_appLE]
    exact IsClosedImmersion.spec_of_surjective _ hs
  choose U hyU hU using H'
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) U ?_ fun y => ?_
  · rintro _ ⟨y, rfl⟩
    exact (le_iSup U y : U y ≤ ⨆ i, U i) (hyU y)
  · have := hU y
    infer_instance

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem lift_immersion_of_reduced : ∀ (X Y P : Scheme.{0}) (f : X ⟶ P) (j : Y ⟶ P), IsReduced X → IsImmersion j → Set.range f ⊆ Set.range j → ∃ g : X ⟶ Y, g ≫ j = f := by
  intro X Y P f j _ _ hfj
  have hr : Set.range f ⊆ Set.range (j.coborderRange).ι := by
    intro x hx
    obtain ⟨y, rfl⟩ := hfj hx
    exact ⟨j.liftCoborder y, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι]⟩
  let f' := IsOpenImmersion.lift (j.coborderRange).ι f hr
  have hf' : f' ≫ (j.coborderRange).ι = f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense j.liftCoborder f' Set.univ dense_univ
    (fun x _ ↦ by
      obtain ⟨y, hy⟩ := hfj ⟨x, rfl⟩
      refine ⟨y, (j.coborderRange).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι, hy, ← Scheme.Hom.comp_apply, hf'])
  exact ⟨g, by rw [← Scheme.Hom.liftCoborder_ι j, ← Category.assoc, hg, hf']⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem pspace_noeth_and_pullback : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
    IsProper π → ∀ N : ℕ, IsNoetherian (PSpace R N) ∧ IsNoetherian (pullback (PSpace.str R N) π) := by
  intro R _ _ S π hπ N
  have hP : IsProper (PSpace.str R N) := isProper_str R N
  have h1 : IsNoetherian (PSpace R N) := by
    have : IsLocallyNoetherian (PSpace R N) := LocallyOfFiniteType.isLocallyNoetherian (PSpace.str R N)
    have : CompactSpace (PSpace R N) := QuasiCompact.compactSpace_of_compactSpace (PSpace.str R N)
    exact {}
  refine ⟨h1, ?_⟩
  haveI := hπ
  have : IsProper (pullback.fst (PSpace.str R N) π) := inferInstance
  haveI := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (PSpace.str R N) π)
  haveI := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (PSpace.str R N) π)
  exact {}

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.stalk_normal_flat_of_smooth_over_regular_local : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (X : Scheme.{0}) (p : X ⟶ Sp R), Smooth p → ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧ (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat ∧ Function.Injective (Spec.preimage (X.fromSpecStalk x ≫ p)).hom := by
  first | exact @GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular | exact GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular | (intros; apply GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.flat_openPart_groupScheme_productMap : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Flat H.hom → Flat ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  first | exact @GlobalTheory.Mum.FlatMul.main | exact GlobalTheory.Mum.FlatMul.main | (intros; apply GlobalTheory.Mum.FlatMul.main <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lift_of_isReduced_of_isImmersion_range : ∀ (X Y P : Scheme.{0}) (f : X ⟶ P) (j : Y ⟶ P), IsReduced X → IsImmersion j → Set.range f ⊆ Set.range j → ∃ g : X ⟶ Y, g ≫ j = f := by
  first | exact @GlobalTheory.Mum.lift_immersion_of_reduced | exact GlobalTheory.Mum.lift_immersion_of_reduced | (intros; apply GlobalTheory.Mum.lift_immersion_of_reduced <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isNoetherian_projectiveSpace_and_pullback_proper : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → ∀ N : ℕ, IsNoetherian (PSpace R N) ∧ IsNoetherian (pullback (PSpace.str R N) π) := by
  first | exact @GlobalTheory.Mum.pspace_noeth_and_pullback | exact GlobalTheory.Mum.pspace_noeth_and_pullback | (intros; apply GlobalTheory.Mum.pspace_noeth_and_pullback <;> assumption)

end
end
