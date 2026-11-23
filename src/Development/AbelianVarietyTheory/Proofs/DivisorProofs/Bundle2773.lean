module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonHomExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mul_of_isDominant_pair : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], GlobalTheory.SS.SmConn A → ∀ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left → ∀ (Y : Over (Sp K)) (x₁ x₂ y₁ y₂ : Y ⟶ A), IsDominant (lift x₁ x₂).left → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₁ → u ≫ f = w ≫ y₁) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₂ → u ≫ f = w ≫ y₂) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ (x₁ * x₂) → u ≫ f = w ≫ (y₁ * y₂)) → ∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f := by
  intro K _ A _ hA V j f hj Y x₁ x₂ y₁ y₂ hdom h₁ h₂ h₃ Z u₁ u₂ u₃ hu
  obtain ⟨_, hsm, hsep, _, _⟩ := hA
  let R : A.left.Opens := j.left.opensRange
  let U : (A ⊗ A).left.Opens :=
    (fst A A).left ⁻¹ᵁ R ⊓ (snd A A).left ⁻¹ᵁ R ⊓ (fst A A * snd A A).left ⁻¹ᵁ R
  let W : Over (Sp K) := Over.mk (U.ι ≫ (A ⊗ A).hom)
  let ιW : W ⟶ A ⊗ A := Over.homMk U.ι rfl
  have : IsOpenImmersion ιW.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hWU : ∀ q : W.left, ιW.left q ∈ U := fun q => (Scheme.Opens.range_ι U).subset ⟨q, rfl⟩
  have hR : ∀ (g : A ⊗ A ⟶ A) (q : W.left), ιW.left q ∈ g.left ⁻¹ᵁ R →
      (ιW ≫ g).left q ∈ Set.range j.left := fun g q h => by
    rw [Over.comp_left, Scheme.Hom.comp_apply]; exact h
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ fst A A) fun q => hR _ q (hWU q).1.1
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ snd A A) fun q => hR _ q (hWU q).1.2
  obtain ⟨v₃, hv₃⟩ := GlobalTheory.GenericHom.exists_lift j (ιW ≫ (fst A A * snd A A)) fun q => hR _ q (hWU q).2
  have : Smooth (A ⊗ A).hom := inferInstanceAs (Smooth (pullback.fst A.hom A.hom ≫ A.hom))
  have : Smooth W.hom := inferInstanceAs (Smooth (U.ι ≫ (A ⊗ A).hom))
  have := GlobalTheory.isNormalScheme_of_smooth (S := Spec (.of K)) W.hom
  have : IsReduced W.left := GlobalTheory.IsNormalScheme.isReduced
  let Y' : Y.left.Opens := (lift x₁ x₂).left ⁻¹ᵁ U
  let Z' : Over (Sp K) := Over.mk (Y'.ι ≫ Y.hom)
  let w : Z' ⟶ Y := Over.homMk Y'.ι rfl
  let p : Z' ⟶ W := Over.homMk ((lift x₁ x₂).left ∣_ U) (by
    show (lift x₁ x₂).left ∣_ U ≫ U.ι ≫ (A ⊗ A).hom = Y'.ι ≫ Y.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w])
  have hpw : p ≫ ιW = w ≫ lift x₁ x₂ := Over.OverMorphism.ext (morphismRestrict_ι _ _)
  have : IsDominant p.left := IsZariskiLocalAtTarget.restrict hdom U
  have e₁ : p ≫ v₁ ≫ f = w ≫ y₁ :=
    h₁ Z' w (p ≫ v₁) (by rw [Category.assoc, hv₁, ← Category.assoc, hpw, Category.assoc, lift_fst])
  have e₂ : p ≫ v₂ ≫ f = w ≫ y₂ :=
    h₂ Z' w (p ≫ v₂) (by rw [Category.assoc, hv₂, ← Category.assoc, hpw, Category.assoc, lift_snd])
  have e₃ : p ≫ v₃ ≫ f = w ≫ (y₁ * y₂) :=
    h₃ Z' w (p ≫ v₃) (by
      rw [Category.assoc, hv₃, ← Category.assoc, hpw, Category.assoc, MonObj.comp_mul, lift_fst, lift_snd])
  have key : (v₁ ≫ f) * (v₂ ≫ f) = v₃ ≫ f := by
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated A.hom ?_ p.left ?_)
    · rw [Over.w, Over.w]
    · have : p ≫ ((v₁ ≫ f) * (v₂ ≫ f)) = p ≫ (v₃ ≫ f) := by
        rw [MonObj.comp_mul, e₁, e₂, e₃, MonObj.comp_mul]
      exact congrArg CommaMorphism.left this
  have hU : ∀ q : Z.left, (lift (u₁ ≫ j) (u₂ ≫ j)).left q ∈ Set.range ιW.left := by
    intro q
    show _ ∈ Set.range U.ι
    rw [Scheme.Opens.range_ι]
    have hq : ∀ (g : A ⊗ A ⟶ A) (u : Z ⟶ V), lift (u₁ ≫ j) (u₂ ≫ j) ≫ g = u ≫ j →
        (lift (u₁ ≫ j) (u₂ ≫ j)).left q ∈ g.left ⁻¹ᵁ R := fun g u e => by
      show g.left ((lift (u₁ ≫ j) (u₂ ≫ j)).left q) ∈ Set.range j.left
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
      exact ⟨u.left q, by rw [Over.comp_left, Scheme.Hom.comp_apply]⟩
    exact ⟨⟨hq _ u₁ (lift_fst _ _), hq _ u₂ (lift_snd _ _)⟩,
      hq _ u₃ (by rw [MonObj.comp_mul, lift_fst, lift_snd, hu])⟩
  obtain ⟨g, hg⟩ := GlobalTheory.GenericHom.exists_lift ιW (lift (u₁ ≫ j) (u₂ ≫ j)) hU
  have canc : ∀ a b : Z ⟶ V, a ≫ j = b ≫ j → a = b := fun a b e =>
    Over.OverMorphism.ext ((cancel_mono j.left).1 (congrArg CommaMorphism.left e))
  have c₁ : g ≫ v₁ = u₁ := canc _ _ (by rw [Category.assoc, hv₁, ← Category.assoc, hg, lift_fst])
  have c₂ : g ≫ v₂ = u₂ := canc _ _ (by rw [Category.assoc, hv₂, ← Category.assoc, hg, lift_snd])
  have c₃ : g ≫ v₃ = u₃ := canc _ _ (by
    rw [Category.assoc, hv₃, ← Category.assoc, hg, MonObj.comp_mul, lift_fst, lift_snd, hu])
  rw [← c₁, ← c₂, ← c₃, Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul, key]

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.ZH

theorem thetaSys_gen_tuple (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) :
    ∃ (J₀ : Type) (_ : Fintype J₀) (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) ∧
      Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω := by
  obtain ⟨s, hs⟩ := S.fg
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  let t₀ : Option s → Ω := fun i => match i with | none => 1 | some y => (y : Ω)
  refine ⟨Option s, inferInstance, t₀, ⟨none, one_ne_zero⟩, ?_⟩
  set K := Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) with hK
  have hbase : ∀ a : o, algebraMap o Ω a ∈ K := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hgen : ∀ y ∈ s, y ∈ K := by
    intro y hy
    apply Subfield.subset_closure
    refine Or.inr ⟨(x₀, none), (x₀, some ⟨y, hy⟩), ?_⟩
    simp only [t₀, mul_one]
    field_simp
  let KA : Subalgebra o Ω :=
    { K.toSubring with algebraMap_mem' := hbase }
  have hR : S.R ≤ KA := by
    rw [← hs]
    exact Algebra.adjoin_le (fun y hy => hgen y hy)
  have hall : ∀ x : Ω, x ∈ K := by
    intro x
    obtain ⟨a, ha, b, hb, rfl⟩ := S.frac x
    exact K.div_mem (hR ha) (hR hb)
  refine ⟨⟨{1}, eq_top_iff.mpr fun x _ => ?_⟩⟩
  simp only [Finset.coe_singleton]
  rw [Submodule.mem_span_singleton]
  exact ⟨⟨x, hall x⟩, by simp [Algebra.smul_def]; rfl⟩

end GlobalTheory.ZH
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.HHFibre

open GlobalTheory.ZH GlobalTheory.ZH.RatModel

theorem isHom_of_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω} {q : Y.Z ⟶ M.Z}
    (hq : Y.pt ≫ q = M.pt) : M.IsHom Y (AlgHom.id o Ω) q := by
  show Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt
  rw [hq]
  have : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _
    rw [← Spec.map_id]; rfl
  rw [this, Category.id_comp]

theorem exists_pt (X : Scheme.{0}) (w : X) : ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X),
    y (IsLocalRing.closedPoint K) = w :=
  ⟨X.residueField w, inferInstance, X.fromSpecResidueField w, Scheme.fromSpecResidueField_apply _ _⟩

theorem isUnit_of_isUnit_comap {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω}
    {q : Y.Z ⟶ M.Z} (hq : M.IsHom Y (AlgHom.id o Ω) q) (w : Y.Z) {a : Ω} (ha : a ∈ M.O (q w))
    (ha' : a ∈ Y.O w) (hu : IsUnit (⟨a, ha'⟩ : Y.O w)) : IsUnit (⟨a, ha⟩ : M.O (q w)) := by
  obtain ⟨K, _, y, hy0⟩ := exists_pt Y.Z w
  have hy : Set.range y = {w} := hy0 ▸ range_eq_singleton y (IsLocalRing.closedPoint K)
  have hyq : Set.range (y ≫ q) = {q w} := by
    have := range_eq_singleton (y ≫ q) (IsLocalRing.closedPoint K)
    refine this.trans ?_
    rw [← hy0]
    rfl
  rw [← val_ne_zero_iff hyq]
  rw [← val_ne_zero_iff hy] at hu
  have ha2 : a ∈ M.O (q (y (IsLocalRing.closedPoint K))) := by rw [hy0]; exact ha
  have e := hq.val_comp y (IsLocalRing.closedPoint K) ha2
  simp only [AlgHom.id_apply] at e
  show M.val (y ≫ q) a ≠ 0
  rw [e]
  exact hu

theorem HH_eq_of_hom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M Y : RatModel o Ω)
    (q : Y.Z ⟶ M.Z), Y.pt ≫ q = M.pt → M.HasDiv S.th → ∀ w : Y.Z, S.HH Y w = S.HH M (q w) := by
  intro o Ω _ _ _ S M Y q hq hdiv w
  have hh := isHom_of_pt hq
  unfold ThetaSys.HH
  congr 1
  ext x
  simp only [ThetaSys.supI, Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨x₀, h₀⟩ := hdiv (q w)
    have h₀' : Y.Div S.th x₀ w := by simpa using hh.div h₀
    rw [h₀.div_iff_isUnit]
    exact isUnit_of_isUnit_comap hh w _ _ ((h₀'.div_iff_isUnit x).1 hx)
  · intro hx
    simpa using hh.div hx

end GlobalTheory.Poinc.HHFibre
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.mem_stalk_of_classicalValues_norm_le_one : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ f ∈ M.ringOn (U₀ : Set M.Z), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ x y → ‖M.val (gPt p ≫ y) f‖ ≤ 1) → f ∈ M.O x := by
  first | exact @GlobalTheory.Poinc.mem_O_of_norm_val_le_one | exact GlobalTheory.Poinc.mem_O_of_norm_val_le_one | (intros; apply GlobalTheory.Poinc.mem_O_of_norm_val_le_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DvrTrait
open GlobalTheory.Points

theorem exists_factor_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {K : Type} [Field K] (y : Sp K ⟶ M.Z) (hy : ∀ w, y w = genericPoint M.Z) :
    ∃ β : Ω →+* K, y = spMap β ≫ M.pt := by
  have hs : ∀ w, y w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf y _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  refine ⟨β, ?_⟩
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
  have h1 := top_le_preimage_of_specializes hs hz
  have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
  refine ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_
  exact ((valR_spMap_comp β M.pt U h2 f).trans (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f)).symm

theorem exists_trait : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y X M : RatModel o Ω)
    (f : M.Z ⟶ X.Z) (d : Y.Z ⟶ X.Z), X.IsHom M (AlgHom.id o Ω) f → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d →
    ∀ z : M.Z, f z ∈ Set.range d → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (ξ : Sp V ⟶ M.Z) (τ : Sp V ⟶ Y.Z) (κ : Ω →+* FractionRing V), z ∈ Set.range ξ ∧
      spMap (algebraMap V (FractionRing V)) ≫ ξ = spMap κ ≫ M.pt ∧
      spMap (algebraMap V (FractionRing V)) ≫ τ = spMap κ ≫ Y.pt := by
  intro o Ω _ _ _ _ Y X M f d hf hd hop z hz
  obtain ⟨V, _, _, _, _, ξ, -, hξ, w, hw⟩ := GlobalTheory.DvrCentre.exists_complete_dvr_centre o Ω M z
  have ef : M.pt ≫ f = X.pt := by
    have h := hf
    have e : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    rw [RatModel.IsHom, e, Category.id_comp] at h
    exact h
  have ed : Y.pt ≫ d = X.pt := by
    have h := hd
    have e : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    rw [RatModel.IsHom, e, Category.id_comp] at h
    exact h
  have hbot : ξ (⊥ : PrimeSpectrum V) = genericPoint M.Z := by
    have h2 : (⊥ : PrimeSpectrum V) ⤳ w := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have h3 := h2.map ξ.continuous
    rw [hw] at h3
    exact (h3.antisymm (genericPoint_specializes _)).eq
  have hy : ∀ u, (spMap (algebraMap V (FractionRing V)) ≫ ξ) u = genericPoint M.Z := fun u => by
    refine (Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg ξ ?_) hbot)
    rw [Subsingleton.elim u (⊥ : PrimeSpectrum (FractionRing V))]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V)))
  obtain ⟨κ, hκ⟩ := exists_factor_pt M _ hy
  have hsp : ∀ u : Sp V, (ξ ≫ f) u ⤳ f z := fun u => by
    rw [← hξ, Scheme.Hom.comp_apply]
    exact ((IsLocalRing.specializes_closedPoint (R := V) u).map ξ.continuous).map f.continuous
  have hr : Set.range (ξ ≫ f) ⊆ Set.range d := by
    rintro _ ⟨u, rfl⟩
    exact (hsp u).mem_open d.isOpenEmbedding.isOpen_range hz
  refine ⟨V, inferInstance, inferInstance, inferInstance, ξ, IsOpenImmersion.lift d (ξ ≫ f) hr, κ,
    ⟨_, hξ⟩, hκ, ?_⟩
  rw [← cancel_mono d, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, hκ, Category.assoc,
    Category.assoc, ef, ed]

end GlobalTheory.DvrTrait
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.NormalClosureRing

theorem exists_integralClosure_finite : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (κ : o₁ →+* o₂), κ.Finite → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ h.Finite ∧ IsIntegrallyClosed R ∧ ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ x ∈ R, σ x ∈ R := by
  intro o₁ Ω₁ _ _ _ _ R₁ hR₁ hfrac o₂ Ω₂ _ _ _ _ _ _ κ hκ hcomp
  haveI : IsDedekindDomain o₁ := ArithBase.ded (Ω := Ω₁)
  haveI : CharZero Ω₁ := ArithBase.char (o := o₁)
  have hinj₁ : Function.Injective (algebraMap o₁ Ω₁) := ArithBase.inj
  haveI : CharZero o₁ := (algebraMap o₁ Ω₁).charZero
  haveI : Algebra.FiniteType o₁ R₁ := (Subalgebra.fg_iff_finiteType R₁).mp hR₁
  haveI : FaithfulSMul o₁ R₁ := (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b hab => hinj₁ (congrArg Subtype.val hab)
  haveI : FaithfulSMul R₁ Ω₁ := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI : IsFractionRing R₁ Ω₁ := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hfrac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  haveI : IsScalarTower R₁ Ω₁ Ω₂ := inferInstance
  let C := integralClosure R₁ Ω₂
  have hmem : ∀ x : o₂, algebraMap o₂ Ω₂ x ∈ C := by
    intro x
    obtain ⟨p, hp, hpx⟩ := hκ.to_isIntegral x
    refine ⟨p.map (algebraMap o₁ R₁), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have := congrArg (algebraMap o₂ Ω₂) hpx
    rw [Polynomial.hom_eval₂, map_zero, hcomp] at this
    exact this
  let R : Subalgebra o₂ Ω₂ :=
    { toSubsemiring := C.toSubsemiring
      algebraMap_mem' := hmem }
  let h : R₁ →+* R := (algebraMap R₁ Ω₂).codRestrict R fun a => (isIntegral_algebraMap : IsIntegral R₁ (algebraMap R₁ Ω₂ a))
  have hh : ∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a := fun a => rfl
  haveI : Module.Finite R₁ C := GlobalTheory.finite_integralClosure_dedekind o₁ R₁ Ω₁ Ω₂
  classical
  have hfg : R.FG := by
    obtain ⟨s, hs⟩ := hR₁
    obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule R₁ C).FG)
    refine ⟨s.image (algebraMap Ω₁ Ω₂) ∪ t.image Subtype.val, le_antisymm ?_ ?_⟩
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe] at hy
      rcases hy with ⟨a, ha, rfl⟩ | ⟨z, -, rfl⟩
      · have ha' : a ∈ R₁ := hs ▸ Algebra.subset_adjoin ha
        exact (h ⟨a, ha'⟩).2
      · exact z.2
    · set A := Algebra.adjoin o₂ ((s.image (algebraMap Ω₁ Ω₂) ∪ t.image Subtype.val : Finset Ω₂) : Set Ω₂)
      have hR₁A : ∀ z ∈ Algebra.adjoin o₁ (s : Set Ω₁), algebraMap Ω₁ Ω₂ z ∈ A := by
        intro z hz
        induction hz using Algebra.adjoin_induction with
        | mem z hz => exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hz)))
        | algebraMap r =>
          have := congrArg (fun f => f r) hcomp
          simp only [RingHom.comp_apply] at this
          rw [← this]
          exact A.algebraMap_mem _
        | add x y _ _ hx hy => rw [map_add (f := _)]; exact A.add_mem hx hy
        | mul x y _ _ hx hy => rw [map_mul]; exact A.mul_mem hx hy
      suffices key : ∀ y : C, y ∈ Submodule.span R₁ (t : Set C) → (y : Ω₂) ∈ A from
        fun x hx => key ⟨x, hx⟩ (ht ▸ Submodule.mem_top)
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy)))
      | zero => exact A.zero_mem
      | add y z _ _ hy hz => exact A.add_mem hy hz
      | smul r y _ hy =>
        convert A.mul_mem (hR₁A r.1 (hs ▸ r.2)) hy using 1
        first | rfl | exact Algebra.smul_def r (y : Ω₂) | simp [Algebra.smul_def]
  letI : Algebra R₁ R := h.toAlgebra
  haveI : IsScalarTower R₁ R Ω₂ := .of_algebraMap_eq fun a => rfl
  haveI : IsIntegralClosure R R₁ Ω₂ :=
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := fun {x} => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩ }
  have hfin : h.Finite := GlobalTheory.finite_of_isIntegralClosure_dedekind o₁ R₁ Ω₁ Ω₂ R
  have hic : IsIntegrallyClosed R := integralClosure.isIntegrallyClosedOfFiniteExtension (R := R₁) Ω₁ (L := Ω₂)
  refine ⟨R, h, hfg, ?_, hh, hfin, hic, ?_⟩
  · intro x
    have hxi : IsIntegral Ω₁ x := Algebra.IsIntegral.isIntegral x
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors R₁) x hxi
    have hm0 : algebraMap R₁ Ω₂ (m : R₁) ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply R₁ Ω₁ Ω₂]
      exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors m.2)
    refine ⟨_, hm, algebraMap R₁ Ω₂ (m : R₁), isIntegral_algebraMap, ?_⟩
    rw [Submonoid.smul_def, Algebra.smul_def, mul_div_cancel_left₀ _ hm0]
  · intro σ x hx
    exact (show IsIntegral R₁ x from hx).map (σ.toAlgHom.restrictScalars R₁)

end GlobalTheory.Poinc.NormalClosureRing
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem realPt_comp_pow {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (u : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    u ≫ x ^ n = (u ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem realPt_inj_of_grpPullback : ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₂ : ThetaSys o₂ Ω₂) (ρ₂ : S₂.Real) {T : Scheme.{0}} (G : Over T) [GrpObj G] (f : Sp S₂.R ⟶ T) (φ : ρ₂.P.A.left ⟶ G.left), IsGrpPullback ρ₂.P.A G f φ → ∀ x y : S₂.Gam, (ρ₂.pt x).left ≫ φ = (ρ₂.pt y).left ≫ φ → x = y := by
  intro o₂ Ω₂ _ _ _ S₂ ρ₂ T G _ f φ hφ x y hxy
  have hpt : ρ₂.pt x = ρ₂.pt y := by
    ext
    exact hφ.1.hom_ext hxy (by simp only [Category.assoc, Over.w])
  have hzero : ρ₂.pt 0 = 1 := by
    have h := ρ₂.pt_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hsmul : ∀ (a : S₂.Gam) (n : ℕ), ρ₂.pt (n • a) = ρ₂.pt a ^ n := by
    intro a n
    induction n with
    | zero => rw [zero_smul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, ρ₂.pt_add, ih, pow_succ]
  have hkill : ∀ a : S₂.Gam, ρ₂.pt a ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [← hsmul]
    have : (S₂.r * S₂.N) • a = 0 := by
      funext i
      simp [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self]
    rw [this, hzero]
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap ((algebraMap Ω₂ K).comp (S₂.R.val : S₂.R →+* Ω₂))
  let u : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  have hz : (u ≫ ρ₂.pt x) ^ (S₂.r * S₂.N) = 1 := by
    rw [← realPt_comp_pow, hkill, MonObj.comp_one]
  obtain ⟨a, _, huniq⟩ := ρ₂.pt_bij K x₀ (u ≫ ρ₂.pt x) hz
  have h1 := huniq x rfl
  have h2 := huniq y (by rw [hpt])
  exact h1.trans h2.symm

end GlobalTheory.Poinc.Sep
end
end
