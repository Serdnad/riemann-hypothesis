module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuativeLiftExistsUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem torsionAlong_iff_pullback_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (N : ℕ), IsGrpPullback G₀ G x ψ → (∀ i : Γ.G.left ⟶ G.left, Γ.IsTorsionAlong G x N i → ∃ i₀ : Γ.G.left ⟶ G₀.left, i₀ ≫ ψ = i ∧ Γ.IsTorsionAlong G₀ (𝟙 _) N i₀) ∧ ∀ i₀ : Γ.G.left ⟶ G₀.left, Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ → Γ.IsTorsionAlong G x N (i₀ ≫ ψ) :=
  @PositivityTheory.UnitarySelfGeneration.isTorsionAlong_iff_of_isGrpPullback

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem eq_of_isIso_restrict {W X' : Scheme.{0}} (f : X' ⟶ W) (U : W.Opens) (hU : IsIso (f ∣_ U)) {y y' : X'}
    (hy : f y ∈ U) (hy' : f y' ∈ U) (e : f y = f y') : y = y' := by
  haveI := IsOpenImmersion.of_isIso (f ∣_ U)
  let a : (f ⁻¹ᵁ U : Scheme) := ⟨y, hy⟩
  let a' : (f ⁻¹ᵁ U : Scheme) := ⟨y', hy'⟩
  have h : (f ∣_ U) a = (f ∣_ U) a' :=
    Subtype.ext (by rw [morphismRestrict_base_coe, morphismRestrict_base_coe]; exact e)
  exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective h)

private theorem eq_closedPoint_of_isField {R : Type} [CommRing R] [IsLocalRing R] (hR : IsField R)
    (z : PrimeSpectrum R) : z = IsLocalRing.closedPoint R := by
  apply PrimeSpectrum.ext
  have h := (IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).1 hR
  have h1 : z.asIdeal ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal z.isPrime.ne_top
  show z.asIdeal = IsLocalRing.maximalIdeal R
  rw [h] at h1 ⊢
  exact le_bot_iff.1 h1

private theorem eq_genPt_of_specializes_of_bijective {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hb).toMulEquiv
  have hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨q, rfl⟩ := hy'
  rw [eq_closedPoint_of_isField hF q, Scheme.fromSpecStalk_closedPoint]

private theorem surjective_stalkClosedPointTo_of_comp {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
    (g : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y) (ξ : Spec (CommRingCat.of Ω) ⟶ Y) (h : g ≫ f = ξ)
    (hξ : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) :
    Function.Surjective (Scheme.stalkClosedPointTo g).hom := by
  subst h
  rw [Scheme.stalkClosedPointTo_comp] at hξ
  intro z
  obtain ⟨a, ha⟩ := hξ z
  exact ⟨(Scheme.Hom.stalkMap f _).hom a, ha⟩

theorem exists_lift_isCptGen : ∀ (W X' : Scheme.{0}) (f : X' ⟶ W) (U : W.Opens) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W),
    IsIso (f ∣_ U) → genPt ξ ∈ U → IsCptGen ξ → (∀ x : X', IsDomain (X'.presheaf.stalk x)) →
    ∃ ξ' : Sp Ω ⟶ X', ξ' ≫ f = ξ ∧ IsCptGen ξ' := by
  intro W X' f U Ω _ ξ hiso hU hξ hdom
  obtain ⟨hb, -⟩ := hξ
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [eq_closedPoint_of_isField (Field.toIsField Ω) z]
    exact hU
  let ξ' : Sp Ω ⟶ X' := IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hfac : ξ' ≫ f = ξ := by
    simp only [ξ', Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]
  have hfg : f (genPt ξ') = genPt ξ := by
    have h3 := Scheme.Hom.comp_apply ξ' f (IsLocalRing.closedPoint Ω)
    rw [hfac] at h3
    exact h3.symm
  have hmem : genPt ξ' ∈ f ⁻¹ᵁ U := by
    show f (genPt ξ') ∈ U
    rw [hfg]; exact hU
  refine ⟨ξ', hfac, ?_⟩
  refine isCptGen_of_maximal_of_surjective hdom ξ' ?_ ?_
  · intro y hy
    have hyU : y ∈ f ⁻¹ᵁ U := hy.mem_open (f ⁻¹ᵁ U).isOpen hmem
    have h1 : f y ⤳ genPt ξ := by
      have h2 := hy.map f.continuous
      rwa [hfg] at h2
    exact eq_of_isIso_restrict f U hiso hyU hmem ((eq_genPt_of_specializes_of_bijective ξ hb (f y) h1).trans hfg.symm)
  · exact surjective_stalkClosedPointTo_of_comp ξ' f ξ hfac hb.2

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.integral_element_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ), IsCptGen ξ → IsIntegrallyClosed (X.presheaf.stalk p.1) → ∀ a : Ω, IsIntegral ℤ a → a ∈ regAt ξ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntReg.mem_regAt_of_isIntegral_of_stalk | exact GlobalTheory.CompanionTheory.Ar.IntReg.mem_regAt_of_isIntegral_of_stalk | (intros; apply GlobalTheory.CompanionTheory.Ar.IntReg.mem_regAt_of_isIntegral_of_stalk <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SqAdd

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {S : Scheme.{0}} {C B : Type} [CommRing C] [CommRing B]

theorem dualMap_comp_algebraMap (φ : C →+* B) :
    (dualMap φ).comp (algebraMap C (DualNumber C)) = (algebraMap B (DualNumber B)).comp φ := by
  refine RingHom.ext fun c => ?_
  apply TrivSqZeroExt.ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : C →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualMap φ) =
      φ.comp (TrivSqZeroExt.fstHom C C C).toRingHom := by
  refine RingHom.ext fun c => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

def epsIdeal (B : Type) [CommRing B] : Ideal (DualNumber B) :=
  RingHom.ker (TrivSqZeroExt.fstHom B B B).toRingHom

theorem epsIdeal_sq : epsIdeal B ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have ha' : a.fst = 0 := ha
  have hb' : b.fst = 0 := hb
  rw [Ideal.mem_bot]
  apply TrivSqZeroExt.ext <;> simp [ha', hb']

def redMap (B : Type) [CommRing B] : B →+* DualNumber B ⧸ epsIdeal B :=
  (Ideal.Quotient.mk (epsIdeal B)).comp (algebraMap B (DualNumber B))

theorem mk_eq_redMap_comp :
    Ideal.Quotient.mk (epsIdeal B) = (redMap B).comp (TrivSqZeroExt.fstHom B B B).toRingHom := by
  refine RingHom.ext fun a => ?_
  change Ideal.Quotient.mk (epsIdeal B) a = Ideal.Quotient.mk (epsIdeal B) (algebraMap B (DualNumber B) a.fst)
  rw [Ideal.Quotient.eq]
  change (TrivSqZeroExt.fstHom B B B).toRingHom _ = 0
  simp [TrivSqZeroExt.algebraMap_eq_inl]

def restr (φ : C →+* B) (y : Sp C ⟶ S) :
    Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ epsAt y :=
  Over.homMk (spMap (dualMap φ)) (by
    change spMap _ ≫ spMap _ ≫ y = spMap _ ≫ spMap _ ≫ y
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom (dualMap_comp_algebraMap φ))

theorem red_restr (G : Over S) [GrpObj G] (φ : C →+* B) (y : Sp C ⟶ S) (v : epsAt y ⟶ G) (tv : IsTanAt G y v) :
    spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ (restr φ y ≫ v).left =
      spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
        (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left := by
  have hred : spMap (redMap B) = spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (algebraMap B (DualNumber B)) := by
    rw [← Spec.map_comp]; rfl
  have hmk : spMap (Ideal.Quotient.mk (epsIdeal B)) =
      spMap (redMap B) ≫ spMap (TrivSqZeroExt.fstHom B B B).toRingHom := by
    rw [← Spec.map_comp]
    exact congrArg (fun f => spMap f) mk_eq_redMap_comp
  have hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (dualMap φ) =
      spMap φ ≫ spMap (TrivSqZeroExt.fstHom C C C).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => spMap f) (fst_comp_dualMap φ)
  let T : Over S := Over.mk (spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
    spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y)
  let m₁ : T ⟶ Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) :=
    Over.homMk (spMap (Ideal.Quotient.mk (epsIdeal B))) rfl
  let m₂ : T ⟶ Over.mk y := Over.homMk (spMap (redMap B) ≫ spMap φ) (by
    change (spMap (redMap B) ≫ spMap φ) ≫ y = _
    rw [hred]
    simp [T])
  have c : m₁ ≫ (1 : _ ⟶ G) = m₂ ≫ (1 : _ ⟶ G) := by
    rw [MonObj.comp_one, MonObj.comp_one]
  have c' : spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
      (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left =
      (spMap (redMap B) ≫ spMap φ) ≫ (1 : Over.mk y ⟶ G).left := congrArg CommaMorphism.left c
  rw [c']
  have tv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left := tv
  rw [← tv']
  change spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (dualMap φ) ≫ v.left = _
  rw [hmk]
  simp only [Category.assoc]
  rw [reassoc_of% hfst]

theorem top_le_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (k : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ k ⁻¹ᵁ U) :
    ⊤ ≤ (p ≫ k) ⁻¹ᵁ U := fun z _ => by
  change k (p z) ∈ U
  exact h (show p z ∈ (⊤ : Y.Opens) from trivial)

theorem appTop_appLE {X Y Z : Scheme.{0}} (p : X ⟶ Y) (k : Y ⟶ Z) (k' : X ⟶ Z) (e : k' = p ≫ k) (U : Z.Opens)
    (h : ⊤ ≤ k ⁻¹ᵁ U) (h' : ⊤ ≤ k' ⁻¹ᵁ U) (s : Γ(Z, U)) :
    p.appTop.hom ((k.appLE U ⊤ h).hom s) = (k'.appLE U ⊤ h').hom s := by
  subst e
  have hle : (⊤ : X.Opens) ≤ p ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  have hp : p.appTop = p.appLE ⊤ ⊤ hle := Scheme.Hom.app_eq_appLE ..
  have : k.appLE U ⊤ h ≫ p.appTop = (p ≫ k).appLE U ⊤ h' := by
    rw [hp]
    exact Scheme.Hom.appLE_comp_appLE ..
  rw [← this]
  rfl

theorem tan_local (G : Over S) [GrpObj G] [IsLocalRing B] (φ : C →+* B) (y : Sp C ⟶ S) (v w : epsAt y ⟶ G)
    (tv : IsTanAt G y v) (tw : IsTanAt G y w) (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U)
    (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U) (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)) :
    (spMap (dualMap φ)).appTop.hom
        (((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s) =
      (spMap (dualMap φ)).appTop.hom ((v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s) := by
  have hmul : ((restr φ y ≫ v) * (restr φ y ≫ w)).left = spMap (dualMap φ) ≫ (v * w).left :=
    congrArg CommaMorphism.left (MonObj.comp_mul (restr φ y) v w).symm
  have hone : (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left =
      spMap (dualMap φ) ≫ (1 : epsAt y ⟶ G).left :=
    congrArg CommaMorphism.left (MonObj.comp_one (restr φ y)).symm
  have hxv : ⊤ ≤ (restr φ y ≫ v).left ⁻¹ᵁ U := top_le_comp (spMap (dualMap φ)) v.left U hv
  have hxw : ⊤ ≤ (restr φ y ≫ w).left ⁻¹ᵁ U := top_le_comp (spMap (dualMap φ)) w.left U hw
  have hxvw : ⊤ ≤ ((restr φ y ≫ v) * (restr φ y ≫ w)).left ⁻¹ᵁ U := by
    rw [hmul]; exact top_le_comp _ _ U hvw
  have hx1 : ⊤ ≤ (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left ⁻¹ᵁ U := by
    rw [hone]; exact top_le_comp _ _ U h1
  have key := GlobalTheory.T.first_order_points_commute S G B (spMap φ ≫ y) (DualNumber B) (algebraMap B (DualNumber B)) (epsIdeal B)
    epsIdeal_sq (restr φ y ≫ v) (restr φ y ≫ w) (red_restr G φ y v tv) (red_restr G φ y w tw) U hxv hxw hxvw hx1 s
  rw [map_add (f := _), map_add (f := _),
    appTop_appLE (spMap (dualMap φ)) _ _ hmul U hvw hxvw s,
    appTop_appLE (spMap (dualMap φ)) _ _ hone U h1 hx1 s,
    appTop_appLE (spMap (dualMap φ)) v.left (restr φ y ≫ v).left rfl U hv hxv s,
    appTop_appLE (spMap (dualMap φ)) w.left (restr φ y ≫ w).left rfl U hw hxw s]
  exact key

theorem dualMap_fst (φ : C →+* B) (a : DualNumber C) : (dualMap φ a).fst = φ a.fst := by
  simp [dualMap]

theorem dualMap_snd (φ : C →+* B) (a : DualNumber C) : (dualMap φ a).snd = φ a.snd := by
  simp [dualMap]

theorem dual_eq_of_localization (a b : DualNumber C)
    (h : ∀ (q : Ideal C) [q.IsMaximal], dualMap (algebraMap C (Localization.AtPrime q)) a =
      dualMap (algebraMap C (Localization.AtPrime q)) b) : a = b := by
  have h0 : ∀ r r' : C, (∀ (q : Ideal C) [q.IsMaximal], algebraMap C (Localization.AtPrime q) r =
      algebraMap C (Localization.AtPrime q) r') → r = r' := by
    intro r r' hr
    rw [← sub_eq_zero]
    refine eq_zero_of_localization _ fun q hq => ?_
    rw [map_sub, hr q, sub_self]
  apply TrivSqZeroExt.ext
  · exact h0 _ _ fun q _ => by
      rw [← dualMap_fst, ← dualMap_fst, h q]
  · exact h0 _ _ fun q _ => by
      rw [← dualMap_snd, ← dualMap_snd, h q]

theorem gamma_eq_of_localization (a b : Γ(Sp (DualNumber C), ⊤))
    (h : ∀ (q : Ideal C) [q.IsMaximal], (spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom a =
      (spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom b) : a = b := by
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).commRingCatIsoToRingEquiv.injective
  refine hinj (dual_eq_of_localization _ _ fun q _ => ?_)
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap (algebraMap C (Localization.AtPrime q))))
  have e' : ∀ c : Γ(Sp (DualNumber C), ⊤), dualMap (algebraMap C (Localization.AtPrime q))
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Localization.AtPrime q)))).hom
        ((spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom c) := fun c =>
    (congrArg (fun f => f.hom c) e).symm
  rw [e', e', h q]

theorem tan_mul_add : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S)
    (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
    ∀ (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U) (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U)
      (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)),
      ((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s =
        (v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s := by
  intro S G _ C _ y v w tv tw U hv hw hvw h1 s
  exact gamma_eq_of_localization _ _ fun q _ =>
    tan_local G (algebraMap C (Localization.AtPrime q)) y v w tv tw U hv hw hvw h1 s

end GlobalTheory.CompanionTheory.Ar.SqAdd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.prime_chart_existsUnique_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ), x c ≠ 0 → ∀ I : Ideal (Algebra.adjoin o (Set.range fun j => x j / x c)), I.IsPrime → ∃! p : Cpt ξ, InChart ξ x c p ∧ ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c), s ∉ I ↔ unitAt ξ p (s : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chart_point_of_prime | exact GlobalTheory.CompanionTheory.Ar.chart_point_of_prime | (intros; apply GlobalTheory.CompanionTheory.Ar.chart_point_of_prime <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.coord_over_int_of_finite_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] [Module.Finite ℤ o] (κ : Type) [Finite κ] (x : κ → Ω), CoordTie o ξ x → ∃ (N : ℕ) (x' : Fin (N + 1) → Ω), CoordTie ℤ ξ x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite | exact GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.valuative_lift_existsUnique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), CoordTie ℤ ξ x → ∀ (C : Type) [Field C] (V : ValuationSubring C) (zC : Spec (CommRingCat.of C) ⟶ X), genPt ξ ⤳ centre zC → ∃! z : Spec (CommRingCat.of V) ⟶ X, genPt ξ ⤳ centre z ∧ Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z = zC := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coord_point_extends | exact GlobalTheory.CompanionTheory.Ar.coord_point_extends | (intros; apply GlobalTheory.CompanionTheory.Ar.coord_point_extends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac

theorem exists_frac_field {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {W : Scheme.{0}}
    {ξ : Spec (CommRingCat.of Ω) ⟶ W} {κ : Type} {x : κ → Ω} (h : CoordTie F ξ x) :
    ∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ r ∈ Algebra.adjoin F (Set.range fun j => x j / x c),
      ∃ s ∈ Algebra.adjoin F (Set.range fun j => x j / x c), s ≠ 0 ∧ a * s = r := by
  let p₀ : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := h.cover p₀
  obtain ⟨U, hU, hq⟩ := h.affine c hc.1
  have h0 : genPt ξ ∈ U := (hq _).2 ⟨specializes_rfl, hc⟩
  have key : ∀ r : Γ(W, U), (Scheme.stalkClosedPointTo ξ).hom (W.presheaf.germ U (genPt ξ) h0 r) ∈
      Algebra.adjoin F (Set.range fun j => x j / x c) := fun r => by
    rw [h.ring c hc.1]
    intro q hqc
    have hqU : q.1 ∈ U := (hq _).2 ⟨q.2, hqc⟩
    refine ⟨W.presheaf.germ U q.1 hqU r, ?_⟩
    show (Scheme.stalkClosedPointTo ξ).hom (W.presheaf.stalkSpecializes q.2 (W.presheaf.germ U q.1 hqU r)) = _
    congr 1
    exact W.presheaf.germ_stalkSpecializes_apply hqU q.2 r
  refine ⟨c, hc.1, fun a => ?_⟩
  obtain ⟨s, rfl⟩ := h.gen.bij.2 a
  letI := W.presheaf.algebra_section_stalk (⟨genPt ξ, h0⟩ : U)
  have hl := hU.isLocalization_stalk ⟨genPt ξ, h0⟩
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨genPt ξ, h0⟩).asIdeal.primeCompl
    (S := W.presheaf.stalk (genPt ξ)) s
  refine ⟨_, key r, _, key t, ?_, ?_⟩
  · have := IsLocalization.map_units (W.presheaf.stalk (genPt ξ)) t
    exact (this.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  · exact (map_mul (Scheme.stalkClosedPointTo ξ).hom _ _).symm.trans (congrArg _ e)

theorem exists_clear {o F : Type} [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] {Ω : Type}
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] {S : Set Ω} {b : Ω}
    (hb : b ∈ Algebra.adjoin F S) :
    ∃ d : o, d ≠ 0 ∧ ∃ g ∈ Algebra.adjoin o S, algebraMap o Ω d * b = g := by
  induction hb using Algebra.adjoin_induction with
  | mem y hy => exact ⟨1, one_ne_zero, y, Algebra.subset_adjoin hy, by simp⟩
  | algebraMap f =>
    obtain ⟨⟨n, d⟩, e⟩ := IsLocalization.surj (nonZeroDivisors o) f
    refine ⟨d, nonZeroDivisors.ne_zero d.2, algebraMap o Ω n, Subalgebra.algebraMap_mem _ n, ?_⟩
    rw [IsScalarTower.algebraMap_apply o F Ω n, IsScalarTower.algebraMap_apply o F Ω d, ← map_mul, ← e, mul_comm]
  | add u v _ _ hu hv =>
    obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := hu
    obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := hv
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, algebraMap o Ω d₂ * g₁ + algebraMap o Ω d₁ * g₂,
      add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) m₁) (mul_mem (Subalgebra.algebraMap_mem _ _) m₂), ?_⟩
    rw [← e₁, ← e₂, map_mul]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := hu
    obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := hv
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, g₁ * g₂, mul_mem m₁ m₂, ?_⟩
    rw [← e₁, ← e₂, map_mul]
    ring

theorem algebraMap_ne_zero {o F : Type} [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] {Ω : Type}
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] {d : o} (hd : d ≠ 0) : algebraMap o Ω d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply o F Ω d]
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd)

theorem chartRing_frac : ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type)
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (W : Scheme.{0}) (ξ' : Sp Ω ⟶ W) (κ : Type) (t : κ → Ω),
    CoordTie F ξ' t → ∃ c₀, t c₀ ≠ 0 ∧ ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀),
      ∃ h ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀), h ≠ 0 ∧ a = g / h := by
  intro o F _ _ _ _ _ Ω _ _ _ _ W ξ' κ t hT
  obtain ⟨c, hc, hf⟩ := exists_frac_field hT
  refine ⟨c, hc, fun a => ?_⟩
  obtain ⟨r, hr, s, hs, hs0, e⟩ := hf a
  obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := exists_clear (o := o) hr
  obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := exists_clear (o := o) hs
  have n₁ := algebraMap_ne_zero (F := F) (Ω := Ω) h₁
  have n₂ := algebraMap_ne_zero (F := F) (Ω := Ω) h₂
  have hg₂ : g₂ ≠ 0 := e₂ ▸ mul_ne_zero n₂ hs0
  refine ⟨algebraMap o Ω d₂ * g₁, mul_mem (Subalgebra.algebraMap_mem _ _) m₁,
    algebraMap o Ω d₁ * g₂, mul_mem (Subalgebra.algebraMap_mem _ _) m₂, mul_ne_zero n₁ hg₂, ?_⟩
  rw [eq_div_iff (mul_ne_zero n₁ hg₂), ← e₁, ← e₂, ← e]
  ring

end GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Reindex

theorem coordTie_one_block (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ)
    (x : Fin (N + 1) → Ω) (h : CoordTie ℤ ξ x) :
    CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) := by
  have he : Function.Surjective (fun c' : Unit → Fin (N + 1) => c' ()) :=
    fun j => ⟨fun _ => j, rfl⟩
  have hfun : (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) =
      fun c' : Unit → Fin (N + 1) => x (c' ()) := by
    funext c'
    simp
  rw [hfun]
  have hc : ∀ (c : Unit → Fin (N + 1)) p,
      InChart ξ (fun c' : Unit → Fin (N + 1) => x (c' ())) c p ↔ InChart ξ x (c ()) p :=
    fun c p => and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (c ()) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    exact ⟨fun _ => c, (hc _ p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (c ()) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have hr : (Set.range fun j : Unit → Fin (N + 1) => x (j ()) / x (c ())) =
        Set.range fun j => x j / x (c ()) :=
      he.range_comp fun j => x j / x (c ())
    simpa only [hc, hr] using h.ring (c ()) h0 a

end GlobalTheory.CompanionTheory.Ar.SncBase.Reindex
end
