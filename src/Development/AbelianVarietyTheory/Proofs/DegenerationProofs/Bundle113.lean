module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsaRos
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGrpObjSplitExtensionOfGenerators
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ModPrim

theorem exists_unit_and_residue_point : Out.Laws → Out.Laws2 → ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (c : Sp (OO p) ⟶ G.left) (w : J → OO p), c ≫ G.hom = spMap j → Crd H σ c w → (∃ i, cls i = 0 ∧ IsUnit (w i)) ∧ ∃ x : m.Φ.Pt, x.left ≫ m.r = rPt p ≫ c ∧ Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
  intro L₁ L₂ p _ V _ j G _ g N N' X _ q H J _ σ cls m hB c w hc hw
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have pb : IsPullback m.r m.Φ.G.hom G.hom (rPt p ≫ spMap j) := m.cart.1
  have hsq : (rPt p ≫ c) ≫ G.hom = 𝟙 _ ≫ rPt p ≫ spMap j := by
    rw [Category.assoc, hc, Category.id_comp]
  let x : m.Φ.Pt := Over.homMk (pb.lift (rPt p ≫ c) (𝟙 _) hsq) (pb.lift_snd _ _ hsq)
  have hx : x.left ≫ m.r = rPt p ≫ c := pb.lift_fst _ _ hsq
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists (R := kb p) (m.Φ.H_isLB 1) m.F x.left
  have h₁ := m.red x v hv
  rw [hx] at h₁
  have h₂ := CrdCalc.crd_map (IsLocalRing.residue (OO p)) hw
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique h₁ h₂
  have h₃ : Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
    have := CrdCalc.crd_smul u hv
    rwa [← funext hu] at this
  refine ⟨?_, x, hx, h₃⟩
  have hcov := (GlobalTheory.T.immBy_weight_zero' L₁ L₂ (kb p) m.Φ g N N' _ J _ m.F m.pol hB m.good m.dim).1
  have hmem : (x.left : Sp (kb p) ⟶ m.Φ.G.left) (IsLocalRing.closedPoint (kb p)) ∈
      ⨆ i ∈ {i | m.xe.symm (cls i) = 0}, Out.nonzeroLocus (m.F i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hmem
  obtain ⟨i, hi, hm⟩ := hmem
  refine ⟨i, m.xe.symm.map_eq_zero_iff.1 hi, ?_⟩
  have h₄ := (CrdCalc.crd_isUnit_iff i h₃).2 ((CrdCalc.top_le_iff _ _).2 hm)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h₄.ne_zero

end GlobalTheory.ZH.ModPrim
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.MultInt

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem pow_left_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {T : Over S'} {T₀ : Over S}
    (h : T.left ⟶ T₀.left) (hh : h ≫ T₀.hom = T.hom ≫ f) (x : T ⟶ (Over.pullback f).obj G) (x₀ : T₀ ⟶ G)
    (hx : h ≫ x₀.left = x.left ≫ pullback.fst G.hom f) (k : ℕ) :
    h ≫ (x₀ ^ k).left = (x ^ k).left ≫ pullback.fst G.hom f := by
  let h' : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk h hh
  have e : TorsionLift.ptsEquiv f G T _ rfl x = h' ≫ x₀ :=
    Over.OverMorphism.ext ((TorsionLift.ptsEquiv_left f G T _ rfl x).trans hx.symm)
  rw [← TorsionLift.ptsEquiv_left f G T _ rfl, map_pow, e, ← comp_pow]
  rfl

theorem exists_finite_factor {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] {X : Scheme.{0}} (s : X ⟶ Sp V)
    [LocallyOfFiniteType s] (φ : V →+* PadicAlgCl p) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K₀] (hφ : ∀ v, φ v ∈ K₀) (x : Sp (PadicAlgCl p) ⟶ X) (hx : x ≫ s = spMap φ) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K ∧ FiniteDimensional ℚ_[p] K ∧
      ∃ x' : Sp K ⟶ X, spMap K.val.toRingHom ≫ x' = x := by
  obtain ⟨U, hU, ψ', hψ'⟩ := exists_affineOpen_factor_of_isLocalRing x
  let A : Type := Γ(X, U)
  let i : Sp A ⟶ X := hU.fromSpec
  haveI : IsOpenImmersion i := hU.isOpenImmersion_fromSpec
  let ψ : A →+* PadicAlgCl p := ψ'.hom
  have hψ : spMap ψ ≫ i = x := hψ'
  obtain ⟨α, hα⟩ : ∃ α : V →+* A, spMap α = i ≫ s := by
    obtain ⟨α, hα⟩ := Spec.map_surjective (i ≫ s)
    exact ⟨α.hom, hα⟩
  have hft : α.FiniteType := by
    have : LocallyOfFiniteType (spMap α) := by rw [hα]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hψα : ψ.comp α = φ := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (?_ : spMap _ = spMap _))
    rw [← spMap_comp_spMap, hα, ← Category.assoc, hψ, hx]
  letI := α.toAlgebra
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (self := hft)
  haveI : Finite (ψ '' (t : Set A)) := (t.finite_toSet.image _).to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (ψ '' (t : Set A))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) := K₀ ⊔ IntermediateField.adjoin ℚ_[p] (ψ '' (t : Set A))
  have hk : K₀ ≤ K := le_sup_left
  have hmem : ∀ x, ψ x ∈ K := by
    intro x
    have hx : x ∈ Algebra.adjoin V (t : Set A) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact (le_sup_right : _ ≤ K) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      change (ψ.comp α) r ∈ K
      rw [hψα]; exact hk (hφ r)
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨K, hk, IntermediateField.finiteDimensional_sup _ _, spMap (ψ.codRestrict K hmem) ≫ i, ?_⟩
  rw [← Category.assoc, spMap_comp_spMap]
  exact hψ

theorem isProjOver_snd_snd {V F O K : Type} [CommRing V] [CommRing F] [CommRing O] [CommRing K] {X : Scheme.{0}}
    (s : X ⟶ Sp V) (α : V →+* F) (β : F →+* K) (ψ : V →+* O) (χ : O →+* K) (h : β.comp α = χ.comp ψ)
    (hp : IsProjOver (pullback.snd s (spMap α))) :
    IsProjOver (pullback.snd (pullback.snd s (spMap ψ)) (spMap χ)) := by
  have e : spMap χ ≫ spMap ψ = spMap β ≫ spMap α := by rw [spMap_comp_spMap, spMap_comp_spMap, h]
  have H := (IsPullback.of_hasPullback (pullback.snd s (spMap ψ)) (spMap χ)).paste_horiz
    (IsPullback.of_hasPullback s (spMap ψ))
  rw [e] at H
  exact ProjSpace.isProjOver_of_isPullback_spMap β
    (IsPullback.of_right' H (IsPullback.of_hasPullback s (spMap α))) hp

end GlobalTheory.ZH.MultInt

namespace GlobalTheory.ZH
open MultInt

theorem exists_int_pow : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : u.PtC), ∃ k : ℕ, 1 ≤ k ∧ u.Int (a ^ k) := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u a
  obtain ⟨-, -, -, K₀, hK₀, hr⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  haveI := u.semi.smooth
  haveI := u.semi.separated
  let θ : FractionRing u.V →+* PadicAlgCl p := algebraMap _ _
  let α : u.V →+* FractionRing u.V := algebraMap _ _
  have hθ : ∀ v, θ v ∈ K₀ := fun v => show θ v ∈ (K₀ : Set _) from hr ▸ ⟨v, rfl⟩
  have ha : u.toG a ≫ u.G.hom = spMap (θ.comp α) := by
    have := Over.w a
    rw [← spMap_comp_spMap, ThetaSys.Real.UTest.toG, Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ spMap α) this
  obtain ⟨K, hK, hfd, x, hx⟩ := exists_finite_factor u.G.hom (θ.comp α) K₀ (fun v => hθ _) (u.toG a) ha
  let β : FractionRing u.V →+* K := θ.codRestrict K fun v => hK (hθ v)
  let ψ : u.V →+* integralClosure ℤ_[p] K := (β.comp α).codRestrict (integralClosure ℤ_[p] K) fun v =>
    (mem_integralClosure_padicInt_iff K _).mpr ((u.norm_le _).2 ⟨v, rfl⟩)
  let χ : integralClosure ℤ_[p] K →+* K := algebraMap _ _
  have hc : β.comp α = χ.comp ψ := rfl
  have hxG : x ≫ u.G.hom = spMap χ ≫ spMap ψ := by
    obtain ⟨δ, hδ⟩ := Spec.map_surjective (x ≫ u.G.hom)
    have h1 : spMap K.val.toRingHom ≫ spMap δ.hom = spMap (θ.comp α) := by
      rw [← ha, ← hx, Category.assoc, ← hδ]; rfl
    rw [spMap_comp_spMap] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 : δ.hom = χ.comp ψ := RingHom.ext fun v => Subtype.ext (RingHom.congr_fun h2 v)
    rw [spMap_comp_spMap, ← h3, ← hδ]; rfl
  have hp : IsProjOver (pullback.snd u.G.hom (spMap α)) := by
    have : IsIso u.U.gen.inv.left := ((Over.forget _).mapIso u.U.gen).isIso_inv
    refine ProjSpace.isProjOver_of_isIso_comp (Y := pullback u.G.hom (spMap α)) u.U.gen.inv.left ?_
    have := ProjSpace.isProjOver_polAV u.A
    rw [← Over.w u.U.gen.inv] at this
    exact this
  let G' := (Over.pullback (spMap ψ)).obj u.G
  haveI : LocallyOfFiniteType G'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd u.G.hom (spMap ψ)))
  haveI : IsSeparated G'.hom := inferInstanceAs (IsSeparated (pullback.snd u.G.hom (spMap ψ)))
  let a' : Over.mk (spMap χ) ⟶ G' := Over.homMk (pullback.lift x (spMap χ) hxG) (pullback.lift_snd _ _ _)
  obtain ⟨k, hk, g, hg⟩ := GlobalTheory.T.exists_pow_point_integral_padic_groupScheme p K G' (isProjOver_snd_snd u.G.hom α β ψ χ hc hp) a'
  let a₀ : Over.mk (spMap χ ≫ spMap ψ) ⟶ u.G := Over.homMk x hxG
  have e₁ := pow_left_pullback (spMap ψ) u.G (T := Over.mk (spMap χ)) (𝟙 _) (Category.id_comp _) a' a₀
    ((Category.id_comp _).trans (pullback.lift_fst _ _ _).symm) k
  have e₂ := pow_left_pullback (jK u.V) u.G (spMap K.val.toRingHom)
    (show spMap K.val.toRingHom ≫ spMap χ ≫ spMap ψ = spMap θ ≫ spMap α by
      simp only [spMap_comp_spMap]; rfl) a a₀ hx k
  have hgw : g.left ≫ pullback.snd u.G.hom (spMap ψ) = 𝟙 _ := Over.w g
  have hg' : spMap χ ≫ g.left = (a' ^ k).left := by
    rw [← hg]; rfl
  refine ⟨k, hk, spMap (integralClosureToPadicAlgClIntegers K) ≫ g.left ≫ pullback.fst u.G.hom (spMap ψ), ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hgw, spMap_comp_spMap]
    rfl
  · have e₃ : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) = spMap K.val.toRingHom ≫ spMap χ := by
      rw [spMap_comp_spMap, spMap_comp_spMap]; rfl
    rw [reassoc_of% e₃, reassoc_of% hg']
    refine Eq.trans ?_ e₂
    exact congrArg _ (e₁.symm.trans (Category.id_comp _))

end GlobalTheory.ZH
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.BiextTriv

theorem nonempty_biTriv_of_isIntegrallyClosed (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G) (c : CubicalStr G L)
    (i : splitTorus _ X ⟶ G) [IsMonHom i] : Nonempty (BiTriv c i) := by
  have : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  have : IsIntegral (G ⊗ G).left := by
    have : Smooth (fst G G).left := inferInstanceAs (Smooth (pullback.fst G.hom G.hom))
    have : GeometricallyConnected (fst G G).left :=
      inferInstanceAs (GeometricallyConnected (pullback.fst G.hom G.hom))
    exact isIntegral_of_smooth_of_geometricallyConnected (fst G G).left
  have : IsIntegral (splitTorus (Spec (CommRingCat.of A)) X ⊗ G).left := by
    have : Smooth (snd (splitTorus (Spec (CommRingCat.of A)) X) G).left :=
      inferInstanceAs (Smooth (pullback.snd (splitTorus (Spec (CommRingCat.of A)) X).hom G.hom))
    have : GeometricallyIntegral (snd (splitTorus (Spec (CommRingCat.of A)) X) G).left :=
      inferInstanceAs (GeometricallyIntegral (pullback.snd (splitTorus (Spec (CommRingCat.of A)) X).hom G.hom))
    exact isIntegral_of_geometricallyIntegral (snd (splitTorus (Spec (CommRingCat.of A)) X) G).left
  obtain ⟨s, hs, hn⟩ := exists_normalised_gen (φ := lamφ i) (ε := Oε) (fun U hU => by
      have : IsAffine U.1.toScheme := U.2
      have : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
      have h := (HasRingHomProperty.appTop (P := @Smooth) (U.1.ι ≫ G.hom) inferInstance)
      algebraize [(U.1.ι ≫ G.hom).appTop.hom]
      have : IsIntegrallyClosed Γ(Spec (CommRingCat.of A), ⊤) :=
        IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
      exact isIntegrallyClosed_of_smooth Γ(Spec (CommRingCat.of A), ⊤) _) L.isLB fun V _ h => by
    refine (prod_lam i 1 (𝟙 G) V h).trans ?_
    simp [lamForm]
  have R := (rep_val hs).mul (rep_lam i hs (fst (splitTorus _ X) G) 1).inv
  obtain ⟨s', hs', hv⟩ := exists_gen_of_rep L.isLB (lamφ i) Oε R fun V _ h => by simp [lamForm]
  have hv' : ∀ (Z : Over (Spec (CommRingCat.of A))) (t : Z ⟶ splitTorus _ X) (x : Z ⟶ G) z J, Good L.L z J →
      val s' (lift t x).left z J = val s (lift t x).left z J * (val s (lift t (1 : Z ⟶ G)).left z J)⁻¹ :=
    fun Z t x z J hJ => by rw [hv _ _ z J hJ, ← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one]
  refine nonempty_biTriv c i hs' (fun Z y z J hJ => (hv' Z 1 y z J hJ).trans ?_) fun Z t z J hJ => ?_
  · exact mul_inv_eq_one.2 ((hn Z y z J hJ).trans (hn Z 1 z J hJ).symm)
  · rw [hv' Z t 1 z J hJ, mul_inv_cancel]

theorem nonempty_biTriv_normal : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G) (c : CubicalStr G L) (i : splitTorus _ X ⟶ G), IsMonHom i → Nonempty (BiTriv c i) :=
  fun _ _ A _ _ _ _ X _ _ _ G _ _ _ _ L c i _ => nonempty_biTriv_of_isIntegrallyClosed A X G L c i

end GlobalTheory.BiextTriv
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_rigidified_cubical_symmetric_extension_normalBase : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], IsNormalScheme S → ∀ (U : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (a : A.left ⟶ G.left), IsGrpPullback A G j a → ∀ (L : RigLB A) (c : CubicalStr A L) (M : LB G.left), M.IsLB → LBIso (M.pull a) L.L → ∃ (L' : RigLB G) (c' : CubicalStr G L') (m : CubeMap A G), m.F = a ∧ m.e = j ∧ m.IsPullCubical c c' ∧ (L.IsSymmetric → L'.IsSymmetric) := by
  first | exact @GlobalTheory.NormalCubeExt.exists_cubical_extension | exact GlobalTheory.NormalCubeExt.exists_cubical_extension | (intros; apply GlobalTheory.NormalCubeExt.exists_cubical_extension <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundle_spreads_out_from_genericFibre_proper : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → Flat f → IsProper f → ∀ L₀ : LB X₀, L₀.IsLB → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g → ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') := by
  first | exact @GlobalTheory.GenSpread.lineBundle_spreads_out | exact GlobalTheory.GenSpread.lineBundle_spreads_out | (intros; apply GlobalTheory.GenSpread.lineBundle_spreads_out <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_smoothOfRelativeDimension_spread_from_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → IsProper f → SmoothOfRelativeDimension n f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → SmoothOfRelativeDimension n f' := by
  first | exact @GlobalTheory.GenSpread.exists_smoothOfRelativeDimension | exact GlobalTheory.GenSpread.exists_smoothOfRelativeDimension | (intros; apply GlobalTheory.GenSpread.exists_smoothOfRelativeDimension <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pointIndependence_spread_to_geometricFibres : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSeparated G.hom → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (n k : ℕ) (y : Fin n → (baseOver (Sp R) ⟶ G)) (y₀ : Fin n → (baseOver (Sp K) ⟶ A)), (∀ i, (y₀ i).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ c c' : Fin n → Fin k, linComb y₀ (fun i => (c i : ℕ)) = linComb y₀ (fun i => (c' i : ℕ)) → c = c') → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] (π : G'.left ⟶ G.left) (y' : Fin n → (baseOver (Sp R') ⟶ G')), IsGrpPullback G' G (spMap g) π → (∀ i, (y' i).left ≫ π = spMap g ≫ (y i).left) → ∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R') (c c' : Fin n → Fin k), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c' i : ℕ)) → c = c' := by
  first | exact @GlobalTheory.GenSpread.exists_forall_linComb_injective | exact GlobalTheory.GenSpread.exists_forall_linComb_injective | (intros; apply GlobalTheory.GenSpread.exists_forall_linComb_injective <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_rigidification_spread_from_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Rigidified A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Rigidified G' L' := by
  first | exact @GlobalTheory.GenSpread.exists_rigidified | exact GlobalTheory.GenSpread.exists_rigidified | (intros; apply GlobalTheory.GenSpread.exists_rigidified <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

theorem _root_.GlobalTheory.T.polarisation_generating_section_pullback_local_base : Laws → ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (f : R →+* R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (Φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull Φ)), IsGrpPullback P'.A P.A (spMap f) Φ → w.IsGen → ∀ th : H0 P.L 1, (∀ s : H0 P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal P.A.hom r) * th.f j) → ∃ th' : H0 P'.L 1, (∀ s : H0 P'.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal P'.A.hom r) * th'.f j) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι) (J' : (Z ⟶ P'.A.left) → P'.L.ι), Good P.L z J → Good P'.L z J' → sval th (r ≫ Φ) z J = (gw w r z (J (r ≫ Φ)) (J' r)).val * sval th' r z J' := by
  first | exact @GlobalTheory.GeneratorPull.exists_generator_pull | exact GlobalTheory.GeneratorPull.exists_generator_pull | (intros; apply GlobalTheory.GeneratorPull.exists_generator_pull <;> assumption)
end
