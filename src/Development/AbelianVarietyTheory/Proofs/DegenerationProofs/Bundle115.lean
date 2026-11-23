module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle109
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle091
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle110
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosureLifting

theorem exists_lift {Z Y : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (j : Y ⟶ Z) [IsOpenImmersion j] [Nonempty Y] :
    ∃ x : Sp K ⟶ Y, x ≫ j = gp := by
  have hr : Set.range gp ⊆ Set.range j := by
    rw [hgp, Set.singleton_subset_iff]
    exact (genericPoint_specializes (j (Classical.arbitrary Y))).mem_open
      j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  exact ⟨_, IsOpenImmersion.lift_fac j gp hr⟩

theorem flat_of_charZero {Z : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] [CharZero K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (π : Z ⟶ Sp ℤ) : Flat π := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) Z.affineOpenCover.openCover fun i => ?_
  let R := Z.affineOpenCover.X i
  let j : Spec R ⟶ Z := Z.affineOpenCover.f i
  have : IsOpenImmersion j := Z.affineOpenCover.map_prop i
  change Flat (j ≫ π)
  rcases isEmpty_or_nonempty (Spec R) with h | h
  · infer_instance
  obtain ⟨x, -⟩ := exists_lift gp hgp j
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 this
  have : CharZero R := (Spec.preimage x).hom.charZero
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Flat)]
  have e : φ.hom = algebraMap ℤ R := RingHom.ext_int _ _
  rw [e, RingHom.flat_algebraMap_iff]
  infer_instance

theorem exists_section_of_local {Z G : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (q : G ⟶ Z) [IsSeparated q] (ξ : Sp K ⟶ G)
    (H : ∀ z : Z, ∃ (W : Z.Opens) (h : W.toScheme ⟶ G), z ∈ W ∧ h ≫ q = W.ι ∧
      ∀ x : Sp K ⟶ W.toScheme, x ≫ W.ι = gp → x ≫ h = ξ) :
    ∃ e : Z ⟶ G, e ≫ q = 𝟙 Z ∧ gp ≫ e = ξ := by
  choose W h hz hq hξ using H
  have hd : IsDominant gp := ⟨by
    rw [DenseRange, hgp, dense_iff_closure_eq]
    exact genericPoint_spec Z⟩
  have hx : ∀ z, ∃ x : Sp K ⟶ (W z).toScheme, x ≫ (W z).ι = gp := fun z =>
    have : Nonempty (W z).toScheme := ⟨⟨z, hz z⟩⟩
    exists_lift gp hgp _
  choose x hx using hx
  have hW : TopologicalSpace.IsOpenCover W :=
    top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hz z⟩
  let 𝒰 := Z.openCoverOfIsOpenCover W hW
  have hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ h a = pullback.snd (W a).ι (W b).ι ≫ h b := by
    intro a b
    let m : Sp K ⟶ pullback (W a).ι (W b).ι := pullback.lift (x a) (x b) ((hx a).trans (hx b).symm)
    have e : m ≫ pullback.fst _ _ ≫ (W a).ι = gp := by rw [pullback.lift_fst_assoc, hx]
    have : IsDominant (m ≫ pullback.fst _ _ ≫ (W a).ι) := e ▸ hd
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ (W a).ι)
    have : IsReduced (pullback (W a).ι (W b).ι) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)
    refine ext_of_isDominant_of_isSeparated q ?_ m ?_
    · rw [Category.assoc, Category.assoc, hq, hq, pullback.condition]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hξ _ _ (hx a), hξ _ _ (hx b)]
  have he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms h hc = h a := fun a => 𝒰.ι_glueMorphisms h hc a
  refine ⟨𝒰.glueMorphisms h hc, 𝒰.hom_ext _ _ fun (a : Z) => ?_, ?_⟩
  · change (W a).ι ≫ _ = (W a).ι ≫ _
    rw [← Category.assoc, he, hq, Category.comp_id]
  · rw [← hx (genericPoint Z), Category.assoc, he, hξ _ _ (hx _)]

theorem eSec_fst {B B' : Scheme.{0}} (u : B' ⟶ B) (A : Over B) [GrpObj A] :
    eSec ((Over.pullback u).obj A) ≫ pullback.fst A.hom u = u ≫ eSec A := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem proj_zero_of_eq_bot {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

theorem exists_crd_ne_zero [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (ρ : S.Real) {K : Type} [Field K]
    (y : Sp K ⟶ ρ.P.A.left) : ∃ v i, ρ.Crd y v ∧ v i ≠ 0 := by
  let y' : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left :=
    pullback.lift (f := (baseOver (Sp S.R)).hom) (g := ρ.P.A.hom) (y ≫ ρ.P.A.hom) y (Category.comp_id _)
  have hM : (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).IsLB := LB.isLB_linComb ρ.P.isLB _ _
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists hM ρ.s y'
  have hm : y' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (ρ.s i) := by
    rw [(ThetaSys.Real.immBy_basis hL o Ω S ρ).1]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  exact ⟨v, i, ⟨y', pullback.lift_snd _ _ _, hv⟩,
    ((CrdCalc.crd_isUnit_iff i hv).2 ((CrdCalc.top_le_iff y' _).2 hi)).ne_zero⟩

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem range_subset [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) :
    Set.range Q.a₀ ⊆ Set.range Q.G.ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨K, _, x, rfl⟩ : ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ pullback ρ.P.A.hom Q.u₀),
      x (IsLocalRing.closedPoint K) = w :=
    ⟨_, inferInstance, Scheme.fromSpecResidueField _ w, Scheme.fromSpecResidueField_apply w _⟩
  obtain ⟨v, i, hv, hi⟩ := exists_crd_ne_zero hL ρ (x ≫ pullback.fst _ _)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((x ≫ Q.a₀) ≫ Q.P.hom ≫ M.s)
  have hz : ∀ s, ((x ≫ Q.a₀) ≫ Q.P.hom) s ∈ U₀ := fun s => by
    rw [Category.assoc, Q.cart.w, ← Category.assoc]
    exact ((x ≫ pullback.snd _ _) s).2
  have key := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q K (x ≫ Q.a₀) _ ψ.hom v
    Set.range_unique (Or.inr (hz _)) hψ.symm (Q.crd K x v hv)).2 ⟨i, by
      rw [proj_zero_of_eq_bot (hB.gen _ (hz _)),
        Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne hj, map_zero, zero_mul]) (by simp)]
      simpa using hi⟩
  exact key (Set.mem_univ (IsLocalRing.closedPoint K))

theorem nonempty_ext : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), Nonempty Q.Ext := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q
  have := ArithBase.char (o := o) (Ω := Ω)
  have := M.sep
  have := M.lft
  have := M.qc
  have := Q.proper
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.2 (ArithBase.ft (o := o) (Ω := Ω)))
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h1 : (ρ.pt 0).left = eSec ρ.P.A := by
    have e : toUnit (baseOver (Sp S.R)) = 𝟙 (𝟙_ (Over (Sp S.R))) := toUnit_unique _ _
    rw [h0, Hom.one_def, e]
    exact congrArg CommaMorphism.left (Category.id_comp _)
  let a : pullback ρ.P.A.hom Q.u₀ ⟶ Q.G.toScheme := IsOpenImmersion.lift Q.G.ι Q.a₀ (range_subset hL hB Q)
  have ha : a ≫ Q.G.ι = Q.a₀ := IsOpenImmersion.lift_fac _ _ _
  let ε : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ := eSec ((Over.pullback Q.u₀).obj ρ.P.A)
  have hε₁ : ε ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A := eSec_fst Q.u₀ ρ.P.A
  have hε₂ : ε ≫ pullback.snd _ _ = 𝟙 _ := Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]
  have : Nonempty U₀.toScheme := hB.ov.ne.to_subtype
  obtain ⟨t, ht⟩ := exists_lift M.pt M.gen U₀.ι
  obtain ⟨e, he, he'⟩ := exists_section_of_local M.pt M.gen (Q.G.ι ≫ Q.P.hom) (t ≫ ε ≫ a) fun z => by
    obtain ⟨W, h, hz, hh, H⟩ := GlobalTheory.T.exists_section_extending_torsionPoints_support hL o Ω S ρ M U₀ EE hB Q z 0 (zero_mem _)
    refine ⟨W, h, hz, hh, fun x hx => ?_⟩
    rw [← cancel_mono Q.G.ι, Category.assoc, H Ω x (t ≫ ε) ?_ ?_]
    · simp only [Category.assoc, ha]
    · rw [Category.assoc, reassoc_of% hε₂, hx, ht]
    · rw [Category.assoc, Category.assoc, reassoc_of% hε₂, hε₁, h1]
  have : IsDominant (t ≫ U₀.ι) := ht ▸ M.isDominant_pt
  have : IsDominant t := .of_comp_of_isOpenImmersion t U₀.ι
  refine ⟨{
    π := M.s ≫ spMap (algebraMap ℤ o)
    flat := flat_of_charZero M.pt M.gen _
    lft := inferInstance
    qc := inferInstance
    sep := inferInstance
    normal := hB.ov.normal
    ne := hB.ov.ne
    ab := TLinPf.isAb_pullback _ _ ρ.P.isAb
    dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      (ρ.g_eq ▸ ρ.P.smoothDim)
    a := a
    a_eq := ha
    e := e
    e_sec := he
    e_zero := ?_ }⟩
  change U₀.ι ≫ e = ε ≫ a
  refine ext_of_isDominant_of_isSeparated (Q.G.ι ≫ Q.P.hom) ?_ t ?_
  · rw [Category.assoc, he, Category.assoc, reassoc_of% ha, Q.cart.w, reassoc_of% hε₂, Category.comp_id]
  · rw [← Category.assoc, ht, he']

end GlobalTheory.ZH.ClosureLifting
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem geometricallyConnected_of_generic_of_special (W L : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] {X : Scheme.{0}} (f : X ⟶ Sp W)
    (h₁ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W L))))
    (h₂ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W (IsLocalRing.ResidueField W))))) :
    GeometricallyConnected f := by
  have key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω),
      GeometricallyConnected (pullback.snd f (spMap a)) →
      ∀ (Z : Scheme.{0}) (fst : Z ⟶ X) (snd : Z ⟶ Sp Ω), IsPullback fst snd f (spMap (ψ.comp a)) →
      ConnectedSpace Z := by
    intro Ω F _ _ a ψ h Z fst snd hZ
    have e : spMap (ψ.comp a) = spMap ψ ≫ spMap a := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e] at hZ
    have sq : IsPullback (pullback.lift fst (snd ≫ spMap ψ) (hZ.w.trans (Category.assoc _ _ _).symm)) snd
        (pullback.snd f (spMap a)) (spMap ψ) :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact hZ) (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback f (spMap a))
    exact GeometricallyConnected.geometrically_connectedSpace (f := pullback.snd f (spMap a)) _ _ _ sq
  refine ⟨fun Ω _ q Z fst snd hZ => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  change IsPullback fst snd f (spMap φ.hom) at hZ
  by_cases h : RingHom.ker φ.hom = ⊥
  · have hinj := (RingHom.injective_iff_ker_eq_bot _).2 h
    have e : (IsFractionRing.lift (K := L) hinj).comp (algebraMap W L) = φ.hom :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    rw [← e] at hZ
    exact key Ω L _ _ h₁ Z fst snd hZ
  · have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)
    let ψ : IsLocalRing.ResidueField W →+* Ω :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ.hom fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)
    have e : ψ.comp (algebraMap W (IsLocalRing.ResidueField W)) = φ.hom := RingHom.ext fun x => rfl
    rw [← e] at hZ
    exact key Ω _ _ _ h₂ Z fst snd hZ

theorem isSemiAbelian_of_abelian_generic_of_torusExt : NfSt := by
  intro W _ _ _ L _ _ _ A _ hA G _ hc hs hsep hqc ⟨e, _⟩ hT
  obtain ⟨k, _, _, _, ⟨E⟩⟩ := GlobalTheory.T.exists_finite_splitTorusExtension_of_torusExtension _ _ hT
  have hw : (baseChange W L G).hom = e.hom.left ≫ A.hom := (Over.w e.hom).symm
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have := hA.proper
  have := hA.geomConnected
  have hp : IsProper (baseChange W L G).hom := by rw [hw]; infer_instance
  have hg : GeometricallyConnected (baseChange W L G).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨by rw [hw, Category.comp_id]⟩) hA.geomConnected
  have hk := (GlobalTheory.torusExtension_smooth_geometricallyConnected _ E).2.2.2.1
  have hsurj : Surjective (spMap (algebraMap (IsLocalRing.ResidueField W) k)) :=
    ⟨fun z => ⟨_, Subsingleton.elim (spMap (algebraMap (IsLocalRing.ResidueField W) k)
      (default : PrimeSpectrum _)) z⟩⟩
  have hsp : GeometricallyConnected (specialFibre W G).hom :=
    @GlobalTheory.geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _
      (IsPullback.of_hasPullback (specialFibre W G).hom (spMap (algebraMap (IsLocalRing.ResidueField W) k)))
      hsurj hk
  have hgc : GeometricallyConnected G.hom := geometricallyConnected_of_generic_of_special W L G.hom hg hsp
  refine isSemiAbelian_of_proper_generic_of_torusExtension W L G ⟨hc, hs, hsep, hqc, hgc⟩ hp k
    ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) ?_ ?_ ?_
  · rw [RingHom.ker_comp_of_injective _ (algebraMap (IsLocalRing.ResidueField W) k).injective]
    exact IsLocalRing.ker_residue
  · refine RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective) ?_
    exact Algebra.IsIntegral.isIntegral
  · have e' : spMap ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) =
        spMap (algebraMap (IsLocalRing.ResidueField W) k) ≫ spMap (algebraMap W (IsLocalRing.ResidueField W)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e']
    have : IsMonHom (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso _ _ G).inv)
    exact ⟨torusExtOfIso (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm E⟩

end GlobalTheory.SS
end
