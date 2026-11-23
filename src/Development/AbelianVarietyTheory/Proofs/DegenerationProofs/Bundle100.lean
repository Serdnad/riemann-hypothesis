module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.IsTorus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_semiAbelian_model_torusExtension_of_potModel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'), Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧ ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G), IsSemiAbelian G ∧ (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧ Nonempty (TorusExtension (specialFibre V' G)) := by
  intro V _ _ _ _ K _ _ _ _ A _ hP
  obtain ⟨W, L, _, _, _, _, _, _, _, _, e, hfin, -, hW, G, _, hmod, hG⟩ := hP
  have hinj : Function.Injective (algebraMap V W) := by
    have h : Function.Injective ((algebraMap W L).comp (algebraMap V W)) := by
      rw [e]; exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    exact Function.Injective.of_comp (f := algebraMap W L) h
  haveI hKL : FiniteDimensional K L := by
    letI : Algebra V L := ((algebraMap W L).comp (algebraMap V W)).toAlgebra
    haveI : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' e
    haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
    exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)
  obtain ⟨W', _, _, _, hW', _, hfin', hinj', -, hG', hT⟩ := GlobalTheory.T.exists_finite_dvr_torusExtension_specialFibre' W G hG
  obtain ⟨_, hK', e', hmod'⟩ := GlobalTheory.T.groupScheme_model_finite_ring_extension V K A L W e G hmod W' hfin' hinj'
  letI : Algebra V W' := ((algebraMap W W').comp (algebraMap V W)).toAlgebra
  haveI : IsScalarTower V W W' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨FractionRing W', inferInstance, inferInstance, hK', W', inferInstance, inferInstance, inferInstance, hW',
    inferInstance, inferInstance, inferInstance, Module.Finite.trans W W', hinj'.comp hinj, e',
    baseChange W W' G, inferInstance, hG', hmod', hT⟩

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section

namespace GlobalTheory.RosatiDescent

theorem exists_gen_of_rosatiAdj {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    {f g : A ⟶ A} (h : RosatiAdj A L f g) : ∃ t : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), t.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := h (default : PrimeSpectrum k)
  obtain rfl : U = ⊤ := eq_top_iff.2 fun x _ => by
    rwa [Subsingleton.elim (α := PrimeSpectrum k) x default]
  have e : rosatiφ A f g = fun i => (A ⊗ A).left.topIso.inv ≫ ((A ⊗ A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ A f g i :=
    funext fun i => ((A ⊗ A).left.topIso.inv_hom_id_assoc _).symm
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ _ ht _⟩

theorem rosatiAdj_descend {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)} {A : Over (Sp K)}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A₀) {Φ : A.left ⟶ A₀.left}
    (h : IsGrpPullback A A₀ (spMap i) Φ) {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hw : LBIso L (L₀.pull Φ)) {f g : A ⟶ A} {f₀ g₀ : A₀ ⟶ A₀} (hf : f.left ≫ Φ = Φ ≫ f₀.left)
    (hg : g.left ≫ Φ = Φ ≫ g₀.left) (hr : RosatiAdj A L f g) : RosatiAdj A₀ L₀ f₀ g₀ := by
  have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
  let U₂ := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have u₁ : U₂.left ≫ (fst A₀ A₀).left = (fst A A).left ≫ Φ := TripleDescent.lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd A₀ A₀).left = (snd A A).left ≫ Φ := TripleDescent.lift_left_snd _ _
  have P₂ : IsPullback U₂.left (A ⊗ A).hom (A₀ ⊗ A₀).hom (spMap i) :=
    TripleDescent.isPullback_tensor h.1 h.1 _ u₁ u₂
  have v₁ : (fst A A ≫ f).left ≫ Φ = U₂.left ≫ (fst A₀ A₀ ≫ f₀).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, ← u₁, Category.assoc]
  have v₂ : (snd A A ≫ g).left ≫ Φ = U₂.left ≫ (snd A₀ A₀ ≫ g₀).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, ← u₂, Category.assoc]
  have hψ : ∀ k, rosatiφ A f g k ≫ Φ = U₂.left ≫ rosatiφ A₀ f₀ g₀ k := fun k => by
    fin_cases k
    exacts [ArcPull.mul_push h U₂.left v₁ u₂.symm, v₁, u₂.symm, ArcPull.mul_push h U₂.left u₁.symm v₂, u₁.symm, v₂]
  obtain ⟨t, ht⟩ := exists_gen_of_rosatiAdj hr
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hL₀ hL t ht
  obtain ⟨u, hu⟩ := (lb_gen_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom _ _ A₂.smooth A₂.proper A₂.geomConnected P₂).1
    (LB.LinComb L₀ (rosatiφ A₀ f₀ g₀) rosatiε) (DVR.linComb_isLB _ hL₀ _ _)
    (gen_chartPull (chartPullOut L₀ _ _ U₂.left _ hψ) c hc)
  exact fun s => ⟨⊤, trivial, _, DVR.pullGen_isGen _ _ _ _ hu _⟩

end GlobalTheory.RosatiDescent

theorem GlobalTheory.polOAct_descend_of_generators : ∀ (O : Type) [CommRing O] [StarRing O] (J : Type) (gen : J → O), Subring.closure (Set.range gen) = ⊤ → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → LBIso P.L (P₀.L.pull Φ) → ∀ (oa : P.OAct O) (a₀ : J → (P₀.A ⟶ P₀.A)), (∀ j, (oa.act (gen j)).left ≫ Φ = Φ ≫ (a₀ j).left) → ∃ oa₀ : P₀.OAct O, ∀ c, (oa.act c).left ≫ Φ = Φ ≫ (oa₀.act c).left := by
  intro O _ _ J gen hgen K₀ K _ _ i P₀ P Φ h hw oa a₀ ha
  have := P₀.isAb.comm
  have := P.isAb.comm
  obtain ⟨r, -, hr⟩ := oAct_descend_of_generators O J gen K₀ K i P₀.A P.A Φ (ofRingAct oa.toRingAct) a₀ hgen h ha
  exact ⟨⟨r.toRingAct, fun a => RosatiDescent.rosatiAdj_descend i P₀.isAb h P₀.isLB P.isLB hw (hr a) (hr (star a))
    (oa.rosati a)⟩, hr⟩
end
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.IsoFinite

open GlobalTheory.Spread GlobalTheory.HomDescent

variable {k : Type} [CommRing k] {C : Type} [CommRing C] [Algebra k C] {A A' : Over (Sp k)}

theorem comm_bcMap (R : Subalgebra k C)
    (f : (Over.pullback (spMap (algebraMap k C))).obj A ⟶ (Over.pullback (spMap (algebraMap k C))).obj A')
    (g : (Over.pullback (spMap (algebraMap k R))).obj A ⟶ (Over.pullback (spMap (algebraMap k R))).obj A')
    (h : bcMap A.hom R.val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _) :
    f.left ≫ bcMap A'.hom R.val = bcMap A.hom R.val ≫ g.left := by
  have hf : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  have hg : g.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w g
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (f.left ≫ ·) (bcMap_fst A'.hom R.val)).trans
      (h.symm.trans (Category.assoc _ _ _).symm))
  · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    have a₁ := congrArg (f.left ≫ ·) (bcMap_snd A'.hom R.val)
    have a₂ := congrArg (bcMap A.hom R.val ≫ ·) hg
    have a₃ := congrArg (· ≫ spMap R.val.toRingHom) hf
    exact a₁.trans ((Category.assoc _ _ _).symm.trans
      (a₃.trans ((bcMap_snd A.hom R.val).symm.trans a₂.symm)))

variable [GrpObj A] [GrpObj A']

theorem exists_fg_iso [QuasiCompact A.hom] [IsSeparated A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [QuasiCompact A'.hom] [IsSeparated A'.hom] [Flat A'.hom] [LocallyOfFinitePresentation A'.hom]
    (e : (Over.pullback (spMap (algebraMap k C))).obj A ≅ (Over.pullback (spMap (algebraMap k C))).obj A')
    [IsMonHom e.hom] :
    ∃ (R : Subalgebra k C)
      (g : (Over.pullback (spMap (algebraMap k R))).obj A ≅ (Over.pullback (spMap (algebraMap k R))).obj A'),
      R.FG ∧ IsMonHom g.hom := by
  obtain ⟨R₁, f₁, hR₁, _, h₁⟩ := exists_fg_isMonHom e.hom
  obtain ⟨R₂, f₂, hR₂, _, h₂⟩ := exists_fg_isMonHom e.inv
  let R : Subalgebra k C := R₁ ⊔ R₂
  obtain ⟨g₁, m₁, k₁⟩ := exists_specialise f₁ (Subalgebra.inclusion (le_sup_left : R₁ ≤ R))
  obtain ⟨g₂, m₂, k₂⟩ := exists_specialise f₂ (Subalgebra.inclusion (le_sup_right : R₂ ≤ R))
  have c₁ := comm_bcMap R e.hom g₁ ((congrArg (_ ≫ ·) k₁).trans
    ((bcMap_comp_of_eq_assoc A.hom _ _ R₁.val (fun _ => rfl) _).trans h₁))
  have c₂ := comm_bcMap R e.inv g₂ ((congrArg (_ ≫ ·) k₂).trans
    ((bcMap_comp_of_eq_assoc A'.hom _ _ R₂.val (fun _ => rfl) _).trans h₂))
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom R.val.toRingHom)
    Subtype.val_injective
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
    inferInstanceAs (Flat (pullback.snd _ _))
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
    inferInstanceAs (Flat (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsIso g₁ := ExtUnique.isIso_of_isPullback (isGrpPullback_bcMap A R.val).1
    (isGrpPullback_bcMap A' R.val).1 e g₁ g₂ c₁ c₂
  exact ⟨R, asIso g₁, hR₁.sup hR₂, m₁⟩

theorem exists_iso_specialise {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (g : (Over.pullback (spMap (algebraMap k R))).obj A ≅ (Over.pullback (spMap (algebraMap k R))).obj A')
    [IsMonHom g.hom] (ρ : R →ₐ[k] S) :
    ∃ e : (Over.pullback (spMap (algebraMap k S))).obj A ≅ (Over.pullback (spMap (algebraMap k S))).obj A',
      IsMonHom e.hom := by
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_bcMap A ρ) (isGrpPullback_pullback _ _)
  obtain ⟨b, hb, -⟩ := grpPullback_iso (isGrpPullback_pullback _ _) (isGrpPullback_bcMap A' ρ)
  exact ⟨a ≪≫ (Over.pullback (spMap ρ.toRingHom)).mapIso g ≪≫ b,
    inferInstanceAs (IsMonHom (a.hom ≫ (Over.pullback (spMap ρ.toRingHom)).map g.hom ≫ b.hom))⟩

theorem exists_finite_iso : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (T T' : Over (Spec (CommRingCat.of k))) [GrpObj T] [GrpObj T'], IsAffineHom T.hom → IsAffineHom T'.hom → LocallyOfFiniteType T.hom → LocallyOfFiniteType T'.hom → (∃ e : fieldBaseChange k Ω T ≅ fieldBaseChange k Ω T', IsMonHom e.hom) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k') (e : fieldBaseChange k k' T ≅ fieldBaseChange k k' T'), IsMonHom e.hom := by
  intro k Ω _ _ _ T T' _ _ _ _ _ _ ⟨e, he⟩
  have : LocallyOfFinitePresentation T.hom := inferInstance
  have : LocallyOfFinitePresentation T'.hom := inferInstance
  obtain ⟨R, g, hR, hg⟩ := exists_fg_iso (k := k) (C := Ω) (A := T) (A' := T') e
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (R ⧸ m) := .of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  obtain ⟨e', he'⟩ := exists_iso_specialise g (Ideal.Quotient.mkₐ k m)
  exact ⟨R ⧸ m, inferInstance, inferInstance, this, e', he'⟩

end GlobalTheory.IsoFinite
end
end
