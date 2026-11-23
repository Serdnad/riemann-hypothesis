module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SqHorizontal

theorem exists_of_atPrime {C S : Type} [CommRing C] [CommRing S] [Algebra C S] (p : Ideal C) [p.IsPrime]
    [IsLocalization.AtPrime S p] (H : C) (T W : S) (hW : IsUnit W) (e : T ^ 2 = W * algebraMap C S H) :
    ∃ a b c : C, b ∉ p ∧ c ∉ p ∧ b * H = c * a ^ 2 := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj p.primeCompl T
  obtain ⟨⟨d, t⟩, hd⟩ := IsLocalization.surj p.primeCompl W
  dsimp only at ha hd
  have hdu : d ∈ p.primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_to_map_iff S p, ← hd]
    exact hW.mul (IsLocalization.map_units S t)
  have key : algebraMap C S (d * (s : C) ^ 2 * H) = algebraMap C S ((t : C) * a ^ 2) := by
    simp only [map_mul, map_pow]
    rw [← ha, ← hd, mul_pow, e]
    ring
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).1 key
  refine ⟨a, u * (d * (s : C) ^ 2), u * t, ?_, ?_, ?_⟩
  · exact p.primeCompl.mul_mem u.2 (p.primeCompl.mul_mem hdu (p.primeCompl.pow_mem s.2 2))
  · exact p.primeCompl.mul_mem u.2 t.2
  · linear_combination hu

theorem isIso_stalkMap {X Y : Scheme.{0}} (φ : X ⟶ Y) [Flat φ] [SurjectiveOnStalks φ] (x : X) :
    IsIso (φ.stalkMap x) := by
  have h1 := Flat.stalkMap φ x
  have h2 := φ.stalkMap_surjective x
  algebraize [(φ.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (φ x))
    (B := X.presheaf.stalk x)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x), h2⟩

theorem exists_of_stalk {X Y : Scheme.{0}} (f : Y ⟶ X) (x : X) (q : Spec (X.presheaf.stalk x)) (y : Y)
    [IsIso (f.stalkMap y)] (hy : X.fromSpecStalk x q = f y) (U : X.Opens) (hx : x ∈ U) (hyU : f y ∈ U)
    (h : Γ(X, U)) (T W : Y.presheaf.stalk y) (hW : IsUnit W)
    (e : T ^ 2 = W * (Y.presheaf.germ (f ⁻¹ᵁ U) y hyU).hom ((f.app U).hom h)) :
    ∃ a b c : X.presheaf.stalk x, b ∉ q.asIdeal ∧ c ∉ q.asIdeal ∧
      b * (X.presheaf.germ U x hx).hom h = c * a ^ 2 := by
  let ψ : Y.presheaf.stalk y ⟶ (Spec (X.presheaf.stalk x)).presheaf.stalk q :=
    inv (f.stalkMap y) ≫ X.presheaf.stalkSpecializes (specializes_of_eq hy) ≫ (X.fromSpecStalk x).stalkMap q
  have hψ : f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) y hyU ≫ ψ =
      X.presheaf.germ U x hx ≫ StructureSheaf.toStalk (X.presheaf.stalk x) q := by
    rw [← Category.assoc, ← Scheme.Hom.germ_stalkMap f U y hyU]
    simp only [ψ, Category.assoc, IsIso.hom_inv_id_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
    rw [Scheme.Hom.germ_stalkMap, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  letI : Algebra (X.presheaf.stalk x) ((Spec (X.presheaf.stalk x)).presheaf.stalk q) :=
    (StructureSheaf.toStalk (X.presheaf.stalk x) q).hom.toAlgebra
  have hl : IsLocalization.AtPrime ((Spec (X.presheaf.stalk x)).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (X.presheaf.stalk x) q
  refine exists_of_atPrime (S := (Spec (X.presheaf.stalk x)).presheaf.stalk q) q.asIdeal _
    (ψ.hom T) (ψ.hom W) (hW.map ψ.hom) ?_
  rw [← map_pow, e, map_mul]
  congr 1
  exact congrArg (fun k => k.hom h) hψ

theorem horizontal : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (L2 : LB G₁.left) (h : L2.Sec) (Lθ : LB (pullback G₁.hom (jK R'))), Lθ.IsLB → ∀ θ : Lθ.Sec, (∀ j i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (L2.U j)).hom (h.f j))) → ∀ x : G₁.left, ∀ j (hx : x ∈ L2.U j), ∀ p : Ideal (G₁.left.presheaf.stalk x), p.IsPrime → Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p = ⊥ → ∃ a b c : G₁.left.presheaf.stalk x, b ∉ p ∧ c ∉ p ∧ b * (G₁.left.presheaf.germ (L2.U j) x hx).hom (h.f j) = c * a ^ 2 := by
  intro R' _ _ _ _ G₁ _ _ _ L2 h Lθ hL θ hθ x j hx p hp hc
  have : IsPreimmersion (jK R') := IsPreimmersion.of_isLocalization (nonZeroDivisors R') (S := FractionRing R')
  have : Flat (jK R') := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (FractionRing R') (nonZeroDivisors R'))
  let q : Spec (G₁.left.presheaf.stalk x) := ⟨p, hp⟩
  have e₁ : G₁.left.fromSpecStalk x ≫ G₁.hom = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
      G₁.hom.appTop ≫ G₁.left.presheaf.germ ⊤ x trivial) := by
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
      ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R')).inv, ← Scheme.ΓSpecIso_inv_naturality]
    simp
  have e₂ : G₁.hom (G₁.left.fromSpecStalk x q) = jK R' (⊥ : PrimeSpectrum (FractionRing R')) := by
    rw [← Scheme.Hom.comp_apply, e₁]
    apply PrimeSpectrum.ext
    refine hc.trans ?_
    exact (Ideal.comap_bot_of_injective (algebraMap R' (FractionRing R'))
      (IsFractionRing.injective R' (FractionRing R'))).symm
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e₂
  have hs : SurjectiveOnStalks (pullback.fst G₁.hom (jK R')) :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback _ _).flip inferInstance
  have := isIso_stalkMap (pullback.fst G₁.hom (jK R')) y
  have hyU : pullback.fst G₁.hom (jK R') y ∈ L2.U j := by
    rw [hy]
    have : G₁.left.fromSpecStalk x q ∈ Set.range (G₁.left.fromSpecStalk x) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open this (L2.U j).isOpen hx
  obtain ⟨i, hi⟩ : ∃ i, y ∈ Lθ.U i := by
    have : y ∈ ⨆ i, Lθ.U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨w, hw⟩ := hθ j i
  have hm : y ∈ pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i := ⟨hyU, hi⟩
  have hw' := congrArg ((pullback G₁.hom (jK R')).presheaf.germ _ y hm).hom hw
  rw [map_pow, map_mul] at hw'
  refine exists_of_stalk (pullback.fst G₁.hom (jK R')) x q y hy.symm (L2.U j) hx hyU (h.f j) _ _
    (w.isUnit.map ((pullback G₁.hom (jK R')).presheaf.germ _ y hm).hom) (hw'.trans ?_)
  congr 1
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

end GlobalTheory.SqHorizontal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorDown

theorem ext_of_fraction_meet : ∀ (Z : Scheme.{0}) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (gam : FractionRing R →+* FractionRing R'), (∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x) → ∀ (x : Sp (FractionRing R) ⟶ Z) (a' : Sp R' ⟶ Z), jK R' ≫ a' = spMap gam ≫ x → ∃ a : Sp R ⟶ Z, jK R ≫ a = x := by
  intro Z R R' _ _ _ _ _ gam hgam x a' hx
  obtain ⟨U, hU, hz, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens)
    (show a' (IsLocalRing.closedPoint R') ∈ (⊤ : Z.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hra : Set.range a' ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map a'.continuous).mem_open U.isOpen hz
  have hrx : Set.range x ⊆ Set.range hU'.fromSpec := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t'⟩ : Nonempty (Sp (FractionRing R')) := inferInstance
    have e1 : (spMap gam) t' = t := Subsingleton.elim _ _
    have e2 := congrArg (fun h : Sp (FractionRing R') ⟶ Z => h t') hx
    simp only [Scheme.Hom.comp_apply] at e2
    rw [← e1, ← e2]
    exact hra ⟨_, rfl⟩
  have ha₁ := IsOpenImmersion.lift_fac hU'.fromSpec a' hra
  have hx₁ := IsOpenImmersion.lift_fac hU'.fromSpec x hrx
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec a' hra)] at ha₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)] at hx₁
  set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec a' hra) with hψ
  set χ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hχ
  have key : ψ ≫ CommRingCat.ofHom (algebraMap R' (FractionRing R')) = χ ≫ CommRingCat.ofHom gam := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ha₁, hx₁]
    exact hx
  have hmem : ∀ b : Γ(Z, U), χ.hom b ∈ (algebraMap R (FractionRing R)).range := by
    intro b
    have e := congrArg (fun h => h.hom b) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    obtain ⟨r, hr⟩ := hgam (χ.hom b) (ψ.hom b) e
    exact ⟨r, hr⟩
  have hinj : Function.Injective (algebraMap R (FractionRing R)).rangeRestrict := fun a b h =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)
  let eR := RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
    ⟨hinj, RingHom.rangeRestrict_surjective _⟩
  let θ : Γ(Z, U) →+* R := eR.symm.toRingHom.comp (χ.hom.codRestrict _ hmem)
  have hθ : ∀ b, algebraMap R (FractionRing R) (θ b) = χ.hom b := by
    intro b
    have := eR.apply_symm_apply (χ.hom.codRestrict _ hmem b)
    exact congrArg Subtype.val this
  refine ⟨Spec.map (CommRingCat.ofHom θ : Γ(Z, U) ⟶ CommRingCat.of R) ≫ hU'.fromSpec, ?_⟩
  rw [← hx₁, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext b
  exact hθ b

end GlobalTheory.TorDown
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mum.ThickChart

theorem isPushout_quotMap (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (K : Ideal R) :
    IsPushout (CommRingCat.ofHom (algebraMap R C)) (CommRingCat.ofHom (Ideal.Quotient.mk K))
      (CommRingCat.ofHom (Ideal.Quotient.mk (K.map (algebraMap R C))))
      (CommRingCat.ofHom (Ideal.quotientMap (K.map (algebraMap R C)) (algebraMap R C) Ideal.le_comap_map)) := by
  refine ⟨⟨by ext x; rfl⟩, ⟨PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom
    (Ideal.Quotient.lift (K.map (algebraMap R C)) s.inl.hom ?_)) ?_ ?_ ?_⟩⟩
  · intro a ha
    have : K.map (algebraMap R C) ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h := congrArg (fun f => f.hom x) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h
      rw [Ideal.mem_comap, RingHom.mem_ker, h, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    exact this ha
  · intro s
    ext x
    rfl
  · intro s
    ext x
    exact congrArg (fun f => f.hom x) s.condition
  · intro s m h1 _
    ext x
    exact congrArg (fun f => f.hom x) h1

theorem isPullback_quotMap (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (K : Ideal R) :
    IsPullback (spMap (Ideal.Quotient.mk (K.map (algebraMap R C))))
      (spMap (Ideal.quotientMap (K.map (algebraMap R C)) (algebraMap R C) Ideal.le_comap_map))
      (spMap (algebraMap R C)) (spMap (Ideal.Quotient.mk K)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotMap R C K)

theorem thick_chart : ∀ (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (C' : Type) [CommRing C'] [Algebra R' C'] (j : Sp C' ⟶ G'.left) [IsOpenImmersion j], j ≫ G'.hom = spMap (algebraMap R' C') → ∀ (e : ℕ), ∃ (je : Sp (C' ⧸ (I ^ (e + 1)).map (algebraMap R' C')) ⟶ (thickObj R' I e G').left) (_ : IsOpenImmersion je), je.opensRange = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ j.opensRange ∧ IsPullback je (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C')))) (pullback.fst G'.hom (thick R' I e)) j ∧ je ≫ (thickObj R' I e G').hom = spMap (Ideal.quotientMap ((I ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C') Ideal.le_comap_map) := by
  intro R' _ I G' C' _ _ j _ hj e
  have outer := isPullback_quotMap R' C' (I ^ (e + 1))
  have right : IsPullback (pullback.snd G'.hom (thick R' I e)) (pullback.fst G'.hom (thick R' I e))
      (thick R' I e) G'.hom := (IsPullback.of_hasPullback G'.hom (thick R' I e)).flip
  have hw : (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C'))) ≫ j) ≫ G'.hom =
      spMap (Ideal.quotientMap ((I ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C') Ideal.le_comap_map) ≫
        thick R' I e := by
    rw [Category.assoc, hj]
    exact outer.w
  let je := pullback.lift _ _ hw
  have hje1 : je ≫ pullback.fst G'.hom (thick R' I e) = spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C'))) ≫ j :=
    pullback.lift_fst _ _ _
  have hje2 : je ≫ pullback.snd G'.hom (thick R' I e) =
      spMap (Ideal.quotientMap ((I ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C') Ideal.le_comap_map) :=
    pullback.lift_snd _ _ _
  have big : IsPullback (je ≫ pullback.snd G'.hom (thick R' I e))
      (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C')))) (thick R' I e) (j ≫ G'.hom) := by
    rw [hje2, hj]
    exact outer.flip
  have sq : IsPullback je (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C'))))
      (pullback.fst G'.hom (thick R' I e)) j := IsPullback.of_right big hje1 right
  haveI hoi : IsOpenImmersion je := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  refine ⟨je, hoi, ?_, sq, hje2⟩
  have h1 : sq.isoPullback.hom ≫ pullback.fst (pullback.fst G'.hom (thick R' I e)) j = je := sq.isoPullback_hom_fst
  have h2 : Set.range je = Set.range (pullback.fst (pullback.fst G'.hom (thick R' I e)) j) := by
    rw [← h1, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr sq.isoPullback.hom.surjective, Set.image_univ]
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, h2, IsOpenImmersion.range_pullbackFst]

end GlobalTheory.Mum.ThickChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteLift

theorem exists_retraction {V B : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [CommRing B]
    (φ : V →+* B) (hφ : φ.IsIntegral) (ψ : B →+* FractionRing V)
    (h : ψ.comp φ = algebraMap V (FractionRing V)) :
    ∃ s : B →+* V, s.comp φ = RingHom.id V ∧ (algebraMap V (FractionRing V)).comp s = ψ := by
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
  have hmem : ∀ b, ψ b ∈ (algebraMap V (FractionRing V)).range := by
    intro b
    obtain ⟨p, hp, hpb⟩ := hφ b
    have : IsIntegral V (ψ b) := ⟨p, hp, by rw [← h, ← Polynomial.hom_eval₂, hpb, map_zero]⟩
    exact IsIntegrallyClosed.algebraMap_eq_of_integral this
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  have key : ∀ b, algebraMap V (FractionRing V) (e.symm (ψ.codRestrict _ hmem b)) = ψ b := fun b =>
    congrArg Subtype.val (e.apply_symm_apply (ψ.codRestrict _ hmem b))
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), ?_, ?_⟩
  · ext v
    apply hinj
    exact (key (φ v)).trans (DFunLike.congr_fun h v)
  · ext b
    exact key b

theorem exists_lift {V : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    {X Z : Scheme.{0}} (π : X ⟶ Z) [IsFinite π] (f : Sp V ⟶ Z) (y : Sp (FractionRing V) ⟶ X)
    (h : y ≫ π = jK V ≫ f) : ∃ l : Sp V ⟶ X, l ≫ π = f ∧ jK V ≫ l = y := by
  have : IsAffine (pullback π f) := isAffine_of_isAffineHom (pullback.snd π f)
  let P := pullback π f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (P.isoSpec.inv ≫ pullback.snd π f)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (pullback.lift y (jK V) h ≫ P.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hfin
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _
  obtain ⟨s, hs1, hs2⟩ := exists_retraction φ.hom hfin.to_isIntegral ψ.hom
    (congrArg CommRingCat.Hom.hom hc)
  have h1 : Spec.map (CommRingCat.ofHom s) ≫ P.isoSpec.inv ≫ pullback.snd π f = 𝟙 _ := by
    rw [← hφ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext hs1
  have h2 : jK V ≫ Spec.map (CommRingCat.ofHom s) =
      pullback.lift y (jK V) h ≫ P.isoSpec.hom := by
    rw [← hψ, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hs2
  refine ⟨Spec.map (CommRingCat.ofHom s) ≫ P.isoSpec.inv ≫ pullback.fst π f, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h1]
  · rw [reassoc_of% h2, Iso.hom_inv_id_assoc]
    exact pullback.lift_fst _ _ _

theorem exists_stalk_lift : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsIntegrallyClosed V₁ → ∀ (X Z : Scheme.{0}) (π : X ⟶ Z), IsFinite π → ∀ (f : Sp V₁ ⟶ Z) (yM : Sp (FractionRing V₁) ⟶ X), yM ≫ π = jK V₁ ≫ f → ∃ (z₁ : X) (ev : X.presheaf.stalk z₁ →+* V₁), IsLocalHom ev ∧ spMap ev ≫ X.fromSpecStalk z₁ ≫ π = f ∧ jK V₁ ≫ spMap ev ≫ X.fromSpecStalk z₁ = yM := by
  intro V _ _ _ hV X Z π hπ f y h
  obtain ⟨l, h1, h2⟩ := exists_lift π f y h
  have e : spMap (Scheme.stalkClosedPointTo (R := .of V) l).hom ≫ X.fromSpecStalk _ = l :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of V) l
  refine ⟨_, (Scheme.stalkClosedPointTo (R := .of V) l).hom, inferInstance, ?_, ?_⟩
  · rw [reassoc_of% e, h1]
  · rw [e, h2]

end GlobalTheory.FiniteLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RetractGeneric

theorem isProper_of_retract {S : Scheme.{0}} {X Y : Over S} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) (hY : IsProper Y.hom) : IsProper X.hom := by
  have hl : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, h, Over.id_left]
  have h1 : IsSeparated (r.left ≫ X.hom) := by rw [Over.w r]; infer_instance
  have h2 : IsSeparated r.left := IsSeparated.of_comp r.left X.hom
  have h3 : IsClosedImmersion (i.left ≫ r.left) := by rw [hl]; infer_instance
  have h4 : IsClosedImmersion i.left := IsClosedImmersion.of_comp i.left r.left
  rw [← Over.w i]
  infer_instance

theorem isAbelianScheme_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ((Over.pullback (jK R)).obj G' ≅ A'.A) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme ((Over.pullback (jK R)).obj G) := by
  intro R _ _ A' G' _ _ _ e G _ _ hG inc pr _ _ h
  have hK := IsSemiAbelian.pullback (jK R) G hG
  have hp : IsProper ((Over.pullback (jK R)).obj G).hom :=
    isProper_of_retract ((Over.pullback (jK R)).map inc ≫ e.hom)
      (e.inv ≫ (Over.pullback (jK R)).map pr)
      (by rw [Category.assoc, e.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp, h,
        CategoryTheory.Functor.map_id]) A'.isAb.proper
  exact ⟨hK.comm, hK.smooth, hp, hK.geomConnected⟩

end GlobalTheory.Mum.RetractGeneric
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.semiAbelian_end_generic_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = φ := by
  intro R _ _ _ _ G _ hG φ hφ
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.of_isGenericPointHom
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R)
    (GlobalTheory.IsGenericPointHom.fractionField R (FractionRing R)) hG hG φ
  exact ⟨F, hF, hF'⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.isAbelianScheme_genericFibre_injective_domain_map : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (G : Over (Sp R)) [GrpObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → IsAbelianScheme ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) := by
  first | exact @GlobalTheory.Desc.isAbelianScheme_generic_of_injective | exact GlobalTheory.Desc.isAbelianScheme_generic_of_injective | (intros; apply GlobalTheory.Desc.isAbelianScheme_generic_of_injective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.semiAbelian_hom_extends_from_generic_fibre : ∀ (E : Type) [CommRing E] [IsDomain E] [IsNoetherianRing E] [IsIntegrallyClosed E] (G H : Over (Sp E)) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback (jK E)).obj G ⟶ (Over.pullback (jK E)).obj H, IsMonHom f → ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (jK E)).map F = f := by
  first | exact @GlobalTheory.Desc.semiAbelian_hom_extend_generic | exact GlobalTheory.Desc.semiAbelian_hom_extend_generic | (intros; apply GlobalTheory.Desc.semiAbelian_hom_extend_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_point_translates_in_open_semiAbelian_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ V : G.left.Opens, (∃ y₀ ∈ V, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ z : (G ⊗ G).left, (fst G G).left z = y ∧ (fst G G * snd G G).left z ∈ V ∧ (fst G G * (snd G G)⁻¹).left z ∈ V := by
  first | exact @GlobalTheory.ShearMeet.exists_fst_mul_mem | exact GlobalTheory.ShearMeet.exists_fst_mul_mem | (intros; apply GlobalTheory.ShearMeet.exists_fst_mul_mem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_generator_mumfordBundle_inv_pullback_primitive : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (_ : CubicalStr B M), IsAbelianScheme B → ∃ u : LB.Gen (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])), u.IsGen := by
  first | exact @GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial | exact GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial | (intros; apply GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial <;> assumption)
end
