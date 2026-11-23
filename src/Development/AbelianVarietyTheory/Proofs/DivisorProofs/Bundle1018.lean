module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.Bundle002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open Module

namespace GlobalTheory.PolExistsRing

theorem mem_of_annihilates {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (ψ : LinearMap.BilinForm R V) [hψ : ψ.IsPerfPair] (W W' : Submodule R V) (hc : IsCompl W W')
    [Module.Finite R W'] [Module.Projective R W'] [Module.Finite R (Dual R W)]
    [Module.Projective R (Dual R W)]
    (hrk : ∀ p : PrimeSpectrum R, rankAtStalk W' p = rankAtStalk (Dual R W) p)
    (hiso : ∀ f ∈ W, ∀ g ∈ W, ψ f g = 0) (f : V) (hf : ∀ g ∈ W, ψ f g = 0) : f ∈ W := by
  let Φ : W' →ₗ[R] Dual R W := W.subtype.dualMap ∘ₗ ψ ∘ₗ W'.subtype
  let e := Submodule.prodEquivOfIsCompl W W' hc
  have hdec : ∀ v : V, (((e.symm v).1 : W) : V) + ((e.symm v).2 : V) = v := fun v ↦ by
    rw [← Submodule.coe_prodEquivOfIsCompl' W W' hc, LinearEquiv.apply_symm_apply]
  have hΦ' : ∀ v : V, ∀ g : W, Φ (e.symm v).2 g = ψ v g := by
    intro v g
    have h := congrArg (fun u ↦ ψ u g) (hdec v)
    simp only [map_add (f := _), LinearMap.add_apply] at h
    rw [hiso _ (Submodule.coe_mem _) g g.2, zero_add] at h
    simpa [Φ] using h
  have hΦ : Function.Surjective Φ := by
    intro l
    obtain ⟨v, hv⟩ := hψ.bijective_left.2 (l ∘ₗ W.projectionOnto W' hc)
    refine ⟨(e.symm v).2, LinearMap.ext fun g ↦ ?_⟩
    rw [hΦ' v g, hv]
    simp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Φ LinearMap.id hΦ
  have hsinj : Function.Injective s := fun x y h ↦ by
    have := congrArg Φ h
    rwa [← LinearMap.comp_apply, hs, ← LinearMap.comp_apply, hs] at this
  have hc2 : IsCompl (LinearMap.range s) (LinearMap.ker Φ) := by
    have h := LinearMap.isCompl_of_proj (f := s.rangeRestrict ∘ₗ Φ) (fun x ↦ by
      obtain ⟨_, y, rfl⟩ := x
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply]
      rw [← LinearMap.comp_apply Φ s, hs, LinearMap.id_apply])
    have hk : LinearMap.ker s.rangeRestrict = ⊥ := by
      rw [LinearMap.ker_rangeRestrict]; exact LinearMap.ker_eq_bot.2 hsinj
    rwa [LinearMap.ker_comp_of_ker_eq_bot _ hk] at h
  let ep := Submodule.prodEquivOfIsCompl _ _ hc2
  let es : Dual R W ≃ₗ[R] LinearMap.range s := LinearEquiv.ofInjective s hsinj
  haveI : Module.Finite R (LinearMap.range s) := Module.Finite.equiv es
  haveI : Module.Projective R (LinearMap.range s) := Module.Projective.of_equiv es
  let pr : W' →ₗ[R] LinearMap.ker Φ := LinearMap.snd R _ _ ∘ₗ ep.symm.toLinearMap
  have hpr : pr ∘ₗ (LinearMap.ker Φ).subtype = LinearMap.id := LinearMap.ext fun x ↦ by
    simp [pr, ep, Submodule.prodEquivOfIsCompl_symm_apply_right]
  haveI : Module.Finite R (LinearMap.ker Φ) :=
    Module.Finite.of_surjective pr (fun x ↦ ⟨x, by simpa using congrArg (fun m ↦ m x) hpr⟩)
  haveI : Module.Projective R (LinearMap.ker Φ) := Module.Projective.of_split _ _ hpr
  have hr0 : rankAtStalk (R := R) (LinearMap.ker Φ) = 0 := by
    have h1 := rankAtStalk_eq_of_equiv ep
    rw [rankAtStalk_prod, rankAtStalk_eq_of_equiv es.symm] at h1
    funext p
    have := congrFun h1 p
    simp only [Pi.add_apply] at this
    rw [hrk p] at this
    simp only [Pi.zero_apply]
    omega
  haveI := (rankAtStalk_eq_zero_iff_subsingleton).1 hr0
  have hb : (e.symm f).2 ∈ LinearMap.ker Φ := LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ by
    rw [hΦ' f g]; exact hf g g.2)
  have h0 : (e.symm f).2 = 0 := by
    have := Subsingleton.elim (⟨_, hb⟩ : LinearMap.ker Φ) 0
    simpa using congrArg Subtype.val this
  rw [← hdec f, h0]
  simp

theorem mem_of_annihilates_dual {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ψ : LinearMap.BilinForm R (Dual R M)) [ψ.IsPerfPair] (F N : Submodule R M) (hc : IsCompl F N)
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R F] [Module.Projective R F] (g : ℕ)
    (hM : ∀ p : PrimeSpectrum R, rankAtStalk M p = 2 * g)
    (hF : ∀ p : PrimeSpectrum R, rankAtStalk F p = g)
    (hiso : ∀ f ∈ F.dualAnnihilator, ∀ h ∈ F.dualAnnihilator, ψ f h = 0) (f : Dual R M)
    (hf : ∀ h ∈ F.dualAnnihilator, ψ f h = 0) : f ∈ F.dualAnnihilator := by
  let e := Submodule.prodEquivOfIsCompl F N hc
  have hdec : ∀ x : M, (((e.symm x).1 : F) : M) + ((e.symm x).2 : M) = x := fun x ↦ by
    rw [← Submodule.coe_prodEquivOfIsCompl' F N hc, LinearEquiv.apply_symm_apply]
  have hc' : IsCompl F.dualAnnihilator N.dualAnnihilator := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro φ ⟨h1, h2⟩
      rw [Submodule.mem_bot]
      refine LinearMap.ext fun x ↦ ?_
      rw [← hdec x, map_add (f := _), (Submodule.mem_dualAnnihilator _).1 h1 _ (Submodule.coe_mem _),
        (Submodule.mem_dualAnnihilator _).1 h2 _ (Submodule.coe_mem _)]
      simp
    · rw [codisjoint_iff_le_sup]
      intro φ _
      rw [Submodule.mem_sup]
      refine ⟨φ ∘ₗ N.subtype ∘ₗ LinearMap.snd R F N ∘ₗ e.symm.toLinearMap, ?_,
        φ ∘ₗ F.subtype ∘ₗ LinearMap.fst R F N ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
      · refine (Submodule.mem_dualAnnihilator _).2 fun x hx ↦ ?_
        simp [e]
        rw [Submodule.projection_apply_of_mem_right _ hx, map_zero]
      · refine (Submodule.mem_dualAnnihilator _).2 fun x hx ↦ ?_
        simp [e]
        rw [Submodule.projection_apply_of_mem_right _ hx, map_zero]
      · refine LinearMap.ext fun x ↦ ?_
        conv_rhs => rw [← hdec x]
        simp [add_comm]
  let eW' : Dual R F ≃ₗ[R] N.dualAnnihilator :=
    (Submodule.quotientEquivOfIsCompl N F hc.symm).dualMap.trans (Submodule.dualQuotEquivDualAnnihilator N)
  let eW : Dual R N ≃ₗ[R] F.dualAnnihilator :=
    (Submodule.quotientEquivOfIsCompl F N hc).dualMap.trans (Submodule.dualQuotEquivDualAnnihilator F)
  have hpN : (N.projectionOnto F hc.symm) ∘ₗ N.subtype = LinearMap.id :=
    LinearMap.ext fun x ↦ Submodule.projectionOnto_apply_left hc.symm x
  haveI : Module.Projective R N := Module.Projective.of_split _ _ hpN
  haveI : Module.Finite R N := Module.Finite.of_surjective _ (Submodule.projectionOnto_surjective hc.symm)
  let eN : Dual R F.dualAnnihilator ≃ₗ[R] N := eW.dualMap.trans (Module.evalEquiv R N).symm
  haveI : Module.Finite R N.dualAnnihilator := Module.Finite.equiv eW'
  haveI : Module.Projective R N.dualAnnihilator := Module.Projective.of_equiv eW'
  haveI : Module.Finite R (Dual R F.dualAnnihilator) := Module.Finite.equiv eN.symm
  haveI : Module.Projective R (Dual R F.dualAnnihilator) := Module.Projective.of_equiv eN.symm
  refine mem_of_annihilates ψ _ _ hc' (fun p ↦ ?_) hiso f hf
  rw [← rankAtStalk_eq_of_equiv eW', rankAtStalk_eq_of_equiv eN, GlobalTheory.TopExt.rankAtStalk_dual F p, hF p]
  have h1 := congrFun (rankAtStalk_eq_of_equiv e) p
  rw [rankAtStalk_prod, Pi.add_apply, hM p, hF p] at h1
  omega

end GlobalTheory.PolExistsRing

namespace GlobalTheory.PolExistsRing

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem polForm_exists : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π →
    ∃ ψ : LinearMap.BilinForm S (HdR A), IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
      (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧
      ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  intro P E _ _ _ H Dw l Xo S _ x A _ π hπ
  open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.Limits
    CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
  have hA : IsAbelianScheme A := by
    have hG := ObjDim.isAbelianScheme Xo.univ
    have := hG.comm
    have hcomm : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
        ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hcomm, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨h0, -, -, -, e, he⟩ := P.1 S A _ hA gA
  have hLB : (Xo.univ.t.PP.L.pull π).IsLB := pull_isLB Xo.univ.t.PP.isLB π
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso S ⊥ (dp0 S) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := GlobalTheory.PolExists.exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 S) (𝟙 _) A
    rw [show prim (dp0 S) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 S) (A.hom ≫ 𝟙 _) (Xo.univ.t.PP.L.pull π) (∑ k, cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, cup _ (a k) (b k) := by

      rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  have hpol : IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) (wedgeForm (dp0 S) (𝟙 _) A a' b') :=
    ⟨n, a', b', hz', rfl⟩
  have hK : Out.KTriv A (Xo.univ.t.PP.L.pull π) :=
    kTriv_pull hπ Xo.univ.t.PP.isLB hLB ((isGen_iff _).1 (GlobalTheory.PolExists.isGen_self hLB)) Xo.univ.ktriv
  obtain ⟨hiso, hperf⟩ := P.2.2.2.2 S A _ hA gA _ hLB _ hpol
  have hperf' := hperf hK
  refine ⟨_, hpol, hiso, hperf', fun f hf ↦ ?_⟩

  obtain ⟨hfin, hproj, hrk⟩ := AbelianDeRham.Free.prim P.1 hA gA
  obtain ⟨-, ⟨N, hN⟩, hFfin, hFproj, hFrk⟩ := P.2.1 S A _ hA gA
  exact mem_of_annihilates_dual (wedgeForm (dp0 S) (𝟙 _) A a' b') (PrimitiveSubmodule A) N hN _ hrk hFrk hiso f hf

end GlobalTheory.PolExistsRing
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

theorem IsDual.eq_of_evc {S : Scheme.{0}} {A B' T : Over S} [GrpObj A] [GrpObj B'] {P' : LB (A ⊗ B').left}
    (h : IsDual A B' P') {y₁ y₂ : T ⟶ B'}
    (e : evc h.isLB (fst A T) (snd A T ≫ y₁) = evc h.isLB (fst A T) (snd A T ≫ y₂)) : y₁ = y₂ := by
  have hM : (ev P' (fst A T) (snd A T ≫ y₁)).IsLB := pull_isLB h.isLB _
  have ha : IsAdditive (ev P' (fst A T) (snd A T ≫ y₁)) := by
    refine (isAdditive_iff hM).2 fun Y a a' t ↦ ?_
    rw [evc_ev h.isLB, evc_ev h.isLB, evc_ev h.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ y₁)
  exact (h.univ T _ hM ha).unique ((cls_eq_iff hM hM).1 rfl)
    ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)

theorem comp_mul_eq {S : Scheme.{0}} {G Y : Over S} [MonObj G] (f : Y ⟶ G ⊗ G) :
    f ≫ μ = (f ≫ fst G G) * (f ≫ snd G G) := by
  show _ = lift _ _ ≫ μ
  rw [lift_comp_fst_snd]

theorem isMonHom_of_classifying : ∀ (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B']
    (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left), IsDual A B' P' → IsAdditive (swap P') → P.IsLB →
    IsAdditive (swap P) → ∀ x : B ⟶ B', LBIso P (ev P' (fst A B) (snd A B ≫ x)) → IsMonHom x := by
  intro S A B B' _ _ _ P P' h' ha' hP ha x e
  have hP' := h'.isLB
  have hE : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB hP' _
  have c : cls P hP = cls _ hE := (cls_eq_iff hP hE).2 e
  have K : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B), evc hP a b = evc hP' a (b ≫ x) := by
    intro Y a b
    have k := evc_ev hP' (fst A B) (snd A B ≫ x) hE a b
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k, evc, evc, c]
  have hs : (swap P).IsLB := pull_isLB hP _
  have hs' : (swap P').IsLB := pull_isLB hP' _
  have addR : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hP a (b * b') = evc hP a b + evc hP a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs).1 ha Y b b' a
    rwa [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs] at k
  have addR' : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B'),
      evc hP' a (b * b') = evc hP' a b + evc hP' a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs').1 ha' Y b b' a
    rwa [evc_swap hP' hs', evc_swap hP' hs', evc_swap hP' hs'] at k
  have oneR : ∀ (Y : Over S) (a : Y ⟶ A), evc hP a (1 : Y ⟶ B) = 0 := fun Y a ↦ by
    rw [← evc_swap hP hs]; exact ha.evc_one hs a
  have oneR' : ∀ (Y : Over S) (a : Y ⟶ A), evc hP' a (1 : Y ⟶ B') = 0 := fun Y a ↦ by
    rw [← evc_swap hP' hs']; exact ha'.evc_one hs' a
  have u : ∀ (G : Over S) [MonObj G], snd A (𝟙_ (Over S)) ≫ (η : 𝟙_ (Over S) ⟶ G) = 1 := fun G _ ↦ by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A (𝟙_ (Over S))) (toUnit _)]
  refine ⟨?_, ?_⟩
  · apply h'.eq_of_evc
    rw [← Category.assoc, ← K, u, u, oneR, oneR']
  · apply h'.eq_of_evc
    rw [← Category.assoc, ← Category.assoc, comp_mul_eq, comp_mul_eq, ← K, addR, K, K, ← addR']
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd]

end GlobalTheory.AbDual
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

theorem isDual_of_iso (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B']
    (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left) (h : IsDual A B' P') (hP : P.IsLB) (x : B ⟶ B') (hx : IsIso x)
    (hm : IsMonHom x) (e : LBIso P (ev P' (fst A B) (snd A B ≫ x))) : IsDual A B P := by
  have c : cls P hP = cls _ (pull_isLB h.isLB (lift (fst A B) (snd A B ≫ x)).left) :=
    (cls_eq_iff _ _).2 e
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B), evc hP a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    rw [evc, c, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  have iso : ∀ (T : Over S) (M : LB (A ⊗ T).left) (hM : M.IsLB) (w : T ⟶ B),
      LBIso M (ev P (fst A T) (snd A T ≫ w)) ↔ LBIso M (ev P' (fst A T) (snd A T ≫ w ≫ x)) := by
    intro T M hM w
    rw [← cls_eq_iff hM (pull_isLB hP _), ← cls_eq_iff hM (pull_isLB h.isLB _), cls_ev hP, cls_ev h.isLB, key,
      Category.assoc]
  refine ⟨hP, (isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (triv_ev_iff hP _ _).2 ?_, fun T M hM hM' ↦ ?_⟩
  · rw [key, key, key]
    exact (isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ x)
  · rw [key, MonObj.one_comp]
    exact (triv_ev_iff h.isLB _ _).1 h.zero
  · obtain ⟨z, hz, hu⟩ := h.univ T M hM hM'
    refine ⟨z ≫ inv x, (iso T M hM _).2 ?_, fun w hw ↦ ?_⟩
    · rwa [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · rw [← hu _ ((iso T M hM w).1 hw), Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem transport : ∀ (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left), IsDual A B' P' → P.IsLB → ∀ x : B ⟶ B', IsIso x → IsMonHom x → LBIso P (ev P' (fst A B) (snd A B ≫ x)) → IsDual A B P :=
  fun S A B B' _ _ _ P P' h hP x hx hm e ↦ isDual_of_iso S A B B' P P' h hP x hx hm e

end GlobalTheory.AbDual
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.AbDual

theorem lbIso_swap_and_triv_of_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (l : A ⟶ B), LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) → LBIso (GlobalTheory.AbDual.ev P (fst A A) (snd A A ≫ 𝟙 A)) (GlobalTheory.AbDual.ev (GlobalTheory.AbDual.swap P₀) (fst A A ≫ l) (snd A A)) ∧ ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen := by
  intro k _ A B _ _ P₀ hD P hP hsym l hl
  have hP₀ := hD.isLB
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB :=
    fun hL F => ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL F
  have pullIso : ∀ {X Y Z : Scheme.{0}} {M : LB Y} {N : LB X} {f : Y ⟶ X},
      LBIso M (N.pull f) → (g : Z ⟶ Y) → LBIso (M.pull g) (N.pull (g ≫ f)) := by
    intro X Y Z M N f H g
    exact H.chartPull (chartPullPull M g)
      (chartPullSame N (fun _ : PUnit => g ≫ f) (fun _ : PUnit => f) (fun _ => 1) g fun _ => rfl)
  have key : ∀ (Y : Over (Sp k)) (a b : Y ⟶ A), LBIso (ev P a b) (ev P₀ b (a ≫ l)) := by
    intro Y a b
    have hs := pullIso hsym (lift a b).left
    have hl' := pullIso hl (lift b a).left
    have es : LBIso (ev P a b) (ev P b a) := by
      simpa only [← Over.comp_left, comp_lift, lift_snd, lift_fst] using hs
    have el : LBIso (ev P b a) (ev P₀ b (a ≫ l)) := by
      simpa only [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc] using hl'
    exact (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).1
      (((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 es).trans
       ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 el))
  refine ⟨?_, fun T x hx => ?_⟩
  · have hs : LBIso (swap P₀) (swap P₀) := (CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB hP₀ _)).1 rfl
    have hs' := pullIso hs (lift (fst A A ≫ l) (snd A A)).left
    have hs'' : LBIso (ev (swap P₀) (fst A A ≫ l) (snd A A)) (ev P₀ (snd A A) (fst A A ≫ l)) := by
      simpa only [swap, ev, ← Over.comp_left, comp_lift, lift_fst, lift_snd] using hs'
    apply (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _)).1
    exact ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 (by simpa only [Category.comp_id] using key (A ⊗ A) (fst A A) (snd A A))).trans
      ((CechPic.cls_eq_iff (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP₀ _)).2 hs'').symm
  · have hk := key (A ⊗ T) (snd A T ≫ x) (fst A T)
    simp only [Category.assoc, hx, MonObj.comp_one] at hk
    have ht : Triv (ev P₀ (fst A T) (1 : A ⊗ T ⟶ B)) := by
      obtain ⟨t, ht⟩ := hD.zero
      have h := DVR.pullGen_isGen _ _ _ t ht (fst A T).left
      simpa only [ev, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] using (show Triv _ from ⟨_, h⟩)
    exact (CechPic.iso_triv_iff _).1 ((CechPic.cls_eq_iff (LB.isLB_triv _) (pull_isLB hP _)).1
      (((CechPic.cls_eq_iff (LB.isLB_triv _) (pull_isLB hP₀ _)).2 ((CechPic.iso_triv_iff _).2 ht)).trans
        ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 hk).symm))

end GlobalTheory.AbDual
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem isAdditive_swap_of_isDual (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hd : IsDual A B P) :
    IsAdditive (swap P) := by
  have hP := hd.isLB
  have ext : ∀ {Y : Over S} {x y : Y ⟶ B},
      (∀ (Z : Over S) (u : Z ⟶ Y) (a : Z ⟶ A), evc hP a (u ≫ x) = evc hP a (u ≫ y)) → x = y := by
    intro Y x y h
    have hM : (ev P (fst A Y) (snd A Y ≫ x)).IsLB := pull_isLB hP _
    refine (hd.univ Y _ hM ((isAdditive_iff hM).2 fun Z a a' t ↦ ?_)).unique
      ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB hP _)).1 ?_)
    · simp only [evc_ev hP, lift_fst, lift_snd_assoc]
      exact (isAdditive_iff hP).1 hd.additive _ _ _ _
    · exact h (A ⊗ Y) (snd A Y) (fst A Y)
  have h₁ : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ fst B B)).IsLB := pull_isLB hP _
  have h₂ : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ snd B B)).IsLB := pull_isLB hP _
  have hM := isLB_tens h₁ h₂
  have eM : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B ⊗ B),
      evc hM a t = evc hP a (t ≫ fst B B) + evc hP a (t ≫ snd B B) := by
    intro Y a t
    show CechPic.pull _ (cls _ hM) = _
    rw [cls_tens h₁ h₂ hM, map_add (f := _)]
    exact congrArg₂ (· + ·) ((evc_ev hP _ _ h₁ a t).trans (by rw [lift_fst, lift_snd_assoc]))
      ((evc_ev hP _ _ h₂ a t).trans (by rw [lift_fst, lift_snd_assoc]))
  obtain ⟨m, hm, -⟩ := hd.univ (B ⊗ B) _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ by
    rw [eM, eM, eM, (isAdditive_iff hP).1 hd.additive, (isAdditive_iff hP).1 hd.additive]
    abel)
  have hm' : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ m)).IsLB := pull_isLB hP _
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B ⊗ B),
      evc hP a (t ≫ m) = evc hP a (t ≫ fst B B) + evc hP a (t ≫ snd B B) := by
    intro Y a t
    have e : evc hM a t = evc hm' a t := by rw [evc, evc, (cls_eq_iff hM hm').2 hm]
    rw [← eM, e, evc_ev hP, lift_fst, lift_snd_assoc]
  have hl : ∀ {Y : Over S} (b : Y ⟶ B), lift b 1 ≫ m = b := fun b ↦ ext fun Z u a ↦ by
    rw [← Category.assoc, key]
    simp only [Category.assoc, comp_lift, lift_fst, lift_snd, MonObj.comp_one, evc_one_right hP hd.zero, add_zero]
  have hr : ∀ {Y : Over S} (b : Y ⟶ B), lift 1 b ≫ m = b := fun b ↦ ext fun Z u a ↦ by
    rw [← Category.assoc, key]
    simp only [Category.assoc, comp_lift, lift_fst, lift_snd, MonObj.comp_one, evc_one_right hP hd.zero, zero_add]
  have e1 : ∀ (X : Over S) [MonObj X], (1 : 𝟙_ (Over S) ⟶ X) = η[X] := fun X _ ↦ by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hη : η[B ⊗ B] ≫ m = η[B] := by
    have e : (1 : 𝟙_ (Over S) ⟶ B ⊗ B) = lift (1 : 𝟙_ (Over S) ⟶ B) 1 := by
      ext <;> simp
    rw [← e1 (B ⊗ B), ← e1 B, e, hl]
  haveI : IsMonHom m := GlobalTheory.rigidity_holds S (B ⊗ B) B (AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB) hB m hη
  have hs : (swap P).IsLB := pull_isLB hP _
  refine (isAdditive_iff hs).2 fun Y b b' a ↦ ?_
  rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs]
  have e : b * b' = lift b b' ≫ m := by
    have e' : lift b b' = lift b 1 * lift 1 b' := by
      ext <;> simp [MonObj.mul_comp]
    rw [e', MonObj.mul_comp, hl, hr]
  rw [e, key, lift_fst, lift_snd]

theorem isDual_isAdditive_swap : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left),
    IsAbelianScheme B → IsDual A B P → IsAdditive (swap P) :=
  fun _ _ _ _ _ _ hB hd ↦ isAdditive_swap_of_isDual hB hd

end GlobalTheory.AbDual
end
end
