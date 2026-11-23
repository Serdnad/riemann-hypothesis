module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModifSections

open Opposite

theorem isIntegral_of_iso_comp {A B C E : CommRingCat.{0}} (i : A ⟶ B) (f : B ⟶ C) (m : C ⟶ E) [IsIso i]
    [IsIso m] (h : (i ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv i ≫ (i ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv i)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (V : Z₂.Opens) (hV : IsAffineOpen V) : (ρ.app V).hom.IsIntegral := by
  have : IsAffine V.toScheme := hV
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ V)
  rw [morphismRestrict_appTop] at h
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (q : A = B), IsIso (eqToHom q) := fun q => by
    subst q; rw [eqToHom_refl]; infer_instance
  exact @isIntegral_of_iso_comp _ _ _ _ _ _ _ (hi _) (hi _) h

theorem isNormalScheme_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) [Smooth p] :
    GlobalTheory.IsNormalScheme Y :=
  (GlobalTheory.isNormalScheme_iff Y).2 (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
    ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))

theorem exists_germ_eq {Y : Scheme.{0}} [IsIntegral Y] [GlobalTheory.IsNormalScheme Y] (y : Y) (hy : y = genericPoint Y)
    (V : Y.Opens) (hyV : y ∈ V) (t : Y.presheaf.stalk y)
    (h : ∀ x ∈ V, ∃ (W : Y.Opens) (hW : y ∈ W), x ∈ W ∧ W ≤ V ∧
      (Y.presheaf.germ W y hW).hom.IsIntegralElem t) :
    ∃ a : Γ(Y, V), Y.presheaf.germ V y hyV a = t := by
  subst hy
  have : Nonempty V := ⟨⟨_, hyV⟩⟩
  refine GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV, hi⟩ := h x hx
  have hne : Nonempty W := ⟨⟨_, hW⟩⟩
  have := GlobalTheory.IsNormalScheme.isIntegrallyClosedIn_functionField (X := Y) W
  obtain ⟨s, hs⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := Γ(Y, W)) (A := Y.functionField)).1 hi
  exact ⟨W, hne, s, hxW, hWV, hs⟩

theorem isoOver_top {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [GlobalTheory.IsNormalScheme Y]
    (σ : X ⟶ Y) [UniversallyClosed σ] (U : Y.Opens) [IsIso (σ ∣_ U)]
    (hU : ((σ ⁻¹ᵁ U : X.Opens) : Set X).Nonempty) : IsoOver σ ⊤ := by
  intro V _
  have hηU : genericPoint X ∈ σ ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (σ ⁻¹ᵁ U).isOpen).2 (by simpa using hU)
  have hmem : ∀ V : Y.Opens, (V : Set Y).Nonempty → σ (genericPoint X) ∈ V := by
    intro V hV
    obtain ⟨y, hyV, hyU⟩ := nonempty_preirreducible_inter V.isOpen U.isOpen hV ⟨_, hηU⟩
    obtain ⟨x, hx⟩ := (σ ∣_ U).surjective ⟨y, hyU⟩
    have hx' : σ x.1 = y := (morphismRestrict_base_coe σ U x).symm.trans (congrArg Subtype.val hx)
    have hne : ((σ ⁻¹ᵁ V : X.Opens) : Set X).Nonempty := ⟨x.1, show σ x.1 ∈ V from hx' ▸ hyV⟩
    exact ((genericPoint_spec X).mem_open_set_iff (σ ⁻¹ᵁ V).isOpen).2 (by simpa using hne)
  have hgen : σ (genericPoint X) = genericPoint Y := by
    have h1 : σ (genericPoint X) ⤳ genericPoint Y :=
      specializes_iff_forall_open.2 fun s hs hg => hmem ⟨s, hs⟩ ⟨_, hg⟩
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hS : IsIso (σ.stalkMap (genericPoint X)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap σ U ⟨_, hηU⟩)).1
      (((isIso_iff_isIso_stalkMap (σ ∣_ U)).1 inferInstance).2 ⟨_, hηU⟩)
  have hSb := ConcreteCategory.bijective_of_isIso (σ.stalkMap (genericPoint X))
  by_cases hV : (V : Set Y).Nonempty
  swap
  · exact isoOver_of_isIso σ (O := U) V fun y hy => (hV ⟨y, hy⟩).elim
  have hyV := hmem V hV
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a a' e => ?_, fun b => ?_⟩
  · apply germ_injective_of_isIntegral Y (σ (genericPoint X)) hyV
    apply hSb.1
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, e]
  obtain ⟨t, ht⟩ := hSb.2 (X.presheaf.germ (σ ⁻¹ᵁ V) (genericPoint X) hyV b)
  obtain ⟨a, ha⟩ := exists_germ_eq (σ (genericPoint X)) hgen V hyV t fun y hy => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    have hWV' : W ≤ V := hWV
    have hηW : σ (genericPoint X) ∈ W := hmem W ⟨y, hyW⟩
    refine ⟨W, hηW, hyW, hWV', ?_⟩
    have hi := isIntegral_app σ W hW (X.presheaf.map (homOfLE (σ.preimage_mono hWV')).op b)
    have h2 := RingHom.IsIntegralElem.map hi (X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW).hom
    have e1 : (X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW).hom.comp (σ.app W).hom =
        (σ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.germ W (σ (genericPoint X)) hηW).hom :=
      RingHom.ext fun a => (Scheme.Hom.germ_stalkMap_apply σ W _ hηW a).symm
    have e2 : X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW
        (X.presheaf.map (homOfLE (σ.preimage_mono hWV')).op b) = σ.stalkMap (genericPoint X) t := by
      exact (X.presheaf.germ_res_apply (homOfLE (σ.preimage_mono hWV')) _ hηW b).trans ht.symm
    rw [e1, e2] at h2
    have h3 := RingHom.IsIntegralElem.map h2 (inv (σ.stalkMap (genericPoint X))).hom
    have e3 : (inv (σ.stalkMap (genericPoint X))).hom.comp (σ.stalkMap (genericPoint X)).hom =
        RingHom.id _ := by
      rw [← CommRingCat.hom_comp, IsIso.hom_inv_id]; rfl
    rwa [← RingHom.comp_assoc, e3, RingHom.id_comp, ← RingHom.comp_apply, e3, RingHom.id_apply] at h3
  refine ⟨a, germ_injective_of_isIntegral X (genericPoint X) hyV ?_⟩
  rw [← Scheme.Hom.germ_stalkMap_apply, ha, ht]

theorem modification_lineBundleGlobalSectionsDim_pull_eq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k) (U : Y.Opens) (D : ℕ),
    SmoothOfRelativeDimension D p → IsProjOver p → ∀ (M : Modif p U D) [IsIntegral M.X] (B : LB Y), B.IsLB →
    letI := algebraΓOfHom p; letI := algebraΓOfHom M.str; lbH0 k (B.pull M.σ) = lbH0 k B := by
  intro k _ Y _ p U D hs hp M _ B hB
  haveI := hs
  haveI : Smooth p := SmoothOfRelativeDimension.smooth D p
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  haveI : IsProper (M.σ ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver M.proj
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  haveI : IsProper M.σ := IsProper.of_comp M.σ p
  haveI := M.iso
  have hb := (isoOver_top M.σ U M.dense.nonempty).bijective_pull (p := p) hB (W := ⊤) le_top le_top
  letI := algebraΓOfHom p
  letI := algebraΓOfHom M.str
  rw [← H0.finrank_top M.str (B.pull M.σ), ← H0.finrank_top p B]
  exact (LinearEquiv.ofBijective _ hb).finrank_eq.symm

end GlobalTheory.ModifSections
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.BotScal

open GlobalTheory.KappaArith (AwayIm)

variable {D : D7} {T : Type} {Lc : LevCh D T}

theorem xi_awayIm_of_infPart {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ) (u : (AE D)ˣ)
    (hu : infPart D (u : AE D) = 1) : AwayIm D m ((Lc.xi t u : Circle) : ℂ) := by
  obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2 (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3)
    (Lc.xi t) (Lc.xiH t) (hL.xi t)
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom u)
  rw [hprod u hu S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact AwayIm.prod _ _ fun P _ => GlobalTheory.KappaArith.awayIm_val hL hx m P (Formalism.L2.Host.atFin P (k P))

theorem xi_awayIm {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ) (u : (AE D)ˣ) :
    AwayIm D m ((Lc.xi t u : Circle) : ℂ) := by
  obtain ⟨v, hv1, hv2, hv3⟩ := GlobalTheory.TameFinitePart.exists_lift D (Units.map (finPart D).toMonoidHom u)
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  have h1 : Lc.xi t (u * v⁻¹) = 1 := GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (by
    rw [Units.val_mul, map_mul, hv3]
    exact Units.mul_inv (Units.map (finPart D).toMonoidHom u))
  have h2 : Lc.xi t u = Lc.xi t v := by
    have := congrArg (· * Lc.xi t v) h1
    simpa [map_mul, map_inv] using this
  rw [h2]
  exact xi_awayIm_of_infPart hL hx m v hv1

end GlobalTheory.BotScal

namespace GlobalTheory.BotScal

theorem moved_vacua_scal : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (Y : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    ∃ r r' : T → ℂ, (∀ t, r t ≠ 0 ∧ r' t ≠ 0) ∧ (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω μ₀ (g, h) Y.vac) ∧
      (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' μ₀ (g', h) Y.vac') ∧
      ∀ t, ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ r' t / r t = D.what₂.embLL ζ * (r' μ₀ / r μ₀) := by
  intro D T Lc sc G μ₀ hL W S hN i j A A' WW Y hY g hg g' hg' h hh
  have hI := hY.2.2.2.2.2.2.2
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (GlobalTheory.Grid.neg A) ((GlobalTheory.Grid.ofSgn true A).symm g)
  obtain ⟨x', hx'⟩ := GlobalTheory.RecDict.exists_isDetRoot D A' g'
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D WW h
  have hvac : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW Y.vac := hI.isVac.2.theta
  have hvac' : IsThetaFunO W.ψ A' WW Y.vac' := hI.isVac'.2.theta
  have e := fun t => GlobalTheory.WeilChange.weilData_differ_by_splitFac D W.ψ (GlobalTheory.Grid.neg A) WW _ _ _ _ _ _ (hI.weil μ₀) (hI.weil t) _ h x y hx hy _ hvac
  have e' := fun t => GlobalTheory.WeilChange.weilData_differ_by_splitFac D W.ψ A' WW _ _ _ _ _ _ (hI.weil' μ₀) (hI.weil' t) g' h x' y hx' hy _ hvac'
  let a : T → (AE D)ˣ →* Circle := fun t => Lc.mu t (↑j + 1) * Lc.eta ^ (rankV D ↑i ↑j % 2)
  let b : (AE D)ˣ →* Circle := G.ch.chi (D.R.m - ↑i) * Lc.eta ^ (rankV D ↑i ↑j % 2)
  refine ⟨fun t => ((splitFacO b (b / a t) x y : Circle) : ℂ) * ((splitFacO b (b / a μ₀) x y : Circle) : ℂ)⁻¹,
    fun t => ((splitFacO (a t) (a t / b) x' y : Circle) : ℂ) * ((splitFacO (a μ₀) (a μ₀ / b) x' y : Circle) : ℂ)⁻¹,
    fun t => ⟨?_, ?_⟩, fun t => ?_, fun t => ?_, ?_⟩
  rotate_left 2
  · have := e t
    simp only [GlobalTheory.Grid.WRep.toSgn, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MonoidHom.id_apply] at this
    exact this
  · exact e' t
  · intro t
    have hb : Lc.xi μ₀ = 1 := MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi μ₀))
    obtain ⟨ζ, hζ, hζe⟩ := xi_awayIm hL (hN.chars.xi t) (Qn G t) (x'⁻¹ * y * x⁻¹)
    refine ⟨ζ, hζ, ?_⟩
    rw [hζe]
    simp only [splitFacO, a, b, LevCh.mu, Formalism.IndefR.Lift.tup, hb, Circle.coe_mul, Circle.coe_inv, MonoidHom.div_apply,
      MonoidHom.mul_apply, MonoidHom.one_apply, map_mul, map_inv, Circle.coe_div, mul_one]
    field_simp [Circle.coe_ne_zero]
  · exact mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))
  · exact mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))

end GlobalTheory.BotScal
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FlatCM.GramInt

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

theorem weilEq_act_left {A B : PAT H (Sp (𝓞 K))} {f g : A.t.G ⟶ B.t.G} {r : 𝓞 E} {k : Type} [Field k]
    {t : Sp k ⟶ Sp (𝓞 K)} (s : 𝓞 E) (h : WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) t) :
    WeilEq B.t.PP.L (A.t.act.act s ≫ f) g A.t.PP.L (A.t.act.act (s * r)) (𝟙 _) t := by
  intro n x y c hn hx hy
  haveI := A.t.act.hom s
  have hx' : (x ≫ A.t.act.act s) ^ n = 1 := by rw [← pow_comp, hx]; simp
  have := h n (x ≫ A.t.act.act s) y c hn hx' hy
  simpa only [Category.assoc, A.t.act.mul] using this
end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {σ₁ : K →+* ℂ} {A B : PAT H (Sp (𝓞 K))}

theorem isLinearHom_finprod {I₀ : Type} (S : Finset I₀) (F : I₀ → (A.t.G ⟶ B.t.G))
    (hF : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (F i)) :
    GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (∏ i ∈ S, F i) :=
  Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg)
    (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hF i

theorem weilEq_prod_right {I₀ : Type} (f : A.t.G ⟶ B.t.G) (hf : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act f)
    (G : I₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G i)) (r : I₀ → 𝓞 E)
    (h : ∀ i, WeilEq B.t.PP.L f (G i) A.t.PP.L (A.t.act.act (r i)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {T : Finset I₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L f (∏ i ∈ T, G i) A.t.PP.L (A.t.act.act (∑ i ∈ T, r i)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact GlobalTheory.T.weilPairingCompatible_add_second_position_complex E H K σ₁ A B f (G a) _ hf.isMonHom (hG a).isMonHom
      (isLinearHom_finprod s G hG).isMonHom _ _ (h a) ih

theorem weilEq_prod_prod {I₀ J₀ : Type} (F : I₀ → (A.t.G ⟶ B.t.G)) (hF : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (F i))
    (G : J₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ j, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G j)) (r : I₀ → J₀ → 𝓞 E)
    (h : ∀ i j, WeilEq B.t.PP.L (F i) (G j) A.t.PP.L (A.t.act.act (r i j)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {S : Finset I₀} (hS : S.Nonempty) {T : Finset J₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L (∏ i ∈ S, F i) (∏ j ∈ T, G j) A.t.PP.L (A.t.act.act (∑ i ∈ S, ∑ j ∈ T, r i j)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => simpa using weilEq_prod_right (F a) (hF a) G hG (r a) (h a) hT
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact GlobalTheory.T.weilPairingCompatible_add_first_position_complex E H K σ₁ A B (F a) _ _ (hF a).isMonHom (isLinearHom_finprod s F hF).isMonHom
      (isLinearHom_finprod T G hG).isMonHom _ _ (weilEq_prod_right (F a) (hF a) G hG (r a) (h a) hT) ih

theorem weilEq_pow_pow (f g : A.t.G ⟶ B.t.G) (hf : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act f)
    (hg : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act g) (r : 𝓞 E)
    (h : WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    WeilEq B.t.PP.L (f ^ n) (g ^ m) A.t.PP.L (A.t.act.act ((n * m : ℕ) * r)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have e1 : f ^ n = ∏ _i ∈ Finset.range n, f := by simp
  have e2 : g ^ m = ∏ _j ∈ Finset.range m, g := by simp
  have e3 : ((n * m : ℕ) : 𝓞 E) * r = ∑ _i ∈ Finset.range n, ∑ _j ∈ Finset.range m, r := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [e1, e2, e3]
  exact weilEq_prod_prod (fun _ => f) (fun _ => hf) (fun _ => g) (fun _ => hg) (fun _ _ => r) (fun _ _ => h)
    (Finset.nonempty_range_iff.2 hn.ne') (Finset.nonempty_range_iff.2 hm.ne')
end

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p : ℕ}

theorem weilEq_combo (X : CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E))
    (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)) (hG : GlobalTheory.FlatCM.IsGram X gP gQ) (hp : 0 < p) (x y : Fin p → 𝓞 E) :
    WeilEq X.B.t.PP.L (∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a))
      (∏ b, ((X.A true).t.act.act (y b) ≫ GlobalTheory.FlatCM.phiP X b)) (X.A true).t.PP.L
      ((X.A true).t.act.act (∑ a, ∑ b, x a * gP a b * H.bar (y b))) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have hne : (Finset.univ : Finset (Fin p)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hp⟩⟩
  have hlin : ∀ (z : Fin p → 𝓞 E) a, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act
      ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) := fun z a =>
    (GlobalTheory.Serre.IsLinearHom.act _ _).comp (X.lin (Sum.inl a))
  refine weilEq_prod_prod _ (hlin x) _ (hlin y) _ (fun a b => ?_) hne hne
  have h1 := weilEq_act_left (x a) (hG.1 a b)
  exact GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj E H K σ₁ (X.A true) X.B _ _ (hlin x a).isMonHom (X.lin (Sum.inl b)).isMonHom _ (y b) h1

theorem integral_of_coords (X : CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E))
    (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)) (hG : GlobalTheory.FlatCM.IsGram X gP gQ) (barE : E →+* E)
    (hbar : ∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) {c d : Fin p → E}
    (hc : c ∈ GlobalTheory.FlatCM.HomLat.coords X) (hd : d ∈ GlobalTheory.FlatCM.HomLat.coords X) :
    ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨0, by simp⟩
  obtain ⟨n, hn, x, hx, f, hf, hfx⟩ := hc
  obtain ⟨m, hm, y, hy, g, hg, hgy⟩ := hd
  obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP
    f g hf hg
  have h1 := weilEq_pow_pow f g hf hg r hr hn hm
  rw [hfx, hgy] at h1
  have h2 := weilEq_combo X gP gQ hG hp x y
  have h3 : WeilEq (X.A true).t.PP.L ((X.A true).t.act.act ((n * m : ℕ) * r)) (𝟙 _) (X.A true).t.PP.L
      ((X.A true).t.act.act (∑ a, ∑ b, x a * gP a b * H.bar (y b))) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun k u v e hk hu hv =>
    (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)
  have h4 := GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ h3
  refine ⟨r, ?_⟩
  have h5 := congrArg (fun z : 𝓞 E => (z : E)) h4

  simp only [map_mul, map_natCast, map_sum] at h5
  have hnm : ((n * m : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne'
  apply mul_left_cancel₀ hnm
  rw [h5]
  simp only [hx, hy, ← hbar, map_mul, map_natCast, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end

theorem gram_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X,
        ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X gP gQ hG barE hbar c hc d hd

  have step : ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ d ∈ GlobalTheory.FlatCM.HomLat.lat X,
      ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b) := by
    intro c hc d hd
    induction hd using Submodule.span_induction with
    | mem d hd => exact integral_of_coords X gP gQ hG barE hbar hc hd
    | zero => exact ⟨0, by simp⟩
    | add d d' _ _ h h' =>
      obtain ⟨y, hy⟩ := h
      obtain ⟨y', hy'⟩ := h'
      refine ⟨y + y', ?_⟩
      simp only [map_add (f := _), hy, hy', Pi.add_apply, mul_add, Finset.sum_add_distrib]
    | smul s d _ h =>
      obtain ⟨y, hy⟩ := h
      refine ⟨H.bar s * y, ?_⟩
      simp only [map_mul, ← hbar, hy, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  induction hc using Submodule.span_induction with
  | mem c hc => exact step c hc d hd
  | zero => exact ⟨0, by simp⟩
  | add c c' _ _ h h' =>
    obtain ⟨y, hy⟩ := h
    obtain ⟨y', hy'⟩ := h'
    refine ⟨y + y', ?_⟩
    simp only [map_add (f := _), hy, hy', Pi.add_apply, add_mul, Finset.sum_add_distrib]
  | smul s c _ h =>
    obtain ⟨y, hy⟩ := h
    refine ⟨s * y, ?_⟩
    simp only [map_mul, hy, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

end GlobalTheory.FlatCM.GramInt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.l2A_transport_gram_transpose : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, GlobalTheory.WeilL2Words.l2A D.host.F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A D.host.F μ Φ := by
  first | exact @GlobalTheory.WeilL2Transport.l2A_transport | exact GlobalTheory.WeilL2Transport.l2A_transport | (intros; apply GlobalTheory.WeilL2Transport.l2A_transport <;> assumption)
end
