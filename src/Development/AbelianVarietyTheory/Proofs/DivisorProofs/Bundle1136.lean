module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle942
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.VB GlobalTheory.Conormal

namespace GlobalTheory.ConormalFrame

theorem sub_isLocalizedModule {X : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent] (N : Sub F)
    {U : X.Opens} (hU : IsAffineOpen U)
    (h : ∀ (f : Γ(X, U)) (t : Γ(F, U)),
      GlobalTheory.Twist.resM F (X.basicOpen_le f) t ∈ N.sec _ → ∃ n : ℕ, f ^ n • t ∈ N.sec U)
    (f : Γ(X, U)) : IsLocalizedModule.Away f (GlobalTheory.QCoh.resBasicOpen N.toMod f) := by
  refine (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff _ f).2 ⟨fun s => ?_, fun t ht => ?_⟩
  · obtain ⟨n, t, e⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_res F hU f (X.basicOpen_le f) rfl
      (N.incl.app _ s)
    obtain ⟨m, hm⟩ := h f t (by
      change F.presheaf.map _ t ∈ _
      rw [← e]
      exact (N.sec _).smul_mem _ (N.incl_app_mem s))
    refine ⟨m + n, N.mkSec _ hm, N.incl_app_injective _ ?_⟩
    rw [Scheme.Modules.Hom.app_smul, GlobalTheory.QCoh.app_res, Sub.incl_app_mkSec, Scheme.Modules.map_smul,
      ← e, pow_add, mul_smul, map_pow]
  · obtain ⟨n, e⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_zero F hU f (X.basicOpen_le f) rfl
      (N.incl.app _ t) (by rw [← GlobalTheory.QCoh.app_res, ht, map_zero])
    exact ⟨n, N.incl_app_injective _ (by rw [Scheme.Modules.Hom.app_smul, e, map_zero])⟩

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}


include he in
theorem preimage_eq (c : IsChart π e U W) : e ⁻¹ᵁ W = U :=
  le_antisymm ((le_preimage_iff he).1 (e.preimage_mono c.le_base)) c.le


include he in
theorem isQuasicoherent_restrict_ideal (c : IsChart π e U W) :
    ((ideal e).restrict c.affine.fromSpec).IsQuasicoherent := by
  have := (isVB_structureModule X).isQuasicoherent
  refine (GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff _ c.affine).2
    (sub_isLocalizedModule _ c.affine fun f (t : Γ(X, W)) ht => ?_)
  have hcpt : IsCompact ((e ⁻¹ᵁ W : S.Opens) : Set S) := by
    rw [preimage_eq he c]; exact c.affine_base.isCompact
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact S
    (U := e ⁻¹ᵁ W) hcpt (e.appLE W _ le_rfl t) (e.appLE W _ le_rfl f) (by
      have hle : S.basicOpen (e.appLE W _ le_rfl f) ≤ e ⁻¹ᵁ X.basicOpen f := by
        rw [Scheme.Hom.appLE_eq_app, e.preimage_basicOpen]
      have := congrArg (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG S hle)
        (show e.appLE _ _ le_rfl (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X (X.basicOpen_le f) t) = 0 from ht)
      rw [GlobalTheory.DualPull.resG_appLE, GlobalTheory.DualPull.appLE_resG, map_zero] at this
      exact (GlobalTheory.DualPull.resG_appLE e _ _ _).trans this)
  refine ⟨n, ?_⟩
  change e.appLE W _ le_rfl (f ^ n * t) = 0
  rw [map_mul, map_pow, hn]

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}


include he in
theorem isQuasicoherent_conormal : (conormal e).IsQuasicoherent := by
  refine GlobalTheory.QCoh.isQuasicoherent_of_forall_exists_affine _ fun x => ?_
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  have := isQuasicoherent_restrict_ideal he c
  refine ⟨U, c.affine_base, hx,
    (GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff _ c.affine_base).mp ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec Γ(S, U)).ringCatSheaf).prop_of_iso
    ((GlobalTheory.QCoh.restrictPullbackIso
      (IsAffineOpen.SpecMap_appLE_fromSpec e c.affine c.affine_base c.le)).app (ideal e))
    (GlobalTheory.QCoh.isQuasicoherent_pullback_Spec (e.appLE W U c.le) ((ideal e).restrict c.affine.fromSpec))

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

open GlobalTheory.QCoh


set_option backward.isDefEq.respectTransparency false in
theorem isBaseChange_pullbackSections {X Y : Scheme.{0}} (f : X ⟶ Y) (G : Y.Modules)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [(G.restrict hV.fromSpec).IsQuasicoherent] (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEAlgebra f e
    letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
    haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
    IsBaseChange Γ(X, U) (pullbackSections f G e) := by
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  obtain ⟨a, ha⟩ := exists_equiv_pullback_Spec (f.appLE V U e) (G.restrict hV.fromSpec)
  have w := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e
  let κ : Γ((Scheme.Modules.pullback (Spec.map (f.appLE V U e))).obj (G.restrict hV.fromSpec), ⊤)
      ≃ₗ[Γ(X, U)] Γ(((Scheme.Modules.pullback f).obj G).restrict hU.fromSpec, ⊤) :=
    (moduleSpecΓFunctor.mapIso ((restrictPullbackIso w).app G)).toLinearEquiv
  refine IsBaseChange.of_equiv
    ((sectionsEquivFromSpec G hV).baseChange Γ(Y, V) Γ(X, U) _ _ ≪≫ₗ a ≪≫ₗ κ ≪≫ₗ
      (sectionsEquivFromSpec _ hU).symm) fun s ↦ ?_
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq, LinearEquiv.baseChange_tmul, ha, sectionsEquivFromSpec_apply,
    sectionsEquivFromSpec_apply, res_pullbackSections]
  refine Eq.trans ?_ (restrictPullbackIso_hom_app_pullbackSections w G (V' := ⊤) (U' := ⊤)
    (fromSpec_image_le hV ⊤) le_rfl _ s)
  exact congr(κ $(res_self _ le_rfl _)).symm

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}

theorem ofAugCot_bijective (c : IsChart π e U W) : Function.Bijective (c.ofAugCot he) := by
  letI := c.algebra
  letI := GlobalTheory.QCoh.appLEAlgebra e c.le
  letI := GlobalTheory.QCoh.appLEModule e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := GlobalTheory.QCoh.appLE_isScalarTower e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := AugCot.isScalarTower_of_algebraMap_eq (c.aug he) fun _ => rfl
  haveI := isQuasicoherent_restrict_ideal he c
  have hb := isBaseChange_pullbackSections e (ideal e) c.affine_base c.affine c.le
  let g : Γ(ideal e, W) →ₗ[Γ(X, W)] AugCot (c.aug he) := (RingHom.ker (c.aug he)).toCotangent ∘ₗ
    (GlobalTheory.QCoh.appLinear (idealSub e).incl W).codRestrict (RingHom.ker (c.aug he)) fun s =>
      (c.aug_eq_zero_iff he).2 ((idealSub e).incl_app_mem s)
  have key (x : RingHom.ker (c.aug he)) : c.ofAugCot he ((RingHom.ker (c.aug he)).toCotangent x) =
      cls c.le x ((c.aug_eq_zero_iff he).1 x.2) := d_eq_cls he _ _ _
  refine Function.bijective_iff_has_inverse.2 ⟨hb.lift g, fun x => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := (RingHom.ker (c.aug he)).toCotangent_surjective x
    rw [key]
    exact hb.lift_eq g _
  · refine hb.inductionOn y (fun s => ?_) (fun r y hy => ?_) fun y z hy hz => ?_
    · rw [hb.lift_eq]
      exact key _
    · rw [map_smul, map_smul, hy]
      rfl
    · rw [map_add (f := _), map_add (f := _), hy, hz]
      rfl


include he in
theorem exists_isFrame [Smooth π] (x : S) :
    ∃ (U : S.Opens) (n : ℕ) (s : Fin n → Γ(conormal e, U)), x ∈ U ∧ IsFrame s := by
  have := isQuasicoherent_conormal he
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  letI := c.algebra
  have : Algebra.Smooth Γ(S, U) Γ(X, W) := Smooth.smooth_appLE π c.affine_base c.affine c.le_base
  let E := LinearEquiv.ofBijective (c.ofAugCot he) (ofAugCot_bijective he c)
  have := Module.Finite.equiv E
  have := Module.Projective.of_equiv E
  exact Summand.exists_frame_of_projective c.affine_base ⟨x, hx⟩

end GlobalTheory.ConormalFrame

theorem GlobalTheory.ConormalFrame.exists_isFrame_omega : ∀ (O : Type) [CommRing O] (A : Over (Sp O))
    [GrpObj A] [Smooth A.hom] (x : Sp O), ∃ (U : (Sp O).Opens) (n : ℕ)
    (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)), x ∈ U ∧ GlobalTheory.VB.IsFrame s :=
  fun _ _ A _ _ x => GlobalTheory.ConormalFrame.exists_isFrame (GlobalTheory.LieVB.sec_hom η[A]) x
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoSeq

section General

variable {O : Type} [CommRing O] {X T T' S : Scheme.{0}} {A B A' B' : X.Modules}

def sqIso {b : S ⟶ T} {a : T ⟶ X} {c : S ⟶ T'} {a' : T' ⟶ X} (w : b ≫ a = c ≫ a') :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b ≅ Scheme.Modules.pullback a' ⋙ Scheme.Modules.pullback c :=
  Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫ (Scheme.Modules.pullbackComp c a').symm

structure Datum (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ) where

  D : X.Modules

  ρ : O →+* End D

  a : A ⟶ D

  b : D ⟶ B

  u : A' ⟶ D

  v : D ⟶ B'
  w₁ : a ≫ b = 0
  w₂ : u ≫ v = 0
  isVB : IsVB D r
  exact₁ : (ShortComplex.mk a b w₁).ShortExact
  exact₂ : (ShortComplex.mk u v w₂).ShortExact
  equiv_a : IsEquivariant α ρ a
  equiv_b : IsEquivariant ρ β b
  equiv_u : IsEquivariant α' ρ u
  equiv_v : IsEquivariant ρ β' v

variable (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ)

variable {α β α' β' r}

def biprodAct (α : O →+* End A) (β : O →+* End B) : O →+* End (A ⊞ B) where
  toFun x := End.of (biprod.map (act α x) (act β x))
  map_one' := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act]
  map_mul' x y := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act, Category.assoc]
  map_zero' := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act]
  map_add' x y := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act]

def Datum.split (α : O →+* End A) (β : O →+* End B) {m n : ℕ} (hA : IsVB A m) (hB : IsVB B n) :
    Datum α β β α (m + n) where
  D := A ⊞ B
  ρ := biprodAct α β
  a := biprod.inl
  b := biprod.snd
  u := biprod.inr
  v := biprod.fst
  w₁ := by simp
  w₂ := by simp
  isVB := hA.biprod hB
  exact₁ := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
  exact₂ := (ShortComplex.Splitting.mk (S := ShortComplex.mk (biprod.inr : B ⟶ A ⊞ B) biprod.fst (by simp))
    biprod.snd biprod.inl (by simp) (by simp) (by rw [add_comm]; exact biprod.total)).shortExact
  equiv_a x := by simp [act, biprodAct]
  equiv_b x := by simp [act, biprodAct]
  equiv_u x := by simp [act, biprodAct]
  equiv_v x := by simp [act, biprodAct]

end General

section Dieu

variable {O : Type} [CommRing O] (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}}
  [Algebra k Γ(C, ⊤)] {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Dieu

end GlobalTheory.TwoSeq
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory

namespace GlobalTheory.StalkLength

theorem length_stalk_pushforward {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i]
    (F : Y.Modules) (y : Y) :
    Module.length (X.presheaf.stalk (i y))
        (((Scheme.Modules.pushforward i).obj F).presheaf.stalk (i y) :) =
      Module.length (Y.presheaf.stalk y) (F.presheaf.stalk y :) := by
  let G := (Scheme.Modules.pushforward i).obj F
  let φ := i.stalkMap y
  letI : Algebra (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) := φ.hom.toAlgebra
  letI : Module (X.presheaf.stalk (i y)) (F.presheaf.stalk y :) :=
    Module.compHom _ (algebraMap (X.presheaf.stalk (i y)) (Y.presheaf.stalk y))
  haveI : IsScalarTower (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) (F.presheaf.stalk y :) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let Ψ : (G.presheaf.stalk (i y) :) →+ (F.presheaf.stalk y :) :=
    (F.presheaf.stalkPushforward _ i.base y).hom
  have hΨ (U : X.Opens) (hU : i y ∈ U) (s : Γ(G, U)) :
      Ψ (G.presheaf.germ U _ hU s) = F.presheaf.germ (i ⁻¹ᵁ U) y hU s :=
    congr($(TopCat.Presheaf.stalkPushforward_germ _ i.base F.presheaf U y hU).hom s)
  have hiso := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _
    (f := i.base) i.isClosedEmbedding.isInducing F.presheaf y
  have hbij : Function.Bijective Ψ :=
    ConcreteCategory.bijective_of_isIso (F.presheaf.stalkPushforward _ i.base y)
  have hsmul (a : X.presheaf.stalk (i y)) (m : (G.presheaf.stalk (i y) :)) :
      Ψ (a • m) = φ.hom a • Ψ m := by
    obtain ⟨U₁, hU₁, r, rfl⟩ := X.presheaf.germ_exist a
    obtain ⟨U₂, hU₂, s, rfl⟩ := G.presheaf.germ_exist m
    have hU : i y ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
    rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) _ hU,
      ← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) _ hU]
    generalize X.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op r = r'
    generalize G.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op s = s'
    rw [← GlobalTheory.QCoh.germ_smul G, hΨ, hΨ]
    refine (GlobalTheory.QCoh.germ_smul F (U := i ⁻¹ᵁ (U₁ ⊓ U₂)) _ _ (i.app _ r') s').trans ?_
    congr 1
    exact congr($(Scheme.Hom.germ_stalkMap i (U₁ ⊓ U₂) y hU).hom r').symm
  let e : (G.presheaf.stalk (i y) :) ≃ₗ[X.presheaf.stalk (i y)] (F.presheaf.stalk y :) :=
    { AddEquiv.ofBijective Ψ hbij with map_smul' := hsmul }
  exact e.length_eq.trans (Module.length_eq_of_surjective (i.stalkMap_surjective y))

theorem length_stalk_pushforward_genericPoint : ∀ (X : Scheme.{0}) (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [GlobalTheory.QCoh.IsFiniteQC G],
    Module.length (X.presheaf.stalk (redι Z (genericPoint _)))
      (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) =
      (GlobalTheory.VB.genRank G : ℕ∞) := by
  intro X Z _ G _
  rw [length_stalk_pushforward]
  exact Module.length_eq_finrank (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.functionField
    (GlobalTheory.VB.genStalk G)

end GlobalTheory.StalkLength
end

section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.Adelic.LinSys

theorem finrank_quotient_piece_le_sections (k : Type) [Field k] (S : LinSys k) (hS : S.IsVariety)
    (m : ℕ) : Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) ≤ lbH0 k (lbPow S.L m) := by
  classical
  let : Module k (lbPow S.L m).Sec := Module.compHom (lbPow S.L m).Sec (algebraMap k Γ(S.Y, ⊤))
  have : IsScalarTower k Γ(S.Y, ⊤) (lbPow S.L m).Sec :=
    ⟨fun a b s => by
      show (a • b) • s = algebraMap k Γ(S.Y, ⊤) a • (b • s)
      rw [Algebra.smul_def, mul_smul]⟩
  have hfin : Module.Finite k (coh (twist (structureModule S.Y) (lbPow S.L m)) 0) :=
    finite_coh_zero_twist_of_isProjOver (f := S.str) (fun _ => rfl) hS.proj (isLB_lbPow S.isLB m)
  have : Module.Finite k (lbPow S.L m).Sec :=
    Module.Finite.equiv ((cohZeroTwistEquiv (lbPow S.L m)).restrictScalars k)
  rw [lineBundleGlobalSectionsDim_eq_finrank]
  let V := homogeneousSubmodule (Fin S.N) k m

  let φ : V →ₗ[k] (lbPow S.L m).Sec :=
    { toFun := fun g => S.form g.2
      map_add' := fun g h => (ProjCoh.formSecAdd k S.b (m : ℤ)).map_add
        ⟨g.1, mem_polyGrading_natCast.2 g.2⟩ ⟨h.1, mem_polyGrading_natCast.2 h.2⟩
      map_smul' := fun c g => ProjCoh.formSec_smul k S.b c (mem_polyGrading_natCast.2 g.2) _ }

  let f : V →ₗ[k] MvPolynomial (Fin S.N) k ⧸ S.imageIdeal :=
    (Ideal.Quotient.mkₐ k S.imageIdeal).toLinearMap ∘ₗ V.subtype
  have hker : LinearMap.ker f = LinearMap.ker φ := by
    ext g
    simp only [LinearMap.mem_ker]
    change Ideal.Quotient.mk S.imageIdeal g.1 = 0 ↔ S.form g.2 = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact S.mem_imageIdeal_iff g.2
  have hrange : quotPiece S.imageIdeal (m : ℤ) = LinearMap.range f := by
    rw [quotPiece_natCast, LinearMap.range_comp, Submodule.range_subtype]
  rw [hrange, ← f.quotKerEquivRange.finrank_eq, (Submodule.quotEquivOfEq _ _ hker).finrank_eq,
    φ.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_le _

end GlobalTheory.Adelic.LinSys
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB → ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  first | exact @GlobalTheory.BigFieldChange.isBig_pull_iff | exact GlobalTheory.BigFieldChange.isBig_pull_iff | (intros; apply GlobalTheory.BigFieldChange.isBig_pull_iff <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smoothAlgebra_lifts_over_square_zero_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  first | exact @GlobalTheory.smooth_lifts_over_sqZero | exact GlobalTheory.smooth_lifts_over_sqZero | (intros; apply GlobalTheory.smooth_lifts_over_sqZero <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.eqv_cechAug_of_isIntegralHom_of_surjective_of_sh : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)), IsIntegralHom g → Surjective g → Eqv _ (cechAug g) (tw q i) := by
  first
  | exact @GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian
  | exact GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian
  | (intros; apply GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.class_vanishes_away_nonZeroDivisor : ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ (n i : ℤ) (z : Ht q (sp R) n i), pull _ (spMap (algebraMap R (FractionRing R))) _ _ z = 0 → ∃ g ∈ nonZeroDivisors R, pull _ (spMap (algebraMap R (Localization.Away g))) _ _ z = 0 := by
  first | (exact @GlobalTheory.EtC.classVanishesAwayNZD) | (exact GlobalTheory.EtC.classVanishesAwayNZD) | (intros; apply GlobalTheory.EtC.classVanishesAwayNZD  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = 0 → ∃ v, u = v ^ q := by
  first | (exact @GlobalTheory.EtC.eq_pow_of_kum_eq_zero) | (exact GlobalTheory.EtC.eq_pow_of_kum_eq_zero) | (intros; apply GlobalTheory.EtC.eq_pow_of_kum_eq_zero  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

theorem _root_.GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain : ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B], ¬ IsField B → IsUnit (q : B) → ∀ (n i : ℤ) (x : Ht q (sp B) n i), pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 → ∃ f : B, f ≠ 0 ∧ ¬ IsUnit f ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.classVanishesAway) | (exact GlobalTheory.EtC.classVanishesAway) | (intros; apply GlobalTheory.EtC.classVanishesAway  <;> assumption)
end
