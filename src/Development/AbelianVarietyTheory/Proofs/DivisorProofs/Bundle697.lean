module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle358
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle664
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle001
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.PurityStep

theorem finite_quot (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R) : Module.Finite (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
  Module.Finite.of_restrictScalars_finite R _ _

theorem lowDim (R : Type) [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 2) :
    PurityFree R := by
  intro A _ _ _ hA _
  refine GlobalTheory.AnnRegSeq.free_of_modDepthGE 2 R A hA ?_
  have h1 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    rw [h1]; exact_mod_cast h
  exact_mod_cast this

theorem hyperplane (R : Type) [CommRing R] [IsRegularLocalRing R]
    (hc : IsAdicComplete (maximalIdeal R) R) (hd : 3 ≤ ringKrullDim R) (f : R)
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span {f})]
    (hP : PurityFree (R ⧸ Ideal.span {f})) : PurityFree R := by
  intro A _ _ _ hA het
  have h3 := GlobalTheory.T.depth_ge_three_finite_etale_punctured_regular R hc hd f hf hf2 hP A hA het
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf2 (zero_mem _)
  have hreg := GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hA) het f hf0
  haveI := finite_quot R A f
  exact GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local R A f hf hreg (hP _ (GlobalTheory.T.modDepthGE_quotient_span_of_isSMulRegular R A f hf hreg 2 h3) (GlobalTheory.T.etale_quotient_of_etale_punctured' R A f het))

theorem purityFree_of_ringKrullDim (n : ℕ) : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S],
    ringKrullDim S = n → PurityFree S := by
  induction n with
  | zero =>
    intro S _ _ hS
    exact lowDim S (by rw [hS]; norm_num)
  | succ n ih =>
    intro S _ _ hS
    by_cases h2 : n + 1 ≤ 2
    · exact lowDim S (by rw [hS]; exact_mod_cast h2)
    refine GlobalTheory.T.purityFree_of_complete_regularLocal S fun S' _ _ hc hd' => ?_
    rw [hS] at hd'
    have hsq : ¬ maximalIdeal S' ≤ maximalIdeal S' ^ 2 := by
      intro h
      have h0 := GlobalTheory.AnnRegSeq.maximalIdeal_eq_bot_of_le_sq h
      have := ringKrullDim_eq_zero_of_isField ((IsLocalRing.isField_iff_maximalIdeal_eq (R := S')).mpr h0)
      rw [this] at hd'
      exact absurd hd' (by norm_cast)
    obtain ⟨f, hf, hf2⟩ := Set.not_subset.mp hsq
    haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hf
    haveI hQ := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2
    have hdim := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2
    have hsp : ((maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (S' ⧸ Ideal.span {f}) := IsRegularLocalRing.spanFinrank_maximalIdeal
    rw [← hsp, hd'] at hdim
    have hk : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank = n := by
      have : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank + 1 = n + 1 := by
        exact_mod_cast hdim
      omega
    refine hyperplane S' hc ?_ f hf hf2 (ih _ ?_)
    · rw [hd']; exact_mod_cast (by omega : 3 ≤ n + 1)
    · rw [← hsp, hk]

theorem free_of_etale_punctured : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 3 ≤ ringKrullDim R → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Module.Free R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hreg hd het
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hreg
  refine purityFree_of_ringKrullDim _ R hreg.symm A (GlobalTheory.T.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing' R A (le_trans (by norm_num) hd)) het

end GlobalTheory.PurityStep
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

theorem coindQ_map_res {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map f (Sec.res g x) = Sec.res g (Sec.map f x) := by
  have := congrArg (fun h => h.hom x) (f.hom.naturality g.op)
  simpa using this

theorem coindQ_res_res (F : Shv R) {W V U : Scheme.{0}} (g : W ⟶ V) (x : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.res x s) = Sec.res (g ≫ x) s := by
  simp [Sec.res]

def coindQ_gen (J : Shv R) (U : Scheme.{0}) : ((free R).obj (yoneda.obj U) ⟶ J) →ₗ[ULift.{1} R] Sec J U where
  toFun ψ := Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

theorem coindQ_gen_bijective (J : Shv R) (U : Scheme.{0}) : Function.Bijective (coindQ_gen J U) := by
  obtain ⟨hex, huniq, hres, -⟩ := GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj U) J
  have key : ∀ (V : Scheme.{0}) (x : V ⟶ U),
      freeGen R (yoneda.obj U) V x = Sec.res x (freeGen R (yoneda.obj U) U (𝟙 U)) := by
    intro V x
    rw [hres V U x (𝟙 U)]
    simp
  constructor
  · intro ψ ψ' h
    apply huniq
    intro V x
    rw [key V x, coindQ_map_res, coindQ_map_res]
    exact congrArg (Sec.res x) h
  · intro s
    obtain ⟨ψ, hψ⟩ := hex (fun V x => Sec.res x s) (fun W V g x => by
      rw [coindQ_res_res]; rfl)
    refine ⟨ψ, ?_⟩
    show Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U)) = s
    rw [hψ U (𝟙 U)]
    simp [Sec.res]

theorem coindQ_injSec (J : Shv R) (hJ : ∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J))
    (U : Scheme.{0}) : Injective (J.obj.obj (op U)) := by
  have := hJ (yoneda.obj U)
  have hI : Injective (ModuleCat.of (ULift.{1} R) ((free R).obj (yoneda.obj U) ⟶ J)) :=
    Module.injective_object_of_injective_module _ _
  exact Injective.of_iso (LinearEquiv.ofBijective (coindQ_gen J U) (coindQ_gen_bijective J U)).toModuleIso hI

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

theorem coindQ_exactAt_succ {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R)
    (hJ : ∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) (n : ℕ) :
    (coindCx φ J).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro U b hb
  have := coindQ_injSec J hJ U
  let b' : (scalarsRes φ).complex.X (n + 1) ⟶ J.obj.obj (op U) := b
  have hb' : (scalarsRes φ).complex.d (n + 2) (n + 1) ≫ b' = 0 := by
    have h2 : (coindCx φ J).d (n + 1) (n + 2) = (homSh J).map ((scalarsRes φ).complex.d (n + 2) (n + 1)).op :=
      coindCx_d φ J (n + 1)
    have hb2 : Sec.map ((coindCx φ J).d (n + 1) (n + 2)) b = 0 := hb
    rw [h2] at hb2
    exact hb2
  let a' := ((scalarsRes φ).exact_succ n).descToInjective b' hb'
  have ha' : (scalarsRes φ).complex.d (n + 1) n ≫ a' = b' :=
    ((scalarsRes φ).exact_succ n).comp_descToInjective b' hb'
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ?_⟩
  have h1 : (coindCx φ J).d n (n + 1) = (homSh J).map ((scalarsRes φ).complex.d (n + 1) n).op :=
    coindCx_d φ J n
  have key : Sec.map ((coindCx φ J).d n (n + 1)) (a' : Sec ((coindCx φ J).X n) U) = b := by
    rw [h1]; exact ha'
  exact ⟨Sec.res g (a' : Sec ((coindCx φ J).X n) U),
    (coindQ_map_res ((coindCx φ J).d n (n + 1)) g _).trans (congrArg (Sec.res g) key)⟩

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

abbrev coindQ_p {S : Type} [CommRing S] (φ : R →+* S) :
    (scalarsRes φ).complex.X 0 ⟶ scalarsMod φ :=
  (scalarsRes φ).π.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).hom

instance {S : Type} [CommRing S] (φ : R →+* S) : Epi (coindQ_p φ) := by
  exact epi_comp _ _

theorem coindQ_d_p {S : Type} [CommRing S] (φ : R →+* S) :
    (scalarsRes φ).complex.d 1 0 ≫ coindQ_p φ = 0 := by
  show _ ≫ (_ ≫ _) = 0
  rw [ProjectiveResolution.complex_d_comp_π_f_zero_assoc, zero_comp]

def coindQ_sc {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) : ShortComplex (Shv R) :=
  ShortComplex.mk (coindToHom φ J ≫ (homSh J).map (coindQ_p φ).op)
    ((homSh J).map ((scalarsRes φ).complex.d 1 0).op) (by
      rw [Category.assoc, ← Functor.map_comp, ← op_comp, coindQ_d_p, op_zero, Functor.map_zero, comp_zero])

theorem coindQ_sc_f_sec {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) (U : Scheme.{0})
    (a : Sec ((restr φ).obj ((coind φ).obj J)) U) :
    Sec.map (coindQ_sc φ J).f a =
      (coindQ_p φ ≫ homOfLin (ModuleCat.CoextendScalars.equiv (liftHom φ) _ a) : _ ⟶ J.obj.obj (op U)) := rfl

theorem coindQ_sc_inj {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) (U : Scheme.{0}) :
    Function.Injective (Sec.map (coindQ_sc φ J).f (U := U)) := by
  intro a a' h
  have h' := (coindQ_sc_f_sec φ J U a).symm.trans (h.trans (coindQ_sc_f_sec φ J U a'))
  have h3 := (cancel_epi (coindQ_p φ)).1 h'
  apply ModuleCat.CoextendScalars.ext
  exact congrArg ModuleCat.Hom.hom h3

theorem coindQ_sc_mono {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) : Mono (coindQ_sc φ J).f := by
  suffices h : Mono (coindQ_sc φ J).f.hom from Sheaf.Hom.mono_of_presheaf_mono _ _ _
  have hU : ∀ U, Mono ((coindQ_sc φ J).f.hom.app U) := by
    intro U
    rw [ModuleCat.mono_iff_injective]
    exact coindQ_sc_inj φ J U.unop
  exact NatTrans.mono_of_mono_app _

theorem coindQ_sc_exact {S : Type} [CommRing S] (φ : R →+* S) (J : Shv R) : (coindQ_sc φ J).Exact := by
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro U b hb
  let b' : (scalarsRes φ).complex.X 0 ⟶ J.obj.obj (op U) := b
  have hb' : (scalarsRes φ).complex.d 1 0 ≫ b' = 0 := hb
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' (scalarsRes φ).isColimitCokernelCofork b' hb'
  let c : scalarsMod φ ⟶ J.obj.obj (op U) :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (scalarsMod φ)).inv ≫ l
  have hc : coindQ_p φ ≫ c = b' := by
    simp only [c, coindQ_p, Category.assoc, Iso.hom_inv_id_assoc]
    exact hl
  let a : Sec ((restr φ).obj ((coind φ).obj J)) U := (ModuleCat.CoextendScalars.equiv (liftHom φ) _).symm c.hom
  have key : Sec.map (coindQ_sc φ J).f a = b := by
    rw [coindQ_sc_f_sec]
    exact hc
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g a, ?_⟩⟩
  exact (coindQ_map_res _ g _).trans (congrArg (Sec.res g) key)

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

theorem coindAug_quasiIso : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R),
    (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → QuasiIso (coindAug φ J) := by
  intro R S _ _ φ J hJ
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨coindQ_sc_exact φ J, coindQ_sc_mono φ J⟩
      refine ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · simp only [Iso.refl_hom, Category.comp_id]
        exact (coindAug_f_zero φ J).symm
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        exact (coindCx_d φ J 0).symm
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
    exact coindQ_exactAt_succ φ J hJ n

end GlobalTheory.EtC
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

theorem secMap_res' {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.hom.naturality g.op)) x).symm

theorem secMap_nsmul' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map f (c • x) = c • Sec.map f x :=
  map_nsmul (f.hom.app (op U)).hom c x

theorem secMap_zero' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} :
    Sec.map f (0 : Sec F U) = 0 :=
  map_zero (f.hom.app (op U)).hom

theorem extSh_hom_ext (φ : R →+* S) {F : Shv R} {M : Shv S} (a b : (extSh φ).obj F ⟶ M)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map a (extSh.sec φ F U y) = Sec.map b (extSh.sec φ F U y)) : a = b := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))
    a.hom b.hom M.property ?_
  ext U : 2
  apply ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext y
  exact h (unop U) y

end

theorem extAug_comp_ext : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ) (K : Cx (ZMod q))
    (u u' : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K),
    (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
      Sec.map (u.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ)) =
        Sec.map (u'.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ))) →
    extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u = extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u' := by
  intro Q q _ hq i K u u' h
  have e : ∀ (v : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K) (V : Scheme.{0}) (z : Sec (tw Q i) V),
      Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ v.f 0)
          (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) V z) =
        Sec.map (v.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app V 0 (Sec.map (resι _ (tw Q i)) z)) := by
    intro v V z
    change Sec.map (v.f 0) (Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i))) _) = _
    rw [extSh.sec_map]
    rfl
  have key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ u.f 0 =
      (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ u'.f 0 := by
    apply extSh_hom_ext
    intro U y
    apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ (K.X 0) U).1
    obtain ⟨S, hS, hy⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated Q i).1 U y
    refine ⟨S, hS, fun V g hg => ?_⟩
    dsimp only
    rw [secMap_res', secMap_res', extSh.sec_res, e, e]
    rcases hy V g hg with h0 | ⟨ζ, c, hc⟩
    · rw [h0, secMap_zero', map_zero, secMap_zero', secMap_zero']
    · rw [hc, secMap_nsmul', map_nsmul, secMap_nsmul', secMap_nsmul']
      exact congrArg (c • ·) (h V ζ)
  have hv : ∀ v : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K, (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ v).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ v.f 0 := by
    intro v
    have hs := HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0 (tw Q i)
    change (((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫
        v.f 0 = _
    have hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
        (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
          (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) := by
      rw [hs]
      exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)
    exact (congrArg (· ≫ v.f 0) hs').trans (Category.assoc _ _ _)
  apply HomologicalComplex.from_single_hom_ext
  rw [hv, hv, key]

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.FlatExtAcyc

variable {R : Type} [CommRing R]

lemma sres_comp {F : Shv R} {U V W : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (s : Sec F U) :
    Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

lemma sres_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := a.hom.naturality g.op
  exact congrArg (fun t => t.hom x) this.symm

lemma sres_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  (F.obj.map g.op).hom.map_zero

lemma nsmul_self_eq_zero (q : ℕ) {F : Shv (ZMod q)} {U : Scheme.{0}} (z : Sec F U) : q • z = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

end GlobalTheory.EtC.FlatExtAcyc


open GlobalTheory.EtC.FlatExtAcyc in
theorem GlobalTheory.EtC.flatExtAcyc.main : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (K : Cx (ZMod Q)) (a : ℤ) [K.IsStrictlyGE a], (∀ n, FlatS (K.X n)) → K.Acyclic → (extCx (ZMod.castHom hq (ZMod q)) K).Acyclic := by
  intro Q q _ hq K a _ hflat hK
  have hqe : q * (Q / q) = Q := Nat.mul_div_cancel' hq
  have hKloc : ∀ (n : ℤ) (U : Scheme.{0}) (b : Sec (K.X n) U), Sec.map (K.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) c = Sec.res g b := by
    intro n U b hb
    have hex : (K.sc' (n - 1) n (n + 1)).Exact := (K.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).1 (hK n)
    exact ((GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally _ _).1 hex) U b hb
  have hz : ∀ n, n < a → ∀ (U : Scheme.{0}) (x : Sec (K.X n) U), x = 0 := by
    intro n hn U x
    have hZ : IsZero (K.X n) := K.isZero_of_isStrictlyGE a n hn
    have e1 : 𝟙 (K.X n) = 0 := hZ.eq_of_src _ _
    have h1 : Sec.map (𝟙 (K.X n)) x = x := rfl
    rw [← h1, e1]; rfl
  have hQ : ∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (q * (Q / q)) • y = 0 := by
    intro n U y
    rw [hqe, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod Q))]
    have : ((Q : ℕ) : ULift.{1} (ZMod Q)) = 0 := by ext; simp
    rw [this, zero_smul]
  have hst := GlobalTheory.T.etaleComplex_staircase_locally_exact (ZMod Q) q (Q / q) K a hz hQ
    (fun n U x hx => GlobalTheory.T.locallyFlatEtaleSheaf_locally_divisible Q q (Q / q) hqe (K.X n) (hflat n) U x hx)
    (fun n U x hx => GlobalTheory.T.locallyFlatEtaleSheaf_locally_divisible Q (Q / q) q (by rw [mul_comm]; exact hqe) (K.X n) (hflat n) U x hx) hKloc
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp), GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]

  suffices H : ∀ (U : Scheme.{0}) (z : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj (K.X n)) U),
      Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (K.d n (n + 1))) z = 0 →
      Loc U fun V g => ∃ b : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj (K.X (n - 1))) V,
        Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (K.d (n - 1) n)) b = Sec.res g z from H
  intro U z hzz
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.1 U _ ?_
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (GlobalTheory.T.etaleSheafExtendScalars_zmod_section_locally_tmul Q q hq (K.X n) U z) ?_
  rintro V g ⟨x, hx⟩
  have hdx : extSh.sec (ZMod.castHom hq (ZMod q)) (K.X (n + 1)) V (Sec.map (K.d n (n + 1)) x) = 0 := by
    rw [← extSh.sec_map, hx, ← sres_map, hzz, sres_zero]
  have hloc := GlobalTheory.T.etaleSheafExtendScalars_zmod_kernel_locally_multiple Q q hq (K.X (n + 1)) V _ hdx
  have hloc' : Loc V fun W k => ∃ y : Sec (K.X (n + 1)) W, Sec.map (K.d n (n + 1)) (Sec.res k x) = q • y := by
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _ hloc ?_
    rintro W k ⟨y, hy⟩
    exact ⟨y, by rw [← sres_map, hy]⟩
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _ (hst n V x hloc') ?_
  rintro W k ⟨u, y, hy⟩
  refine ⟨extSh.sec (ZMod.castHom hq (ZMod q)) (K.X (n - 1)) W u, ?_⟩
  rw [extSh.sec_map, ← sres_comp, ← hx, extSh.sec_res, hy, map_add (f := _), map_nsmul, nsmul_self_eq_zero, add_zero]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

theorem _root_.GlobalTheory.T.line_bundle_sections_product_base_change : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M t A' B' φA' φB' Φ' → ∃ c, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  first | (exact @GlobalTheory.HomFixMat.exists_isMat) | (exact GlobalTheory.HomFixMat.exists_isMat) | (intros; apply GlobalTheory.HomFixMat.exists_isMat <;> assumption)
end
