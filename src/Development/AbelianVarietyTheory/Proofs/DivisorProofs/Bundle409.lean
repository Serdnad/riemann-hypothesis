module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

universe u

namespace GlobalTheory.LocalizedFinsetForAll

theorem loc_forall_finset {U : Scheme.{0}} {ι : Type u} (s : Finset ι)
    {P : ι → (V : Scheme.{0}) → (V ⟶ U) → Prop} (h : ∀ i ∈ s, GlobalTheory.EtC.Loc U (P i)) :
    GlobalTheory.EtC.Loc U fun (V : Scheme.{0}) (g : V ⟶ U) ↦ ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s _ ih =>
    obtain ⟨S, hS, hSP⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨T, hT, hTP⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨S ⊓ T, GrothendieckTopology.intersection_covering _ hS hT, fun V g hg i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hSP V g hg.1
    · exact hTP V g hg.2 i hi

end GlobalTheory.LocalizedFinsetForAll
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

def biprodPresheaf (P₁ P₂ : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (P₁.obj U × P₂.obj U)
  map f := ModuleCat.ofHom ((P₁.map f).hom.prodMap (P₂.map f).hom)
  map_id U := by ext x <;> simp
  map_comp f g := by ext x <;> simp

theorem secBiprod_total (M N : Shv R) (U : Scheme.{0}) (y : Sec (M ⊞ N) U) :
    y = Sec.map (biprod.inl : M ⟶ M ⊞ N) (Sec.map biprod.fst y) + Sec.map (biprod.inr : N ⟶ M ⊞ N) (Sec.map biprod.snd y) := by
  conv_lhs => rw [show y = (((𝟙 (M ⊞ N)) : M ⊞ N ⟶ M ⊞ N).hom.app (op U)).hom y from rfl, ← biprod.total]
  rfl

theorem secBiprod_inl_fst (M N : Shv R) {U : Scheme.{0}} (a : Sec M U) :
    Sec.map (biprod.fst : M ⊞ N ⟶ M) (Sec.map (biprod.inl : M ⟶ M ⊞ N) a) = a := by
  change ((biprod.inl ≫ biprod.fst : M ⟶ M).hom.app (op U)).hom a = a
  rw [biprod.inl_fst]; rfl

theorem secBiprod_inr_fst (M N : Shv R) {U : Scheme.{0}} (b : Sec N U) :
    Sec.map (biprod.fst : M ⊞ N ⟶ M) (Sec.map (biprod.inr : N ⟶ M ⊞ N) b) = 0 := by
  change ((biprod.inr ≫ biprod.fst : N ⟶ M).hom.app (op U)).hom b = 0
  rw [biprod.inr_fst]; rfl

theorem secBiprod_inl_snd (M N : Shv R) {U : Scheme.{0}} (a : Sec M U) :
    Sec.map (biprod.snd : M ⊞ N ⟶ N) (Sec.map (biprod.inl : M ⟶ M ⊞ N) a) = 0 := by
  change ((biprod.inl ≫ biprod.snd : M ⟶ N).hom.app (op U)).hom a = 0
  rw [biprod.inl_snd]; rfl

theorem secBiprod_inr_snd (M N : Shv R) {U : Scheme.{0}} (b : Sec N U) :
    Sec.map (biprod.snd : M ⊞ N ⟶ N) (Sec.map (biprod.inr : N ⟶ M ⊞ N) b) = b := by
  change ((biprod.inr ≫ biprod.snd : N ⟶ N).hom.app (op U)).hom b = b
  rw [biprod.inr_snd]; rfl

noncomputable section

def biprodPresheafMap {M N : Shv R} {P₁ P₂ : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ₁ : P₁ ⟶ M.obj) (φ₂ : P₂ ⟶ N.obj) :
    biprodPresheaf P₁ P₂ ⟶ (M ⊞ N).obj where
  app U := ModuleCat.ofHom (LinearMap.coprod (((biprod.inl : M ⟶ M ⊞ N).hom.app U).hom ∘ₗ (φ₁.app U).hom)
    (((biprod.inr : N ⟶ M ⊞ N).hom.app U).hom ∘ₗ (φ₂.app U).hom))
  naturality U V f := by
    ext ⟨a, b⟩
    have h1 := congrArg (fun g => ModuleCat.Hom.hom g a) (φ₁.naturality f)
    have h2 := congrArg (fun g => ModuleCat.Hom.hom g b) (φ₂.naturality f)
    have h3 := congrArg (fun g => ModuleCat.Hom.hom g ((φ₁.app U).hom a)) ((biprod.inl : M ⟶ M ⊞ N).hom.naturality f)
    have h4 := congrArg (fun g => ModuleCat.Hom.hom g ((φ₂.app U).hom b)) ((biprod.inr : N ⟶ M ⊞ N).hom.naturality f)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1 h2 h3 h4
    change (((biprod.inl : M ⟶ M ⊞ N).hom).app V).hom ((φ₁.app V).hom ((P₁.map f).hom a)) +
        (((biprod.inr : N ⟶ M ⊞ N).hom).app V).hom ((φ₂.app V).hom ((P₂.map f).hom b)) =
      ((M ⊞ N).obj.map f).hom ((((biprod.inl : M ⟶ M ⊞ N).hom).app U).hom ((φ₁.app U).hom a) +
        (((biprod.inr : N ⟶ M ⊞ N).hom).app U).hom ((φ₂.app U).hom b))
    rw [map_add (f := _), h1, h2, h3, h4]

theorem secRes_secMap {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := congrArg (fun h => ModuleCat.Hom.hom h a) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  exact h.symm

theorem flatS_biprod : ∀ (R : Type) [CommRing R] (M N : Shv R), FlatS M → FlatS N → FlatS (M ⊞ N) := by
  intro R _ M N ⟨P₁, φ₁, s₁, i₁, f₁⟩ ⟨P₂, φ₂, s₂, i₂, f₂⟩
  refine ⟨biprodPresheaf P₁ P₂, biprodPresheafMap φ₁ φ₂, ?_, ?_, ?_⟩
  · intro U y
    obtain ⟨S, hS, hS'⟩ := s₁ U (Sec.map biprod.fst y)
    obtain ⟨T, hT, hT'⟩ := s₂ U (Sec.map biprod.snd y)
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    obtain ⟨x₁, hx₁⟩ := hS' V g hg.1
    obtain ⟨x₂, hx₂⟩ := hT' V g hg.2
    refine ⟨(x₁, x₂), ?_⟩
    change Sec.map (biprod.inl : M ⟶ M ⊞ N) ((φ₁.app (op V)).hom x₁) +
      Sec.map (biprod.inr : N ⟶ M ⊞ N) ((φ₂.app (op V)).hom x₂) = Sec.res g y
    rw [hx₁, hx₂, ← secRes_secMap, ← secRes_secMap, ← map_add (f := _)]
    exact congrArg (Sec.res g) (secBiprod_total M N U y).symm
  · rintro U ⟨a, b⟩ hx
    change Sec.map (biprod.inl : M ⟶ M ⊞ N) ((φ₁.app (op U)).hom a) +
      Sec.map (biprod.inr : N ⟶ M ⊞ N) ((φ₂.app (op U)).hom b) = 0 at hx
    have ha : (φ₁.app (op U)).hom a = 0 := by
      have e : ∀ x y : Sec (M ⊞ N) U, Sec.map (biprod.fst : M ⊞ N ⟶ M) (x + y) =
          Sec.map biprod.fst x + Sec.map biprod.fst y := fun x y => map_add _ x y
      have z : Sec.map (biprod.fst : M ⊞ N ⟶ M) (0 : Sec (M ⊞ N) U) = 0 := map_zero _
      have h := congrArg (Sec.map (biprod.fst : M ⊞ N ⟶ M)) hx
      rwa [e, secBiprod_inl_fst, secBiprod_inr_fst, add_zero, z] at h
    have hb : (φ₂.app (op U)).hom b = 0 := by
      have e : ∀ x y : Sec (M ⊞ N) U, Sec.map (biprod.snd : M ⊞ N ⟶ N) (x + y) =
          Sec.map biprod.snd x + Sec.map biprod.snd y := fun x y => map_add _ x y
      have z : Sec.map (biprod.snd : M ⊞ N ⟶ N) (0 : Sec (M ⊞ N) U) = 0 := map_zero _
      have h := congrArg (Sec.map (biprod.snd : M ⊞ N ⟶ N)) hx
      rwa [e, secBiprod_inl_snd, secBiprod_inr_snd, zero_add, z] at h
    obtain ⟨S, hS, hS'⟩ := i₁ U a ha
    obtain ⟨T, hT, hT'⟩ := i₂ U b hb
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    change ((P₁.map g.op).hom a, (P₂.map g.op).hom b) = 0
    rw [hS' V g hg.1, hT' V g hg.2]
    rfl
  · intro U hU
    haveI := f₁ U hU
    haveI := f₂ U hU
    exact GlobalTheory.flat_prod (R := ULift.{1} R) (A := P₁.obj (op U)) (B := P₂.obj (op U))

end

end GlobalTheory.EtC
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

instance restr_additive (φ : R →+* S) : (restr φ).Additive where
  map_add {F G} {f g} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

abbrev rcx (φ : R →+* S) : Cx S ⥤ Cx R := (restr φ).mapHomologicalComplex _

def rAug (φ : R →+* S) {F : Shv S} {C : Cx S} (ε : sgl F ⟶ C) : sgl ((restr φ).obj F) ⟶ (rcx φ).obj C :=
  (HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F ≫ (rcx φ).map ε

def idSemi (φ : R →+* S) (K : Cx S) : SemiMap K ((rcx φ).obj K) where
  app _ _ := { toFun := fun a => a, map_zero' := rfl, map_add' := fun _ _ => rfl }
  nat _ _ _ := rfl
  comm _ _ _ _ := rfl

end

section
variable {S R : Type} [CommRing S] [CommRing R]

def SemiMap.sub {I : Cx S} {J : Cx R} (ρ ρ' : SemiMap I J) : SemiMap I J where
  app U s := ρ.app U s - ρ'.app U s
  nat g s a := by simp [map_sub, ρ.nat, ρ'.nat]
  comm U s t a := by simp [map_sub, ρ.comm, ρ'.comm]

end

section
variable {S R : Type} [CommRing S] [CommRing R]

theorem ulift_intCast_smul {T : Type} [CommRing T] (M : ModuleCat.{1} (ULift.{1} T)) (x : M) (k : ℤ) :
    (ULift.up (k : T) : ULift.{1} T) • x = k • x := by
  rw [show (ULift.up (k : T) : ULift.{1} T) = ((k : ULift.{1} T)) from rfl]
  exact Int.cast_smul_eq_zsmul _ k x

def SemiMap.toZl {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (s : ℤ) (U : Scheme.{0}ᵒᵖ) :
    ((restr (Int.castRingHom S)).obj (I.X s)).obj.obj U ⟶ ((restr (Int.castRingHom R)).obj (J.X s)).obj.obj U :=
  ModuleCat.ofHom (X := ((restr (Int.castRingHom S)).obj (I.X s)).obj.obj U)
      (Y := ((restr (Int.castRingHom R)).obj (J.X s)).obj.obj U)
    { toFun := ρ.app U.unop s
      map_add' := map_add _
      map_smul' := fun r a => by
        have h1 : ∀ b : Sec (I.X s) U.unop, (ULift.up ((r.down : ℤ) : S) : ULift.{1} S) • b = r.down • b :=
          fun b => ulift_intCast_smul _ b _
        have h2 : ∀ b : Sec (J.X s) U.unop, (ULift.up ((r.down : ℤ) : R) : ULift.{1} R) • b = r.down • b :=
          fun b => ulift_intCast_smul _ b _
        exact (congrArg (ρ.app U.unop s) (h1 a)).trans ((map_zsmul _ _ _).trans (h2 _).symm) }

def SemiMap.toZs {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (s : ℤ) :
    (restr (Int.castRingHom S)).obj (I.X s) ⟶ (restr (Int.castRingHom R)).obj (J.X s) :=
  ⟨{ app := ρ.toZl s
     naturality := fun U V g => by
       ext a
       change ρ.app V.unop s (Sec.res g.unop a) = Sec.res g.unop (ρ.app U.unop s a)
       exact (ρ.nat g.unop s a).symm }⟩

def SemiMap.toZ {I : Cx S} {J : Cx R} (ρ : SemiMap I J) :
    (rcx (Int.castRingHom S)).obj I ⟶ (rcx (Int.castRingHom R)).obj J where
  f s := ρ.toZs s
  comm' s t _ := by
    apply Sheaf.hom_ext
    ext U a
    change Sec.map (J.d s t) (ρ.app U.unop s a) = ρ.app U.unop t (Sec.map (I.d s t) a)
    exact ρ.comm U.unop s t a

end

section
variable {R S : Type} [CommRing R] [CommRing S]

theorem restr_eq (φ : R →+* S) : restr φ = sheafCompose _ (ModuleCat.restrictScalars.{1} (liftHom φ)) := rfl

theorem restr_exact (φ : R →+* S) : PreservesFiniteLimits (restr φ) ∧ PreservesFiniteColimits (restr φ) := by
  rw [restr_eq]
  have adj₁ := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (liftHom φ))
  have adj₂ := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (liftHom φ))
  have := adj₁.isRightAdjoint
  have := adj₂.isLeftAdjoint
  let j : sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} (liftHom φ)) ≅
      Sheaf.composeAndSheafify Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} (liftHom φ)) :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ (sheafificationNatIso _ _)
  exact ⟨inferInstance, preservesFiniteColimits_of_natIso j.symm⟩

instance restr_preservesHomology (φ : R →+* S) : (restr φ).PreservesHomology := by
  obtain ⟨_, _⟩ := restr_exact φ
  infer_instance

theorem rAug_quasiIso (φ : R →+* S) {F : Shv S} {C : Cx S} (ε : sgl F ⟶ C) [QuasiIso ε] : QuasiIso (rAug φ ε) := by
  unfold rAug
  have h1 : QuasiIso ((rcx φ).map ε) := HomologicalComplex.quasiIso_map_of_preservesHomology ε (restr φ)
  have h2 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F) :=
    quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h2) (hφ' := h1) _ _

end

section
variable {R S : Type} [CommRing R] [CommRing S]

theorem rAug_f_zero (φ : R →+* S) {F : Shv S} {C : Cx S} (ε : sgl F ⟶ C) (U : Scheme.{0}) (a : Sec F U) :
    Sec.map ((rAug φ ε).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) =
      (show Sec ((restr φ).obj (C.X 0)) U from Sec.map (ε.f 0) (Sec.map (sglι F) a)) := by
  have h : sglι ((restr φ).obj F) ≫ (rAug φ ε).f 0 = (restr φ).map (sglι F ≫ ε.f 0) := by
    set_option backward.isDefEq.respectTransparency false in
    simp [rAug, sglι]
  have := congrArg (fun m => Sec.map m (show Sec ((restr φ).obj F) U from a)) h
  exact this

end

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.NullHtpyStair

variable {R : Type} [CommRing R]

theorem lift_of_subsingleton {A : Shv R} {M : Cx R} {m' m : ℤ} (hm : m' + 1 = m)
    (hA : Subsingleton (CohomologyClass (sgl A) M m)) (f : A ⟶ M.X m) (hf : f ≫ M.d m (m + 1) = 0) :
    ∃ g : A ⟶ M.X m', g ≫ M.d m' m = f := by
  have h0 : CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add m) (m + 1) rfl hf) = 0 := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m' hm] at h0
  obtain ⟨β, hβ⟩ := h0
  refine ⟨sglι A ≫ β.v 0 m' (by omega), ?_⟩
  have := congrArg (fun c => c.v 0 m (zero_add m)) hβ
  beta_reduce at this
  rw [δ_v m' m hm β 0 m (zero_add m) m' 1 (by omega) (by omega), Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v] at this
  have hd : (sgl A).d 0 1 = 0 := (HomologicalComplex.isZero_single_obj_X _ _ _ 1 (by omega)).eq_of_tgt _ _
  rw [hd, zero_comp, smul_zero, add_zero] at this
  rw [Category.assoc, this]
  exact Iso.inv_hom_id_assoc _ _

theorem comp_d_eq_zero {K M : Cx R} {n : ℤ} (c : Cochain K M n) (hc : δ n (n + 1) c = 0) (p : ℤ)
    (h1 : ∀ q hq, c.v (p + 1) q hq = 0) : c.v p (p + n) rfl ≫ M.d (p + n) (p + n + 1) = 0 := by
  have := congrArg (fun c' => c'.v p (p + n + 1) (by omega)) hc
  simp only [Cochain.zero_v] at this
  rw [δ_v n (n + 1) rfl c p (p + n + 1) (by omega) (p + n) (p + 1) (by omega) rfl, h1, comp_zero, smul_zero,
    add_zero] at this
  exact this

def Good {K M : Cx R} {n : ℤ} (z : Cocycle K M n) (k : ℕ) (y : Cochain K M (n - 1)) : Prop :=
  ∀ p q (hpq : p + n = q), -(k : ℤ) < p → (δ (n - 1) n y).v p q hpq = (z : Cochain K M n).v p q hpq

theorem step {K M : Cx R} {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k : ℕ) (y : Cochain K M (n - 1)) (hy : Good z k y) :
    ∃ g : K.X (-(k : ℤ)) ⟶ M.X (-(k : ℤ) + (n - 1)), Good z (k + 1) (y + Cochain.single g (n - 1)) := by
  let c : Cochain K M n := (z : Cochain K M n) - δ (n - 1) n y
  have hc : δ n (n + 1) c = 0 := by
    simp only [c, δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero]
  have h1 : ∀ q hq, c.v (-(k : ℤ) + 1) q hq = 0 := fun q hq => by
    simp only [c, Cochain.sub_v, hy (-(k : ℤ) + 1) q hq (by omega), sub_self]
  obtain ⟨g, hg⟩ := hK (-(k : ℤ)) (-(k : ℤ) + (n - 1)) (-(k : ℤ) + n) (by omega) (by omega)
    (c.v (-(k : ℤ)) (-(k : ℤ) + n) rfl) (comp_d_eq_zero c hc _ h1)
  refine ⟨g, fun p q hpq hp => ?_⟩
  rw [δ_add, Cochain.add_v]
  by_cases hpp : p = -(k : ℤ)
  · subst hpp
    obtain rfl : q = -(k : ℤ) + n := by omega
    rw [δ_v (n - 1) n (by omega) (Cochain.single g (n - 1)) _ _ hpq (-(k : ℤ) + (n - 1)) (-(k : ℤ) + 1) (by omega) rfl,
      Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), comp_zero, smul_zero, add_zero, hg]
    simp only [c, Cochain.sub_v]
    abel
  · rw [hy p q hpq (by omega), δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega), Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
    simp

def seq {K M : Cx R} [K.IsStrictlyLE 0] {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k : ℕ) : {y : Cochain K M (n - 1) // Good z k y} :=
  Nat.rec (motive := fun k => {y : Cochain K M (n - 1) // Good z k y})
    (⟨0, fun p q hpq hp => (K.isZero_of_isStrictlyLE 0 p (by omega)).eq_of_src _ _⟩ : {y : Cochain K M (n - 1) // Good z 0 y})
    (fun k ih => ⟨ih.1 + Cochain.single (step hK z k _ ih.2).choose (n - 1), (step hK z k _ ih.2).choose_spec⟩) k

theorem seq_agree {K M : Cx R} [K.IsStrictlyLE 0] {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k j : ℕ) (hkj : k ≤ j) (p q : ℤ) (hpq : p + (n - 1) = q) (hp : -(k : ℤ) < p) :
    (seq hK z j).1.v p q hpq = (seq hK z k).1.v p q hpq := by
  induction j, hkj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [← ih]
    show ((seq hK z j).1 + Cochain.single _ (n - 1)).v p q hpq = _
    rw [Cochain.add_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), add_zero]

end GlobalTheory.NullHtpyStair


open GlobalTheory.NullHtpyStair in
theorem GlobalTheory.nullHtpy_stair : ∀ (R : Type) [CommRing R] (K M : Cx R) [K.IsStrictlyLE 0],
    (∀ p n : ℤ, p ≤ 0 → Subsingleton (CohomologyClass (sgl (K.X p)) M n)) → ∀ n : ℤ,
    Subsingleton (CohomologyClass K M n) := by
  intro R _ K M _ hA n
  have hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f :=
    fun p m' m hp hm f hf => GlobalTheory.NullHtpyStair.lift_of_subsingleton hm (hA p m hp) f hf
  suffices h : ∀ x : CohomologyClass K M n, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨Cochain.mk (fun p q hpq => (GlobalTheory.NullHtpyStair.seq hK z ((-p).toNat + 1)).1.v p q hpq), ?_⟩
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) (by omega) rfl, Cochain.mk_v, Cochain.mk_v,
    ← GlobalTheory.NullHtpyStair.seq_agree hK z ((-(p + 1)).toNat + 1) ((-p).toNat + 1)
      (by omega) (p + 1) q _ (by omega),
    ← δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) (by omega) rfl]
  exact (GlobalTheory.NullHtpyStair.seq hK z ((-p).toNat + 1)).2 p q hpq (by omega)
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.InjResCmp

variable {R : Type} [CommRing R]

theorem cpush_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpush K (𝟙 I) n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpush_comp (K : Cx R) {I J L : Cx R} (f : I ⟶ J) (g : J ⟶ L) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f ≫ g) n x = cpush K g n (cpush K f n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpush_homotopy (K : Cx R) {I J : Cx R} {f g : I ⟶ J} (h : Homotopy f g) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K f n x = cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  change CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨x.1.comp z (by omega), ?_⟩
  rw [δ_comp x.1 z (by omega) (n + 1) 0 n (by omega) (by omega) (by omega)]
  simp [zcomp, hz, Cochain.comp_add]

open DerivedCategory in
theorem exists_quasiIso (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C) [QuasiIso ε] [(res R M).IsKInjective] :
    ∃ u : C ⟶ res R M, QuasiIso u := by
  letI := HasDerivedCategory.standard (Shv R)
  have : QuasiIso (resAug M) := (inferInstance : QuasiIso (injectiveResolution M).ι')
  let e : Q.obj C ≅ Q.obj (res R M) := (asIso (Q.map ε)).symm ≪≫ asIso (Q.map (resAug M))
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj C)
    (res R M)).surjective
    ((quotientCompQhIso (Shv R)).hom.app C ≫ e.hom ≫ (quotientCompQhIso (Shv R)).inv.app (res R M))
  obtain ⟨u, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨u, ?_⟩
  rw [← isIso_Q_map_iff_quasiIso]
  have h1 := quotientCompQhIso_hom_naturality u
  have h2 : Q.map u = (quotientCompQhIso (Shv R)).inv.app C ≫ Qh.map ((HomotopyCategory.quotient _ _).map u) ≫
      (quotientCompQhIso (Shv R)).hom.app (res R M) := by
    rw [h1]; simp
  rw [h2, hg]
  infer_instance

theorem hyper_iso_of_injective_resolution : ∀ (R : Type) [CommRing R] (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C),
    C.IsStrictlyGE 0 → (∀ t, Injective (C.X t)) → QuasiIso ε → ∀ (K : Cx R) (n : ℤ),
    Nonempty (HK R K M n ≃+ CohomologyClass K C n) := by
  intro R _ M C ε hC hI hε K n
  haveI := hC
  haveI : ∀ t, Injective (C.X t) := hI
  haveI := hε
  haveI : C.IsKInjective := isKInjective_of_injective C 0
  haveI : (res R M).IsKInjective := (inferInstance : (injectiveResolution M).cochainComplex.IsKInjective)
  obtain ⟨u, hu⟩ := exists_quasiIso M C ε
  obtain ⟨e, -⟩ := (CochainComplex.IsKInjective.quasiIso_iff u).1 hu
  exact ⟨{ toFun := cpush K e.inv n
           invFun := cpush K e.hom n
           left_inv := fun x => by
             change cpush K e.hom n (cpush K e.inv n x) = x
             rw [← cpush_comp, cpush_homotopy K e.homotopyInvHomId, cpush_id]
           right_inv := fun y => by
             change cpush K e.inv n (cpush K e.hom n y) = y
             rw [← cpush_comp, cpush_homotopy K e.homotopyHomInvId, cpush_id]
           map_add' := map_add _ }⟩

end GlobalTheory.EtC.InjResCmp
end
end
