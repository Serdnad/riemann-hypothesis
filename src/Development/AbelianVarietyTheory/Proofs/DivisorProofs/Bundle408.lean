module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section
namespace GlobalTheory.EtC.SwapTransfer

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.SwapTransfer.negOnePow_sq' (n m : ℤ) :
    (n.negOnePow : ℤ) * ((m.negOnePow : ℤ) * (n.negOnePow : ℤ)) = m.negOnePow := by
  rw [mul_left_comm, ← Units.val_mul, Int.units_mul_self, Units.val_one, mul_one]

def flipPair {I J K : Cx R} (μ : Pair I J K) : Pair J I K where
  mul U t s w h := (((s * t).negOnePow : ℤ) • μ.mul U s t w (by omega)).flip
  nat g t s w h b a := by
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, Sec.res, map_zsmul]
    rw [← Sec.res, μ.nat]
  leibniz U t s w h b a := by
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, Sec.map, map_zsmul]
    rw [← Sec.map, μ.leibniz]
    have h1 : (s * (t + 1)).negOnePow = (s * t).negOnePow * s.negOnePow := by
      rw [mul_add, mul_one, Int.negOnePow_add]
    have h2 : ((s + 1) * t).negOnePow = (s * t).negOnePow * t.negOnePow := by
      rw [add_mul, one_mul, Int.negOnePow_add]
    rw [h1, h2]
    simp only [Units.smul_def, smul_add, smul_smul, Units.val_mul]
    rw [negOnePow_sq']
    exact add_comm _ _

def swIdx {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) : {p : ℤ × ℤ // p.1 + p.2 = w} :=
  ⟨(p.1.2, p.1.1), by have := p.2; simp only at this ⊢; omega⟩

def swapT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens J I U w := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    ((p.1.1 * p.1.2).negOnePow : ℤ) • ((DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIdx p)) ∘ₗ
      (TensorProduct.comm (ULift.{1} R) (Sec (I.X p.1.1) U) (Sec (J.X p.1.2) U)).toLinearMap)

end GlobalTheory.EtC.SwapTransfer

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem flipPair_mul_eq_negOnePow_smul_mul {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    (_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ).mul U t s w (by omega) b a = (s * t).negOnePow • μ.mul U s t w h a b := by
  rw [Units.smul_def]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem koszulSwap_lof_tmul_lemma_5 (I J : _root_.GlobalTheory.EtC.Cx R) (U : Scheme.{0}) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      (s * t).negOnePow • DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (J.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (I.X q.1.2) U)
          ⟨(t, s), by omega⟩ (b ⊗ₜ a) := by
  unfold _root_.GlobalTheory.EtC.SwapTransfer.swapT
  erw [DirectSum.toModule_lof]
  rw [Units.smul_def]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem lift_lof_tmul {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    μ.lift U w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) = μ.mul U s t w h a b := by
  unfold _root_.GlobalTheory.EtC.Pair.lift
  erw [DirectSum.toModule_lof]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem lift_comp_swapT_eq_flipPair_lift {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) (w : ℤ) :
    μ.lift U w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w =
      (_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ).lift U w := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨t, s⟩, h⟩
  apply TensorProduct.ext'
  intro b a
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, lift_lof_tmul, lift_lof_tmul, Units.smul_def, mul_comm t s]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem swapT_comp_swapT (I J : _root_.GlobalTheory.EtC.Cx R) (U : Scheme.{0}) (w : ℤ) :
    _root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w = LinearMap.id := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, koszulSwap_lof_tmul_lemma_5, smul_smul, mul_comm t s, Int.units_mul_self, one_smul]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem tensorRestrict_lof_tmul_lemma_7 (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}} (g : V ⟶ U) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.Tens.res g w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) V ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) V)
          ⟨(s, t), h⟩ (_root_.GlobalTheory.EtC.Sec.res g a ⊗ₜ _root_.GlobalTheory.EtC.Sec.res g b) := by
  unfold _root_.GlobalTheory.EtC.Tens.res
  erw [DirectSum.lmap_lof]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem res_comp_swapT (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    _root_.GlobalTheory.EtC.Tens.res g w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w =
      _root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w ∘ₗ _root_.GlobalTheory.EtC.Tens.res g w := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, tensorRestrict_lof_tmul_lemma_7, tensorRestrict_lof_tmul_lemma_7, koszulSwap_lof_tmul_lemma_5]


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
theorem _root_.GlobalTheory.EtC.Pair.exists_isFlip (R : Type) [CommRing R]
    {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) :
    ∃ ν : _root_.GlobalTheory.EtC.Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧
      (μ.IsTensor → ν.IsTensor) := by
  refine ⟨_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ, ?_, ?_, ?_⟩
  · intro U s t w h a b
    exact flipPair_mul_eq_negOnePow_smul_mul μ U s t w h a b
  · intro U t s w h b a
    rw [flipPair_mul_eq_negOnePow_smul_mul μ U s t w (by omega) a b, smul_smul, mul_comm t s, Int.units_mul_self, one_smul]
  · rintro ⟨hsurj, hinj⟩
    refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
    · obtain ⟨S, hS, hP⟩ := hsurj U w y
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨x, hx⟩ := hP V g hg
      refine ⟨_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w x, ?_⟩
      rw [← lift_comp_swapT_eq_flipPair_lift, LinearMap.comp_apply, ← LinearMap.comp_apply (_root_.GlobalTheory.EtC.SwapTransfer.swapT J I V w), swapT_comp_swapT, LinearMap.id_apply]
      exact hx
    · have hx' : μ.lift U w (_root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w x) = 0 := by
        rw [← LinearMap.comp_apply, lift_comp_swapT_eq_flipPair_lift]
        exact hx
      obtain ⟨S, hS, hP⟩ := hinj U w _ hx'
      refine ⟨S, hS, fun V g hg => ?_⟩
      have hV := congrArg (_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w) (hP V g hg)
      rw [← LinearMap.comp_apply (_root_.GlobalTheory.EtC.Tens.res g w), res_comp_swapT, LinearMap.comp_apply,
        ← LinearMap.comp_apply (_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w), swapT_comp_swapT, LinearMap.id_apply, map_zero] at hV
      exact hV

end GlobalTheory.EtC

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SuppSub

variable {R : Type} [CommRing R] (Z : Scheme.{0} → Prop) (hZ : ∀ (V U : Scheme.{0}) (_ : V ⟶ U), Z U → Z V)

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (f ≫ g) a = Sec.res f (Sec.res g a) := by
  change (F.obj.map (f ≫ g).op).hom a = _
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

def sv {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sieve U where
  arrows V g := Z V ∨ Sec.res g a = 0
  downward_closed {V W} g hg f := by
    rcases hg with h | h
    · exact Or.inl (hZ _ _ f h)
    · right
      rw [res_comp, h]; exact map_zero (F.obj.map f.op).hom

theorem loc_iff {F : Shv R} {U : Scheme.{0}} (a : Sec F U) :
    (Loc U fun V g => Z V ∨ Sec.res g a = 0) ↔ sv Z hZ a ∈ Scheme.etaleTopology U := by
  constructor
  · rintro ⟨S, hS, h⟩
    exact GrothendieckTopology.superset_covering _ (fun V g hg => h V g hg) hS
  · intro h
    exact ⟨_, h, fun V g hg => hg⟩

def supp (F : Shv R) (U : Scheme.{0}) : Submodule (ULift.{1} R) (Sec F U) where
  carrier := {a | sv Z hZ a ∈ Scheme.etaleTopology U}
  zero_mem' := by
    change sv Z hZ (0 : Sec F U) ∈ Scheme.etaleTopology U
    refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.top_mem U)
    intro V g _
    exact Or.inr (map_zero (F.obj.map g.op).hom)
  add_mem' {a b} ha hb := by
    change sv Z hZ a ∈ Scheme.etaleTopology U at ha
    change sv Z hZ b ∈ Scheme.etaleTopology U at hb
    change sv Z hZ (a + b) ∈ Scheme.etaleTopology U
    refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.intersection_covering ha hb)
    intro V g hg
    rcases hg.1 with h | h
    · exact Or.inl h
    rcases hg.2 with h' | h'
    · exact Or.inl h'
    · right; change (F.obj.map g.op).hom (a + b) = 0; rw [map_add (f := _)]; exact (congrArg₂ (· + ·) h h').trans (add_zero 0)
  smul_mem' c a ha := by
    change sv Z hZ a ∈ Scheme.etaleTopology U at ha
    change sv Z hZ (c • a) ∈ Scheme.etaleTopology U
    refine Scheme.etaleTopology.superset_covering ?_ ha
    intro V g hg
    rcases hg with h | h
    · exact Or.inl h
    · right; change (F.obj.map g.op).hom (c • a) = 0; rw [map_smul]; exact (congrArg (c • ·) h).trans (smul_zero c)

theorem supp_res {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) {a : Sec F U} (ha : a ∈ supp Z hZ F U) :
    Sec.res g a ∈ supp Z hZ F V := by
  refine GrothendieckTopology.superset_covering _ (fun W f hf => ?_) (Scheme.etaleTopology.pullback_stable g (show sv Z hZ a ∈ Scheme.etaleTopology U from ha))
  change Z W ∨ Sec.res (f ≫ g) a = 0 at hf
  rw [res_comp] at hf
  exact hf

def suppP (F : Shv R) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (supp Z hZ F U.unop)
  map {U V} g := ModuleCat.ofHom ((F.obj.map g).hom.restrict (fun a ha => supp_res Z hZ g.unop ha))
  map_id U := by
    ext ⟨a, ha⟩
    change (F.obj.map (𝟙 U)).hom a = a
    rw [F.obj.map_id]; rfl
  map_comp {U V W} f g := by
    ext ⟨a, ha⟩
    change (F.obj.map (f ≫ g)).hom a = (F.obj.map g).hom ((F.obj.map f).hom a)
    rw [F.obj.map_comp]; rfl

def suppT (F : Shv R) : Subfunctor (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) where
  obj U := {a | a ∈ supp Z hZ F U.unop}
  map {U V} g a ha := supp_res Z hZ g.unop ha

theorem sheafT (F : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.property)

theorem suppT_isSheaf (F : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (suppT Z hZ F).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ (sheafT F)]
  intro U s hs
  change sv Z hZ (F := F) (U := U.unop) s ∈ Scheme.etaleTopology U.unop
  refine Scheme.etaleTopology.transitive hs _ (fun V f hf => ?_)
  have hf' : sv Z hZ (Sec.res f s) ∈ Scheme.etaleTopology V := hf
  refine Scheme.etaleTopology.superset_covering (fun W h hh => ?_) hf'
  change Z W ∨ Sec.res (h ≫ f) s = 0
  rw [res_comp]
  exact hh

theorem sectionsWithSupport_isSheaf (F : Shv R) : Presheaf.IsSheaf Scheme.etaleTopology (suppP Z hZ F) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _), isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_iso _ (NatIso.ofComponents (fun U => Iso.refl _) (fun _ => rfl)).symm (suppT_isSheaf Z hZ F)

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  change (φ.hom.app (op U) ≫ G.obj.map g.op).hom a = (F.obj.map g.op ≫ φ.hom.app (op V)).hom a
  rw [φ.hom.naturality]

theorem supp_map {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {a : Sec F U} (ha : a ∈ supp Z hZ F U) :
    Sec.map φ a ∈ supp Z hZ G U := by
  refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) (show sv Z hZ a ∈ Scheme.etaleTopology U from ha)
  rcases hg with h | h
  · exact Or.inl h
  · right
    change Sec.res g (Sec.map φ a) = 0
    rw [res_map, h]
    exact map_zero (φ.hom.app (op V)).hom

def suppS (F : Shv R) : Shv R := ⟨suppP Z hZ F, sectionsWithSupport_isSheaf Z hZ F⟩

def suppF : Shv R ⥤ Shv R where
  obj F := suppS Z hZ F
  map {F G} φ := ObjectProperty.homMk
    { app U := ModuleCat.ofHom ((φ.hom.app U).hom.restrict (fun a ha => supp_map Z hZ φ ha))
      naturality U V g := by
        ext ⟨a, ha⟩
        exact Subtype.ext (res_map φ g.unop a).symm }
  map_id F := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    rfl

def suppι : suppF Z hZ ⟶ 𝟭 (Shv R) where
  app F := ObjectProperty.homMk
    { app U := ModuleCat.ofHom (supp Z hZ F U.unop).subtype
      naturality U V g := by
        ext ⟨a, ha⟩
        rfl }
  naturality F G φ := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    rfl

instance : (suppF Z hZ (R := R)).PreservesZeroMorphisms where
  map_zero F G := by
    apply ObjectProperty.hom_ext
    ext U ⟨a, ha⟩
    apply Subtype.ext
    change ((0 : F ⟶ G).hom.app U).hom a = 0
    simp

def suppCx (C : Cx R) : Cx R := ((suppF Z hZ).mapHomologicalComplex _).obj C

def suppCxι (C : Cx R) : suppCx Z hZ C ⟶ C where
  f n := (suppι Z hZ).app (C.X n)
  comm' i j _ := (suppι Z hZ).naturality (C.d i j)

theorem exists_supp_sub : ∀ (R : Type) [CommRing R] (C : Cx R) (Z : Scheme.{0} → Prop), (∀ (V U : Scheme.{0}) (_ : V ⟶ U), Z U → Z V) → ∃ (D : Cx R) (ι : D ⟶ C), (∀ n U, Function.Injective (Sec.map (ι.f n) (U := U))) ∧ ∀ n U (a : Sec (C.X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔ Loc U fun V g => Z V ∨ Sec.res g a = 0 := by
  intro R _ C Z hZ
  refine ⟨suppCx Z hZ C, suppCxι Z hZ C, fun n U => ?_, fun n U a => ?_⟩
  · intro b b' h
    exact Subtype.ext (p := fun x => x ∈ supp Z hZ (C.X n) U) h
  · rw [loc_iff Z hZ]
    constructor
    · rintro ⟨b, rfl⟩
      exact (show ↥(supp Z hZ (C.X n) U) from b).2
    · intro h
      exact ⟨(⟨a, h⟩ : ↥(supp Z hZ (C.X n) U)), rfl⟩

end GlobalTheory.EtC.SuppSub
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.BiprodCls

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull {K L M : _root_.GlobalTheory.EtC.Cx R} (f : K ⟶ L)
    (g : L ⟶ M) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    _root_.GlobalTheory.EtC.cpull f I n (_root_.GlobalTheory.EtC.cpull g I n x) =
      _root_.GlobalTheory.EtC.cpull (f ≫ g) I n x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_add {K L : _root_.GlobalTheory.EtC.Cx R} (f g : K ⟶ L)
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    _root_.GlobalTheory.EtC.cpull (f + g) I n x =
      _root_.GlobalTheory.EtC.cpull f I n x + _root_.GlobalTheory.EtC.cpull g I n x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk, ← CohomologyClass.mk_add]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.add_comp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_zero {K L : _root_.GlobalTheory.EtC.Cx R}
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    _root_.GlobalTheory.EtC.cpull (0 : K ⟶ L) I n x = 0 := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk, ← CohomologyClass.mk_zero]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_id {K : _root_.GlobalTheory.EtC.Cx R}
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass K I n) :
    _root_.GlobalTheory.EtC.cpull (𝟙 K) I n x = x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp]

end GlobalTheory.EtC.BiprodCls

namespace GlobalTheory.EtC
open BiprodCls

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.cpull_biprod_bijective : ∀ (R : Type) [CommRing R]
    (K L I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ),
    Function.Bijective fun x : CohomologyClass (K ⊞ L) I n =>
      (_root_.GlobalTheory.EtC.cpull (biprod.inl : K ⟶ K ⊞ L) I n x,
        _root_.GlobalTheory.EtC.cpull (biprod.inr : L ⟶ K ⊞ L) I n x) := by
  intro R _ K L I n
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y => _root_.GlobalTheory.EtC.cpull (biprod.fst : K ⊞ L ⟶ K) I n y.1 +
    _root_.GlobalTheory.EtC.cpull (biprod.snd : K ⊞ L ⟶ L) I n y.2, fun x => ?_, fun y => ?_⟩
  · simp only [_root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, ← _root_.GlobalTheory.EtC.BiprodCls.cpull_add,
      biprod.total, _root_.GlobalTheory.EtC.BiprodCls.cpull_id]
  · obtain ⟨a, b⟩ := y
    simp only [map_add (f := _), _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, biprod.inl_fst, biprod.inl_snd,
      biprod.inr_fst, biprod.inr_snd, _root_.GlobalTheory.EtC.BiprodCls.cpull_id,
      _root_.GlobalTheory.EtC.BiprodCls.cpull_zero, add_zero, zero_add]

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_cocycle_of_map_to_X_one :
    ∀ (C : Shv ℤ) (I : Cx ℤ) (ψ : C ⟶ I.X 1), ψ ≫ I.d 1 2 = 0 →
      ∃ w : Cocycle (sgl C) I 1, sglι C ≫ w.1.v 0 1 (zero_add 1) = ψ := by
  intro C I ψ hψ
  refine ⟨Cocycle.fromSingleMk ψ (zero_add 1) 2 (by norm_num) hψ, ?_⟩
  rw [Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v]
  exact (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 C).inv_hom_id_assoc ψ

end GlobalTheory.EtC
end
