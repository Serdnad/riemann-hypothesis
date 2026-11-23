module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorOfFlatComplexes
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle455
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthRestrictColumns
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.flat_tensor_of_flat_complexes : ∀ (R : Type) [CommRing R] {I J T : Cx R} (τ : Pair I J T), τ.IsTensor → (∀ t, FlatS (I.X t)) → (∀ t, FlatS (J.X t)) → ∀ w, FlatS (T.X w) := by
  first | (exact @GlobalTheory.EtC.FlatTens.flatS_tens) | (exact GlobalTheory.EtC.FlatTens.flatS_tens) | (intros; apply GlobalTheory.EtC.FlatTens.flatS_tens  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.PostFun

variable {R : Type} [CommRing R]

theorem post_eq_cpush (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) :
    HK.post R K φ n = cpush K (resMap R φ) n := rfl

def resMapIdHomotopy (F : Shv R) : Homotopy (resMap R (𝟙 F)) (𝟙 (res R F)) := by
  have H2 := (InjectiveResolution.descIdHomotopy F (injectiveResolution F)).extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_id] at H2
  exact H2

def resMapCompHomotopy {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) :
    Homotopy (resMap R (φ ≫ ψ)) (resMap R φ ≫ resMap R ψ) := by
  have H2 := (InjectiveResolution.descCompHomotopy φ ψ (injectiveResolution F) (injectiveResolution G)
    (injectiveResolution M)).extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp] at H2
  exact H2

def resMapAddHomotopy {F G : Shv R} (φ ψ : F ⟶ G) :
    Homotopy (resMap R (φ + ψ)) (resMap R φ + resMap R ψ) := by
  have H : Homotopy (InjectiveResolution.desc (φ + ψ) (injectiveResolution G) (injectiveResolution F))
      (InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F) +
        InjectiveResolution.desc ψ (injectiveResolution G) (injectiveResolution F)) := by
    apply InjectiveResolution.descHomotopy (φ + ψ)
    · simp
    · simp [Preadditive.comp_add, Preadditive.add_comp, Functor.map_add (f := _)]
  have H2 := H.extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_add] at H2
  exact H2

theorem cpush_add (K : Cx R) {I J : Cx R} (f g : I ⟶ J) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f + g) n x = cpush K f n x + cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _ + CohomologyClass.mk _
  rw [← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add, Cochain.comp_add]

theorem post_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.post R K (𝟙 F) n x = x := by
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapIdHomotopy F), InjResCmp.cpush_id]

theorem post_comp (K : Cx R) {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) (n : ℤ) (x : HK R K F n) :
    HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x) := by
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapCompHomotopy φ ψ), InjResCmp.cpush_comp]
  rfl

theorem post_add (K : Cx R) {F G : Shv R} (φ ψ : F ⟶ G) (n : ℤ) :
    HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n := by
  ext x
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapAddHomotopy φ ψ), cpush_add]
  rfl

def postHom (K : Cx R) (F G : Shv R) (n : ℤ) : (F ⟶ G) →+ (HK R K F n →+ HK R K G n) :=
  AddMonoidHom.mk' (fun φ => HK.post R K φ n) (fun φ ψ => post_add K φ ψ n)

theorem post_zsmul (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (c : ℤ) (n : ℤ) (x : HK R K F n) :
    HK.post R K (c • φ) n x = c • HK.post R K φ n x := by
  have h := map_zsmul (postHom K F G n) c φ
  exact DFunLike.congr_fun h x

theorem pull_post {K L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) (x : HK R K F n) :
    HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) :=
  ZcFun.cpull_cpush f (resMap R φ) n x

theorem main : ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ), (∀ (F : Shv R) x, HK.post R K (𝟙 F) n x = x) ∧ (∀ {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) x, HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x)) ∧ (∀ {F G : Shv R} (φ ψ : F ⟶ G), HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n) ∧ (∀ {F G : Shv R} (φ : F ⟶ G) (c : ℤ) x, HK.post R K (c • φ) n x = c • HK.post R K φ n x) ∧ ∀ {L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) x, HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) := by
  intro R _ K n
  exact ⟨fun F x => post_id K F n x, fun φ ψ x => post_comp K φ ψ n x, fun φ ψ => post_add K φ ψ n,
    fun φ c x => post_zsmul K φ c n x, fun f _ _ φ x => pull_post f φ n x⟩

end GlobalTheory.EtC.PostFun
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscChains

def heExt {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] {K L : ChainComplex C ℕ}
    (h : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingDownNat) (L.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap h.hom _
  inv := HomologicalComplex.extendMap h.inv _
  homotopyHomInvId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((h.homotopyHomInvId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((h.homotopyInvHomId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

variable (R : Type) [CommRing R]

def heN (P : PSh) :
    HomotopyEquiv ((chainsN R).obj (disc.obj P)) ((ChainComplex.single₀ (Shv R)).obj ((free R).obj P)) :=
  (HomotopyEquiv.ofIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).mapIso
      (Functor.constComp _ P (free R)))).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const ((free R).obj P)).homotopyEquiv

lemma heN_inv_f_zero (P : PSh) :
    (heN R P).inv.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom := by
  dsimp [heN, HomotopyEquiv.trans, HomotopyEquiv.ofIso, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv]
  erw [HomologicalComplex.comp_f]
  erw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  simp
  exact Category.comp_id _

def he (P : PSh) : HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)) :=
  (HomotopyEquiv.ofIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat ((free R).obj P) 0 0
      (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).symm).trans
    (heExt (heN R P)).symm

lemma he_hom_f_zero (P : PSh) : sglι _ ≫ (he R P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv := by
  dsimp [he, heExt, HomotopyEquiv.trans, HomotopyEquiv.symm, HomotopyEquiv.ofIso]
  erw [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl), heN_inv_f_zero]
  rw [sglι, chainsXIso]
  erw [Category.assoc, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Iso.inv_hom_id_assoc]

end GlobalTheory.EtC.DiscChains

namespace GlobalTheory.EtC

theorem chains_disc_homotopyEquiv : ∀ (R : Type) [CommRing R] , ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)), (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧ ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) = (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom := by
  intro R _
  refine ⟨DiscChains.he R, DiscChains.he_hom_f_zero R, fun {P Q} f => ?_⟩
  obtain ⟨-, hnat, -⟩ := GlobalTheory.EtC.chains_basic R
  apply HomologicalComplex.from_single_hom_ext
  apply (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((free R).obj P)) _ _).1
  change sglι _ ≫ _ = sglι _ ≫ _
  have e1 : ((DiscChains.he R P).hom ≫ (chains R).map (disc.map f)).f 0 =
      (DiscChains.he R P).hom.f 0 ≫ ((chains R).map (disc.map f)).f 0 := HomologicalComplex.comp_f _ _ _
  have e2 : ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (DiscChains.he R Q).hom).f 0 =
      ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 ≫ (DiscChains.he R Q).hom.f 0 :=
    HomologicalComplex.comp_f _ _ _
  rw [e1, e2, ← Category.assoc, DiscChains.he_hom_f_zero]
  have h1 : sglι ((free R).obj P) ≫ ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 =
      (free R).map f ≫ sglι ((free R).obj Q) := by
    change _ ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    erw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h1, Category.assoc, DiscChains.he_hom_f_zero]
  rw [← cancel_mono (chainsXIso R (disc.obj Q) 0).hom]
  have h2 := hnat (disc.map f) 0
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [h2]
  simp

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.cone_kinj_and_bijective_iff : ∀ (R : Type) [CommRing R] {D C : Cx R} (f : D ⟶ C) (m : ℤ),
    D.IsStrictlyGE m → C.IsStrictlyGE m → (∀ n, CategoryTheory.Injective (D.X n)) →
    (∀ n, CategoryTheory.Injective (C.X n)) → (mappingCone f).IsKInjective ∧ ∀ K : Cx R,
      ((∀ n, Function.Bijective (cpush K f n)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n)) := by
  intro R _ D C f m hD hC iD iC
  refine ⟨?_, ?_⟩
  · haveI : ∀ n, Injective ((mappingCone f).X n) := fun n =>
      Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm
        (@Injective.instBiprod _ _ _ _ _ _ (iD (n + 1)) (iC n))
    haveI : (mappingCone f).IsStrictlyGE (m - 1) := CochainComplex.isStrictlyGE_mappingCone f m m (m - 1) (by omega)
    exact isKInjective_of_injective _ (m - 1)
  · intro K
    have ex := fun n => GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K f n
    constructor
    · intro hb n
      refine ⟨fun x y => ?_⟩
      have h0 : ∀ x : CohomologyClass K (mappingCone f) n, x = 0 := by
        intro x
        have h1 : cpush K f (n + 1) (cpost K (mappingCone.fst f) n (n + 1) rfl x) = 0 :=
          ((ex n).2.2 _).2 ⟨x, rfl⟩
        have h2 : cpost K (mappingCone.fst f) n (n + 1) rfl x = 0 :=
          (hb (n + 1)).1 (by rw [h1, map_zero])
        obtain ⟨y, rfl⟩ := ((ex n).2.1 x).1 h2
        obtain ⟨z, rfl⟩ := (hb n).2 y
        exact ((ex n).1 _).2 ⟨z, rfl⟩
      rw [h0 x, h0 y]
    · intro hs n
      refine ⟨?_, fun y => ?_⟩
      · rw [injective_iff_map_eq_zero]
        intro z hz
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by ring⟩
        obtain ⟨w, rfl⟩ := ((ex k).2.2 z).1 hz
        rw [Subsingleton.elim w 0, map_zero]
      · exact ((ex n).1 y).1 (Subsingleton.elim _ _)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ExtHom

variable {R : Type} [CommRing R]

theorem cochain_sgl_neg_one_eq_zero (F : Shv R) (I : Cx R) [I.IsStrictlyGE 0]
    (β : Cochain (sgl F) I (-1)) : β = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hp : p = 0
  · subst hp
    exact (I.isZero_of_isStrictlyGE 0 q (by omega)).eq_of_tgt _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F p hp).eq_of_src _ _

theorem ofHom_eq_of_cls {T I : Cx R} {f g : T ⟶ I}
    (h : CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g)) :
    ∃ β : Cochain T I (-1), Cochain.ofHom f = δ (-1) 0 β + Cochain.ofHom g := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (-1) (by omega)] at h
  obtain ⟨β, hβ⟩ := h
  refine ⟨β, ?_⟩
  rw [hβ]
  simp

end GlobalTheory.EtC.ExtHom


open GlobalTheory.EtC.ExtHom in
theorem GlobalTheory.EtC.extHom_of_quasiIso : ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε], (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m') := by
  intro R _ F T I _ _ ε _
  have hb := GlobalTheory.EtC.cpull_bijective_of_quasiIso R ε I 0
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨y, hy⟩ := hb.2 (CohomologyClass.mk (Cocycle.ofHom a))
    obtain ⟨z, rfl⟩ := y.mk_surjective
    refine ⟨Cocycle.homOf z, ?_⟩
    have hz : Cocycle.ofHom (ε ≫ Cocycle.homOf z) = zcomp (Cocycle.ofHom ε) z (zero_add 0) := by
      apply Cocycle.ext
      simp [zcomp, Cochain.ofHom_comp]
    have h2 : CohomologyClass.mk (Cocycle.ofHom (ε ≫ Cocycle.homOf z)) = CohomologyClass.mk (Cocycle.ofHom a) := by
      rw [hz]; exact hy
    obtain ⟨β, hβ⟩ := ofHom_eq_of_cls h2
    rw [cochain_sgl_neg_one_eq_zero F I β, δ_zero, zero_add] at hβ
    exact (Cocycle.equivHom _ _).injective (Cocycle.ext hβ)
  · have h1 : cpull ε I 0 (CohomologyClass.mk (Cocycle.ofHom m)) = cpull ε I 0 (CohomologyClass.mk (Cocycle.ofHom m')) := by
      simp only [cpull, cpre_mk]
      congr 1
      apply Cocycle.ext
      change (Cochain.ofHom ε).comp (Cochain.ofHom m) (zero_add 0) = (Cochain.ofHom ε).comp (Cochain.ofHom m') (zero_add 0)
      rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp, h]
    obtain ⟨β, hβ⟩ := ofHom_eq_of_cls (hb.1 h1)
    exact ⟨(Cochain.equivHomotopy m m').symm ⟨β, hβ⟩⟩
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (I : Cx R) [I.IsKInjective] (n : ℤ), Function.Bijective (cpull f I n) := by
  first | (exact @GlobalTheory.EtC.cpull_bijective_of_quasiIso) | (exact GlobalTheory.EtC.cpull_bijective_of_quasiIso) | (intros; apply GlobalTheory.EtC.cpull_bijective_of_quasiIso  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeRes

variable {C : Type*} [Category C] [Abelian C]


open DerivedCategory Pretriangulated in
theorem quasiIso_mappingCone_map {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) [QuasiIso a] [QuasiIso b] :
    QuasiIso (mappingCone.map φ₁ φ₂ a b comm) := by
  letI := HasDerivedCategory.standard C
  rw [← isIso_Q_map_iff_quasiIso]
  exact isIso₃_of_isIso₁₂ (Q.mapTriangle.map (mappingCone.triangleMap φ₁ φ₂ a b comm))
    (mappingCone_triangle_distinguished φ₁) (mappingCone_triangle_distinguished φ₂)
    (show IsIso (Q.map a) from inferInstance) (show IsIso (Q.map b) from inferInstance)

theorem homotopy_of_mk_eq {K L : CochainComplex C ℤ} {f g : K ⟶ L}
    (h : CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g)) : Nonempty (Homotopy f g) := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (-1) (by omega)] at h
  obtain ⟨β, hβ⟩ := h
  refine ⟨(Cochain.equivHomotopy f g).symm ⟨β, ?_⟩⟩
  rw [hβ]
  simp

theorem quasiIso_of_homotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) (hg : QuasiIso g) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, h.homologyMap_eq]
  infer_instance

variable {R : Type} [CommRing R]

theorem mk_ofHom_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) :
    CohomologyClass.mk (Cocycle.ofHom (f ≫ g)) = cpull f M 0 (CohomologyClass.mk (Cocycle.ofHom g)) := by
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem resAug_comm {F G : Shv R} (φ : F ⟶ G) :
    (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G = resAug F ≫ resMap R φ :=
  (InjectiveResolution.Hom.ι'_comp_hom'
    (⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
      InjectiveResolution.desc_commutes_zero φ _ _⟩ : InjectiveResolution.Hom _ _ φ)).symm

instance resAug_quasiIso (F : Shv R) : QuasiIso (resAug F) := (inferInstance : QuasiIso (injectiveResolution F).ι')

instance res_isKInjective (F : Shv R) : (res R F).IsKInjective :=
  inferInstanceAs ((injectiveResolution F).cochainComplex.IsKInjective)

theorem cone_isKInjective {F G : Shv R} (φ : F ⟶ G) : (mappingCone (resMap R φ)).IsKInjective := by
  haveI : ∀ n, Injective ((res R F).X n) := fun n => inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  haveI : ∀ n, Injective ((res R G).X n) := fun n => inferInstanceAs (Injective ((injectiveResolution G).cochainComplex.X n))
  haveI : (res R F).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  haveI : (res R G).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution G).cochainComplex.IsStrictlyGE 0)
  haveI : ∀ n, Injective ((mappingCone (resMap R φ)).X n) := fun n =>
    Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resMap R φ) n (n + 1) rfl).symm inferInstance
  haveI : (mappingCone (resMap R φ)).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  exact isKInjective_of_injective _ (-1)

end GlobalTheory.EtC.ConeRes


open GlobalTheory.EtC.ConeRes in
theorem GlobalTheory.EtC.cone_resMap_homotopyEquiv : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
    ∃ e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃),
      Nonempty (Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g)) := by
  intro R _ S hS
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact :=
    hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI := mappingCone.quasiIso_descShortComplex hS'
  haveI := cone_isKInjective S.f
  let q := mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))
  let m := mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) (resAug_comm S.f)
  haveI : QuasiIso m := quasiIso_mappingCone_map _ _ _ _ _
  obtain ⟨c, hc⟩ := (GlobalTheory.EtC.cpull_bijective_of_quasiIso R m (res R S.X₃) 0).2
    (CohomologyClass.mk (Cocycle.ofHom (q ≫ resAug S.X₃)))
  obtain ⟨z, rfl⟩ := c.mk_surjective
  let u : mappingCone (resMap R S.f) ⟶ res R S.X₃ := Cocycle.homOf z
  have hz : z = Cocycle.ofHom u := (Cocycle.ofHom_homOf_eq_self z).symm
  rw [hz, ← mk_ofHom_comp] at hc
  obtain ⟨H1⟩ := homotopy_of_mk_eq hc
  haveI : QuasiIso (m ≫ u) := quasiIso_of_homotopy H1 ((quasiIso_iff_comp_left q (resAug S.X₃)).2 (resAug_quasiIso S.X₃))
  haveI : QuasiIso u := (quasiIso_iff_comp_left m u).1 inferInstance
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff u).1 inferInstance
  refine ⟨e, homotopy_of_mk_eq ?_⟩
  apply (GlobalTheory.EtC.cpull_bijective_of_quasiIso R (resAug S.X₂) (res R S.X₃) 0).1
  rw [← mk_ofHom_comp, ← mk_ofHom_comp, he]
  have hinr : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ m =
      resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) :=
    mappingCone.inr_desc ((CochainComplex.singleFunctor (Shv R) 0).map S.f) _ _ _
  have hq : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ q =
      (CochainComplex.singleFunctor (Shv R) 0).map S.g := mappingCone.inr_descShortComplex _
  have h1 : resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ u =
      mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ m ≫ u :=
    ((reassoc_of% hinr) u).symm
  have h2 : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫ q ≫ resAug S.X₃ =
      (CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃ :=
    (reassoc_of% hq) (resAug S.X₃)
  exact ((congrArg (fun x => CohomologyClass.mk (Cocycle.ofHom x)) h1).trans (mk_ofHom_comp _ _)).trans
    ((congrArg (cpull _ _ 0) hc).trans ((mk_ofHom_comp _ _).symm.trans
      ((congrArg (fun x => CohomologyClass.mk (Cocycle.ofHom x)) h2).trans
        (congrArg (fun x => CohomologyClass.mk (Cocycle.ofHom x)) (resAug_comm S.g)))))
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.mem_kernel_ideal_of_app_eq_zero_field : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (G H : PDivGroup p K) (f : G ⟶ H) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) • 𝟙 G → g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a : G.A 1, g.app 1 a = 0 → a ∈ kerIdeal (f.app 1) := by
  first | exact @GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero | exact GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero | (intros; apply GlobalTheory.PDivGroup.mem_kerIdeal_of_app_eq_zero <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.pDivGroup_omega_noPTorsion_of_cotangent_injective : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R), (∀ n, Function.Injective (GlobalTheory.PDiv.cotMap (G.mulP n))) → ∀ w : G.omega, (p : R) • w = 0 → w = 0 := by
  first | exact @GlobalTheory.omega_eq_zero_of_p_smul_eq_zero | exact GlobalTheory.omega_eq_zero_of_p_smul_eq_zero | (intros; apply GlobalTheory.omega_eq_zero_of_p_smul_eq_zero <;> assumption)
end

section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_mulPow_fibreRank_eq_pDivGroup :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (k m : ℕ),
      ∃ (r : G.A (k + m) →ₐc[O] G.A k) (μ : G.A k →ₐc[O] G.A (k + m)),
        Function.Surjective r ∧
        RingHom.ker r = torsionIdeal (R := O) (A := G.A (k + m)) (p ^ k) ∧
        (∀ a, μ (r a) = mulBy (R := O) (A := G.A (k + m)) (p ^ m) a) ∧
        ∀ q, fibreRank (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap q = fibreDim (G.A k) q := by
  exact @GlobalTheory.PDivGroup.exists_mulPow_fibreRank_eq
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.le_formalGroupDeterminantPowDepth_of_radii : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (ρ : Fin i → ℝ) (t : Fin d → MvPowerSeries (Fin i) C) (B : ℝ), (∀ a, constantCoeff (t a) = 0) → (∀ a, OrdGe v ρ (t a) 0) → (∀ α ∈ (detPow C i c).support, (((B + c * ∑ a, ρ a : ℝ)) : WithTop ℝ) ≤ v ((detPow C i c).coeff α * mfact α)) → ∀ f : MvPowerSeries (Σ _ : Fin i, Fin d) C, MvIsInt v f → ((B : ℝ) : WithTop ℝ) ≤ v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f)) := by
  first | exact @GlobalTheory.DepthCount.depth_count | exact GlobalTheory.DepthCount.depth_count | (intros; apply GlobalTheory.DepthCount.depth_count <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.differentialOperatorDepth_restrict_columns : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ) (P : MvPolynomial (Σ b : κ', ι (e b)) C), depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) = depth (fun b => G (e b)) (fun b => u (e b)) P := by
  first | exact @GlobalTheory.FGDepth.depth_restrict | exact GlobalTheory.FGDepth.depth_restrict | (intros; apply GlobalTheory.FGDepth.depth_restrict <;> assumption)
end
