module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Functor
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle155
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.HomInj

variable (R : Type) [CommRing R] (P : PSh) (I : Ideal (ULift.{1} R))

def idealFree : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (ULift.{1} (P.obj U) →₀ I)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain I (ULift.{1} R) (fun x => ULift.up (P.map f x.down)))
  map_id U := by
    ext1; apply Finsupp.lhom_ext; intro x a
    simp
  map_comp f g := by
    ext1; apply Finsupp.lhom_ext; intro x a
    simp

def idealIncl : idealFree R P I ⟶ (freeP R).obj P where
  app U := ModuleCat.ofHom (Finsupp.mapRange.linearMap I.subtype)
  naturality U V f := by
    ext1; apply Finsupp.lhom_ext; intro x a
    change Finsupp.mapRange (I.subtype) (map_zero _) (Finsupp.mapDomain _ (Finsupp.single x a)) =
      Finsupp.mapDomain _ (Finsupp.mapRange (I.subtype) (map_zero _) (Finsupp.single x a))
    simp only [Finsupp.mapDomain_single, Finsupp.mapRange_single]
    rfl

instance : Mono (idealIncl R P I) := by
  have : ∀ U, Mono ((idealIncl R P I).app U) := fun U => by
    apply (ModuleCat.mono_iff_injective _).2
    change Function.Injective (Finsupp.mapRange (α := ULift.{1} (P.obj U)) I.subtype (map_zero _))
    exact Finsupp.mapRange_injective _ (map_zero _) Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

end GlobalTheory.EtC.HomInj

namespace GlobalTheory.EtC.HomInj
variable (R : Type) [CommRing R] (P : PSh) (I : Ideal (ULift.{1} R)) (J : Shv R)
  (g : I →ₗ[ULift.{1} R] ((free R).obj P ⟶ J))

def evalAt (U : Scheme.{0}ᵒᵖ) (x : ULift.{1} (P.obj U)) : I →ₗ[ULift.{1} R] J.obj.obj U where
  toFun a := ((g a).hom.app U).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app U).hom (ModuleCat.freeMk x))
  map_add' a b := by rw [map_add (f := _)]; rfl
  map_smul' r a := by rw [map_smul]; rfl

def famHom : idealFree R P I ⟶ J.obj where
  app U := ModuleCat.ofHom (Finsupp.lsum ℕ (evalAt R P I J g U))
  naturality U V f := by
    ext1; apply Finsupp.lhom_ext; intro x a
    change Finsupp.lsum ℕ (evalAt R P I J g V) (Finsupp.mapDomain _ (Finsupp.single x a)) =
      (J.obj.map f).hom (Finsupp.lsum ℕ (evalAt R P I J g U) (Finsupp.single x a))
    rw [Finsupp.mapDomain_single]
    simp only [Finsupp.lsum_single]
    change ((g a).hom.app V).hom _ = (J.obj.map f).hom (((g a).hom.app U).hom _)
    have h1 := congrArg (fun φ => φ.hom (ModuleCat.freeMk x))
      (((toSheafify Scheme.etaleTopology ((freeP R).obj P) : (freeP R).obj P ⟶ ((free R).obj P).obj) ≫ (g a).hom).naturality f)
    change ((g a).hom.app V).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app V).hom
        ((((freeP R).obj P).map f).hom (ModuleCat.freeMk x))) = (J.obj.map f).hom (((g a).hom.app U).hom
        (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app U).hom (ModuleCat.freeMk x))) at h1
    rw [← h1]
    congr 2
    change _ = Finsupp.mapDomain _ (Finsupp.single x (1 : ULift.{1} R))
    erw [Finsupp.mapDomain_single]
    rfl
end GlobalTheory.EtC.HomInj

namespace GlobalTheory.EtC.HomInj

theorem hom_free_injective (R : Type) [CommRing R] (J : Shv R) [Injective J] (P : PSh) :
    Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J) := by
  apply Module.Baer.injective
  intro I g
  let m : (presheafToSheaf Scheme.etaleTopology _).obj (idealFree R P I) ⟶ (free R).obj P :=
    (presheafToSheaf Scheme.etaleTopology _).map (idealIncl R P I)
  let ψ' : (presheafToSheaf Scheme.etaleTopology _).obj (idealFree R P I) ⟶ J :=
    ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).symm (famHom R P I J g)
  have : Mono m := inferInstanceAs (Mono ((presheafToSheaf Scheme.etaleTopology _).map (idealIncl R P I)))
  let f := Injective.factorThru ψ' m
  refine ⟨LinearMap.toSpanSingleton _ _ f, fun a ha => ?_⟩
  rw [LinearMap.toSpanSingleton_apply]
  have hm : m ≫ f = ψ' := Injective.comp_factorThru ψ' m
  have hψ : toSheafify Scheme.etaleTopology (idealFree R P I) ≫ ψ'.hom = famHom R P I J g := by
    have := ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).apply_symm_apply (famHom R P I J g)
    rw [Adjunction.homEquiv_unit] at this
    simpa using this
  have h3 : idealIncl R P I ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ f.hom = famHom R P I J g := by
    have e := toSheafify_naturality Scheme.etaleTopology (idealIncl R P I)
    calc idealIncl R P I ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ f.hom
        = (idealIncl R P I ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P)) ≫ f.hom := (Category.assoc _ _ _).symm
      _ = (toSheafify Scheme.etaleTopology (idealFree R P I) ≫ sheafifyMap Scheme.etaleTopology (idealIncl R P I)) ≫ f.hom := by
          rw [e]
      _ = toSheafify Scheme.etaleTopology (idealFree R P I) ≫ (m ≫ f).hom :=
          Category.assoc (toSheafify Scheme.etaleTopology (idealFree R P I)) (sheafifyMap Scheme.etaleTopology (idealIncl R P I)) f.hom
      _ = famHom R P I J g := by rw [hm, hψ]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ J.property
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  have h4 := congrArg (fun φ => (φ.app U).hom (Finsupp.single x ⟨a, ha⟩)) h3
  have e1 : ((idealIncl R P I).app U).hom (Finsupp.single x (⟨a, ha⟩ : I)) = a • ModuleCat.freeMk (R := ULift.{1} R) x := by
    change Finsupp.mapRange I.subtype (map_zero _) (Finsupp.single x (⟨a, ha⟩ : I)) = _
    rw [Finsupp.mapRange_single]
    change _ = a • Finsupp.single x (1 : ULift.{1} R)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ f.hom).app U).hom
      (((idealIncl R P I).app U).hom (Finsupp.single x ⟨a, ha⟩)) =
    Finsupp.lsum ℕ (evalAt R P I J g U) (Finsupp.single x ⟨a, ha⟩) at h4
  rw [e1] at h4
  erw [LinearMap.map_smul, Finsupp.lsum_single] at h4
  exact h4

end GlobalTheory.EtC.HomInj
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def trivV (N : ℕ) (E : Spc) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (show Fin (n.unop.len + 1) ⥤ (glCat N).obj (Scheme.Γ.obj U) from
          (CategoryTheory.Functor.const _).obj (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))))
      naturality := fun U U' f => by
        ext x
        exact CategoryTheory.Functor.hext (fun _ => rfl)
          (fun _ _ _ => heq_of_eq (map_one (Matrix.GeneralLinearGroup.map _)).symm) }
  naturality n m f := by
    ext U x
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq rfl)

end GlobalTheory.EtC

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem mappingCone_acyclic_of_quasiIso {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) [QuasiIso u] :
    (CochainComplex.mappingCone u).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (inferInstance : QuasiIso u)
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hu
  exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished u)).1 hu

theorem EtC.mappingCone_acyclic :
    ∀ (R : Type) [CommRing R] {C J : Cx R} (u : C ⟶ J) [QuasiIso u], (mappingCone u).Acyclic :=
  fun _ _ _ _ u _ => mappingCone_acyclic_of_quasiIso u

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.bijective_multiplicativeGroup_sections_units :
    ∀ U : Scheme.{0}, Function.Bijective (ofRings.sec unitsF U) := by
  have hGamma : Presheaf.IsSheaf Scheme.etaleTopology.{0} Scheme.Γ := by
    intro R
    have gammaIso : Scheme.Γ ⋙ coyoneda.obj (op R) ≅ yoneda.obj (Spec R) :=
      NatIso.ofComponents
        (fun U => (Equiv.trans (Quiver.Hom.opEquiv)
          (ΓSpec.adjunction.homEquiv U.unop (op R))).toIso)
        (by
          intro U V f
          ext g
          exact ΓSpec.adjunction.homEquiv_naturality_left f.unop g.op)
    exact Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
      (Presieve.isSheaf_iso _ gammaIso.symm
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
  have hUnits : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ unitsF) := by
    apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
    let F := forget₂ CommRingCat.{0} CommMonCat ⋙ CommMonCat.units ⋙
      forget CommGrpCat ⋙ uliftFunctor.{1, 0}
    have hF : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ F) :=
      Presheaf.isSheaf_comp_of_isSheaf _ _ F hGamma
    exact hF
  intro U
  have := isIso_toSheafify Scheme.etaleTopology hUnits
  delta ofRings.sec
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U))
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RetractAcyc

def resMapRetractHomotopy (R : Type) [CommRing R] {M M' : Shv R} (i : M ⟶ M') (r : M' ⟶ M) (h : i ≫ r = 𝟙 M) :
    Homotopy (resMap R i ≫ resMap R r) (𝟙 (res R M)) := by
  have H : Homotopy (InjectiveResolution.desc i (injectiveResolution M') (injectiveResolution M) ≫
      InjectiveResolution.desc r (injectiveResolution M) (injectiveResolution M'))
      (𝟙 (injectiveResolution M).cocomplex) :=
    (InjectiveResolution.descCompHomotopy i r _ _ _).symm.trans
      (by rw [h]; exact InjectiveResolution.descIdHomotopy _ _)
  have H2 := H.extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id] at H2
  exact H2

theorem post_post_of_retract (R : Type) [CommRing R] {M M' : Shv R} (i : M ⟶ M') (r : M' ⟶ M) (h : i ≫ r = 𝟙 M)
    (K : Cx R) (n : ℤ) (x : HK R K M n) : HK.post R K r n (HK.post R K i n x) = x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have Hh := resMapRetractHomotopy R i r h
  change CohomologyClass.mk (zcomp (zcomp α (Cocycle.ofHom (resMap R i)) (add_zero n))
    (Cocycle.ofHom (resMap R r)) (add_zero n)) = CohomologyClass.mk α
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨α.1.comp (Cochain.ofHomotopy Hh) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
  ext p q hpq
  simp [zcomp, Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q)]

theorem subsingleton_of_retract : ∀ (R : Type) [CommRing R] (M M' : Shv R) (i : M ⟶ M') (r : M' ⟶ M), i ≫ r = 𝟙 M →
    ∀ (K : Cx R) (n : ℤ), Subsingleton (HK R K M' n) → Subsingleton (HK R K M n) := by
  intro R _ M M' i r h K n hs
  exact (Function.LeftInverse.injective (g := HK.post R K r n) (f := HK.post R K i n)
    (post_post_of_retract R i r h K n)).subsingleton

end GlobalTheory.EtC.RetractAcyc
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscRep
variable {R : Type} [CommRing R]

def asum (m : ℕ) : ℤ := ∑ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ)

theorem asum_succ (k : ℕ) : asum (k + 1) = asum k + (-1) ^ (k + 1) := by
  rw [asum, Fin.sum_univ_castSucc]
  simp [asum]

theorem asum_even (m : ℕ) : asum m = if Even m then 1 else 0 := by
  induction m with
  | zero => simp [asum]
  | succ k ih =>
    rw [asum_succ, ih]
    rcases Nat.even_or_odd k with h | h
    · have h' : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', (h.add_one).neg_one_pow]
    · have h' : Even (k + 1) := h.add_one
      have h'' : ¬ Even k := Nat.not_even_iff_odd.mpr h
      simp [h', h'', h'.neg_one_pow]

variable (R) in
abbrev C (F : PSh) : ChainComplex (Shv R) ℕ := (chainsN R).obj (disc.obj F)

theorem C_d (F : PSh) (p : ℕ) :
    (C R F).d (p + 1) p = (asum (p + 1)) • (𝟙 ((free R).obj F) : (C R F).X (p + 1) ⟶ (C R F).X p) := by
  rw [show (C R F).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((disc.obj F).δ i) from
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p]
  simp only [asum, Finset.sum_smul, SimplicialObject.δ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (disc.obj F).map (SimplexCategory.δ i).op = 𝟙 F from rfl]
  exact congrArg (fun f => (-1 : ℤ) ^ (i : ℕ) • f) ((free R).map_id F)

def idX (F : PSh) (i j : ℕ) : (C R F).X i ⟶ (C R F).X j := 𝟙 ((free R).obj F)

theorem idX_comp (F : PSh) (i j k : ℕ) : idX (R := R) F i j ≫ idX F j k = idX F i k := Category.id_comp _

theorem C_d' (F : PSh) (p : ℕ) : (C R F).d (p + 1) p = (asum (p + 1)) • idX F (p + 1) p := C_d F p

def piC (F : PSh) : C R F ⟶ C R F where
  f i := if i = 0 then 𝟙 _ else 0
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [if_neg (Nat.succ_ne_zero j), zero_comp, C_d']
    rcases j with _ | j
    · rw [asum_even, if_neg (by decide), zero_smul, zero_comp]
    · rw [if_neg (Nat.succ_ne_zero j), comp_zero]

def htpC (F : PSh) : Homotopy (𝟙 (C R F)) (piC F) where
  hom i j := if i + 1 = j ∧ Odd i then idX F i j else 0
  zero i j w := by
    rw [if_neg]
    rintro ⟨h, -⟩
    exact w h
  comm i := by
    rcases i with _ | k
    · rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, C_d']
      simp [piC, asum_even]
    · rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, C_d', C_d']
      simp only [piC, if_neg (Nat.succ_ne_zero k), add_zero, true_and, asum_even]
      rcases Nat.even_or_odd k with h | h
      · have h1 : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using h
        have h2 : Even (k + 1 + 1) := h1 |> fun _ => (h.add_one).add_one
        have h3 : Odd (k + 1) := h.add_one
        have h4 : ¬ Odd k := Nat.not_odd_iff_even.mpr h
        simp only [h1, h2, h3, h4, if_true, if_false, one_smul, zero_smul, comp_zero, zero_comp, zero_add, idX_comp]
        rfl
      · have h1 : Even (k + 1) := h.add_one
        have h3 : ¬ Odd (k + 1) := Nat.not_odd_iff_even.mpr h1
        simp only [h1, h, h3, if_true, if_false, one_smul, comp_zero, zero_comp, add_zero, idX_comp]
        rfl

def piZ (F : PSh) : (chains R).obj (disc.obj F) ⟶ (chains R).obj (disc.obj F) :=
  HomologicalComplex.extendMap (piC F) ComplexShape.embeddingDownNat

def htpZ (F : PSh) : Homotopy (𝟙 ((chains R).obj (disc.obj F))) (piZ F) :=
  (Homotopy.ofEq (HomologicalComplex.extendMap_id (C R F) ComplexShape.embeddingDownNat).symm).trans
    ((htpC F).extend ComplexShape.embeddingDownNat)

theorem piZ_f (F : PSh) (p : ℕ) (hp : 0 < p) : (piZ (R := R) F).f (-(p : ℤ)) = 0 := by
  have h1 := HomologicalComplex.extendMap_f (piC (R := R) F) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl
  simp only [piC, if_neg hp.ne', zero_comp, comp_zero] at h1
  exact h1

end GlobalTheory.EtC.DiscRep


open GlobalTheory.EtC.DiscRep in
theorem GlobalTheory.EtC.discRep : ∀ (R : Type) [CommRing R] (F : PSh) (I : Cx R) (n : ℤ)
    (x : CohomologyClass ((chains R).obj (disc.obj F)) I n), ∃ α : Cocycle ((chains R).obj (disc.obj F)) I n,
      CohomologyClass.mk α = x ∧ ∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0 := by
  intro R _ F I n x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  refine ⟨zcomp (Cocycle.ofHom (piZ F)) α (zero_add n), ?_, ?_⟩
  · rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨-(n.negOnePow • (Cochain.ofHomotopy (htpZ F)).comp α.1 (by omega)), ?_⟩
    rw [δ_neg, δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
    ext p q hpq
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, smul_smul]
  · intro p hp s h
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) _ _ s (add_zero _) h, piZ_f F p hp]
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem chains_quasiIso_of_sections : ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E'), (∀ U : Scheme.{0}, QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map (((SimplicialObject.whiskering _ _).obj ((evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R))).map f))) → QuasiIso ((chains R).map f) := by
  intro R _ E E' f hf
  let g := ((SimplicialObject.whiskering _ _).obj (freeP R)).map f
  let φ := (AlgebraicTopology.alternatingFaceMapComplex _).map g
  have hφ : QuasiIso φ := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro t
    have e := Arrow.isoOfNatIso (eqToIso (AlgebraicTopology.map_alternatingFaceMapComplex ((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj t))) (Arrow.mk g)
    exact (quasiIso_iff_of_arrow_mk_iso _ _ e).2 (hf t.unop)
  have e := Arrow.isoOfNatIso (eqToIso (AlgebraicTopology.map_alternatingFaceMapComplex (presheafToSheaf (Scheme.etaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))))) (Arrow.mk g)
  have h2 : QuasiIso ((chainsN R).map f) := by
    have : QuasiIso (((presheafToSheaf (Scheme.etaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex _).map φ) := inferInstance
    exact (quasiIso_iff_of_arrow_mk_iso _ _ e).1 this
  change QuasiIso (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat)
  infer_instance

end GlobalTheory.EtC
end
end

section

open Filter Topology

namespace GlobalTheory.WeilM

theorem SB.exists_periodic {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type}
    (L : ι → AddSubgroup X) (hL : ∀ i, IsOpen (L i : Set X)) (hb : ∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) :
    ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  intro f hf
  obtain ⟨hlc, hcs⟩ := hf
  have key : ∀ Y : X, ∃ i, ∀ C ∈ L i, f (Y + C) = f Y := by
    intro Y
    have h1 : f ⁻¹' {f Y} ∈ 𝓝 (Y + 0) := by rw [add_zero]; exact (hlc.isOpen_fiber _).mem_nhds rfl
    have h2 : {C : X | f (Y + C) = f Y} ∈ 𝓝 (0 : X) := (continuous_const_add Y).continuousAt.preimage_mem_nhds h1
    obtain ⟨i, hi⟩ := hb _ h2
    exact ⟨i, fun C hC => hi hC⟩
  choose g hg using key
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun Y => {Z : X | Z - Y ∈ L (g Y)})
    (fun Y => (hL _).preimage (continuous_sub_right Y))
    (fun Z _ => Set.mem_iUnion.2 ⟨Z, by simp⟩)
  have hW : (⋂ Y ∈ t, (L (g Y) : Set X)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun Y _ => (hL _).mem_nhds (L (g Y)).zero_mem
  obtain ⟨j, hj⟩ := hb _ hW
  refine ⟨j, fun Y C hC => ?_⟩
  have hCt : ∀ Y0 ∈ t, C ∈ L (g Y0) := fun Y0 h0 => by
    have := hj hC
    simp only [Set.mem_iInter] at this
    exact this Y0 h0
  by_cases h : ∃ Y0 ∈ t, Y - Y0 ∈ L (g Y0)
  · obtain ⟨Y0, h0, hY⟩ := h
    have e1 := hg Y0 _ hY
    have e2 := hg Y0 _ (add_mem hY (hCt Y0 h0))
    rw [show Y0 + (Y - Y0) = Y by abel] at e1
    rw [show Y0 + (Y - Y0 + C) = Y + C by abel] at e2
    rw [e1, e2]
  · push_neg at h
    have hn : ∀ Z, Z ∈ tsupport f → ∃ Y0 ∈ t, Z - Y0 ∈ L (g Y0) := fun Z hZ => by
      have := ht hZ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
      obtain ⟨Y0, h0, h1⟩ := this
      exact ⟨Y0, h0, h1⟩
    have hY : Y ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn Y hZ
      exact h Y0 h0 h1
    have hYC : Y + C ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn _ hZ
      apply h Y0 h0
      have := sub_mem h1 (hCt Y0 h0)
      rwa [show Y + C - Y0 - C = Y - Y0 by abel] at this
    rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYC]

end GlobalTheory.WeilM
end

section

open IsDedekindDomain

theorem _root_.GlobalTheory.T.continuous_afP_restr : ∀ (p : ℕ), Continuous (GlobalTheory.LKTrip.AfP.restr p) := by
  first | (exact @GlobalTheory.LKTrip.AfP.continuous_restr) | (exact GlobalTheory.LKTrip.AfP.continuous_restr) | (intros; apply GlobalTheory.LKTrip.AfP.continuous_restr  <;> assumption)
end
