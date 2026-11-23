module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SegreGlue
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.AppLEFromOfGlobalSectionsChartHom
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

instance hasFiniteBiproducts_modules (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  .of_hasFiniteProducts

variable {X : Scheme.{u}}

lemma resF_app {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) :
    resF N h (φ.app U m) = φ.app V (resF M h m) := by
  have := congrArg (fun g => g.hom m) (φ.mapPresheaf.naturality (homOfLE h).op)
  exact this.symm

section Biproduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → X.Modules)

lemma biproduct_app_eq_sum (U : X.Opens) (m : Γ(⨁ M, U)) :
    m = ∑ j, (biproduct.ι M j).app U ((biproduct.π M j).app U m) := by
  have h := congrArg (fun g : (⨁ M) ⟶ (⨁ M) => g.app U m) (biproduct.total (f := M))
  simp only [Scheme.Modules.Hom.id_app] at h
  rw [← ConcreteCategory.id_apply (X := Γ(⨁ M, U)) m]
  change _ = ∑ j, ((biproduct.π M j ≫ biproduct.ι M j).app U) m
  rw [← h]
  have : ∀ (s : Finset ι), ((∑ j ∈ s, biproduct.π M j ≫ biproduct.ι M j).app U) m =
      ∑ j ∈ s, ((biproduct.π M j ≫ biproduct.ι M j).app U) m := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
      rw [← ih]
      rfl
  exact this Finset.univ

theorem isQuasicoherent_biproduct [∀ i, (M i).IsQuasicoherent] : (⨁ M).IsQuasicoherent := by
  refine isQuasicoherent_of_affineCover _ (fun V : X.affineOpens => (V : X.Opens)) (fun V => V.2)
    (iSup_affineOpens_eq_top X) ?_ ?_
  · intro V f m
    have key : ∀ j, ∃ (e : ℕ) (m' : Γ(M j, (V : X.Opens))),
        resF (M j) (X.basicOpen_le f) m' =
          resO (X.basicOpen_le f) f ^ e • (biproduct.π M j).app _ m :=
      fun j => qcoh_exists_res_eq (M j) V.2 f _
    choose e m' hm' using key
    refine ⟨∑ j, e j, ∑ j, (biproduct.ι M j).app _ (f ^ (∑ k, e k - e j) • m' j), ?_⟩

    rw [map_sum]
    conv_rhs => rw [biproduct_app_eq_sum M _ m, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [resF_app, resF_smul, hm' j, smul_smul, map_pow, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun k _ => Nat.zero_le (e k))
        (Finset.mem_univ j)), Scheme.Modules.Hom.app_smul]
  · intro V f m hm
    have key : ∀ j, ∃ e : ℕ, f ^ e • (biproduct.π M j).app _ m = 0 := fun j => by
      refine qcoh_exists_pow_smul_eq_zero (M j) V.2 f _ ?_
      rw [resF_app, hm, map_zero]
    choose e he using key
    refine ⟨∑ j, e j, ?_⟩
    rw [biproduct_app_eq_sum M _ m, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Scheme.Modules.Hom.app_smul, ← Nat.sub_add_cancel (Finset.single_le_sum
      (fun k _ => Nat.zero_le (e k)) (Finset.mem_univ j)), pow_add, mul_smul, he j, smul_zero,
      map_zero]

end Biproduct

section Image

lemma surjective_app_of_epi {P Q : X.Modules} (e : P ⟶ Q) [Epi e] [P.IsQuasicoherent]
    [Q.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) : Function.Surjective (e.app V) := by
  have hc : IsColimit (CokernelCofork.ofπ e (kernel.condition e)) :=
    Abelian.epiIsCokernelOfKernel (KernelFork.ofι _ (kernel.condition e)) (kernelIsKernel e)
  let i : cokernel (kernel.ι e) ≅ Q := (cokernelIsCokernel (kernel.ι e)).coconePointUniqueUpToIso hc
  have hi : cokernel.π (kernel.ι e) ≫ i.hom = e :=
    (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom hc WalkingParallelPair.one
  have h1 := surjective_cokernel_π_app (kernel.ι e) hV
  rw [← hi, Scheme.Modules.Hom.comp_app]
  exact (bijective_app_of_iso i V).2.comp h1

lemma range_kernel_ι_cokernel_π_app {P G : X.Modules} (f : P ⟶ G) [P.IsQuasicoherent]
    [G.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) :
    Set.range ((kernel.ι (cokernel.π f)).app V) = Set.range (f.app V) := by
  have hfac : Abelian.factorThruImage f ≫ kernel.ι (cokernel.π f) = f := Abelian.image.fac f
  have hs := surjective_app_of_epi (Abelian.factorThruImage f) hV
  ext m
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨p, rfl⟩ := hs k
    refine ⟨p, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hfac]
  · rintro ⟨p, rfl⟩
    refine ⟨(Abelian.factorThruImage f).app V p, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hfac]

lemma mem_range_app_iff {P G : X.Modules} (f : P ⟶ G) [P.IsQuasicoherent] [G.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) (m : Γ(G, V)) :
    m ∈ Set.range (f.app V) ↔ (cokernel.π f).app V m = 0 := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition,
      Scheme.Modules.Hom.zero_app]
    rfl
  · intro hm
    obtain ⟨k, hk⟩ := kernel_ι_app_exact (cokernel.π f) V m hm
    rw [← range_kernel_ι_cokernel_π_app f hV]
    exact ⟨k, hk⟩

end Image

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

universe u

noncomputable section

namespace ProjSpace

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ} {Y : Scheme.{u}}


variable (A B n) in
def baseChangeIso :
    projectiveSpace B n ≅
      pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  (isPullback_baseChange A B n).isoPullback

lemma baseChangeIso_inv_baseChangeMap :
    (baseChangeIso A B n).inv ≫ baseChangeMap A B n = pullback.fst _ _ :=
  (isPullback_baseChange A B n).isoPullback_inv_fst

lemma baseChangeIso_inv_toSpecBase :
    (baseChangeIso A B n).inv ≫ toSpecBase B n = pullback.snd _ _ :=
  (isPullback_baseChange A B n).isoPullback_inv_snd

def toBaseChange (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    Y ⟶ projectiveSpace B n :=
  ι ≫ (baseChangeIso A B n).inv

instance (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [IsClosedImmersion ι] : IsClosedImmersion (toBaseChange ι) := by
  rw [toBaseChange]
  infer_instance

lemma toBaseChange_baseChangeMap
    (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    toBaseChange ι ≫ baseChangeMap A B n = ι ≫ pullback.fst _ _ := by
  rw [toBaseChange]
  calc
    _ = ι ≫ ((baseChangeIso A B n).inv ≫ baseChangeMap A B n) := by rw [Category.assoc]
    _ = _ := congrArg (fun f => ι ≫ f) (baseChangeIso_inv_baseChangeMap (A := A) (B := B) (n := n))

lemma toBaseChange_toSpecBase
    (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    toBaseChange ι ≫ toSpecBase B n = ι ≫ pullback.snd _ _ := by
  rw [toBaseChange]
  calc
    _ = ι ≫ ((baseChangeIso A B n).inv ≫ toSpecBase B n) := by rw [Category.assoc]
    _ = _ := congrArg (fun f => ι ≫ f) (baseChangeIso_inv_toSpecBase (A := A) (B := B) (n := n))


variable (A) in
def twistingSheafBaseChangeIso (g : Y ⟶ projectiveSpace B n) (k : ℤ) :
    ProjScheme.twistingSheaf (g ≫ baseChangeMap A B n) k ≅ ProjScheme.twistingSheaf g k :=
  ((Scheme.Modules.pullbackComp g (baseChangeMap A B n)).app _).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (pullbackTwistingSheafIso A B n k)


variable (A) in
def twistBaseChangeIso (g : Y ⟶ projectiveSpace B n) (F : Y.Modules) (k : ℤ) :
    ProjScheme.twist (g ≫ baseChangeMap A B n) F k ≅ ProjScheme.twist g F k :=
  whiskerLeftIso F (twistingSheafBaseChangeIso A g k)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace ProjSpace

variable (A : Type u) [CommRing A]

def multiProjDim : (k : ℕ) → (Fin (k + 1) → ℕ) → ℕ
  | 0, n => n 0
  | k + 1, n => n 0 * multiProjDim k (Fin.tail n) + n 0 + multiProjDim k (Fin.tail n)

def multiProjEmbOverBase : (k : ℕ) → (n : Fin (k + 1) → ℕ) →
    {e : MP A k n ⟶ projectiveSpace A (multiProjDim k n) //
      e ≫ toSpecBase A (multiProjDim k n) = mpStr A k n}
  | 0, _ => ⟨𝟙 _, Category.id_comp _⟩
  | k + 1, n =>
    let e' := multiProjEmbOverBase k (Fin.tail n)
    ⟨pullback.map (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) (toSpecBase A (n 0))
        (toSpecBase A (multiProjDim k (Fin.tail n))) (𝟙 _) e'.1 (𝟙 _) (by simp) (by simp [e'.2]) ≫
      segre A (n 0) (multiProjDim k (Fin.tail n)), by
      change (_ ≫ segre A (n 0) (multiProjDim k (Fin.tail n))) ≫ toSpecBase A
          (n 0 * multiProjDim k (Fin.tail n) + n 0 + multiProjDim k (Fin.tail n)) =
        pullback.fst (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) ≫ toSpecBase A (n 0)
      rw [Category.assoc, segre_toSpecBase, pullback.lift_fst_assoc, Category.comp_id]⟩

def multiProjEmb (k : ℕ) (n : Fin (k + 1) → ℕ) :
    MP A k n ⟶ projectiveSpace A (multiProjDim k n) :=
  (multiProjEmbOverBase A k n).1

lemma multiProjEmb_toSpecBase (k : ℕ) (n : Fin (k + 1) → ℕ) :
    multiProjEmb A k n ≫ toSpecBase A (multiProjDim k n) = mpStr A k n :=
  (multiProjEmbOverBase A k n).2

instance isClosedImmersion_multiProjEmb :
    (k : ℕ) → (n : Fin (k + 1) → ℕ) → IsClosedImmersion (multiProjEmb A k n)
  | 0, _ => by
    change IsClosedImmersion (𝟙 _)
    infer_instance
  | k + 1, n => by
    have ih := isClosedImmersion_multiProjEmb k (Fin.tail n)
    have hpb : IsPullback
        (pullback.map (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) (toSpecBase A (n 0))
          (toSpecBase A (multiProjDim k (Fin.tail n))) (𝟙 _) (multiProjEmb A k (Fin.tail n)) (𝟙 _)
          (by simp) (by rw [Category.comp_id, multiProjEmb_toSpecBase]))
        (pullback.snd _ _) (pullback.snd _ _) (multiProjEmb A k (Fin.tail n)) := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
      have h1 : pullback.map (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) (toSpecBase A (n 0))
          (toSpecBase A (multiProjDim k (Fin.tail n))) (𝟙 _) (multiProjEmb A k (Fin.tail n))
          (𝟙 _) (by simp) (by rw [Category.comp_id, multiProjEmb_toSpecBase]) ≫ pullback.fst _ _ =
          pullback.fst _ _ := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      rw [h1, multiProjEmb_toSpecBase]
      exact IsPullback.of_hasPullback _ _
    have : IsClosedImmersion (pullback.map (toSpecBase A (n 0)) (mpStr A k (Fin.tail n))
        (toSpecBase A (n 0)) (toSpecBase A (multiProjDim k (Fin.tail n))) (𝟙 _)
        (multiProjEmb A k (Fin.tail n)) (𝟙 _) (by simp)
        (by rw [Category.comp_id, multiProjEmb_toSpecBase])) :=
      MorphismProperty.of_isPullback hpb.flip ih
    exact @IsClosedImmersion.comp _ _ _ _ (segre A (n 0) (multiProjDim k (Fin.tail n))) this
      inferInstance

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end
