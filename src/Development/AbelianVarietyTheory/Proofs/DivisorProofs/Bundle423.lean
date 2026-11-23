module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle365
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlargeLoc

theorem retract_localises : ∀ (T O A₁ EA₁ : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O]
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T), IsLocalHom i₁ → IsLocalHom (algebraMap T O) →
    ∀ [CommRing EA₁] [Algebra (Polynomial A₁) EA₁] [Algebra A₁ EA₁]
      (QA₁ : Ideal EA₁) [QA₁.IsPrime] (jA₁ : Localization.AtPrime QA₁ →+* O) (ρ' : EA₁ →+* A₁),
    algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ →
    ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 →
    (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
      Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) →
    (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) →
    ∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ρ₁.comp (algebraMap EA₁ (Localization.AtPrime QA₁)) = ρ' := by
  intro T O A₁ EA₁ _ _ _ _ _ _ _ i₁ hi₁ hTO _ _ _ QA₁ _ jA₁ ρ' hX hret hρX hcong hker
  set L := Localization.AtPrime QA₁
  set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X}
  have hI : I ≤ maximalIdeal O := by
    rw [Ideal.span_le]; simpa using hX
  have hunit : ∀ y : QA₁.primeCompl, IsUnit (ρ' y) := by
    intro y
    by_contra hy
    have h1 : ρ' y ∈ maximalIdeal A₁ := (mem_maximalIdeal _).2 hy
    have h2 : algebraMap T O (i₁ (ρ' y)) ∈ maximalIdeal O := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hy ((isUnit_map_iff i₁ _).1 ((isUnit_map_iff (algebraMap T O) _).1 hu))
    have h3 : jA₁ (algebraMap EA₁ L y) ∈ maximalIdeal O := by
      have := hI (hcong y)
      have := (maximalIdeal O).sub_mem h2 this
      simpa using this
    have h4 : IsUnit (jA₁ (algebraMap EA₁ L y)) :=
      (IsLocalization.map_units L y).map jA₁
    exact (mem_maximalIdeal _ |>.1 h3) h4
  let ρ₁ : L →+* A₁ := IsLocalization.lift (M := QA₁.primeCompl) hunit
  have hcomp : ρ₁.comp (algebraMap EA₁ L) = ρ' := by
    ext x; exact IsLocalization.lift_eq _ _
  refine ⟨ρ₁, ⟨?_, ?_, ?_⟩, hcomp⟩
  · rw [IsScalarTower.algebraMap_eq A₁ EA₁ L, ← RingHom.comp_assoc, hcomp, hret]
  · apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker] at hz
      obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective QA₁.primeCompl z
      dsimp only at hz ⊢
      have hx : ρ' x = 0 := by
        have := IsLocalization.lift_mk' (M := QA₁.primeCompl) (S := L) hunit x y
        change ρ₁ _ = _ at this
        rw [hz] at this
        exact (Units.mul_left_eq_zero _).1 this.symm
      obtain ⟨s, hs, hsx⟩ := hker x hx
      have hsy : s * (y : EA₁) ∈ QA₁.primeCompl := QA₁.primeCompl.mul_mem hs y.2
      have heq : IsLocalization.mk' L x y = IsLocalization.mk' L (s * x) (⟨s * y, hsy⟩ : QA₁.primeCompl) := by
        rw [IsLocalization.mk'_eq_iff_eq]
        simp only
        ring_nf
      rw [heq, IsLocalization.mk'_eq_mul_mk'_one]
      apply Ideal.mul_mem_right
      have : algebraMap EA₁ L (s * x) ∈ (Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}).map (algebraMap EA₁ L) :=
        Ideal.mem_map_of_mem _ hsx
      rwa [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply] at this
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
        IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ L]
      change (ρ₁.comp (algebraMap EA₁ L)) _ = 0
      rw [hcomp, hρX]
  · have key : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ₁)) = (Ideal.Quotient.mk I).comp jA₁ := by
      apply IsLocalization.ringHom_ext QA₁.primeCompl
      ext x
      simp only [RingHom.comp_apply]
      rw [Ideal.Quotient.eq]
      have := hcong x
      rw [← hcomp] at this
      simpa using this
    intro x
    have := congrArg (fun f => f x) key
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.1 this

end GlobalTheory.KeyOriginEnlargeLoc
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

def homShEval (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (f : X ⟶ (homSh J).obj (op M)) (m : M) : X ⟶ J :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun x => (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom m
          map_add' := fun x y => by
            rw [map_add (f.hom.app U).hom x y]; rfl
          map_smul' := fun r x => by
            rw [(f.hom.app U).hom.map_smul]; rfl }
     naturality := fun U V g => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        have h := congrArg (fun k => (show M ⟶ J.obj.obj V from k).hom m)
          (congrArg (fun k => (ModuleCat.Hom.hom k) x) (f.hom.naturality g))
        exact h }⟩

def homShCurry (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (f : X ⟶ (homSh J).obj (op M)) :
    M →ₗ[ULift.{1} R] (X ⟶ J) where
  toFun m := homShEval J X M f m
  map_add' m n := by
    apply Sheaf.hom_ext; ext U x
    exact (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom.map_add m n
  map_smul' r m := by
    apply Sheaf.hom_ext; ext U x
    exact (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom.map_smul r m

def homShUncurry (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (l : M →ₗ[ULift.{1} R] (X ⟶ J)) :
    X ⟶ (homSh J).obj (op M) :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun x => (show M ⟶ J.obj.obj U from ModuleCat.ofHom
            { toFun := fun m => ((l m).hom.app U).hom x
              map_add' := fun m n => by rw [map_add l m n]; rfl
              map_smul' := fun r m => by rw [l.map_smul]; rfl })
          map_add' := fun x y => by
            apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
            exact ((l m).hom.app U).hom.map_add x y
          map_smul' := fun r x => by
            apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
            exact ((l m).hom.app U).hom.map_smul r x }
     naturality := fun U V g => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
        exact congrArg (fun k => (ModuleCat.Hom.hom k) x) ((l m).hom.naturality g) }⟩

def homShEquiv (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) :
    (X ⟶ (homSh J).obj (op M)) ≃ (M →ₗ[ULift.{1} R] (X ⟶ J)) where
  toFun := homShCurry J X M
  invFun := homShUncurry J X M
  left_inv f := by
    apply Sheaf.hom_ext; ext U x
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
    rfl
  right_inv l := by
    apply LinearMap.ext; intro m
    apply Sheaf.hom_ext; ext U x
    rfl

theorem homShEquiv_natural_left (J X : Shv R) (M N : ModuleCat.{1} (ULift.{1} R)) (p : M ⟶ N)
    (f : X ⟶ (homSh J).obj (op N)) :
    homShEquiv J X M (f ≫ (homSh J).map p.op) = (homShEquiv J X N f) ∘ₗ p.hom := by
  apply LinearMap.ext; intro m
  apply Sheaf.hom_ext; ext U x
  rfl

theorem homShEquiv_natural_right (J X Y : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (i : X ⟶ Y)
    (f : Y ⟶ (homSh J).obj (op M)) :
    homShEquiv J X M (i ≫ f) = (Linear.leftComp (ULift.{1} R) J i) ∘ₗ (homShEquiv J Y M f) := by
  apply LinearMap.ext; intro m
  apply Sheaf.hom_ext; ext U x
  rfl

theorem homSh_curry : ∀ (R : Type) [CommRing R] (J : Shv R), ∃ e : ∀ (X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)), (X ⟶ (homSh J).obj (op M)) ≃ (M →ₗ[ULift.{1} R] (X ⟶ J)), (∀ (X : Shv R) (M N : ModuleCat.{1} (ULift.{1} R)) (p : M ⟶ N) (f : X ⟶ (homSh J).obj (op N)), e X M (f ≫ (homSh J).map p.op) = (e X N f) ∘ₗ p.hom) ∧ (∀ (X Y : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (i : X ⟶ Y) (f : Y ⟶ (homSh J).obj (op M)), e X M (i ≫ f) = (Linear.leftComp (ULift.{1} R) J i) ∘ₗ (e Y M f)) :=
  fun _ _ J => ⟨homShEquiv J, homShEquiv_natural_left J, fun X Y M i f => homShEquiv_natural_right J X Y M i f⟩

end GlobalTheory.EtC
end
end

section

open IsDedekindDomain NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchDeriv
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem archimedean_map_add (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (a + b) = GlobalTheory.WeilL2Words.arch1 F a + GlobalTheory.WeilL2Words.arch1 F b := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact map_add _ a b
  · exact (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem adeleOfMixedSpaceComponent_finsetSum (f : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (∑ k, f k) = ∑ k, GlobalTheory.WeilL2Words.arch1 F (f k) :=
  map_sum (AddMonoidHom.mk' (GlobalTheory.WeilL2Words.arch1 F) (archimedean_map_add F)) f Finset.univ

theorem adeleJoin_mul_arch1 (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) (k : κ)
    (b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilCont.adeleJoin F x y k * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (x k * b) := by
  unfold GlobalTheory.WeilL2Words.arch1 GlobalTheory.WeilCont.adeleJoin
  refine Prod.ext ?_ ?_
  · exact (map_mul _ (x k) b).symm
  · exact mul_zero (y k)

theorem adeleOfMixedSpaceComponent_mul (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F a * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (a * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact (map_mul _ a b).symm
  · exact mul_zero (0 : FiniteAdeleRing (𝓞 F) F)

theorem adeleJoin_add_arch (x v : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y + GlobalTheory.WeilL2Words.arch F v = GlobalTheory.WeilCont.adeleJoin F (x + v) y := by
  funext i
  refine Prod.ext ?_ ?_
  · exact (map_add _ (x i) (v i)).symm
  · exact add_zero (y i)

theorem adeleJoin_dot_arch (x w : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, x k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleJoin_mul_arch1 F x y k (w k)

theorem arch_dot_arch (v w : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch F v ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, v k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleOfMixedSpaceComponent_mul F (v k) (w k)

theorem mul_arch1 [Invertible (2 : AdeleRing (𝓞 F) F)] (b : mixedEmbedding.mixedSpace F) :
    ⅟(2 : AdeleRing (𝓞 F) F) * GlobalTheory.WeilL2Words.arch1 F b =
      GlobalTheory.WeilL2Words.arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · show (⅟(2 : AdeleRing (𝓞 F) F)).1 * _ = _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero _

end GlobalTheory.ArchDeriv

open GlobalTheory.ArchDeriv
namespace GlobalTheory.WeilL2Words

theorem dS_adeleJoin_eq : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      Differentiable ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.dS F ψ h Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          fderiv ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x h.1 +
            2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
  intro F _ _ _ κ _ ψ ℓ hψ Φ y hs h x
  set s : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y) with hs_def
  set P : mixedEmbedding.mixedSpace F := ∑ k, x k * h.2 k with hP
  set Q : mixedEmbedding.mixedSpace F :=
    InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * ∑ k, h.1 k * h.2 k with hQ
  set r : ℝ → ℝ := fun t => t * ℓ P + t ^ 2 * ℓ Q with hr
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
      fun t => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)) * s (x + t • h.1) := by
    funext t
    have e1 : (t • h).1 = t • h.1 := rfl
    have e2 : (t • h).2 = t • h.2 := rfl
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilL2Words.archPair, e1, e2, adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch,
      mul_arch1, ← archimedean_map_add]
    congr 1
    · rw [hψ]
      congr 2
      have q1 : (∑ k, x k * (t • h.2) k) = t • P := by
        simp only [hP, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]
      have q2 : InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 *
          ∑ k, (t • h.1) k * (t • h.2) k = t ^ 2 • Q := by
        simp only [Pi.smul_apply, smul_mul_smul_comm]
        rw [← Finset.smul_sum, mul_smul_comm, hQ, pow_two]
      rw [q1, q2, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hr' : HasDerivAt r (ℓ P) 0 := by
    have h1 := (hasDerivAt_mul_const (x := (0 : ℝ)) (ℓ P)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (ℓ Q))
    exact h1.congr_deriv (by simp)
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)))
      (Complex.exp (2 * Real.pi * Complex.I * (r 0 : ℂ)) * (2 * Real.pi * Complex.I * (ℓ P : ℂ))) 0 :=
    (hr'.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have hc : HasDerivAt (fun t : ℝ => x + t • h.1) h.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h.1).const_add x
  have hS : HasDerivAt (fun t : ℝ => s (x + t • h.1)) (fderiv ℝ s x h.1) 0 := by
    have hf : HasFDerivAt s (fderiv ℝ s x) (x + (0 : ℝ) • h.1) := by
      rw [zero_smul, add_zero]
      exact (hs x).hasFDerivAt
    exact hf.comp_hasDerivAt (0 : ℝ) hc
  have hD := hE.mul hS
  unfold GlobalTheory.WeilL2Words.dS
  rw [key]
  refine hD.deriv.trans ?_
  have r0 : r 0 = 0 := by simp [hr]
  simp only [r0, zero_smul, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  ring

end GlobalTheory.WeilL2Words

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem cochain_chains_subsingleton {R : Type} [CommRing R] (E : Spc) (I : Cx R) (hI : I.IsStrictlyGE 0) (n : ℤ)
    (hn : n < 0) : Subsingleton (Cochain ((chains R).obj E) I n) := by
  constructor
  intro a b
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : 0 < p
  · have hz : IsZero (((chains R).obj E).X p) :=
      HomologicalComplex.isZero_extend_X ((chainsN R).obj E) ComplexShape.embeddingDownNat p (fun i hi => by
        change -(i : ℤ) = p at hi
        omega)
    exact hz.eq_of_src _ _
  · have hz : IsZero (I.X q) := I.isZero_of_isStrictlyGE 0 q (by omega)
    exact hz.eq_of_tgt _ _

theorem Jcx_isStrictlyGE (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (hI : I.IsStrictlyGE 0) :
    (Jcx R q N I).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have hpre : IsZero (cotPre R q N I n) := by
    refine Functor.isZero _ (fun U => ?_)
    have h := cochain_chains_subsingleton (sch.obj U.unop ⨯ fibQ q N) I hI n hn
    letI : Subsingleton ((cotPre R q N I n).obj U) := h
    exact ModuleCat.isZero_of_subsingleton _
  exact (presheafToSheaf Scheme.etaleTopology.{0} _).map_isZero hpre

end GlobalTheory.EtC

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem comp_trivV (N : ℕ) {E E' : Spc} (f : E' ⟶ E) : f ≫ trivV N E = trivV N E' := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq rfl)

theorem hom_ext_invertibleLocus (q : ℕ) {E : Spc} (f g : E ⟶ disc.obj (invP q)) : f = g := by
  ext n U x
  exact Subsingleton.elim (α := PLift _) _ _

def toInvP (q : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) : disc.obj F ⟶ disc.obj (invP q) :=
  disc.map
    { app := fun U => TypeCat.ofHom fun x => ⟨hF U.unop ⟨x⟩⟩
      naturality := fun _ _ _ => by ext x; rfl }

def fibQ.snd (q N : ℕ) : fibQ q N ⟶ PGL N :=
  pullback.snd (trivV N (disc.obj (invP q))) (PGL.pr N)

theorem fibQ.cond (q N : ℕ) : trivV N (fibQ q N) = fibQ.snd q N ≫ PGL.pr N := by
  show trivV N (pullback (trivV N (disc.obj (invP q))) (PGL.pr N)) = pullback.snd _ _ ≫ PGL.pr N
  rw [← comp_trivV N (pullback.fst (trivV N (disc.obj (invP q))) (PGL.pr N))]
  exact pullback.condition

def fibQ.lift {q N : ℕ} {X : Spc} (a : X ⟶ disc.obj (invP q)) (b : X ⟶ PGL N) (h : trivV N X = b ≫ PGL.pr N) :
    X ⟶ fibQ q N :=
  pullback.lift a b (by rw [comp_trivV]; exact h)

@[simp] theorem fibQ.lift_snd {q N : ℕ} {X : Spc} (a : X ⟶ disc.obj (invP q)) (b : X ⟶ PGL N)
    (h : trivV N X = b ≫ PGL.pr N) : fibQ.lift a b h ≫ fibQ.snd q N = b :=
  pullback.lift_snd (f := trivV N (disc.obj (invP q))) (g := PGL.pr N) a b
    (by rw [comp_trivV]; exact h)

theorem fibQ.hom_ext {q N : ℕ} {X : Spc} {f g : X ⟶ fibQ q N} (h : f ≫ fibQ.snd q N = g ≫ fibQ.snd q N) : f = g :=
  pullback.hom_ext (hom_ext_invertibleLocus q _ _) h

theorem trivProj_iso (q N : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) :
    ∃ θ : disc.obj F ⨯ fibQ q N ≅ pullback (trivV N (disc.obj F)) (PGL.pr N),
      θ.hom ≫ pullback.fst _ _ = prod.fst ∧ θ.hom ≫ pullback.snd _ _ ≫ PGL.line N = prod.snd ≫ lineQ q N := by
  have h1 : prod.fst ≫ trivV N (disc.obj F) = (prod.snd ≫ fibQ.snd q N) ≫ PGL.pr N := by
    rw [comp_trivV, Category.assoc, ← fibQ.cond, comp_trivV]
  have h2 : trivV N (pullback (trivV N (disc.obj F)) (PGL.pr N)) = pullback.snd _ _ ≫ PGL.pr N := by
    rw [← comp_trivV N (pullback.fst (trivV N (disc.obj F)) (PGL.pr N))]
    exact pullback.condition
  let hom : disc.obj F ⨯ fibQ q N ⟶ pullback (trivV N (disc.obj F)) (PGL.pr N) :=
    pullback.lift prod.fst (prod.snd ≫ fibQ.snd q N) h1
  let inv : pullback (trivV N (disc.obj F)) (PGL.pr N) ⟶ disc.obj F ⨯ fibQ q N :=
    prod.lift (pullback.fst _ _) (fibQ.lift (pullback.fst _ _ ≫ toInvP q F hF) (pullback.snd _ _) h2)
  refine ⟨{ hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }, ?_, ?_⟩
  · apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, pullback.lift_fst, Category.id_comp]
    · apply fibQ.hom_ext
      rw [Category.assoc, Category.assoc, ← Category.assoc inv, prod.lift_snd, fibQ.lift_snd, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, prod.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, prod.lift_snd, fibQ.lift_snd, Category.id_comp]
  · exact pullback.lift_fst _ _ _
  · rw [← Category.assoc, pullback.lift_snd, Category.assoc]
    rfl

end GlobalTheory.EtC

end
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay

noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay

theorem hasDerivAt_qZ : ∀ (σ : ℂ) (a : ℤ) (b m : ℕ) (y : ℝ), y ≠ 0 → ∀ t : ℝ,
    HasDerivAt (qZ σ a b m y) (-(a : ℂ) * qZ σ (a + 1) b m y t
      + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t)) t := by
  intro σ a b m y hy t
  have hu := GlobalTheory.HeckeTwo.TermSmooth.u_ne hy t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp.add_const ((y : ℂ) * I)
  have h2 := (hasDerivAt_zpow (-a) ((t : ℂ) + (y : ℂ) * I) (Or.inl hu)).comp t h1
  have h3 : HasDerivAt (fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))) ((2 * t : ℝ) : ℂ) t := by
    have : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).add_const (y ^ 2))
    exact this.ofReal_comp
  have h4 := (Complex.hasStrictDerivAt_cpow_const (c := -σ - (b : ℂ))
      (Complex.ofReal_mem_slitPlane.2 hQ)).hasDerivAt.comp t h3
  have h := (h2.mul h4).mul_const ((y : ℂ) ^ m)
  refine h.congr_deriv ?_
  simp only [qZ, Function.comp_def]
  rw [show -(a + 1) = -a - 1 by ring, show -(a - 1) = -a + 1 by ring, zpow_add_one₀ hu,
    show -σ - ((b + 1 : ℕ) : ℂ) = -σ - (b : ℂ) - 1 by push_cast; ring]
  push_cast
  ring

end GlobalTheory.HeckeTwo.TermDecay
end
end
