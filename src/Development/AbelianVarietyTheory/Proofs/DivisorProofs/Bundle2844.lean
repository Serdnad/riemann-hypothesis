module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem fixed_mem_range : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ), IsGal ρ → ∀ y : FractionRing R', (∀ σ : Gal ρ, fracAut σ.1 y = y) →
    y ∈ (fracMap ρ hρ).range := by
  classical
  intro R R' _ _ _ _ ρ hρ hG y hy
  obtain ⟨hfin, hinv⟩ := hG
  letI : Fintype (Gal ρ) := Fintype.ofFinite _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R') y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set P : R' := ∏ σ ∈ (Finset.univ : Finset (Gal ρ)).erase 1, σ.1 b with hP
  set N : R' := ∏ σ : Gal ρ, σ.1 b with hN
  have hNP : N = b * P := by
    rw [hN, hP, ← Finset.mul_prod_erase Finset.univ (fun σ : Gal ρ => σ.1 b) (Finset.mem_univ 1)]
    rfl
  have hσ0 : ∀ σ : Gal ρ, σ.1 b ≠ 0 := fun σ => (map_ne_zero_iff σ.1 σ.1.injective).2 hb0
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  have hNfix : ∀ τ ∈ Gal ρ, τ N = N := by
    intro τ hτ
    rw [hN, map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : Gal ρ)) _ _ (fun σ => rfl)
  obtain ⟨n, hn⟩ := hinv N hNfix
  have inj := IsFractionRing.injective R' (FractionRing R')
  have hPK : algebraMap R' (FractionRing R') P ≠ 0 := (map_ne_zero_iff _ inj).2 hP0
  have hNK : algebraMap R' (FractionRing R') N ≠ 0 := (map_ne_zero_iff _ inj).2 hN0
  have hy' : algebraMap R' (FractionRing R') a / algebraMap R' (FractionRing R') b
      = algebraMap R' (FractionRing R') (a * P) / algebraMap R' (FractionRing R') N := by
    rw [hNP, map_mul, map_mul, mul_div_mul_right _ _ hPK]
  have hcfix : ∀ τ ∈ Gal ρ, τ (a * P) = a * P := by
    intro τ hτ
    apply inj
    have hyN : algebraMap R' (FractionRing R') (a * P)
        = (algebraMap R' (FractionRing R') a / algebraMap R' (FractionRing R') b) * algebraMap R' (FractionRing R') N := by
      rw [hy', div_mul_cancel₀ _ hNK]
    rw [← fracAut_algebraMap, hyN, map_mul, hy ⟨τ, hτ⟩, fracAut_algebraMap, hNfix τ hτ]
  obtain ⟨m, hm⟩ := hinv (a * P) hcfix
  refine ⟨algebraMap R (FractionRing R) m / algebraMap R (FractionRing R) n, ?_⟩
  rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, hm, hn, hy']

end GlobalTheory.Mum.GenDesc
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem exists_inv (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (D : DegData R (maximalIdeal R))
    (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
    (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U')
    (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    (∀ σ, a.act σ ≫ β = β) → ∀ σ : Gal ρ, ∃ ψ : pullback G'.hom (jK R') ⟶ pullback G'.hom (jK R'),
      ψ ≫ genMap hρ β hβ = genMap hρ β hβ ∧
      ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom ∧
      LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) ((U'.LG.L.pull (pullback.fst G'.hom (jK R'))).pull ψ) := by
  intro hinv σ
  have h₁ : G'.hom ≫ spMap (Gal.hom σ) = a.act σ ≫ G'.hom := ((a.cart σ).1.w).symm
  have h₂ : jK R' ≫ spMap (Gal.hom σ) = spMap (fracAut σ.1).toRingHom ≫ jK R' := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (fracAut_algebraMap σ.1 x).symm
  let ψ := pullback.map G'.hom (jK R') G'.hom (jK R') (a.act σ) (spMap (fracAut σ.1).toRingHom) (spMap (Gal.hom σ)) h₁ h₂
  have hψ₁ : ψ ≫ pullback.fst G'.hom (jK R') = pullback.fst G'.hom (jK R') ≫ a.act σ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom :=
    pullback.lift_snd _ _ _
  have hfr : spMap (fracAut σ.1).toRingHom ≫ spMap (fracMap ρ hρ) = spMap (fracMap ρ hρ) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact fracAut_fracMap hρ σ x
  refine ⟨ψ, ?_, hψ₂, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, genMap_fst, ← Category.assoc, hψ₁, Category.assoc, hinv σ]
    · rw [Category.assoc, genMap_snd, ← Category.assoc, hψ₂, Category.assoc, hfr]
  · obtain ⟨h, bc, hbc, hU, -⟩ := a.unif σ
    obtain ⟨wL, hwL, -⟩ := hU.lg
    have hL : LBIso U'.LG.L (U'.LG.L.pull (a.act σ)) := by
      rw [← hbc]
      exact ⟨wL, hwL⟩
    have hL₀ := U'.LG.isLB
    refine LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL₀ _) (pull_isLB (pull_isLB hL₀ _) _)
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL (pullback.fst G'.hom (jK R')) rfl) ?_
    exact GlobalTheory.GenSpread.lbIso_pull_pull hL₀ ψ hψ₁.symm

end GlobalTheory.Mum.GenDesc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.InvAlg

open TensorProduct

def galDiff (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] :
    R' →ₗ[R] (GlobalTheory.Mum.Gal (algebraMap R R') → R') :=
  LinearMap.pi fun σ => (galAlg σ).toLinearMap - LinearMap.id

theorem galDiff_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (x : R')
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) : galDiff R R' x σ = σ.1 x - x := rfl

theorem flat_tensor_invariants (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] [Algebra R O]
    [Module.Flat R O] :
    Function.Injective (algebraMap R R') → GlobalTheory.Mum.IsGal (algebraMap R R') →
    Function.Injective (algebraMap O (TensorProduct R O R')) ∧
    ∀ t : TensorProduct R O R', (∀ σ, GlobalTheory.InvAlg.galTensor O σ t = t) →
      t ∈ Set.range (algebraMap O (TensorProduct R O R')) := by
  intro hinj hgal
  classical
  haveI : Finite (GlobalTheory.Mum.Gal (algebraMap R R')) := hgal.1
  haveI : Fintype (GlobalTheory.Mum.Gal (algebraMap R R')) := Fintype.ofFinite _
  let incl : R →ₗ[R] R' := Algebra.linearMap R R'
  have hex : Function.Exact incl (galDiff R R') := by
    intro y
    constructor
    · intro hy
      obtain ⟨r, hr⟩ := hgal.2 y (fun σ hσ => by
        have := congrFun hy ⟨σ, hσ⟩
        rw [galDiff_apply] at this
        simpa [sub_eq_zero] using this)
      exact ⟨r, hr⟩
    · rintro ⟨r, rfl⟩
      funext σ
      simp [incl, galDiff_apply, σ.2 r]
  have hmap : ∀ x : O, LinearMap.lTensor O incl ((TensorProduct.rid R O).symm x) =
      algebraMap O (TensorProduct R O R') x := by
    intro x
    simp [incl, Algebra.TensorProduct.algebraMap_apply]
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [← hmap, ← hmap] at hab
    exact (TensorProduct.rid R O).symm.injective
      (Module.Flat.lTensor_preserves_injective_linearMap incl hinj hab)
  · intro t ht
    have hcomp : ∀ u : TensorProduct R O R', ∀ σ,
        TensorProduct.piRight R R O (fun _ : GlobalTheory.Mum.Gal (algebraMap R R') => R')
          (LinearMap.lTensor O (galDiff R R') u) σ = galTensor O σ u - u := by
      intro u σ
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        rw [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
        show x ⊗ₜ[R] galDiff R R' y σ = _
        rw [galDiff_apply, galTensor_tmul, TensorProduct.tmul_sub]
      | add u v hu hv =>
        rw [map_add (f := _), map_add (f := _), Pi.add_apply, hu, hv, map_add (f := _)]
        abel
    have h0 : LinearMap.lTensor O (galDiff R R') t = 0 := by
      apply (TensorProduct.piRight R R O (fun _ : GlobalTheory.Mum.Gal (algebraMap R R') => R')).injective
      funext σ
      rw [hcomp, ht σ, sub_self, map_zero, Pi.zero_apply]
    obtain ⟨y, hy⟩ := (Module.Flat.lTensor_exact O hex t).1 h0
    refine ⟨TensorProduct.rid R O y, ?_⟩
    rw [← hmap, LinearEquiv.symm_apply_apply, hy]

end GlobalTheory.InvAlg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.InvAlg

section CompletionTransfer

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

theorem pow_smul_top_eq_restrictScalars (n : ℕ) :
    (J ^ n • ⊤ : Submodule A B) =
      ((J.map (algebraMap A B)) ^ n • ⊤ : Submodule B B).restrictScalars A := by
  rw [Ideal.smul_top_eq_map, Ideal.map_pow]
  ext x
  simp [smul_eq_mul, Ideal.mul_top]

def levelEquiv (n : ℕ) :
    (B ⧸ (J ^ n • ⊤ : Submodule A B)) ≃ₗ[A] (B ⧸ ((J.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) :=
  (Submodule.quotEquivOfEq _ _ (pow_smul_top_eq_restrictScalars J n)).trans
    (Submodule.Quotient.restrictScalarsEquiv A _)

theorem levelEquiv_transitionMap {m n : ℕ} (hmn : m ≤ n) (q : B ⧸ (J ^ n • ⊤ : Submodule A B)) :
    levelEquiv J m (AdicCompletion.transitionMap J B hmn q) =
      AdicCompletion.transitionMap (J.map (algebraMap A B)) B hmn (levelEquiv J n q) := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

def complEquivFun (x : AdicCompletion J B) : AdicCompletion (J.map (algebraMap A B)) B :=
  ⟨fun n => levelEquiv J n (x.val n), fun {m n} hmn => by
    rw [← levelEquiv_transitionMap, x.property hmn]⟩

theorem complEquivFun_val (x : AdicCompletion J B) (n : ℕ) :
    (complEquivFun J x).val n = levelEquiv J n (x.val n) := rfl

theorem complEquivFun_injective : Function.Injective (complEquivFun (B := B) J) := by
  intro x y h
  refine AdicCompletion.ext fun n => (levelEquiv J n).injective ?_
  have := congrArg (fun z : AdicCompletion (J.map (algebraMap A B)) B => z.val n) h
  simpa only [complEquivFun_val] using this

theorem complEquivFun_surjective : Function.Surjective (complEquivFun (B := B) J) := by
  intro z
  refine ⟨⟨fun n => (levelEquiv J n).symm (z.val n), fun {m n} hmn => ?_⟩, ?_⟩
  · apply (levelEquiv J m).injective
    rw [levelEquiv_transitionMap, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact z.property hmn
  · refine AdicCompletion.ext fun n => ?_
    exact LinearEquiv.apply_symm_apply (levelEquiv J n) (z.val n)

end CompletionTransfer

theorem val_eq_mk_of_evalₐ {R : Type} [CommRing R] (I : Ideal R) (y : AdicCompletion I R) (n : ℕ) (b : R)
    (h : AdicCompletion.evalₐ I n y = Ideal.Quotient.mk _ b) :
    y.val n = Submodule.Quotient.mk b := by
  have hle : I ^ n ≤ (I ^ n • ⊤ : Ideal R) := by rw [smul_eq_mul, Ideal.mul_top]
  rw [← AdicCompletion.eval_apply, ← AdicCompletion.factor_evalₐ_eq_eval I y hle, h]
  rfl

theorem evalₐ_eq_mk_of_val {R : Type} [CommRing R] (I : Ideal R) (y : AdicCompletion I R) (n : ℕ) (b : R)
    (h : y.val n = Submodule.Quotient.mk b) :
    AdicCompletion.evalₐ I n y = Ideal.Quotient.mk _ b := by
  have hle : (I ^ n • ⊤ : Ideal R) ≤ I ^ n := by rw [smul_eq_mul, Ideal.mul_top]
  rw [← AdicCompletion.factor_eval_eq_evalₐ I y hle, AdicCompletion.eval_apply, h]
  rfl

theorem cmap_transfer : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A) (Γ : Type) (g : Γ → (B →ₐ[A] B)),
    Function.Injective (AdicCompletion.map J (Algebra.linearMap A B)) →
    (∀ y, y ∈ LinearMap.range (AdicCompletion.map J (Algebra.linearMap A B)) ↔
      ∀ σ, AdicCompletion.map J (g σ).toLinearMap y = y) →
    Function.Injective (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ∧
    ∀ y, y ∈ Set.range (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ↔
      ∀ σ, GlobalTheory.InvAlg.cmap (g σ).toRingHom (J.map (algebraMap A B)) (J.map (algebraMap A B))
        (GlobalTheory.InvAlg.map_algebraMap_le (g σ) J) y = y := by
  intro A B _ _ _ J Γ g hinj hrange
  have h1 : ∀ x, complEquivFun J (AdicCompletion.map J (Algebra.linearMap A B) x) =
      cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl x := by
    intro x
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [complEquivFun_val, AdicCompletion.map_val_apply, ← ha]
    symm
    apply val_eq_mk_of_evalₐ
    rw [evalₐ_cmap, evalₐ_eq_mk_of_val J x n a ha.symm, Ideal.quotientMap_mk]
    rfl
  have h2 : ∀ σ z, complEquivFun J (AdicCompletion.map J (g σ).toLinearMap z) =
      cmap (g σ).toRingHom (J.map (algebraMap A B)) (J.map (algebraMap A B))
        (map_algebraMap_le (g σ) J) (complEquivFun J z) := by
    intro σ z
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (z.val n)
    rw [complEquivFun_val, AdicCompletion.map_val_apply, ← hb]
    symm
    apply val_eq_mk_of_evalₐ
    refine (evalₐ_cmap _ _ _ _ n _).trans ?_
    rw [evalₐ_eq_mk_of_val _ (complEquivFun J z) n b
      (by rw [complEquivFun_val, ← hb]; rfl), Ideal.quotientMap_mk]
    rfl
  refine ⟨fun x y hxy => hinj (complEquivFun_injective J (by rw [h1, h1, hxy])), fun y => ?_⟩
  obtain ⟨z, rfl⟩ := complEquivFun_surjective J y
  constructor
  · rintro ⟨x, hx⟩ σ
    have hz : z ∈ LinearMap.range (AdicCompletion.map J (Algebra.linearMap A B)) :=
      ⟨x, complEquivFun_injective J (by rw [h1, hx])⟩
    rw [← h2, (hrange z).1 hz σ]
  · intro h
    obtain ⟨x, hx⟩ := (hrange z).2 fun σ => complEquivFun_injective J (by rw [h2, h σ])
    exact ⟨x, by rw [← h1, hx]⟩

end GlobalTheory.InvAlg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem rosati_of_quasiInv_root : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ a : D.O, LBIso (P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left) (P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq P' hP' _ hIso act' hact a
  obtain ⟨e, rfl⟩ := hc
  have hpos : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hunit : IsUnit ((p ^ e : ℕ) : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [← Nat.cast_pow, map_natCast] at this
  obtain ⟨hL', r₁, r₂⟩ := hP'
  haveI := act'.hom a
  haveI := act'.hom (D.star a).unop
  have e₁ : Hecke.sq2 ψ ≫ (lift (fst B B ≫ act'.act a) (snd B B)).left =
      (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left ≫ Hecke.sq2 ψ := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have e₂ : Hecke.sq2 ψ ≫ (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left =
      (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left ≫ Hecke.sq2 ψ := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have u₁ : (lift (1 : B ⟶ B) (𝟙 B)).left ≫ (lift (fst B B ≫ act'.act a) (snd B B)).left =
      𝟙 _ ≫ (lift (1 : B ⟶ B) (𝟙 B)).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have u₂ : (lift (𝟙 B) (1 : B ⟶ B)).left ≫ (lift (fst B B ≫ act'.act a) (snd B B)).left =
      (act'.act a).left ≫ (lift (𝟙 B) (1 : B ⟶ B)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₁ : (lift (1 : B ⟶ B) (𝟙 B)).left ≫ (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left =
      (act'.act (D.star a).unop).left ≫ (lift (1 : B ⟶ B) (𝟙 B)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₂ : (lift (𝟙 B) (1 : B ⟶ B)).left ≫ (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left =
      𝟙 _ ≫ (lift (𝟙 B) (1 : B ⟶ B)).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hL := o.isLB
  have hX₁ : ((P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left).pull (Hecke.sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hL' _) _
  have hX₂ : ((P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left).pull (Hecke.sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hL' _) _
  have hL₁ : (Hecke.lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left) (p ^ e)).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have hL₂ : (Hecke.lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left) (p ^ e)).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have I₁ : LBIso (Hecke.lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left) (p ^ e))
      ((P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left).pull (Hecke.sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => Hecke.sq2 ψ) (fun _ => Hecke.sq2 ψ) (fun _ => 1) _ (fun _ => e₁)) hIso
  have I₂ : LBIso (Hecke.lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left) (p ^ e))
      ((P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left).pull (Hecke.sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => Hecke.sq2 ψ) (fun _ => Hecke.sq2 ψ) (fun _ => 1) _ (fun _ => e₂)) hIso
  have Rm : LBIso (Hecke.lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left) (p ^ e))
      (Hecke.lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left) (p ^ e)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb (o.rosati a) _ _
  have hsq := LBIso.trans hX₁ hL₁ hX₂ I₁.symm (LBIso.trans hL₁ hL₂ hX₂ Rm I₂)
  obtain ⟨t₁, ht₁⟩ := r₁
  obtain ⟨t₂, ht₂⟩ := r₂
  have A₁ : IsAxesTriv B (P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left) :=
    ⟨pull_isLB hL' _,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₁)) t₁ ht₁,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₂)) t₂ ht₂⟩
  have A₂ : IsAxesTriv B (P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left) :=
    ⟨pull_isLB hL' _,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₁)) t₁ ht₁,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₂)) t₂ ht₂⟩
  exact GlobalTheory.QuasiInvPull.lbIso_of_pullback_quasiInverseIsogeny_trivial_axes Y o.A B (p ^ e) ψ ψ' _ _ hB hpos hunit hq A₁ A₂ hsq

end GlobalTheory.UPel.HT.ES
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem over₀_onTorus_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), (∀ b b' : D₁.toPre.P.A ⟶ D₂.toPre.P.A, Over₀ U₁ U₂ a b → Over₀ U₁ U₂ a b' → b = b') ∧ ∀ h h' : D₂.toPre.X → D₁.toPre.X, OnTorus U₁ U₂ a h → OnTorus U₁ U₂ a h' → h = h' := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a
  refine ⟨fun b b' hb hb' => ?_, fun h h' hh hh' => ?_⟩
  · obtain ⟨_, -, -, _⟩ := hR
    have := D₁.toPre.P.isAb.smooth
    have := D₁.toPre.P.isAb.geomConnected
    have := D₁.toPre.P.isAb.proper
    have := D₂.toPre.P.isAb.proper
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I) D₁.toPre.P.A).2 _ b b'
      fun e => ?_
    have := (U₁.gt e).q_flat
    have := (U₁.gt e).q_surj
    have := (U₁.gt e).q_affine
    have := FlatQuotient.epi_of_flat_surjective (U₁.gt e).q
    have k := congrArg (fun q => q.left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e))
      ((cancel_epi _).1 ((hb e).symm.trans (hb' e)))
    exact (pullback.lift_fst _ _ _).symm.trans (k.trans (pullback.lift_fst _ _ _))
  · have := hR.2.2.2
    have := EndTorus.connectedSpace_thickening I 0
    have : Mono (U₂.gt 0).i := by
      have : Mono (η[thickObj R I 0 D₂.toPre.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
      exact (MorphismProperty.monomorphisms _).of_isPullback (U₂.gt 0).isKernel.flip (.infer_property _)
    obtain ⟨t, ht, e⟩ := hh 0
    obtain ⟨t', ht', e'⟩ := hh' 0
    obtain rfl : t = t' := (cancel_mono _).1 (e.symm.trans e')
    funext χ
    exact SplitTorusHom.charUnit_injective (S := Sp (R ⧸ I ^ (0 + 1)))
      (congrArg Units.val ((ht χ).symm.trans (ht' χ)))

end GlobalTheory.Mum.Two
end
end
