module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle841
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle830
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
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerFlat

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (Z : Type) [AddCommGroup Z] [Module R Z] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (Z' : Type) [AddCommGroup Z'] [Module R' Z'] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M') (fN : N →ₛₗ[algebraMap R R'] N'), Function.Injective i → Function.Exact i d → Function.Injective i' → Function.Exact i' d' → (∀ z, i' (fZ z) = fM (i z)) → (∀ x, d' (fM x) = fN (d x)) → Function.Bijective (liftSemi fM) → Function.Injective (liftSemi fN) → Function.Bijective (liftSemi fZ) := by
  intro R R' _ _ _ _ Z _ _ M _ _ N _ _ Z' _ _ M' _ _ N' _ _ i d i' d' fZ fM fN hi hid hi' hid' ci cd hM hN
  have c1 : ∀ x : R' ⊗[R] Z, i' (liftSemi fZ x) = liftSemi fM (LinearMap.lTensor R' i x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r z => simp only [liftSemi_tmul, LinearMap.lTensor_tmul, map_smul, ci]
  have c2 : ∀ x : R' ⊗[R] M, d' (liftSemi fM x) = liftSemi fN (LinearMap.lTensor R' d x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r m => simp only [liftSemi_tmul, LinearMap.lTensor_tmul, map_smul, cd]
  have hiB : Function.Injective (LinearMap.lTensor R' i) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hex : Function.Exact (LinearMap.lTensor R' i) (LinearMap.lTensor R' d) :=
    Module.Flat.lTensor_exact R' hid
  refine ⟨fun x y hxy => hiB (hM.1 ?_), fun z' => ?_⟩
  · rw [← c1, ← c1, hxy]
  · obtain ⟨y, hy⟩ := hM.2 (i' z')
    have h0 : LinearMap.lTensor R' d y = 0 := by
      apply hN
      rw [← c2, hy, map_zero]
      exact (hid' (i' z')).2 ⟨z', rfl⟩
    obtain ⟨x, rfl⟩ := (hex y).1 h0
    exact ⟨x, hi' (by rw [c1, hy])⟩

end GlobalTheory.KerFlat
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.BaseChangeIso

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ e e' f g he he' hc
  have key : (e' ∘ liftSemi f) = (liftSemi g ∘ e.baseChange R') := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m => simp [liftSemi_tmul, LinearMap.baseChange_tmul, hc]
    | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  have hb : Function.Bijective (e.baseChange R') := by
    have h := ((LinearEquiv.ofBijective e he).baseChange R R' M N).bijective
    convert h using 1
    refine congrArg DFunLike.coe ?_
    ext m
    simp
  rw [← Function.Bijective.of_comp_iff' he' (liftSemi f), key, Function.Bijective.of_comp_iff _ hb]

end GlobalTheory.Div.BaseChangeIso
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BaseChangeIso

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ e e' f g he he' h
  have hsq : ∀ x : R' ⊗[R] M, e' (liftSemi f x) = liftSemi g (e.lTensor R' x) := by
    intro x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r m => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, h]
  have hb : Function.Bijective (e.lTensor R') := by
    have := (TensorProduct.congr (LinearEquiv.refl R R') (LinearEquiv.ofBijective e he)).bijective
    convert this using 1
    funext x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r m => rfl
  have hcomp : (⇑e') ∘ (⇑(liftSemi f)) = (⇑(liftSemi g)) ∘ (⇑(e.lTensor R')) := funext hsq
  constructor
  · intro hf
    have h1 : Function.Bijective ((⇑e') ∘ (⇑(liftSemi f))) := he'.comp hf
    rw [hcomp] at h1
    exact (Function.Bijective.of_comp_iff _ hb).mp h1
  · intro hg
    have h1 : Function.Bijective ((⇑(liftSemi g)) ∘ (⇑(e.lTensor R'))) := hg.comp hb
    rw [← hcomp] at h1
    exact (Function.Bijective.of_comp_iff' he' _).mp h1

end GlobalTheory.BaseChangeIso
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_prod_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (f : M →ₛₗ[algebraMap R R'] M') (f' : N →ₛₗ[algebraMap R R'] N') (g : (M × N) →ₛₗ[algebraMap R R'] (M' × N')), (∀ x, g x = (f x.1, f' x.2)) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi f') → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ f f' g hg hf hf'
  have key : ∀ y, liftSemi g y =
      (liftSemi f (TensorProduct.prodRight R R' R' M N y).1,
        liftSemi f' (TensorProduct.prodRight R R' R' M N y).2) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp; rfl
    | tmul x c => simp [liftSemi_tmul, hg]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _)]; ext <;> simp
  have e : ⇑(liftSemi g) = Prod.map (liftSemi f) (liftSemi f') ∘ (TensorProduct.prodRight R R' R' M N) :=
    funext key
  rw [e]
  exact (hf.prodMap hf').comp (TensorProduct.prodRight R R' R' M N).bijective

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_bijective_of_exact_cokernel : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (N : Type) [AddCommGroup N] [Module R N] (Z : Type) [AddCommGroup Z] [Module R Z] (Q : Type) [AddCommGroup Q] [Module R Q] (N' : Type) [AddCommGroup N'] [Module R' N'] (Z' : Type) [AddCommGroup Z'] [Module R' Z'] (Q' : Type) [AddCommGroup Q'] [Module R' Q'] (d : N →ₗ[R] Z) (p : Z →ₗ[R] Q) (d' : N' →ₗ[R'] Z') (p' : Z' →ₗ[R'] Q') (fN : N →ₛₗ[algebraMap R R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fQ : Q →ₛₗ[algebraMap R R'] Q'), Function.Exact d p → Function.Surjective p → Function.Exact d' p' → Function.Surjective p' → (∀ x, d' (fN x) = fZ (d x)) → (∀ z, p' (fZ z) = fQ (p z)) → Function.Surjective (liftSemi fN) → Function.Bijective (liftSemi fZ) → Function.Bijective (liftSemi fQ) := by
  intro R R' _ _ _ N _ _ Z _ _ Q _ _ N' _ _ Z' _ _ Q' _ _ d p d' p' fN fZ fQ hdp hp hdp' hp' sN sZ hN hZ
  have sqN : ∀ x, liftSemi fZ (d.lTensor R' x) = d' (liftSemi fN x) := by
    intro x
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sN]
  have sqZ : ∀ z, liftSemi fQ (p.lTensor R' z) = p' (liftSemi fZ z) := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sZ]
  have ex : Function.Exact (d.lTensor R') (p.lTensor R') := lTensor_exact R' hdp hp
  have ps : Function.Surjective (p.lTensor R') := LinearMap.lTensor_surjective R' hp
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := ps y
    rw [sqZ] at hy
    obtain ⟨x', hx'⟩ := (hdp' (liftSemi fZ z)).1 hy
    obtain ⟨x, rfl⟩ := hN x'
    have : d.lTensor R' x = z := hZ.1 (by rw [sqN, hx'])
    rw [← this]
    exact (ex _).2 ⟨x, rfl⟩
  · intro q'
    obtain ⟨z', rfl⟩ := hp' q'
    obtain ⟨z, rfl⟩ := hZ.2 z'
    exact ⟨p.lTensor R' z, sqZ z⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pi_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (J : Type) [Finite J] (M M' : J → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i) (g : (∀ i, M i) →ₛₗ[algebraMap R R'] (∀ i, M' i)), (∀ x i, g x i = f i (x i)) → (∀ i, Function.Bijective (liftSemi (f i))) → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ J _ M M' _ _ _ _ f g hg hf
  classical
  haveI := Fintype.ofFinite J
  have key : ∀ y : R' ⊗[R] (∀ i, M i),
      liftSemi g y = Pi.map (fun i => liftSemi (f i)) (TensorProduct.piRight R R' R' M y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => funext i; simp [Pi.map]
    | tmul x m =>
      funext i
      simp [liftSemi_tmul, hg, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]; funext i; simp
  have : (liftSemi g : R' ⊗[R] (∀ i, M i) → ∀ i, M' i)
      = Pi.map (fun i => liftSemi (f i)) ∘ (TensorProduct.piRight R R' R' M) := funext key
  rw [this]
  exact (Function.Bijective.piMap hf).comp (TensorProduct.piRight R R' R' M).bijective

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem isKSValue_act : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (a' : OAct O A'), (∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left) → ∀ (z : O) {f : HdR A} {w : epsR R ⟶ A}, IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z) := by
  intro R _ A _ A' _ i h O _ a a' hi z f w hf
  haveI := a.hom z
  haveI := a'.hom z
  obtain ⟨k, ⟨d, hd, e⟩, l⟩ := hf
  rw [act_apply]
  have hm := push_mem_liftFil (epsDP R) h h (a.act z) (a'.act z) (e := (hi z).symm) hd
  have hl := l.push (a.act z)
  refine ⟨push (dp0 R) (𝟙 _) (a.act z) k, ⟨_, hm, fun c ↦ ?_⟩, hl⟩
  have kk : GrpMor (dp0 R) (𝟙 _) A (epsDP R) (DeRham.epsRed R) A
      (algebraMap R (DualNumber R)) (𝟙 _) (a.act z).left :=
    ⟨(constMor A).dp, (constMor A).base, by simpa using (Over.w (a.act z)),
      (homMor (dp0 R) (𝟙 _) (a.act z)).mul⟩
  have hM := homMor (epsDP R) (DeRham.epsRed R) (a.act z)
  have e1 := GrpMor.pull_pull (constMor A) hM kk (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (a.act z)) (constMor A) kk (fun _ ↦ rfl) rfl c
  rw [push_apply]
  change d (hM.pull ((constMor A).pull c)) = _
  rw [e1, ← e2, e]
  rfl
end GlobalTheory.KSExist
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatKerLarge

theorem liftSemi_bijective_of_exact {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    [Module.Flat R R'] {Z M N Z' M' N' : Type*}
    [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Z'] [Module R' Z'] [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']
    (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N')
    (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M')
    (fN : N →ₛₗ[algebraMap R R'] N')
    (hi : Function.Injective i) (hid : Function.Exact i d) (hi' : Function.Injective i')
    (hid' : Function.Exact i' d') (hZ : ∀ z, i' (fZ z) = fM (i z)) (hN : ∀ x, d' (fM x) = fN (d x))
    (hM : Function.Bijective (liftSemi fM)) (hNi : Function.Injective (liftSemi fN)) :
    Function.Bijective (liftSemi fZ) := by
  have sqZ : ∀ w, i' (liftSemi fZ w) = liftSemi fM (i.lTensor R' w) := fun w ↦ by
    induction w with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, hZ]
  have sqN : ∀ w, d' (liftSemi fM w) = liftSemi fN (d.lTensor R' w) := fun w ↦ by
    induction w with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, hN]
  have hinj : Function.Injective (i.lTensor R') :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hex : Function.Exact (i.lTensor R') (d.lTensor R') := Module.Flat.lTensor_exact R' hid
  refine ⟨fun a b hab ↦ hinj (hM.1 ?_), fun z' ↦ ?_⟩
  · rw [← sqZ, ← sqZ, hab]
  · obtain ⟨m, hm⟩ := hM.2 (i' z')
    have h0 : d.lTensor R' m = 0 := hNi (by rw [← sqN, hm, hid'.apply_apply_eq_zero, map_zero])
    obtain ⟨w, rfl⟩ := (hex m).1 h0
    exact ⟨w, hi' (by rw [sqZ, hm])⟩

theorem liftSemi_bijective_of_exact_large : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (Z : Type 1) [AddCommGroup Z] [Module R Z] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type 1) [AddCommGroup N] [Module R N] (Z' : Type 1) [AddCommGroup Z'] [Module R' Z'] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type 1) [AddCommGroup N'] [Module R' N'] (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M') (fN : N →ₛₗ[algebraMap R R'] N'), Function.Injective i → Function.Exact i d → Function.Injective i' → Function.Exact i' d' → (∀ z, i' (fZ z) = fM (i z)) → (∀ x, d' (fM x) = fN (d x)) → Function.Bijective (liftSemi fM) → Function.Injective (liftSemi fN) → Function.Bijective (liftSemi fZ) := by
  intro R R' _ _ _ _ Z _ _ M _ _ N _ _ Z' _ _ M' _ _ N' _ _ i d i' d' fZ fM fN hi hid hi' hid' hZ hN hM hNi
  exact liftSemi_bijective_of_exact i d i' d' fZ fM fN hi hid hi' hid' hZ hN hM hNi

end GlobalTheory.FlatKerLarge
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieDual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem tanVal_pullForm_baseChange {σ : R →+* R'} {A : Over (Sp R)} {B : Over (Sp R')}
    {φ : B.left ⟶ A.left}
    (m : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R') (B.hom ≫ 𝟙 _) σ φ) {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (e : v'.left ≫ φ = spMap (Chart.dualMapR σ) ≫ v.left) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal v' (m.pullForm f) = σ (tanVal v f) := by
  let E := SqExt.dual R
  let E' := SqExt.dual R'
  have hy := pt_w v
  have hy' := pt_w v'
  have hc : ∀ r : R, Chart.dualMapR σ (algebraMap R (DualNumber R) r) =
      algebraMap R' (DualNumber R') (σ r) := fun r => by
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have e₀ : spMap σ ≫ spMap (E.π : E.C →+* E.B) ≫ v.left =
      (spMap (E'.π : E'.C →+* E'.B) ≫ v'.left) ≫ φ := by
    rw [Category.assoc, e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, E, E', TrivSqZeroExt.algebraMap_eq_inl]
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { Chart.dualMapR σ with commutes' := hc }
      φ₀ := σ
      comm := fun b => by
        change σ b.fst = (Chart.dualMapR σ b).fst
        simp [Chart.dualMapR]
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha => by
        have ha' : a.fst = 0 := ha
        change (Chart.dualMapR σ a).fst = 0
        simp [Chart.dualMapR, ha']
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { Chart.dualMapR σ with commutes' := hc } e.symm
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { σ with commutes' := fun _ => rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ => rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun c => (hc c).symm
  have k : E'.val v'.left hy' (m.pullForm f).1 = Chart.dualMapR σ (E.val v.left hy f.1) :=
    (congrArg₂ (fun u v : E'.C => u - v) k2 k1).trans
      ((add_sub_add_right_eq_sub (G := E'.C) _ _ _).trans (map_sub (Chart.dualMapR σ) _ _).symm)
  rw [tanVal_apply, tanVal_apply]
  refine (congrArg (TrivSqZeroExt.snd (R := R')) k).trans ?_
  exact zero_add _

theorem tanVal_list_prod_eq_zero {A : Over (Sp R)} [GrpObj A] (f : Form (A.hom ≫ 𝟙 _)) :
    ∀ l : List (epsR R ⟶ A), (∀ u ∈ l, IsTangent u ∧ tanVal u f = 0) →
      IsTangent l.prod ∧ tanVal l.prod f = 0 := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨?_, by rw [List.prod_nil]; exact tanVal_one f⟩
    rw [List.prod_nil, GrpTangent.isTangent_iff, MonObj.comp_one]
  | cons u l ih =>
    intro h
    obtain ⟨hu, hu0⟩ := h u List.mem_cons_self
    obtain ⟨hl, hl0⟩ := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    rw [List.prod_cons]
    refine ⟨?_, by rw [tanVal_mul hu hl, hu0, hl0, add_zero]⟩
    rw [GrpTangent.isTangent_iff] at hu hl ⊢
    rw [MonObj.comp_mul, hu, hl, _root_.mul_one]

theorem tanVal_pullForm_eq_zero_of_lieBasis : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], Smooth B.hom → ∀ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y → ∀ f : Form (B.hom ≫ 𝟙 (Sp R)), (∀ i, tanVal (y i) f = 0) → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (B' : Over (Sp R')) [GrpObj B'] [IsCommMonObj B'] (φ : B'.left ⟶ B.left), IsGrpPullback B' B (spMap σ) φ → ∀ (m : IsMor (dp0 R) (B.hom ≫ 𝟙 (Sp R)) (dp0 R') (B'.hom ≫ 𝟙 (Sp R')) σ φ) (v : epsR R' ⟶ B'), IsTangent v → tanVal v (m.pullForm f) = 0 := by
  intro R _ B _ _ hs n y hy f hf R' _ σ B' _ _ φ hφ m v hv
  obtain ⟨y', hy', e⟩ := GlobalTheory.exists_isLieBasis_baseChange R R' σ B B' φ hφ hs n y hy
  have h0 : ∀ i, tanVal (y' i) (m.pullForm f) = 0 := fun i => by
    rw [tanVal_pullForm_baseChange m (e i) f, hf i, map_zero]
  obtain ⟨c, ⟨u, hu, rfl⟩, -⟩ := hy'.2 v hv
  have hu' : ∀ i, u i = GrpTangent.epsScale (c i) ≫ y' i := fun i => Over.OverMorphism.ext (hu i)
  refine (tanVal_list_prod_eq_zero (m.pullForm f) _ fun w hw => ?_).2
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
  rw [hu' i]
  exact ⟨GrpTangent.isTangent_epsScale _ (hy'.1 i), by rw [tanVal_epsScale, h0 i, mul_zero]⟩

end GlobalTheory.LieDual
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (f : C →ₐc[k] A), Module.finrank k A = Module.finrank k (LinearMap.range (f : C →ₐ[k] A).toLinearMap) * Module.finrank k (A ⧸ kerIdeal f) := by
  first | exact @GlobalTheory.Dieu.finrank_eq_range_mul_ker | exact GlobalTheory.Dieu.finrank_eq_range_mul_ker | (intros; apply GlobalTheory.Dieu.finrank_eq_range_mul_ker <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D] (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 → ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  first | exact @GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero | exact GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero | (intros; apply GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistReduction_cohomology_map_unique : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (ρ ρ' : SemiMap (res _ (tw Q i)) (res _ (tw q i))), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), ρ.app U 0 (resGen i ζ) = ρ'.app U 0 (resGen i ζ)) → ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i), ρ.op.app E n x = ρ'.op.app E n x := by
  first
  | exact @GlobalTheory.EtC.RedUniq.op_eq
  | exact GlobalTheory.EtC.RedUniq.op_eq
  | (intros; apply GlobalTheory.EtC.RedUniq.op_eq <;> assumption)
end
