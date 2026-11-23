module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle158
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubRedMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle261
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle831
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle717
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle833
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deRhamDerivative_eq_zero_of_symmetric_frame : ∀ (B : Type) [CommRing B] [Algebra ℂ B] (g : ℕ) (d : Fin g → Derivation ℂ B B) (ω : Fin g → Ω[B⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) → (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) → (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) → ∀ k : Fin g → B, (∀ a b, d a (k b) = d b (k a)) → dOne ℂ B (∑ a, k a • ω a) = 0 := by
  first | exact @GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm | exact GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm | (intros; apply GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Charts.Obj.cAlg

namespace GlobalTheory.AnPer.TenFib

open GlobalTheory.CatCoh

variable {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} (D : Type) [CommRing D]
  [Algebra ℂ D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀)

def inc (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) : CoefMap (algebraMap ℂ D) (O (dp0 ℂ) s₀) (K₀.Ten D) where
  G := r₀.functor
  α T := (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom
  naturality _ _ := rfl
  smul T a b := by
    subst hσ
    change ((1 : D) ⊗ₜ[ℂ] (a • (show T.C from b)) : T.ten D) = algebraMap ℂ D a • ((1 : D) ⊗ₜ[ℂ] (show T.C from b) : T.ten D)
    rw [tmul_smul, algebraMap_smul]

theorem ten_fib : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀) (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X₀ ⟶ Sp D₀} (hs : s' = s₀ ≫ spMap π₀) (io : D₀ →+* D) (hio : ∀ d, π (io d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π)) (j₀ : ℂ →+* D₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' j₀ φ), (∀ a, io (j₀ a) = algebraMap ℂ D a) → ∀ (c : FirstDeRham s₀) (p : Λ → ℂ) (per : Λ →+ Hol F₀.V) (q : Λ →+ D), (∀ l, per l = algebraMap ℂ _ (p l)) → (∀ l, q l = algebraMap ℂ D (p l)) → r₀.coef.pull1 c = K₀.perCl per → (r₀.tenCoef π hσ κ hs io hio hπ).pull1 (k.pull1 c) = GlobalTheory.CatCoh.H1.mk _ (K₀.tenZ q) := by
  intro I₀ _ g Λ _ F₀ K₀ D _ _ π X₀ s₀ σ₀ r₀ hσ D₀ _ π₀ κ s' hs io hio hπ j₀ φ hφ k hj c p per q hper hq hc
  subst hφ
  let θ : (inc D r₀ hσ).G ⟶ (k.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)).G :=
    { app := fun T ↦
        { φ := { (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom with
            commutes' := fun a ↦ by
              subst hσ
              change (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D) (algebraMap ℂ T.C a) =
                algebraMap D (T.ten D) (io (j₀ a))
              rw [AlgHom.commutes, hj, ← IsScalarTower.algebraMap_apply] }
          φ₀ := RingHom.id (T.C ⧸ T.J)
          comm := fun b ↦ congrArg (Ideal.Quotient.mk T.J) (by
            change (show T.C from b) = T.red π (1 ⊗ₜ (show T.C from b))
            rw [Charts.Obj.red_tmul, map_one, map_one, _root_.one_mul])
          dp := letI := T.tenRat (D := D); isDPMorphism_of_rat T.δ (T.tenδ π)
            (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom fun b hb ↦ by
              change T.red π (1 ⊗ₜ b) ∈ T.J
              rwa [Charts.Obj.red_tmul, map_one, map_one, _root_.one_mul]
          pt := by
            change spMap (RingHom.id (T.C ⧸ T.J)) ≫ (r₀.obj T).x = (r₀.obj T).x ≫ 𝟙 X₀
            rw [Cris.spMap_id]
            exact (Category.id_comp _).trans (Category.comp_id _).symm }
      naturality := fun _ _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  have e := (inc D r₀ hσ).pullCohomologyOne_eq_of_natTrans _ θ (fun _ _ ↦ rfl) c
  rw [CoefMap.pullCohomologyOne_comp] at e
  refine e.symm.trans ?_
  obtain ⟨f, rfl⟩ := CatCoh.H1.mk_surjective _ c
  obtain ⟨G, hG⟩ := CatCoh.H1.mk_eq_mk.1 hc
  refine CatCoh.H1.mk_eq_mk.2 ⟨fun T ↦ ((1 : D) ⊗ₜ[ℂ] (show T.C from G T) : T.ten D), ?_⟩
  funext T T' ψ
  have h1 := congrFun (congrFun (congrFun hG T) T') ψ
  have h2 : ((1 : D) ⊗ₜ[ℂ] ((show T'.C from G T') - ψ.φ (G T)) : T'.ten D) = (1 : D) ⊗ₜ[ℂ] (show T'.C from f.1 _ _ (r₀.functor.map ψ)) -
      (1 : D) ⊗ₜ[ℂ] (algebraMap (Hol F₀.V) T'.C (per ψ.deg)) := by
    rw [← tmul_sub]; exact congrArg _ h1
  refine (tmul_sub _ _ _).symm.trans (h2.trans ?_)
  congr 1
  change _ = algebraMap D (T'.ten D) (q ψ.deg)
  rw [hper, hq]
  exact (Algebra.TensorProduct.includeRight : T'.C →ₐ[ℂ] T'.ten D).commutes (p ψ.deg)

end GlobalTheory.AnPer.TenFib
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Charts.Obj.cAlg

namespace GlobalTheory.AnPer.TenFam

open GlobalTheory.CatCoh

variable {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀}
  {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) (hπ : IsNilpotent (RingHom.ker π))
  {I : Type} [Fintype I] {F : Fam I g Λ} (K : Charts F) (ν : K₀.K → K.K)
  (Ta : ∀ k, Hol (K.W (ν k)) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k)) (τV : Hol F.V →+* D)
  (hc : ∀ k f, Ta k (K.cst (ν k) f) = τV f ⊗ₜ[ℂ] 1)

def obj (T : K₀.Obj) : K.Obj where
  k := ν T.k
  C := T.ten D
  alg := ((algebraMap D (T.ten D)).comp τV).toAlgebra
  J := T.tenJ π
  nil := T.tenJ_nil π hπ
  ρ := ((Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc).comp (Ta T.k)).toRingHom
  ρ_cst f := by
    change Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc (Ta T.k (K.cst (ν T.k) f)) = τV f ⊗ₜ[ℂ] (1 : T.C)
    rw [hc, Algebra.TensorProduct.map_tmul, map_one]
    rfl

variable (hν : ∀ l k' k, K₀.le l k' k → K.le l (ν k') (ν k))
  (hd : ∀ k a h, Ta k (dw (W := K.W (ν k)) a h) =
    LinearMap.lTensor D (dw (W := K₀.W k) a).toLinearMap (Ta k h))
  (hcl : ∀ l k' k (h₀ : K₀.le l k' k), Close ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k'))) ((Ta k').toRingHom.comp (Charts.sh (hν l k' k h₀))) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k')) (K₀.maps h₀))).comp (Ta k)).toRingHom))


include hd hcl in
theorem close {T T' : K₀.Obj} (f : T ⟶ T') :
    Close (T'.tenJ π) ((obj π hπ K ν Ta τV hc T').ρ.comp (Charts.sh (hν _ _ _ (Charts.Hom.le f))))
      ((Charts.Hom.ten D f : T.ten D →+* T'.ten D).comp (obj π hπ K ν Ta τV hc T).ρ) := by
  have h1 := (hcl _ _ _ (Charts.Hom.le f)).map (J' := T'.tenJ π)
    (Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc).toRingHom (fun c hc' ↦ by
      have : (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W T'.k)) ≤
          (T'.tenJ π).comap (Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc).toRingHom :=
        Ideal.map_le_iff_le_comap.2 fun d hd' ↦ by
          change T'.red π (d ⊗ₜ T'.ρc 1) ∈ T'.J
          rw [Charts.Obj.red_tmul, (RingHom.mem_ker).1 hd', map_zero, zero_mul]
          exact T'.J.zero_mem
      exact this hc')
  have h2 := GlobalTheory.AnPer.Close.tensor_comp (Ta T.k) (hd T.k) T'.J (T'.tenJ π) (fun c hc' ↦ by
      change T'.red π (1 ⊗ₜ c) ∈ T'.J
      rw [Charts.Obj.red_tmul]
      exact T'.J.mul_mem_left _ hc')
    (T'.ρc.comp (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k)) (K₀.maps (Charts.Hom.le f))))
    ((Charts.Hom.φc f).comp T.ρc) f.close
  have e1 : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc
      (Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k))
        (K₀.maps (Charts.Hom.le f))) x) = Algebra.TensorProduct.map (AlgHom.id ℂ D)
        (T'.ρc.comp (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k))
        (K₀.maps (Charts.Hom.le f)))) x := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul d c => rfl
  have e2 : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), Algebra.TensorProduct.map (AlgHom.id ℂ D) ((Charts.Hom.φc f).comp T.ρc) x =
      Charts.Hom.ten D f (Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc x) := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul d c => rfl
  have tr : ∀ {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C} {a b b' c c' : Hol W →+* C},
      Close J a b → Close J b' c → (∀ h, b h = b' h) → (∀ h, c h = c' h) → Close J a c' := by
    intro W C _ J a b b' c c' p q e e'
    obtain rfl : b = b' := RingHom.ext e
    obtain rfl : c = c' := RingHom.ext e'
    exact Relation.ReflTransGen.trans p q
  exact tr h1 h2 (fun h ↦ e1 (Ta T.k h)) (fun h ↦ e2 (Ta T.k h))

def functor : K₀.Obj ⥤ K.Obj where
  obj := obj π hπ K ν Ta τV hc
  map {T T'} f :=
    { φ := { (Charts.Hom.ten D f : T.ten D →+* T'.ten D) with commutes' := fun d ↦ (Charts.Hom.ten D f).commutes (τV d) }
      deg := f.deg
      le := hν _ _ _ (Charts.Hom.le f)
      mem := fun _ h ↦ Charts.Hom.ten_mem π f h
      close := close π hπ K ν Ta τV hc hν hd hcl f }
  map_id T := Charts.hom_ext (fun b ↦ mp_id (K₀.Ten D) T b) rfl
  map_comp f f' := Charts.hom_ext (fun b ↦ mp_comp (K₀.Ten D) f f' b) rfl

def coef : CoefMap τV K.Oc (K₀.Ten D) where
  G := functor π hπ K ν Ta τV hc hν hd hcl
  α T := RingHom.id (T.ten D)
  naturality _ _ := rfl
  smul T b c := (Algebra.smul_def (A := T.ten D) (τV b) c).symm

theorem main : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀) (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X₀ ⟶ Sp D₀} (hs : s' = s₀ ≫ spMap π₀) (io : D₀ →+* D) (hio : ∀ d, π (io d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π)) {I : Type} [Fintype I] {F : Fam I g Λ} (K : Charts F) {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (r : Real K s σ) (ν : K₀.K → K.K) (hν : ∀ l k' k, K₀.le l k' k → K.le l (ν k') (ν k)) (Ta : ∀ k, Hol (K.W (ν k)) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k)) (τV : Hol F.V →+* D), (∀ k f, Ta k (K.cst (ν k) f) = τV f ⊗ₜ[ℂ] 1) → (∀ k a h, Ta k (dw (W := K.W (ν k)) a h) =
    LinearMap.lTensor D (dw (W := K₀.W k) a).toLinearMap (Ta k h)) → (∀ l k' k (h₀ : K₀.le l k' k), Close ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k'))) ((Ta k').toRingHom.comp (Charts.sh (hν l k' k h₀))) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k')) (K₀.maps h₀))).comp (Ta k)).toRingHom)) → ∀ (φ₀ : X₀ ⟶ X), (∀ k, spMap ((Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol (K₀.W k))).comp π) (AlgHom.id ℂ (Hol (K₀.W k))) (fun _ _ ↦ Commute.all _ _)).comp (Ta k)).toRingHom ≫ r.x (ν k) = r₀.x k ≫ φ₀) → ∀ (j : B →+* D₀) (n : IsMor (dp0 B) s κ s' j φ₀), (∀ b, io (j b) = τV (σ b)) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V) (q : Λ →+ D), (∀ l, q l = τV (per l)) → r.coef.pull1 c = K.perCl per → (r₀.tenCoef π hσ κ hs io hio hπ).pull1 (n.pull1 c) = GlobalTheory.CatCoh.H1.mk _ (K₀.tenZ q) := by
  intro I₀ _ g Λ _ F₀ K₀ D _ _ π X₀ s₀ σ₀ r₀ hσ D₀ _ π₀ κ s' hs io hio hπ I _ F K B _ X s σ r ν hν Ta τV hc hd hcl φ₀ hpt
    j n hj c per q hq hper
  let β := coef π hπ K ν Ta τV hc hν hd hcl
  let θ : (r.coef.comp β).G ⟶ (n.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)).G :=
    { app := fun T ↦
        { φ := { RingHom.id (T.ten D) with commutes' := fun b ↦ congrArg (algebraMap D (T.ten D)) (hj b).symm }
          φ₀ := Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl
          comm := fun _ ↦ rfl
          dp := letI := T.tenRat (D := D); isDPMorphism_of_rat _ (T.tenδ π) (RingHom.id (T.ten D)) fun _ h ↦ h
          pt := by
            have e : (Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl).comp
                ((Ideal.Quotient.mk (T.tenJ π)).comp (obj π hπ K ν Ta τV hc T).ρ) =
                ((Ideal.Quotient.mk T.J).comp T.ρ).comp ((Algebra.TensorProduct.lift
                  ((Algebra.ofId ℂ (Hol (K₀.W T.k))).comp π) (AlgHom.id ℂ (Hol (K₀.W T.k)))
                  (fun _ _ ↦ Commute.all _ _)).comp (Ta T.k)).toRingHom := by
              have e' : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), T.red π (Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc x) =
                  T.ρc (Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol (K₀.W T.k))).comp π)
                    (AlgHom.id ℂ (Hol (K₀.W T.k))) (fun _ _ ↦ Commute.all _ _) x) := fun x ↦ by
                induction x using TensorProduct.induction_on with
                | zero => simp only [map_zero]
                | add x y hx hy => simp only [map_add (f := _), hx, hy]
                | tmul d c =>
                  rw [Algebra.TensorProduct.lift_tmul, map_mul]
                  exact congrArg (· * T.ρc c) (T.ρc.commutes (π d)).symm
              exact RingHom.ext fun h ↦ congrArg (Ideal.Quotient.mk T.J) (e' (Ta T.k h))
            change spMap (Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl) ≫
              spMap ((Ideal.Quotient.mk (T.tenJ π)).comp (obj π hπ K ν Ta τV hc T).ρ) ≫ r.x (ν T.k) =
              (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r₀.x T.k) ≫ φ₀
            rw [Category.assoc, ← hpt]
            exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r.x (ν T.k)) ((Cris.spMap_comp _ _).symm.trans
              ((congrArg spMap e).trans (Cris.spMap_comp _ _)))).trans (Category.assoc _ _ _)) }
      naturality := fun _ _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  have h1 := (r.coef.comp β).pullCohomologyOne_eq_of_natTrans (n.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)) θ (fun _ _ ↦ rfl) c
  rw [CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_comp, hper] at h1
  refine h1.symm.trans (congrArg (GlobalTheory.CatCoh.H1.mk _) (Subtype.ext ?_))
  funext T T' f
  change algebraMap D (T'.ten D) (τV (per f.deg)) = algebraMap D (T'.ten D) (q f.deg)
  rw [hq]

end GlobalTheory.AnPer.TenFam
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem cartier_primePow_pairing (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r :=
  convPow_primePow_apply_pow p R h G n r χ a

end GlobalTheory.Katz
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.NormSqOfSquareEqNeg

theorem normSq_of_sq_eq_neg (d : ℕ) (α : ℂ) (h : α ^ 2 = -(d : ℂ)) : (Complex.normSq α : ℂ) = d := by
  have h1 : Complex.normSq α ^ 2 = (d : ℝ) ^ 2 := by
    rw [← map_pow, h, Complex.normSq_neg, Complex.normSq_natCast]
    ring
  have h2 : Complex.normSq α = d := by
    have := Complex.normSq_nonneg α
    nlinarith [sq_nonneg (Complex.normSq α - d), sq_nonneg (Complex.normSq α + d), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  rw [h2]; simp

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ)
    (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ →
    g (s2 Λ₀ / Ω₀ ^ 2) = s2 Λ₁ / Ω₁ ^ 2 := by
  intro K _ _ d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT
  obtain ⟨_, _, _, hL₀, ⟨𝔞, _, hL₁⟩, _, _, hP⟩ := id hT
  obtain ⟨_, hm₀, him, hint⟩ := GlobalTheory.LatOfMult.main K d δ ι 1 Λ₀ hd hδ hL₀
  obtain ⟨_, hm₁, _, _⟩ := GlobalTheory.LatOfMult.main K d δ ι 𝔞 Λ₁ hd hδ hL₁
  have hα : ι δ ≠ 0 := fun h => him (by simp [h])
  have hδ0 : δ ≠ 0 := fun h => hα (by simp [h])
  have hα2 : ι δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hN : (Complex.normSq (ι δ) : ℂ) = d := normSq_of_sq_eq_neg d _ hα2
  have hc : ι δ ^ 2 - (Complex.normSq (ι δ) : ℂ) = -(2 * d : ℂ) := by rw [hα2, hN]; ring
  have hc0 : -(2 * d : ℂ) ≠ 0 := by
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simpa using this
  obtain ⟨S, hS⟩ := kernel_reps_exist Λ₀ (ι δ) hα hm₀
  have hTr := GlobalTheory.T.isLatticeQuotientCorrespondence_of_torsionTransport K ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT
  have hmul : ∀ x x', Tr t x x' → Tr t (δ * x) (δ * x') := fun x x' h => (GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties K t).2.1 δ x x' hint h
  obtain ⟨φ, S', hS', hbij, hrel⟩ := GlobalTheory.WpFam.kerReps_transport K ι Λ₀ Λ₁ (Tr t) δ S hTr hδ0 hmul hS
  have e₀ := quasiPeriodConstIsogeny_thm Λ₀ (ι δ) S hα hm₀ hS
  have e₁ := quasiPeriodConstIsogeny_thm Λ₁ (ι δ) S' hα hm₁ hS'
  rw [hc] at e₀ e₁
  have s₀ : s2 Λ₀ = (∑ P ∈ S, Λ₀.weierstrassP P) / -(2 * d : ℂ) := by
    rw [eq_div_iff hc0, mul_comm, e₀]
  have s₁ : s2 Λ₁ = (∑ P ∈ S', Λ₁.weierstrassP P) / -(2 * d : ℂ) := by
    rw [eq_div_iff hc0, mul_comm, e₁]
  have key : ∀ P ∈ S, g (Λ₀.weierstrassP P / Ω₀ ^ 2) = Λ₁.weierstrassP (φ P) / Ω₁ ^ 2 := by
    intro P hPS
    obtain ⟨k, k', hk, hk', hkk⟩ := hrel P hPS
    have hnot : ι k ∉ Λ₀.lattice := by rw [hk]; exact (hS.1 P hPS).2
    have := (hP k k' hnot hkk).1
    rwa [hk, hk'] at this
  have hsum : ∑ P ∈ S, Λ₁.weierstrassP (φ P) / Ω₁ ^ 2 = ∑ Q ∈ S', Λ₁.weierstrassP Q / Ω₁ ^ 2 :=
    Finset.sum_nbij φ (fun a ha => hbij.mapsTo ha) hbij.injOn hbij.surjOn (fun _ _ => rfl)
  have hg2 : g (-(2 * d : ℂ)) = -(2 * d : ℂ) := by simp [map_neg, map_mul, map_ofNat, map_natCast]

  rw [s₀, s₁, div_right_comm, div_right_comm (∑ P ∈ S', _), map_div₀, hg2, Finset.sum_div, Finset.sum_div, map_sum,
  Finset.sum_congr rfl key, hsum]

end GlobalTheory.NormSqOfSquareEqNeg
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.JointHarm GlobalTheory.FockSeq in
theorem harmonic_homog_of_type : ∀ (p q r s : ℕ),
    (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
      P ∈ harm1 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
    (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
      P ∈ harm2 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) :=
  fun _ _ _ _ =>
    ⟨fun _ P h0 ht hh => isSide_one.homog_of_type isFockIsometry_embedding emb_injective
        Function.bijective_id h0 ht ((mem_harm1 P).1 hh),
      fun _ P h0 ht hh => isSide_two.homog_of_type isFockIsometry_embedding emb_injective
        Prod.swap_bijective h0 ht ((mem_harm2 P).1 hh)⟩

end GlobalTheory.FockAlg
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.JointHarm

theorem finrank_joint_highest_of_shape :
    ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s)) = 1 :=
  fun _ _ _ _ μ μ' => (joint_harmonics μ μ').1

end GlobalTheory.JointHarm
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg

theorem jointHarm_hw_eq_bot : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    ¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s) = ⊥ :=
  fun _ _ _ _ μ μ' => (GlobalTheory.JointHarm.joint_harmonics μ μ').2

end GlobalTheory.FockAlg
end

section

noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

def LabelsChar (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (θ : Tor p d →* ℂˣ) (x : Fbar p) : Prop :=
  x ^ (p ^ d - 1) = 1 ∧ ∀ u : Tor p d, ((θ u : ℂˣ) : ℂ) = GlobalTheory.GLq.thetaOf L d x ((u : (Fbar p)ˣ) : Fbar p)

def LabelsTame (L : GlobalTheory.GLq.LabelDatum p) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ) : Prop :=
  ∀ u : (ZMod p)ˣ, GlobalTheory.GLq.thetaOf L 1 (algebraMap (ZMod p) (Fbar p) (a : ZMod p))
    (algebraMap (ZMod p) (Fbar p) (u : ZMod p)) = ((χ u : ℂˣ) : ℂ)

def rootElt {r : ℕ} {b : Fin r → Fin r} (x : Cyc b → Fbar p) (y : Σ c : Cyc b, Fin (cycLen b c)) : Fbar p :=
  x y.1 ^ p ^ (y.2 : ℕ)

def IsRootPoly {r : ℕ} {b : Fin r → Fin r} (x : Cyc b → Fbar p) (f : (ZMod p)[X]) : Prop :=
  (∀ c, x c ^ (p ^ cycLen b c - 1) = 1) ∧ f.Monic ∧ Formalism.CyclotomicNorms.rootsBar f = Finset.univ.val.map (rootElt x)

def Labels (L : GlobalTheory.GLq.LabelDatum p) {r : ℕ} (s : SSParam p ℂ r) (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]) : Prop :=
  (∀ c, LabelsChar L (s.2 c) (x c)) ∧ IsRootPoly x f

def cuspOn {ι : Type} [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) :
    GlobalTheory.GLq.Gn p (Fintype.card ι) → ℂ := fun y =>
  cuspChar θ ((y : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (ZMod p)).submatrix
    (Fintype.equivFin ι) (Fintype.equivFin ι))

end GlobalTheory.ParamLabel

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.excisionConeMap_quasiIso' : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → QuasiIso (excisionConeMap R A A' f) := by
  first | (exact @GlobalTheory.EtC.excisionConeMap_quasiIso) | (exact GlobalTheory.EtC.excisionConeMap_quasiIso) | (intros; apply GlobalTheory.EtC.excisionConeMap_quasiIso <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

theorem _root_.GlobalTheory.T.mayer_vietoris_exact_etale : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  first | (exact @GlobalTheory.EtC.ExcisionNat.excision_natural) | (exact GlobalTheory.EtC.ExcisionNat.excision_natural) | (intros; apply GlobalTheory.EtC.ExcisionNat.excision_natural <;> assumption)
end
