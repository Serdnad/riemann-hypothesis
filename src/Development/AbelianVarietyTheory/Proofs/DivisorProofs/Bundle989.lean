module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchemePresentingSquareZeroSmoothLiftSystem
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle225
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle973
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_corr_of_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ E : GlobForm s₀ →+ C0 S'.F, (∀ w, S'.IsIdealValuedLiftSystemCochain (E w)) → (∀ (r : R) w, E (π r • w) = r • E w) → (∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = d0 S'.F (E w) U V a) → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar S S' Φ θ hθ E hEI hEs hEd

  have hext : ∀ U : AffOp X₀, ∃! η : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj U,
      (∀ b w, η (S.p U b • w) = (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) b * η w) ∧
      (∀ w, η w ∈ I.map (algebraMap R (S'.F.obj U))) ∧ ∀ w : GlobForm s₀, η (w.1 U) = E w U := fun U ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U (S.F.obj U) (S'.F.obj U) (S.p U) (S.semi U)
      (S.surj U) (S.ker U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) ((Pi.evalAddMonoidHom _ U).comp E)
      (fun r w ↦ by simp [hEs]) (fun w ↦ hEI w U)

  choose η hη using fun U ↦ (hext U).exists
  have hψ : ∀ U : AffOp X₀, ∃ ψ : S.F.obj U →ₐ[R] S'.F.obj U,
      IsTheta I (S.p U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) ψ (-η U) := fun U ↦
    (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj U) I hI π hπ (S.p U) (S.semi U) (S.surj U)
      (S.ker U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)).2 (-η U)
      (fun b w ↦ by rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, (hη U).1, mul_neg])
      (fun w ↦ by rw [AddMonoidHom.neg_apply]; exact neg_mem ((hη U).2.1 w))
  choose ψ hψ using hψ
  have hψv : ∀ U b, ψ U b = Φ.φ U b + η U (D R₀ (Sec s₀ U.unop.1) (S.p U b)) := fun U b ↦ by
    have h := (hψ U).der b
    rw [AddMonoidHom.neg_apply] at h
    change -η U _ = Φ.φ U b - ψ U b at h
    linear_combination h
  refine ⟨ψ, fun U b ↦ ?_, fun U V a b ↦ ?_⟩
  · rw [hψv, map_add (f := _), Φ.red, (S'.ker U _).2 ((hη U).2.1 _), add_zero]
  ·
    let α : S.F.obj U →ₐ[R] S'.F.obj V := (mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)
    let χ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V := θ U V a + (mp S'.F a).toAddMonoidHom.comp (η U) -
      (η V).comp (p1 (OAff s₀) a).toAddMonoidHom
    have hχ : ∀ w, χ w = θ U V a w + mp S'.F a (η U w) - η V (p1 (OAff s₀) a w) := fun _ ↦ rfl

    have hmemV : ∀ w, η V w ∈ I.map (algebraMap R (S'.F.obj V)) := (hη V).2.1
    have hdiff : ∀ c : S.F.obj U, ∀ x ∈ I.map (algebraMap R (S'.F.obj V)),
        (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (mp S.F a c) * x = α c * x := by
      intro c x hx
      have h1 := (hθ U V a).der c
      have h2 : α c - (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (mp S.F a c) ∈ I.map (algebraMap R (S'.F.obj V)) :=
        h1 ▸ (hθ U V a).mem _
      have h3 := mul_eq_zero_of_mem_map hI h2 hx
      rw [sub_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hu := exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U (S.F.obj U) (S'.F.obj V) (S.p U) (S.semi U)
      (S.surj U) (S.ker U) α 0 (fun r w ↦ by simp) (fun w ↦ zero_mem _)
    have hχ0 : χ = 0 := by
      refine hu.unique ⟨fun b w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩ ⟨fun b w ↦ by simp, fun w ↦ zero_mem _, fun w ↦ rfl⟩
      · rw [hχ, hχ, (hθ U V a).smul, (hη U).1, oneFormsMapOfFunctorMorphism_smul, map_mul]
        rw [← S.nat a b, (hη V).1, hdiff _ _ (hmemV _)]
        simp only [α, AlgHom.coe_comp, Function.comp_apply]
        ring
      · rw [hχ]
        exact sub_mem (add_mem ((hθ U V a).mem w) (algHom_mem_map I _ ((hη U).2.1 w))) (hmemV _)
      · rw [hχ, hEd, amitsur_d0_apply, (hη U).2.2, ← w.2 a, (hη V).2.2]
        simp
    have h0 : χ (D R₀ (Sec s₀ U.unop.1) (S.p U b)) = 0 := by rw [hχ0]; rfl
    rw [hχ, p1_D] at h0
    have hn : mp (OAff s₀) a (S.p U b) = S.p V (mp S.F a b) := (S.nat a b).symm
    rw [hn] at h0
    have h1 := (hθ U V a).der b
    simp only [α, AlgHom.coe_comp, Function.comp_apply] at h1
    rw [hψv, hψv, map_add (f := _)]
    simp only [AlgEquiv.coe_toAlgHom] at h0 h1 ⊢
    linear_combination h0 - h1

end GlobalTheory.LiftSys
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem mul_eq_zero_of_mem_sqMap {R : Type} [CommRing R] {I : Ideal R} {B : Type} [CommRing B] [Algebra R B]
    (hJ : I.map (algebraMap R B) ^ 2 = 0) {u v : B} (hu : u ∈ I.map (algebraMap R B))
    (hv : v ∈ I.map (algebraMap R B)) : u * v = 0 := by
  have := Ideal.mul_mem_mul hu hv
  rwa [← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at this

theorem algHom_apply_mem_map {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (f : A →ₐ[R] B) {x : A} (hx : x ∈ I.map (algebraMap R A)) : f x ∈ I.map (algebraMap R B) := by
  have := Ideal.mem_map_of_mem (f : A →+* B) hx
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem eq_of_sub_mem_map {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (hJ : I.map (algebraMap R B) ^ 2 = 0) (f g : A →ₐ[R] B)
    (h : ∀ b, f b - g b ∈ I.map (algebraMap R B)) {x : A} (hx : x ∈ I.map (algebraMap R A)) : f x = g x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, -, rfl⟩ := hy
    rw [AlgHom.commutes, AlgHom.commutes]
  | zero => rw [map_zero, map_zero]
  | add y y' _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), h1, h2]
  | smul a y hy ih =>
    rw [smul_eq_mul, map_mul, map_mul, ← ih, ← sub_eq_zero, ← sub_mul]
    exact mul_eq_zero_of_mem_sqMap hJ (h a) (algHom_apply_mem_map f hy)

theorem locIso_transport : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), (∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a)) ∧ (∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a, d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a)) ∧ ∀ c ∈ I • (⊤ : Submodule R (Cr hI π s₀)), ∃ (z : Z1 S.F) (z' : Z1 S'.F), S.IsIdealValuedLiftSystemCocycle z ∧ H1.mk _ z = S.r hI c ∧ H1.mk _ z' = S'.r hI c ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S S' Φ
  have hres : ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U),
      mp S'.F a (Φ.φ U b) - Φ.φ V (mp S.F a b) ∈ I.map (algebraMap R (S'.F.obj V)) := fun U V a b ↦ by
    rw [← S'.ker V, map_sub, S'.nat a, Φ.red, Φ.red, S.nat a, sub_self]
  have hcomm : ∀ (U V : AffOp X₀) (a : U ⟶ V) (x : S.F.obj U), x ∈ I.map (algebraMap R (S.F.obj U)) →
      mp S'.F a (Φ.φ U x) = Φ.φ V (mp S.F a x) := fun U V a x hx ↦
    eq_of_sub_mem_map (map_sq hI _) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))
      ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a) hx
  have c1 : ∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
    intro z hz
    refine ⟨⟨fun U V a ↦ Φ.φ V (z.1 U V a), ?_⟩, fun U V a ↦ ?_, fun _ _ _ ↦ rfl⟩
    · intro U V W a b
      show Φ.φ W (z.1 U W (a ≫ b)) = mp S'.F b (Φ.φ V (z.1 U V a)) + Φ.φ W (z.1 V W b)
      rw [Z1.comp z a b, map_add (f := _), hcomm V W b _ (hz U V a)]
    · exact algHom_apply_mem_map (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (hz U V a)
  have c2 : ∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a,
      d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a) := by
    intro g hg U V a
    rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, hcomm U V a _ (hg U)]
  refine ⟨c1, c2, fun c hc ↦ ?_⟩
  refine Submodule.smul_induction_on hc ?_ ?_
  · intro r hr c₀ _
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c₀
    let z : Z1 S.F := r • (S.coef hI).pullbackOneCocycle f
    have hzI : S.IsIdealValuedLiftSystemCocycle z := fun U V a ↦ by
      show r • (show S.F.obj V from ev f ((S.thick hI).map a)) ∈ I.map (algebraMap R (S.F.obj V))
      rw [Algebra.smul_def, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hr)
    obtain ⟨z', -, hz'⟩ := c1 z hzI
    refine ⟨z, z', hzI, ?_, ?_, hz'⟩
    · show H1.mk _ (r • _) = S.r hI (r • H1.mk _ f)
      rw [map_smul, map_smul]
      rfl
    · rw [map_smul, show S'.r hI (H1.mk _ f) = H1.mk _ ((S'.coef hI).pullbackOneCocycle f) from rfl, ← map_smul,
        H1.mk_eq_mk]
      let ΦH : ∀ W : AffOp X₀, S.thickObj hI W ⟶ S'.thickObj hI W := fun W ↦
        S.thickHom S' hI (𝟙 W) (Φ.φ W : S.F.obj W →ₐ[R] S'.F.obj W)
          (fun b ↦ (Φ.red W b).trans (mp_id (OAff s₀) W (S.p W b)).symm)
      refine ⟨fun W ↦ -(r • @id (S'.F.obj W) (ev f (ΦH W))), ?_⟩
      funext U V a
      have hz'' := hz' U V a
      have e1 : @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) =
          mp S'.F a (@id (S'.F.obj U) (ev f (ΦH U))) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) :=
        ev_comp f (ΦH U) ((S'.thick hI).map a)
      have e2 : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) =
          Φ.φ V (@id (S.F.obj V) (ev f ((S.thick hI).map a))) + @id (S'.F.obj V) (ev f (ΦH V)) :=
        ev_comp f ((S.thick hI).map a) (ΦH V)
      have e3 : algebraMap R (S'.F.obj V) r * (@id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
          @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a))) = 0 := by
        obtain ⟨⟨Q, hQ⟩, tay⟩ := GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero R R₀ I hI π hπ hk X₀ s₀ S S' U V
        obtain ⟨θ, hθ, -⟩ := (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U)
          (S.semi U) (S.surj U) (S.ker U) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))).1
          ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a)
        have t := tay Q hQ (ΦH U ≫ (S'.thick hI).map a) ((S.thick hI).map a ≫ ΦH V) θ hθ f
        have t' : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
            @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) ∈ I.map (algebraMap R (S'.F.obj V)) := by
          rw [show @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
            @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) = _ from t]
          exact hθ.mem _
        exact mul_eq_zero_of_mem_sqMap (map_sq hI _) (Ideal.mem_map_of_mem _ hr) t'
      show -(r • @id (S'.F.obj V) (ev f (ΦH V))) - mp S'.F a (-(r • @id (S'.F.obj U) (ev f (ΦH U)))) =
        z'.1 U V a - r • @id (S'.F.obj V) (ev f ((S'.thick hI).map a))
      rw [hz'']
      show _ = Φ.φ V (r • @id (S.F.obj V) (ev f ((S.thick hI).map a))) - _
      rw [map_neg, map_smul, map_smul]
      simp only [Algebra.smul_def]
      linear_combination -(algebraMap R (S'.F.obj V) r) * (e1 - e2) - e3
  · rintro x y ⟨z₁, z₁', h₁, hx₁, hx₁', e₁⟩ ⟨z₂, z₂', h₂, hy₂, hy₂', e₂⟩
    refine ⟨z₁ + z₂, z₁' + z₂', fun U V a ↦ ?_, ?_, ?_, fun U V a ↦ ?_⟩
    · show z₁.1 U V a + z₂.1 U V a ∈ _
      exact Ideal.add_mem _ (h₁ U V a) (h₂ U V a)
    · rw [map_add (f := _), map_add (f := _), hx₁, hy₂]
    · rw [map_add (f := _), map_add (f := _), hx₁', hy₂']
    · show z₁'.1 U V a + z₂'.1 U V a = Φ.φ V (z₁.1 U V a + z₂.1 U V a)
      rw [map_add (f := _), e₁, e₂]

end GlobalTheory.LiftSys
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem connForm_sub_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (hC : Const s₀) (S : Sys I π s₀)
    (Q : ∀ U : AffOp X₀, S.thickObj hI U ⟶
      (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop)))
    (hQ : ∀ U b, (Q U).φ b = S.p U b) (f : Z1 (O (divided₂ hI) (s₀ ≫ spMap π))) (g : C0 S.F)
    (hg : d0 S.F g = ((S.coef hI).pullbackOneCocycle f).1) (F : Form s₀) (h : C0 (O (dp0 R₀) s₀))
    (hh : d0 _ h = ((redMor hI hk s₀).coef.pullbackOneCocycle f).1 - F.1.1) (U : AffOp X₀) :
    connForm ((redMor hI hk s₀).coef.pullbackOneCocycle f) (affPt s₀ U.unop) (affPt_w s₀ U.unop) -
        D R₀ (Sec s₀ U.unop.1) (ev f (Q U) : Sec s₀ U.unop.1) =
      connForm F.1 (affPt s₀ U.unop) (affPt_w s₀ U.unop) + D R₀ (Sec s₀ U.unop.1) (S.p U (g U)) := by
  set f₀ := (redMor hI hk s₀).coef.pullbackOneCocycle f with hf₀
  have e : f₀ = F.1 + ⟨d0 _ h, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ h⟩ := by
    apply Subtype.ext
    change f₀.1 = F.1.1 + d0 _ h
    rw [hh]; abel
  let hU : ∀ U : AffOp X₀, Sec s₀ U.unop.1 := fun U ↦
    @id (Sec s₀ U.unop.1) <| h (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop))
  let qU : ∀ U : AffOp X₀, Sec s₀ U.unop.1 := fun U ↦ @id (Sec s₀ U.unop.1) <| ev f (Q U)
  let k : C0 (OAff s₀) := fun U ↦ hU U - S.p U (g U) - qU U
  have hk0 : d0 _ k = 0 := by
    funext U V a
    let tr := Thick.trivHom (hx := affPt_w s₀ U.unop) (T := Thick.triv _ _ (affPt_w s₀ V.unop))
      (Sec.res s₀ (leOfHom a.unop)) (affPt_res s₀ (leOfHom a.unop))
    have h1 := congrArg (fun q ↦ q _ _ tr) hh
    simp only [amitsur_d0_apply, Pi.sub_apply] at h1
    have h0 : F.1.1 _ _ tr = 0 := F.2 tr rfl rfl
    rw [h0, sub_zero] at h1
    have h1' : hU V - Sec.res s₀ (leOfHom a.unop) (hU U) = (f₀.1 _ _ tr : Sec s₀ V.unop.1) := h1
    have h2 := ev_sq f (Q U) ((redMor hI hk s₀).functor.map tr) ((S.thick hI).map a) (Q V) fun c ↦ by
      change Sec.res s₀ (leOfHom a.unop) ((Q U).φ c) = (Q V).φ (mp S.F a c)
      rw [hQ, hQ, S.nat]; rfl
    have h3 : ev f ((S.thick hI).map a) = g V - mp S.F a (g U) := by
      have := congrArg (fun q ↦ q U V a) hg
      simp only [amitsur_d0_apply] at this
      exact this.symm
    have h2' : Sec.res s₀ (leOfHom a.unop) (qU U) + (f₀.1 _ _ tr : Sec s₀ V.unop.1) =
        @id (Sec s₀ V.unop.1) ((Q V).φ (ev f ((S.thick hI).map a))) + qU V := h2
    rw [hQ, id] at h2'
    erw [h3] at h2'
    have nat' : S.p V (mp S.F a (g U)) = Sec.res s₀ (leOfHom a.unop) (S.p U (g U)) := S.nat a (g U)
    rw [map_sub, nat'] at h2'
    change k V - Sec.res s₀ (leOfHom a.unop) (k U) = 0
    simp only [k, map_sub]
    linear_combination h1' + h2'
  obtain ⟨r, hr⟩ := hC k hk0
  have hD : D R₀ (Sec s₀ U.unop.1) (k U) = 0 := by rw [hr U]; exact (D R₀ _).map_algebraMap r
  simp only [k, map_sub] at hD
  rw [e, connForm_add, crystallineConnectionForm_coboundaryZero, ← sub_eq_zero]
  change connForm F.1 _ _ + D R₀ (Sec s₀ U.unop.1) (hU U) - D R₀ (Sec s₀ U.unop.1) (qU U) -
    (connForm F.1 _ _ + D R₀ (Sec s₀ U.unop.1) (S.p U (g U))) = 0
  rw [← hD]; abel

theorem r_eq_neg_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ c ∈ S.K hI, ∀ w, FormOf hI hk c w → ∀ z : Z1 S'.F, (∀ U V a, z.1 U V a = θ U V a (w.1 U)) → S'.r hI c = -H1.mk _ z := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hC S S' Φ θ hΘ c hc w hw z hz
  have T := fun (U V : AffOp X₀) ↦ GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero R R₀ I hI π hπ hk X₀ s₀ S S' U V
  choose Q hQ using fun U ↦ (T U U).1
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 (LinearMap.mem_ker.1 hc)
  obtain ⟨F, hF, hFw⟩ := hw
  obtain ⟨h, hh⟩ := H1.mk_eq_mk.1
    (show H1.mk _ ((redMor hI hk s₀).coef.pullbackOneCocycle f) = H1.mk _ F.1 from hF.symm)
  let ΦU : ∀ U : AffOp X₀, S.thickObj hI U ⟶ S'.thickObj hI U := fun U ↦
    S.thickHom S' hI (𝟙 U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) fun b ↦
      (Φ.red U b).trans (mp_id (OAff s₀) U (S.p U b)).symm
  change H1.mk _ ((S'.coef hI).pullbackOneCocycle f) = -H1.mk _ z
  rw [← map_neg, H1.mk_eq_mk]
  refine ⟨fun U ↦ Φ.φ U (g U) + ev f (ΦU U), ?_⟩
  funext U V a
  let α : S.thickObj hI U ⟶ S'.thickObj hI V := ΦU U ≫ (S'.thick hI).map a
  let β : S.thickObj hI U ⟶ S'.thickObj hI V := (S.thick hI).map a ≫ ΦU V
  have hθ : IsTheta I (S.p U) α.φ β.φ (θ U V a) := hΘ U V a
  have tay := (T U V).2 (Q U) (hQ U) α β (θ U V a) hθ f
  rw [connForm_sub_eq hI hk hC S Q hQ f g hg F h hh U, map_add (f := _)] at tay
  erw [hθ.der (g U)] at tay
  have hw' : connForm F.1 (affPt s₀ U.unop) (affPt_w s₀ U.unop) = w.1 U := by
    rw [← hFw, cmpForm_apply]
  rw [hw', ← hz] at tay
  have E1 : ev f α = mp S'.F a (ev f (ΦU U)) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) := ev_comp f _ _
  have E2 : ev f β = Φ.φ V (ev f ((S.thick hI).map a)) + ev f (ΦU V) := ev_comp f _ _
  have h3 : ev f ((S.thick hI).map a) = g V - mp S.F a (g U) := by
    have := congrArg (fun q ↦ q U V a) hg
    simp only [amitsur_d0_apply] at this
    exact this.symm
  rw [h3, map_sub] at E2
  have E3 : α.φ (g U) = mp S'.F a (Φ.φ U (g U)) := rfl
  have E4 : β.φ (g U) = Φ.φ V (mp S.F a (g U)) := rfl
  erw [E3, E4] at tay
  change Φ.φ V (g V) + ev f (ΦU V) - mp S'.F a (Φ.φ U (g U) + ev f (ΦU U)) =
    @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) - -z.1 U V a
  rw [map_add (f := _)]
  have key : ∀ x y z' p q r s t u : S'.F.obj V, x - y = z' + (p - q) → y = r + s → x = t - q + u →
      t + u - (p + r) = s - -z' := by
    intro x y z' p q r s t u h₁ h₂ h₃
    linear_combination h₁ + h₂ - h₃
  exact key _ _ _ _ _ _ _ _ _ tay E1 E2

end GlobalTheory.LiftSys
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_twist_squareZeroSmoothLiftSystem_by_derivationCocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S : Sys I π s₀) (v : GlobForm s₀ →+ Z1 S.F), (∀ w, S.IsIdealValuedLiftSystemCocycle (v w)) → (∀ (r : R) w, v (π r • w) = r • v w) → ∃ (S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ ∧ ∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = Φ.φ V ((v w).1 U V a) := by
  first | exact @GlobalTheory.LiftSys.exists_twist | exact GlobalTheory.LiftSys.exists_twist | (intros; apply GlobalTheory.LiftSys.exists_twist <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_scheme_presenting_squareZeroSmoothLiftSystem : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ S : Sys I π s₀, ∃ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsClosedImmersion i ∧ Surjective i ∧ Nonempty (S.Presents s i) := by
  first | exact @GlobalTheory.LiftGlue.exists_presents | exact GlobalTheory.LiftGlue.exists_presents | (intros; apply GlobalTheory.LiftGlue.exists_presents <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem weil_unit_phase_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (q : ℕ), q.Prime → 2 < q → ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} → ∏ w : InfinitePlace F, ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  intro F E _ _ _ _ _ _ σ h emb q hq hq2 ht u hu
  have hr := GlobalTheory.T.unit_real_of_sub_one_mem_span_prime E q hq ht u hu
  have hs := GlobalTheory.T.prod_arg_real_unit_eq_one' E q hq hq2 u hu hr
  obtain ⟨hF, hE, h2, -⟩ := h
  let f : InfinitePlace F → InfinitePlace E := fun w => InfinitePlace.mk (emb w).1
  have hcomap : ∀ w, (f w).comap (algebraMap F E) = w := by
    intro w
    simp only [f]
    rw [InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
  have hinj : Function.Injective f := fun a b hab => by
    rw [← hcomap a, ← hcomap b, hab]
  have hcard : Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace E) := by
    have a1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have a2 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have b1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
    have b2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    have c1 := IsTotallyReal.nrComplexPlaces_eq_zero F
    have c2 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have d := Module.finrank_mul_finrank ℚ F E
    rw [h2] at d
    omega
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  have hfac : ∀ w, (emb w).1 ((u : 𝓞 E) : E) = (f w).embedding ((u : 𝓞 E) : E) := by
    intro w
    rcases InfinitePlace.embedding_mk_eq (emb w).1 with h' | h'
    · simp only [f]; rw [h']
    · simp only [f]; rw [h', ComplexEmbedding.conjugate_coe_eq, hr]
  rw [← hs]
  rw [← Fintype.prod_bijective f hbij (fun w => ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun v => (v.embedding ((u : 𝓞 E) : E) / ((‖v.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun w => by rw [hfac w])]

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cohomology_subsingleton_of_cechPicardClass_eq : ∀ (X : Scheme.{0}) (M N : LB X) (hM : M.IsLB) (hN : N.IsLB), cls M hM = cls N hN → ∀ q : ℕ, Subsingleton (coh (LB.toMod M) q) → Subsingleton (coh (LB.toMod N) q) := by
  first | exact @GlobalTheory.Div.coh_subsingleton_of_cls_eq | exact GlobalTheory.Div.coh_subsingleton_of_cls_eq | (intros; apply GlobalTheory.Div.coh_subsingleton_of_cls_eq <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_pushforward_closedImmersion : ∀ (k : Type) [Field k] (X Z : Scheme.{0}) [Algebra k Γ(X, ⊤)] (g : Z ⟶ X) [IsClosedImmersion g] (L : LB X), L.IsLB → ∀ (G : Z.Modules) (m i : ℕ), letI := algebraΓAlong k g; hdim k (twist ((Scheme.Modules.pushforward g).obj G) (lbPow L m)) i = hdim k (twist G (lbPow (L.pull g) m)) i := by
  first | exact @GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion | exact GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion | (intros; apply GlobalTheory.hdim_twist_pushforward_lbPow_of_isClosedImmersion <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

theorem _root_.GlobalTheory.T.exists_descended_normIdealSheaf_finite_normal : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π], IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) → CharZero Γ(Y, ⊤) →
    ∀ I : Y.IdealSheafData, ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      CharZero K ∧ ∃ J : Z.IdealSheafData, (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ U : Z.affineOpens, (U : Set Z) ⊆ Set.range π → (U : Set Z).Nonempty →
        ∃ (_ : Algebra Γ(Z, U) K) (_ : Algebra Γ(Y, π ⁻¹ᵁ U.1) L),
          IsDomain Γ(Z, U) ∧ IsIntegrallyClosed Γ(Z, U) ∧ IsDomain Γ(Y, π ⁻¹ᵁ U.1) ∧ (π.app U.1).hom.Finite ∧
          IsFractionRing Γ(Z, U) K ∧ IsFractionRing Γ(Y, π ⁻¹ᵁ U.1) L ∧
          (algebraMap K L).comp (algebraMap Γ(Z, U) K) = (algebraMap Γ(Y, π ⁻¹ᵁ U.1) L).comp (π.app U.1).hom ∧
          J.ideal U = GlobalTheory.NormSheaf.normIdeal Γ(Z, U) K L Γ(Y, π ⁻¹ᵁ U.1) (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) := by
  first | exact @GlobalTheory.NormSheafDescent.descendedIdealSheaf_exists | exact GlobalTheory.NormSheafDescent.descendedIdealSheaf_exists | (intros; apply GlobalTheory.NormSheafDescent.descendedIdealSheaf_exists <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defectSec_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  intro Q q _ hqQ U u hQ V g
  have hQV : IsUnit (Q : Γ(V, ⊤)) := by
    have := hQ.map g.appTop.hom
    simpa using this
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ V).1
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.2 hQV (Units.map g.appTop.hom.toMonoidHom u)) ?_
  rintro W h ⟨v, hv⟩
  have hres : Sec.res h (Sec.res g (defectSec Q q U u)) = Sec.res (h ≫ g) (defectSec Q q U u) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hres, GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ V _ hQV W h v hv]
  refine GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ W (h ≫ g) v ?_
  rw [hv]
  ext
  simp [Scheme.Hom.comp_appTop] <;> rfl

end GlobalTheory.EtC.RedChern
end
