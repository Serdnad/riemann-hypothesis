module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle243
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LineConst

noncomputable section

namespace GlobalTheory.LineConst
open Polynomial

variable {k : Type} [Field k]

private theorem scaleX_isUnit (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    IsUnit ((algebraMap (Polynomial R) (Localization.Away (X : Polynomial R))).comp (scaleHom k R u) X) := by
  simp only [RingHom.comp_apply, scaleHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_mul]
  refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)
  exact ((isUnit_iff_exists_inv.mpr ⟨v, huv⟩).map Polynomial.C).map _

private def psiHom (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    Localization.Away (X : Polynomial k) →+* Localization.Away (X : Polynomial R) :=
  IsLocalization.Away.lift (X : Polynomial k) (scaleX_isUnit R huv)

private theorem psi_loc (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    (algebraMap (Polynomial R) (Localization.Away (X : Polynomial R))).comp (scaleHom k R u) =
      (psiHom R huv).comp (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k))) :=
  RingHom.ext fun a => by simp only [RingHom.comp_apply, psiHom, IsLocalization.Away.lift_eq]

private theorem psi_inv (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
        Localization.Away (X : Polynomial R))).toRingHom.comp (scaleHom k R v) =
      (psiHom R huv).comp (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial k) :
        Localization.Away (X : Polynomial k))).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    have e : (algebraMap k (Localization.Away (X : Polynomial k))) a =
        algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (X : Polynomial k))]
      rfl
    have e2 : (algebraMap R (Localization.Away (X : Polynomial R))) (algebraMap k R a) =
        algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C (algebraMap k R a)) := by
      rw [IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away (X : Polynomial R))]
      rfl
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C, e, psiHom,
      IsLocalization.Away.lift_eq]
    simp [scaleHom, e2]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
    have hb : psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) =
        algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C u) *
          algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) X := by
      simp [psiHom, IsLocalization.Away.lift_eq, scaleHom]
    have hc : psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) *
        psiHom R huv (IsLocalization.Away.invSelf (X : Polynomial k) : Localization.Away (X : Polynomial k)) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have hl : (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
        Localization.Away (X : Polynomial R))) (scaleHom k R v X) *
        psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) = 1 := by
      rw [hb]
      have hv : (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
          Localization.Away (X : Polynomial R))) (scaleHom k R v X) =
          algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C v) *
            IsLocalization.Away.invSelf (X : Polynomial R) := by
        simp [scaleHom, Polynomial.aeval_def, Polynomial.eval₂_mul]
        congr 1
      rw [hv]
      calc _ = algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C (v * u)) *
            (algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) X *
              IsLocalization.Away.invSelf (X : Polynomial R)) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [IsLocalization.Away.mul_invSelf, mul_comm v u, huv, map_one, map_one, _root_.one_mul]
    exact left_inv_eq_right_inv hl hc

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem scaled_loc (B : Over (Sp k)) (f₀ f₁ : Sp (Polynomial k) ⟶ B.left)
    (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)))
    (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)))
    (hyp : spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁)
    (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ (scaled B f₀ h0 R u).left =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ (scaled B f₁ h1 R v).left := by
  change _ ≫ spMap (scaleHom k R u) ≫ f₀ = _ ≫ spMap (scaleHom k R v) ≫ f₁
  rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, psi_loc R huv, psi_inv R huv,
    ← sp_comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) (psiHom R huv),
    Category.assoc, hyp, ← Category.assoc, sp_comp]

private def locOver (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) :=
  Over.mk (spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R))))

private def locIncl (R : Type) [CommRing R] [Algebra k R] : locOver (k := k) R ⟶ lineOver k R :=
  Over.homMk (spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)))) (by
    change spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫
      spMap (algebraMap k (Polynomial R)) = spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R)))
    rw [sp_comp, ← IsScalarTower.algebraMap_eq])

private def locInv (R : Type) [CommRing R] [Algebra k R] : locOver (k := k) R ⟶ lineOver k R :=
  Over.homMk (spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
      Localization.Away (Polynomial.X : Polynomial R))).toRingHom) (by
    change spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
      Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫
      spMap (algebraMap k (Polynomial R)) = spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R)))
    have e : (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom.comp (algebraMap k (Polynomial R)) =
        algebraMap k (Localization.Away (Polynomial.X : Polynomial R)) := by
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.algebraMap_apply,
        Polynomial.aeval_C]
      exact (IsScalarTower.algebraMap_apply k R (Localization.Away (Polynomial.X : Polynomial R)) a).symm
    rw [sp_comp, e])

theorem famMap_loc_eq : ∀ {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f₀ f₁ : Sp (Polynomial k) ⟶ B.left) (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k))) (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k))), spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ (R : Type) [CommRing R] [Algebra k R] (u v : R), u * v = 1 → spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ famMap B f₀ h0 R u = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ famMap B f₁ h1 R v := by
  intro k _ B _ f₀ f₁ h0 h1 hyp R _ _ u v huv
  have hs : ∀ {a b : R}, a * b = 1 → locIncl (k := k) R ≫ scaled B f₀ h0 R a = locInv R ≫ scaled B f₁ h1 R b := by
    intro a b hab
    ext1
    exact scaled_loc B f₀ f₁ h0 h1 hyp R hab
  have h := congrArg CommaMorphism.left
    (show locIncl (k := k) R ≫ (scaled B f₀ h0 R u * (scaled B f₀ h0 R 1)⁻¹) =
        locInv R ≫ (scaled B f₁ h1 R v * (scaled B f₁ h1 R 1)⁻¹) by
      rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_mul, GrpObj.comp_inv, hs huv, hs (_root_.one_mul 1)])
  exact h

end GlobalTheory.LineConst
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integral_twisted_comparison_at_fixed_section : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  first | exact @GlobalTheory.SectionLattice.integralAtSection_of_conj | exact GlobalTheory.SectionLattice.integralAtSection_of_conj | (intros; apply GlobalTheory.SectionLattice.integralAtSection_of_conj <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical


theorem _root_.GlobalTheory.T.schwartz_inverse_theta_transform_on_real_translates : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ 𝒱 : Set (VA F N → ℂ), (∀ f ∈ 𝒱, Continuous f ∧ QuasiV ψ f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) → (∀ f ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ 𝒱, ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0) → (∀ f ∈ 𝒱, ∀ (x : Fin N → AF F) (k : ℕ), ∃ C : ℝ, ∀ t : Fin N → mixedEmbedding.mixedSpace F, ‖t‖ ^ k * ‖invV ψ ν 𝓓 f (x + embR t)‖ ≤ C) → ∀ f ∈ 𝒱, ∀ x : Fin N → AF F, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = invV ψ ν 𝓓 f (x + embR t) := by
  first | exact @GlobalTheory.ThetaTransform.schwartz_invV_realTranslate | exact GlobalTheory.ThetaTransform.schwartz_invV_realTranslate | (intros; apply GlobalTheory.ThetaTransform.schwartz_invV_realTranslate <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.KerGermInj

open GlobalTheory.AbLaw

theorem gs_id {P : Scheme.{0}} (O : P.Opens) (y : P) (hy : y ∈ O) (a : Γ(P, O)) :
    gs (𝟙 P) y O a = (P.presheaf.germ O y hy).hom a := by
  rw [gs_eq _ y O hy]; rfl

theorem gs_comp {Y Z X : Scheme.{0}} (f : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (f z) ∈ U)
    (a : Γ(X, U)) : gs (f ≫ h) z U a = (f.stalkMap z).hom (gs h (f z) U a) := by
  rw [← gs_pull f h z U hU, gs_eq f z (h ⁻¹ᵁ U) hU, gs_eq h (f z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply f (h ⁻¹ᵁ U) z hU _).symm

theorem fromSpecStalk_comp {R : Type} [CommRing R] {T : Scheme.{0}} (t : T ⟶ Sp R) (x : T) :
    T.fromSpecStalk x ≫ t =
      Spec.map (CommRingCat.ofHom ((T.presheaf.germ ⊤ x trivial).hom.comp (GlobalTheory.FormsLocus.cstT t))) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.FormsLocus.cstT]

theorem eq_zero : ∀ (R : Type) [CommRing R] (X T X' : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (Q : GlobalTheory.AbLaw.Perf f M) (t : T ⟶ Sp R) (φ : X' ⟶ X) (p : X' ⟶ T), IsPullback φ p f t → ∀ e : Fin Q.a → Γ(T, ⊤), (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)).mulVec e = 0 → (∀ (z : X') (i : Q.I), φ z ∈ Q.W i → ∑ k, gs p z ⊤ (e k) * gs φ z (Q.W i) (Q.u k i) = 0) → e = 0 := by
  intro R _ X T X' f M Q t φ p hpb e he hz
  funext k
  apply TopCat.Presheaf.section_ext T.sheaf ⊤
  intro x hx
  change (T.presheaf.germ ⊤ x hx).hom (e k) = (T.presheaf.germ ⊤ x hx).hom 0
  rw [map_zero]
  let ψ : Γ(T, ⊤) →+* T.presheaf.stalk x := (T.presheaf.germ ⊤ x hx).hom
  let ρ : R →+* T.presheaf.stalk x := ψ.comp (GlobalTheory.FormsLocus.cstT t)
  let g := T.fromSpecStalk x
  let fst := pullback.fst p g
  let snd := pullback.snd p g
  let π := fst ≫ φ
  have hsq : IsPullback π snd f (Spec.map (CommRingCat.ofHom ρ)) := by
    have hg : g ≫ t = Spec.map (CommRingCat.ofHom ρ) := fromSpecStalk_comp t x
    have h3 := (IsPullback.of_hasPullback p g).paste_horiz hpb
    rw [hg] at h3
    exact h3
  obtain ⟨E, hE⟩ := Q.sec _ ρ _ π snd hsq
  have hv : (Q.D₀.map ρ).mulVec (fun k => ψ (e k)) = 0 := by
    funext j
    have h1 := RingHom.map_mulVec ψ (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)) e j
    rw [he, Pi.zero_apply, map_zero, Matrix.map_map] at h1
    exact h1.symm
  have hloc : ∀ w : {v : Fin Q.a → T.presheaf.stalk x // (Q.D₀.map ρ).mulVec v = 0},
      (∀ i, ∑ k, cst snd (π ⁻¹ᵁ Q.W i) (w.1 k) * (π.app (Q.W i)).hom (Q.u k i) = 0) → E w = 0 := by
    intro w hw
    have hcov : ⨆ i, π ⁻¹ᵁ Q.W i = ⊤ := Q.iSup_preimage (π := π)
    refine sec_eq_zero_of_local (L := M.pull π) (fun i => π ⁻¹ᵁ Q.W i) hcov
      (fun i => (fun _ => Q.ch i : (M.pull π).ι)) (fun i => le_pull M π (Q.le i)) (E w) ?_
    intro i
    exact (hE w i).trans (hw i)
  have h0 : E ⟨0, by rw [Matrix.mulVec_zero]⟩ = 0 :=
    hloc _ fun i => Finset.sum_eq_zero fun k _ => by
      have hc0 : cst snd (π ⁻¹ᵁ Q.W i) 0 = 0 := map_zero _
      exact (congrArg (· * _) hc0).trans (zero_mul _)
  have h1 : E ⟨fun k => ψ (e k), hv⟩ = 0 := by
    refine hloc _ fun i => ?_
    apply fn_ext
    intro y hy
    have hyi : φ (fst y) ∈ Q.W i := hy

    rw [gs_id _ y hy, gs_id _ y hy, map_zero, map_sum]
    simp only [map_mul]
    have hu : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom ((π.app (Q.W i)).hom (Q.u k i)) =
        (fst.stalkMap y).hom (gs φ (fst y) (Q.W i) (Q.u k i)) := by
      intro k
      rw [← gs_id _ y hy, gs_pull (𝟙 _) π y (Q.W i) hyi, Category.id_comp]
      exact gs_comp fst φ y (Q.W i) hyi _
    have hc : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom (cst snd (π ⁻¹ᵁ Q.W i) (ψ (e k))) =
        (fst.stalkMap y).hom (gs p (fst y) ⊤ (e k)) := by
      intro k
      have hcond : fst ≫ p = snd ≫ g := pullback.condition
      have hA := congrArg (fun h => h.hom (e k)) (Scheme.fromSpecStalk_appTop (X := T) (x := x))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hA
      rw [← gs_id _ y hy, ← gs_comp fst p y ⊤ trivial, hcond]
      refine Eq.trans ?_ (gs_pull snd g y ⊤ trivial (e k))
      refine Eq.trans ?_ (congrArg (gs snd y (g ⁻¹ᵁ ⊤)) hA.symm)
      refine Eq.trans ?_ (gs_res snd y _ (show snd y ∈ g ⁻¹ᵁ ⊤ from trivial) _).symm
      refine Eq.trans (gs_res (𝟙 _) y le_top hy _) ?_
      refine Eq.trans (gs_pull (𝟙 _) snd y ⊤ trivial _) ?_
      rw [Category.id_comp]
      rfl
    have hsum : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom (cst snd (π ⁻¹ᵁ Q.W i) (ψ (e k))) *
        ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom ((π.app (Q.W i)).hom (Q.u k i)) =
        (fst.stalkMap y).hom (gs p (fst y) ⊤ (e k) * gs φ (fst y) (Q.W i) (Q.u k i)) := fun k => by
      rw [hc k, hu k, map_mul]
    simp only [hsum]

    rw [← map_sum, hz (fst y) i hyi, map_zero]
  have h2 := congrFun (congrArg Subtype.val (E.injective (h1.trans h0.symm))) k
  exact h2

end GlobalTheory.KerGermInj
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHBundle

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ}

theorem mem_of_ex_eq {L L' : LB A.left} (u : HolUnif A L g) (u' : HolUnif A L' g) (hex : u'.ex = u.ex)
    {z : Fin g → ℂ} (hz : z ∈ u.Λ) : z ∈ u'.Λ := by
  rw [← u'.ker, hex, u.ker]; exact hz

theorem isFactorAH_divUnif {M M' : LB A.left} (u : HolUnif A M g) (u' : HolUnif A M' g) (hex : u'.ex = u.ex)
    {H H' : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ}
    (h : IsFactorAH u H χ) (h' : IsFactorAH u' H' χ') :
    IsFactorAH (GlobalTheory.SameFactor.divUnif u u' hex) (H' - H)
      (fun l => χ' ⟨l.1, mem_of_ex_eq u u' hex l.2⟩ / χ l) := by
  refine ⟨h'.1.sub h.1, fun l => ?_, fun l p z hz => ?_⟩
  · have := h.2.1 l
    rw [norm_div, h'.2.1]
    exact (by rw [this]; norm_num : (1 : ℝ) / ‖χ l‖ = 1)
  · obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
    have hl : u.ex (z + l) = u.ex z := by
      rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
    have e' := h'.2.2 ⟨l.1, mem_of_ex_eq u u' hex l.2⟩ p.1 z (by rw [hex]; exact h1)
    have e := h.2.2 l p.2 z h2
    have n1 := u.fr_ne p.2 z h2
    have n2 := u.fr_ne p.2 (z + l) (by rw [hl]; exact h2)
    have nχ : χ l ≠ 0 := by
      intro h0; have := h.2.1 l; rw [h0, norm_zero] at this; exact zero_ne_one this
    show u'.fr p.1 z * (u.fr p.2 z)⁻¹ = _ * _ * (u'.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹)
    rw [e', e]
    simp only [Matrix.sub_mulVec, dotProduct_sub, mul_sub]
    rw [show ∀ a b c d : ℂ, a - b + (c - d) = (a + c) - (b + d) from fun _ _ _ _ => by ring, Complex.exp_sub]
    have ne := Complex.exp_ne_zero (↑Real.pi * (z ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) +
        ↑Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))))
    field_simp

end GlobalTheory.AHBundle

theorem GlobalTheory.AHBundle.exists_lb_of_factor_chain {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A]
    (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ) (hL₀ : L₀.IsLB)
    (h₀ : IsFactorAH u₀ H₀ χ₀) (H' : Matrix (Fin g) (Fin g) ℂ)
    (M₁ : LB A.left) (u₁ : HolUnif A M₁ g) (χ₁ : u₁.Λ → ℂ) (hM₁ : M₁.IsLB) (hex₁ : u₁.ex = u₀.ex)
    (h₁ : IsFactorAH u₁ H' χ₁) (k : ℕ) :
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ IsFactorAH u (H' - k • H₀) χ := by
  induction k with
  | zero => exact ⟨M₁, u₁, χ₁, hM₁, hex₁, by simpa using h₁⟩
  | succ k ih =>
    obtain ⟨M, u, χ, hM, hex, h⟩ := ih
    have hd := GlobalTheory.AHBundle.isFactorAH_divUnif u₀ u hex h₀ h
    have e : H' - (k + 1) • H₀ = (H' - k • H₀) - H₀ := by rw [succ_nsmul, sub_add_eq_sub_sub]
    rw [← e] at hd
    exact ⟨_, _, _, LB.isLB_div hM hL₀, rfl, hd⟩

theorem GlobalTheory.AHBundle.exists_lb_of_hermitian_int : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ IsFactorAH u Hm χ := by
  intro g A _ hA L₀ u₀ H₀ χ₀ hL₀ hAH Hm hHm hint
  obtain ⟨n, hn⟩ := (GlobalTheory.T.exists_nat_posDef_add_nsmul_posDef_hermitian) g H₀ Hm hAH.2.1
  have hint0 := (GlobalTheory.T.appellHumbertFactor_imForm_integral_on_lattice) g A L₀ u₀ H₀ χ₀ hL₀ (isFactorAH_of_isAH hAH)
  have hint' : ∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ m : ℤ, (l ⬝ᵥ (Hm + n • H₀).mulVec (star l')).im = m := by
    intro l hl l' hl'
    obtain ⟨m₁, e₁⟩ := hint l hl l' hl'
    obtain ⟨m₂, e₂⟩ := hint0 l hl l' hl'
    refine ⟨m₁ + n * m₂, ?_⟩
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, Complex.add_im,
      nsmul_eq_mul, Complex.mul_im, e₁, e₂]
    push_cast; simp
  have hH' : (Hm + n • H₀).IsHermitian := hHm.add (by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_nsmul, hAH.1.eq])
  obtain ⟨M₁, u₁, χ₁, hM₁, hex₁, h₁⟩ := (GlobalTheory.T.appellHumbert_exists_lineBundle_posDef_hermitian) g A hA L₀ u₀ H₀ χ₀ hL₀ hAH (Hm + n • H₀) hH' hn hint'
  obtain ⟨M, u, χ, hM, hex, h⟩ := GlobalTheory.AHBundle.exists_lb_of_factor_chain L₀ u₀ H₀ χ₀ hL₀ (isFactorAH_of_isAH hAH)
    _ M₁ u₁ χ₁ hM₁ hex₁ (isFactorAH_of_isAH h₁) n
  refine ⟨M, u, χ, hM, hex, ?_⟩
  simpa using h
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := by
  first | exact @GlobalTheory.FockMapEx.fockEx_of_derEx | exact GlobalTheory.FockMapEx.fockEx_of_derEx | (intros; apply GlobalTheory.FockMapEx.fockEx_of_derEx <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineLocus

theorem isLocus_of_isAffineOpen_of_meets_fibres : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ c : Pic A.left, IsLocus c V := by
  intro R _ _ _ _ A _ hA V hV hfib
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hnS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.IsNormalScheme.pred (Sp R)
  obtain ⟨U, c, hU, hc⟩ := GlobalTheory.T.exists_cartier_locus_over_dense_open_base R A hA V hV hfib
  have hVW : V ≤ A.hom ⁻¹ᵁ U ⊔ V := le_sup_right
  have h0 : GlobalTheory.CechPic.pull (A.left.homOfLE hVW) c = 0 := by
    refine GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.2 _ _ _ c _ hc fun y => ?_
    show (A.left.homOfLE hVW ≫ (A.hom ⁻¹ᵁ U ⊔ V).ι) y ∈ V
    rw [Scheme.homOfLE_ι]
    exact y.2
  obtain ⟨c', hc'⟩ := GlobalTheory.T.two_smul_picardClass_extends_abelianScheme (Sp R) hnS A hA U V hU hfib c h0
  have h2 : IsLocus (GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c') ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
    rw [hc', two_nsmul, ← inf_idem ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V)]
    exact hc.add hc
  have : Flat A.hom := inferInstance
  have : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hbig := GlobalTheory.T.mem_preimage_sup_of_stalk_krullDim_le_one_flat A.left (Sp R) A.hom V U hfib hU
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : A.left.IsSeparated := by
    have : IsSeparated (terminal.from A.left) := by rw [← terminal.comp_from A.hom]; infer_instance
    exact ⟨this⟩
  have : GlobalTheory.IsNormalScheme A.left := GlobalTheory.isNormalScheme_of_smooth A.hom
  exact ⟨c', GlobalTheory.T.nonvanishingLocus_extend_from_big_open A.left (GlobalTheory.IsNormalScheme.pred _) V _ hV hVW hbig c' h2⟩

end GlobalTheory.AffineLocus
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_twoTorsion_rigidTranslate_same_mumfordBundle : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (L' : LB P.A.left), L'.IsLB → Rigidified P.A L' → Sym P.A L' → LBIso (abelian₂ P.A L') (abelian₂ P.A P.L) → ∃ x : 𝟙_ (Over (Sp R)) ⟶ P.A, x * x = 1 ∧ LBIso L' (GlobalTheory.RigidTranslate.rigTransl P.L x) := by
  first | exact @GlobalTheory.SymPrincipalTranslate.exists_two_torsion_rigTransl | exact GlobalTheory.SymPrincipalTranslate.exists_two_torsion_rigTransl | (intros; apply GlobalTheory.SymPrincipalTranslate.exists_two_torsion_rigTransl <;> assumption)
end
