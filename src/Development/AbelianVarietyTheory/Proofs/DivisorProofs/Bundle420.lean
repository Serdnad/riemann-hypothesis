module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_ringHom_limit_of_doublingJets : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ∀ φ : ℕ → A → PowerSeries R, (∀ n, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 2) (φ n)) → (∀ n f, (PowerSeries.X : PowerSeries R) ^ (n + 2) ∣ φ (n + 1) f - φ n f) → ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧ PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧ (PowerSeries.rescale 2).comp γ = γ.comp m := by
  first | exact @GlobalTheory.Nef.PathJet.limit_of_jets | exact GlobalTheory.Nef.PathJet.limit_of_jets | (intros; apply GlobalTheory.Nef.PathJet.limit_of_jets <;> assumption)
end

section

open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.isDoublingJetOfOrder_two_firstOrder : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → GlobalTheory.Nef.PathJet.IsJet π ε m β δ 2 (fun f => PowerSeries.C (β (ε f)) + PowerSeries.C (δ f) * PowerSeries.X) := by
  first | exact @GlobalTheory.Nef.PathJet.firstOrder_isJet | exact GlobalTheory.Nef.PathJet.firstOrder_isJet | (intros; apply GlobalTheory.Nef.PathJet.firstOrder_isJet <;> assumption)
end

section

open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_isRingHomModXPow_succ_lift : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (β : B →+* R), π.FormallySmooth → ∀ n : ℕ, 1 ≤ n → ∀ φ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsRingHomMod π β n φ → ∃ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f := by
  first | exact @GlobalTheory.Nef.PathJet.exists_lift_succ | exact GlobalTheory.Nef.PathJet.exists_lift_succ | (intros; apply GlobalTheory.Nef.PathJet.exists_lift_succ <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem theta_bijective (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (U : T.affineOpens) :
    Function.Bijective (theta A B g U) := by
  letI := (secAlg A g U).toAlgebra
  let W : (pullback (str A B) g).Opens := pullback.snd (str A B) g ⁻¹ᵁ (U : T.Opens)
  have H := IsPullback.of_hasPullback (str A B) g
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := (U : T.Opens)) (UX := ⊤) (UY := W)
    le_top le_top (by simp [W])).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) U.2 (isAffineOpen_top _))
  have P₁ := CommRingCat.isPushout_tensorProduct A Γ(T, U) B
  have P₂ : IsPushout (CommRingCat.ofHom (algebraMap A Γ(T, U)))
      (CommRingCat.ofHom (algebraMap A B))
      ((pullback.snd (str A B) g).app U)
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (pullback.fst (str A B) g).appLE ⊤ W (by simp)) := by
    refine po.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of A)) (Iso.refl _)
      (Scheme.ΓSpecIso (CommRingCat.of B)) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← Iso.inv_comp_eq]; rfl
    · have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
      rw [← h1, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    · rw [Scheme.Hom.app_eq_appLE]; rfl
    · simp
  have e : CommRingCat.ofHom (theta A B g U) = (P₁.isoIsPushout _ _ P₂).hom := by
    apply P₁.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom]
      ext c
      have := theta_tmul A B g U c 1
      simp only [map_one, mul_one] at this
      exact this
    · rw [IsPushout.inr_isoIsPushout_hom]
      ext b
      have := theta_tmul A B g U 1 b
      simp only [map_one, one_mul] at this
      exact this
  have : IsIso (CommRingCat.ofHom (theta A B g U)) := by rw [e]; infer_instance
  exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (theta A B g U))

end GlobalTheory.HilbAff
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HilbAff

theorem bc_appLE_comp_psi :
    ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
      (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)) (U : Z.Opens),
      (letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
       ∀ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = secAlg C h U →
         ((bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
           ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U)
           (by simp)).hom.comp (psi A B C) =
         (theta A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).comp
           (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom) := by
  intro A B C _ _ _ _ _ Z h U
  let := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
  intro φ hφ
  have eL : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := C)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫ (pullbackSpecIso A B C).hom.appTop := by
    rw [← pullbackSpecIso_hom_fst, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have eR : (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫
      (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫ (pullbackSpecIso A B C).hom.appTop := by
    rw [← pullbackSpecIso_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  have hpsi : ∀ (c : C) (b : B), psi A B C (c ⊗ₜ[A] b) =
      (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
      (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
    intro c b
    have h1 := congrArg (fun F => F.hom b) eL
    have h2 := congrArg (fun F => F.hom c) eR
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
    rw [h1, h2, ← map_mul, ← map_mul]
    simp [psi]
  have eF : (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop ≫
      (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) =
      (pullback.fst (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) := by
    refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
    exact appLE_eq_of_eq ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) _ _ _ _
  have eS : (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop ≫
      (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) =
      h.appLE ⊤ U (by simp) ≫
        (pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).app U := by
    refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
    refine (appLE_eq_of_eq (f₂ := pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) ≫ h)
      (pullback.lift_snd _ _ _) _ _ _ (by simp)).trans ?_
    rw [Scheme.Hom.app_eq_appLE]; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    have hF := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) eF
    have hS := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)) eS
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hF hS
    have hc : φ c = secAlg C h U c := congrArg (fun f => f c) hφ
    rw [RingHom.comp_apply, hpsi, map_mul, hF, hS, RingHom.comp_apply]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      hc, mul_comm]
    have hθ : theta A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U
        (secAlg C h U c ⊗ₜ[A] b) =
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).app U).hom
          (secAlg C h U c) *
        ((pullback.fst (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).appLE ⊤
          ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U)
          (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
      let : Algebra A Γ(pullback (str A B)
          (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))),
          (pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) :=
        (((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).app U).hom.comp
          (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U)).toAlgebra
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    rw [hθ]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.HilbAff
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open GlobalTheory.HilbAff in

theorem _root_.GlobalTheory.T.affineHilbertBaseChange_appLE_comp_specTensor :
    ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
      (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)) (U : Z.Opens),
      (letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
       ∀ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = secAlg C h U →
         ((bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
           ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U)
           (by simp)).hom.comp (psi A B C) =
         (theta A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).comp
           (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom) := by
  intro A B C _ _ _ _ _ Z h U
  let := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
  intro φ hφ
  have eL : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := C)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫ (pullbackSpecIso A B C).hom.appTop := by
    rw [← pullbackSpecIso_hom_fst, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have eR : (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫
      (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫ (pullbackSpecIso A B C).hom.appTop := by
    rw [← pullbackSpecIso_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  have hpsi : ∀ (c : C) (b : B), psi A B C (c ⊗ₜ[A] b) =
      (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
      (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
    intro c b
    have h1 := congrArg (fun F => F.hom b) eL
    have h2 := congrArg (fun F => F.hom c) eR
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
    rw [h1, h2, ← map_mul, ← map_mul]
    simp [psi]
  have eF : (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop ≫
      (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) =
      (pullback.fst (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) := by
    refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
    exact appLE_eq_of_eq ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) _ _ _ _
  have eS : (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop ≫
      (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) =
      h.appLE ⊤ U (by simp) ≫
        (pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).app U := by
    refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
    refine (appLE_eq_of_eq (f₂ := pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) ≫ h)
      (pullback.lift_snd _ _ _) _ _ _ (by simp)).trans ?_
    rw [Scheme.Hom.app_eq_appLE]; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    have hF := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) eF
    have hS := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)) eS
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hF hS
    have hc : φ c = secAlg C h U c := congrArg (fun f => f c) hφ
    rw [RingHom.comp_apply, hpsi, map_mul, hF, hS, RingHom.comp_apply]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      hc, mul_comm]
    have hθ : theta A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U
        (secAlg C h U c ⊗ₜ[A] b) =
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).app U).hom
          (secAlg C h U c) *
        ((pullback.fst (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).appLE ⊤
          ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U)
          (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
      let : Algebra A Γ(pullback (str A B)
          (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))),
          (pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) :=
        (((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).app U).hom.comp
          (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U)).toAlgebra
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    rw [hθ]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem xI_ideal_top (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
    (J : Ideal (C ⊗[A] B)) :
    (GlobalTheory.HilbAff.xI A B C J).ideal ⟨⊤, isAffineOpen_top _⟩ = J.map (GlobalTheory.HilbAff.psi A B C) := by
  set X := pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C))) with hX
  set e := pullbackSpecIso A B C
  set q : CommRingCat.of (B ⊗[A] C) ⟶ CommRingCat.of ((C ⊗[A] B) ⧸ J) :=
    CommRingCat.ofHom ((Ideal.Quotient.mk J).comp (Algebra.TensorProduct.comm A B C).toRingHom) with hq
  set f : Spec (CommRingCat.of ((C ⊗[A] B) ⧸ J)) ⟶ X := Spec.map q ≫ e.inv with hf
  have hxI : xI A B C J = f.ker := rfl
  have h1 : e.hom.appTop ≫ f.appTop = (Spec.map q).appTop := by
    rw [hf, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
    simp
  have h2 := Scheme.ΓSpecIso_inv_naturality q
  have hcomp : f.appTop.hom.comp (psi A B C) =
      (Scheme.ΓSpecIso (CommRingCat.of ((C ⊗[A] B) ⧸ J))).inv.hom.comp (Ideal.Quotient.mk J) := by
    refine RingHom.ext fun x => ?_
    simp only [psi, RingHom.comp_apply]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, h1, ← h2, CommRingCat.comp_apply]
    congr 1
    simp only [hq, CommRingCat.hom_ofHom, RingHom.comp_apply]
    congr 1
    rw [← Algebra.TensorProduct.comm_symm]
    exact (Algebra.TensorProduct.comm A B C).apply_symm_apply x
  have hsurj : Function.Surjective (psi A B C) := by
    intro y
    refine ⟨(Algebra.TensorProduct.comm A C B).symm
      ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).hom.hom ((pullbackSpecIso A B C).inv.appTop.hom y)), ?_⟩
    simp only [psi, RingHom.comp_apply]
    have h3 : (pullbackSpecIso A B C).inv.appTop ≫ (pullbackSpecIso A B C).hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]; rfl
    have h5 : ∀ z, (Algebra.TensorProduct.comm A C B).toRingEquiv.toRingHom
        ((Algebra.TensorProduct.comm A C B).symm z) = z := fun z =>
      (Algebra.TensorProduct.comm A C B).apply_symm_apply z
    have h6 : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).hom.hom z) = z := fun z => by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    rw [h5, h6, ← CommRingCat.comp_apply, h3, CommRingCat.id_apply]
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of ((C ⊗[A] B) ⧸ J))).inv.hom := by
    intro a b h
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ((C ⊗[A] B) ⧸ J))).hom.hom h
    simpa using this
  have hker : RingHom.ker f.appTop.hom = J.map (psi A B C) := by
    rw [← Ideal.map_comap_of_surjective _ hsurj (RingHom.ker f.appTop.hom), RingHom.comap_ker, hcomp]
    congr 1
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
  rw [hxI, Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal, hker]
  convert Ideal.map_id _
  rw [show ∀ h : (⊤ : X.Opens) ≤ ⊤, homOfLE h = 𝟙 _ from fun _ => Subsingleton.elim _ _, op_id,
    CategoryTheory.Functor.map_id]
  rfl

end GlobalTheory.HilbAff
end

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory

theorem traceOpen_near_of_isUnit : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  intro R _ _ _ a b hsq g hg hu W hW
  set s := g.re with hs
  let φ : R × R → ℍ[R, a, b] := fun p => ⟨p.1, p.2 * g.imI, p.2 * g.imJ, p.2 * g.imK⟩
  have hφ : Continuous φ := by
    apply continuous_induced_rng.2
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa [coords, φ] using continuous_fst
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
  have hφs : φ (s, 1) = g := by ext <;> simp [φ, s]
  have hpre : φ ⁻¹' W ∈ 𝓝 (s, (1 : R)) := hφ.continuousAt.preimage_mem_nhds (by rw [hφs]; exact hW)
  obtain ⟨O₀, hO₀, V, hV, hOV⟩ := mem_nhds_prod_iff.1 hpre
  obtain ⟨U, hU, hUV⟩ := hsq V hV
  set c : R := ((hu.unit⁻¹ : Rˣ) : R) with hc_def
  have hc : c * (1 - s ^ 2) = 1 := by
    rw [hc_def]
    have := hu.unit.inv_mul
    simpa using this
  let r : R → R := fun t => (1 - t ^ 2) * c
  have hr : Continuous r := (continuous_const.sub (continuous_id.pow 2)).mul continuous_const
  have hrs : r s = 1 := by simp only [r]; rw [mul_comm]; exact hc
  refine ⟨interior (O₀ ∩ r ⁻¹' U), isOpen_interior, ?_, ?_⟩
  · rw [mem_interior_iff_mem_nhds]
    refine Filter.inter_mem hO₀ ?_
    exact hr.continuousAt.preimage_mem_nhds (by rw [hrs]; exact hU)
  · intro t ht
    have ht' := interior_subset ht
    obtain ⟨μ, hμV, hμ⟩ := hUV (r t) ht'.2
    refine ⟨φ (t, μ), hOV (Set.mk_mem_prod ht'.1 hμV), ?_, rfl⟩
    have hμ' : μ ^ 2 = (1 - t ^ 2) * c := hμ
    simp only [nrm, φ] at hg ⊢
    linear_combination μ ^ 2 * hg + (1 - s ^ 2) * hμ' + (1 - t ^ 2) * hc

end GlobalTheory
end

section

noncomputable section

open scoped Quaternion Topology

namespace GlobalTheory.QSA

namespace TraceOpenPi

variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {a b : ∀ i, R i}

def comp (i : ι) (x : ℍ[∀ i, R i, a, b]) : ℍ[R i, a i, b i] :=
  ⟨x.re i, x.imI i, x.imJ i, x.imK i⟩

def glue (u : ∀ i, ℍ[R i, a i, b i]) : ℍ[∀ i, R i, a, b] :=
  ⟨fun i => (u i).re, fun i => (u i).imI, fun i => (u i).imJ, fun i => (u i).imK⟩

theorem glue_comp (x : ℍ[∀ i, R i, a, b]) : glue (fun i => comp i x) = x := by
  ext <;> rfl

theorem nrm_comp (i : ι) (x : ℍ[∀ i, R i, a, b]) : nrm (comp i x) = nrm x i := by
  simp [nrm, comp]

theorem nrm_glue (u : ∀ i, ℍ[R i, a i, b i]) : nrm (glue u) = fun i => nrm (u i) := by
  funext i
  simp [nrm, glue]

theorem coords_glue (u : ∀ i, ℍ[R i, a i, b i]) : coords (glue u) = fun k i => coords (u i) k := by
  funext k i
  fin_cases k <;> rfl

theorem continuous_glue [∀ i, TopologicalSpace (R i)] :
    Continuous (glue : (∀ i, ℍ[R i, a i, b i]) → ℍ[∀ i, R i, a, b]) := by
  refine continuous_induced_rng.2 ?_
  have : (coords ∘ (glue : (∀ i, ℍ[R i, a i, b i]) → ℍ[∀ i, R i, a, b])) =
      fun u k i => coords (u i) k := by
    funext u
    exact coords_glue u
  rw [this]
  refine continuous_pi fun k => continuous_pi fun i => ?_
  have hc : Continuous (coords : ℍ[R i, a i, b i] → Fin 4 → R i) := continuous_induced_dom
  exact ((continuous_apply k).comp hc).comp (continuous_apply i)

end TraceOpenPi


open TraceOpenPi in
theorem traceOpen_pi : ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] (a b : ∀ i, R i),
    (∀ i, TraceOpen (R i) (a i) (b i)) → TraceOpen (∀ i, R i) a b := by
  intro ι _ R _ _ a b h g hg W hW
  have hgi : ∀ i, nrm (comp i g) = 1 := fun i => by
    rw [nrm_comp, hg]; rfl
  have hW' : glue ⁻¹' W ∈ 𝓝 (fun i => comp i g) := by
    refine continuous_glue.continuousAt.preimage_mem_nhds ?_
    rw [glue_comp]; exact hW
  rw [nhds_pi, Filter.mem_pi] at hW'
  obtain ⟨I, -, V, hV, hVW⟩ := hW'
  have hO := fun i => h i (comp i g) (hgi i) (V i) (hV i)
  choose O hOo hOn hOt using hO
  refine ⟨Set.univ.pi O, isOpen_set_pi Set.finite_univ fun i _ => hOo i,
    Set.univ_pi_nonempty_iff.2 hOn, fun t ht => ?_⟩
  have ht' := fun i => hOt i (t i) (ht i (Set.mem_univ i))
  choose u huV hun hur using ht'
  refine ⟨glue u, hVW fun i _ => huV i, ?_, ?_⟩
  · rw [nrm_glue]; funext i; exact hun i
  · funext i; exact hur i

end GlobalTheory.QSA
end
end
