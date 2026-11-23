module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle855
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle856
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerateWhittakerDimParabolicInductionCuspidal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityEqSumDegenerate
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle796
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem lTensor_liftSemi_bijective_of_isBaseChange {R R' B B' W W' Ω Ω' : Type} [CommRing R]
    [CommRing R'] [Algebra R R'] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R' B']
    [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R' W']
    [AddCommGroup Ω] [Module R Ω] [Module B Ω] [IsScalarTower R B Ω]
    [AddCommGroup Ω'] [Module R' Ω'] [Module B' Ω'] [IsScalarTower R' B' Ω']
    (α : B →+* B') (f : B →ₛₗ[algebraMap R R'] B') (hf : ∀ b, f b = α b)
    (h1 : Function.Surjective (liftSemi f))
    (m : Ω →ₛₗ[algebraMap R R'] Ω') (hm : ∀ (b : B) (ω : Ω), m (b • ω) = α b • m ω)
    (h2 : Function.Bijective (liftSemi m))
    (e : W →ₗ[R] Ω) (he : IsBaseChange B e) (e' : W' →ₗ[R'] Ω') (he' : IsBaseChange B' e')
    (p : W →ₛₗ[algebraMap R R'] W') (hp : ∀ w, e' (p w) = m (e w)) :
    Function.Bijective (LinearMap.lTensor B' (liftSemi p)) := by
  letI : Module R (B' ⊗[R'] (R' ⊗[R] W)) := Module.compHom _ (algebraMap R R')
  have hsm : ∀ (c : R) (z : B' ⊗[R'] (R' ⊗[R] W)), c • z = algebraMap R R' c • z := fun _ _ ↦ rfl
  have hR : ∀ (c : R) (x : R' ⊗[R] B), c • x = algebraMap R R' c • x := fun c x ↦
    (algebraMap_smul R' c x).symm
  have hW : ∀ (c : R) (w : W), (1 : R') ⊗ₜ[R] (c • w) = algebraMap R R' c • ((1 : R') ⊗ₜ[R] w) := by
    intro c w
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
      Algebra.algebraMap_eq_smul_one]

  let bil : R' ⊗[R] B →ₗ[R] W →ₗ[R] B' ⊗[R'] (R' ⊗[R] W) :=
    LinearMap.mk₂ R (fun x w ↦ liftSemi f x ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] w))
      (fun x y w ↦ by rw [map_add (f := _), TensorProduct.add_tmul])
      (fun c x w ↦ by rw [hR, map_smul, hsm, TensorProduct.smul_tmul'])
      (fun x w w' ↦ by rw [TensorProduct.tmul_add, TensorProduct.tmul_add])
      (fun c x w ↦ by rw [hW, TensorProduct.tmul_smul, hsm])
  let Ψ : R' ⊗[R] (B ⊗[R] W) →ₗ[R] B' ⊗[R'] (R' ⊗[R] W) :=
    TensorProduct.lift bil ∘ₗ (TensorProduct.assoc R R' B W).symm.toLinearMap
  have hΨ : Function.Surjective Ψ := by
    suffices hall : ∀ z, z ∈ LinearMap.range Ψ from
      LinearMap.range_eq_top.1 (eq_top_iff.2 fun z _ ↦ hall z)
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul b t =>
      induction t using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
      | tmul r w =>
        obtain ⟨x, hx⟩ := h1 (r • b)
        refine ⟨TensorProduct.assoc R R' B W (x ⊗ₜ w), ?_⟩
        have e1 : r ⊗ₜ[R] w = r • ((1 : R') ⊗ₜ[R] w) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
          TensorProduct.lift.tmul, bil, LinearMap.mk₂_apply, hx, e1, ← TensorProduct.smul_tmul]
  let Θ : R' ⊗[R] (B ⊗[R] W) ≃ₗ[R] R' ⊗[R] Ω := (he.equiv.restrictScalars R).lTensor R'
  have hΘ : Function.Bijective (fun z ↦ liftSemi m (Θ z)) := h2.comp Θ.bijective
  have key : ∀ z, he'.equiv (LinearMap.lTensor B' (liftSemi p) (Ψ z)) = liftSemi m (Θ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
    | tmul r t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
      | tmul b w =>
        simp only [Ψ, Θ, bil, LinearMap.comp_apply, LinearEquiv.coe_coe,
          TensorProduct.assoc_symm_tmul, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
          liftSemi_tmul, LinearMap.lTensor_tmul, LinearEquiv.lTensor_tmul,
          LinearEquiv.restrictScalars_apply, IsBaseChange.equiv_tmul, one_smul, hf, hp, hm,
          map_smul, smul_assoc]
  refine ⟨fun x y hxy ↦ ?_, fun q ↦ ?_⟩
  · obtain ⟨x0, rfl⟩ := hΨ x
    obtain ⟨y0, rfl⟩ := hΨ y
    have := hΘ.1 (show liftSemi m (Θ x0) = liftSemi m (Θ y0) by rw [← key, ← key, hxy])
    rw [this]
  · obtain ⟨z, hz⟩ := hΘ.2 (he'.equiv q)
    refine ⟨Ψ z, he'.equiv.injective ?_⟩
    rw [key]; exact hz

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem lTensor_liftSemi_pullForm_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → ∀ U : X.affineOpens, IsAffineOpen (φ ⁻¹ᵁ U.1) → Function.Bijective (LinearMap.lTensor (Sec s' (φ ⁻¹ᵁ U.1)) (liftSemi (pullForm h.w))) := by
  intro R R' _ _ _ X X' s s' φ h hF hH hF' hH' U hU
  let U' : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, hU⟩
  let pr : Pair φ := ⟨(U', U), le_rfl⟩
  have hsemi : SemiHom (algebraMap R R') (GlobalTheory.CechDR.secPull s s' pr) := GlobalTheory.CechDR.semiHom_secPull h.w pr
  let f : Sec s U.1 →ₛₗ[algebraMap R R'] Sec s' (φ ⁻¹ᵁ U.1) :=
    { toFun := GlobalTheory.CechDR.secPull s s' pr, map_add' := map_add _, map_smul' := hsemi }
  have h1 : Function.Bijective (liftSemi f) :=
    GlobalTheory.CechDR.bijective_liftSemi_secPull R R' X X' s s' φ h pr rfl f (fun _ ↦ rfl)
  have h2 : Function.Bijective (liftSemi hsemi.m1) :=
    GlobalTheory.kaehler_liftSemi_bijective R R' _ _ (GlobalTheory.CechDR.secPull s s' pr) hsemi f (fun _ ↦ rfl) h1
  let e : GlobForm s →ₗ[R] Ω[Sec s U.1⁄R] :=
    { toFun := fun w ↦ w.1 (Opposite.op U), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have he : IsBaseChange (Sec s U.1) e :=
    isBaseChange_glob1 R (AffOp X) (OAff s) hF hH (Opposite.op U) e (fun _ ↦ rfl)
  let e' : GlobForm s' →ₗ[R'] Ω[Sec s' (φ ⁻¹ᵁ U.1)⁄R'] :=
    { toFun := fun w ↦ w.1 (Opposite.op U'), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have he' : IsBaseChange (Sec s' (φ ⁻¹ᵁ U.1)) e' :=
    isBaseChange_glob1 R' (AffOp X') (OAff s') hF' hH' (Opposite.op U') e' (fun _ ↦ rfl)
  exact lTensor_liftSemi_bijective_of_isBaseChange (GlobalTheory.CechDR.secPull s s' pr) f (fun _ ↦ rfl) h1.2 hsemi.m1
    (fun b ω ↦ hsemi.oneFormMap_smul_semilinear b ω) h2 e he e' he' (pullForm h.w)
    (fun w ↦ ((isPullForm_iff.1 (isPullForm_pullForm h.w w)) pr).symm)

end GlobalTheory.AbCoh
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → CohomZeroIsConstants (OAff q') → ∀ (u : HO1 s₀) (y : HO1 s), TMul h₀.w t u y → pullHO1 w y = 0 → pullHO1 w₀ u = 0 := by
  first | exact @GlobalTheory.AbCoh.tmul_pull_eq_zero | exact GlobalTheory.AbCoh.tmul_pull_eq_zero | (intros; apply GlobalTheory.AbCoh.tmul_pull_eq_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sum_cup_oneForms_zero_imp_coordinates_zero : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • toO F (a k) = 0 := by
  first | exact @GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup | exact GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup | (intros; apply GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sumWedgeGlobalOneForms_eq_zero_iff : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (n : ℕ) (u v : Fin n → Glob1 F), wsum F u v = 0 ↔ ∀ l l' : Glob1 F →ₗ[R] R, ∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k)) = 0 := by
  first | exact @GlobalTheory.AbCoh.wsum_eq_zero_iff | exact GlobalTheory.AbCoh.wsum_eq_zero_iff | (intros; apply GlobalTheory.AbCoh.wsum_eq_zero_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.finrank_characterEigenspace_inf_ker_le : ∀ (Γ V : Type) [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (H : Fin 2 → Subgroup Γ) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ Γ) (b : Fin 2 → MonoidAlgebra ℂ Γ) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ (H k) (n k)) → (∀ k, (n k : ℝ) * Nat.card (H k) ≤ c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) → (∀ k, b k * b k = b k) → (∀ k, b k * Formalism.L2.DIV.lvlIdem Hb lam = Formalism.L2.DIV.lvlIdem Hb lam * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff 1 = (s k : ℂ) / (Nat.card Hb : ℂ)) → (finrank ℂ (eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by
  first | exact @GlobalTheory.BadCount.finrank_eig_inf_ker_le | exact GlobalTheory.BadCount.finrank_eig_inf_ker_le | (intros; apply GlobalTheory.BadCount.finrank_eig_inf_ker_le <;> assumption)
end

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.degenerateWhittakerDim_parabolicInduction_cuspidal : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ j : ℕ, j < r ∨ j = 0 → whCut ψ (parInd b σ) j = splitDoublingNBlock b j * leviWh ψ b σ := by
  first | exact @GlobalTheory.FinGL.WhCutInd.degenerateWhittakerDim_parabolicInduction | exact GlobalTheory.FinGL.WhCutInd.degenerateWhittakerDim_parabolicInduction | (intros; apply GlobalTheory.FinGL.WhCutInd.degenerateWhittakerDim_parabolicInduction <;> assumption)
end

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_eq_sum_degenerateWhittaker : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V) (k : ℕ), k + 1 ≤ r → nPos ψ τ 0 k = ∑ j ∈ Finset.range (k + 1), gam (Fintype.card F) (k - j) * whCut ψ τ j := by
  first | exact @GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum | exact GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum | (intros; apply GlobalTheory.FinGL.PosOne.nPos_zero_eq_sum <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_A_eq {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) (n : ℕ) :
    Module.finrank k (G.A n) = p ^ (n * G.height) := by
  have h := G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

theorem existsUnique_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q : PDivGroup p k)
    (q : G ⟶ Q), IsIsog q → ∃! e : ℕ, HasLogDeg q e := by
  intro p _ k _ _ G Q q hq
  have hp : p.Prime := Fact.out
  obtain ⟨n, q', h1, -⟩ := hq
  have hlag := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k (G.A n) (Q.A n) (q.app n)
  rw [finrank_A_eq] at hlag
  have hdvd : Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) ∣ p ^ (n * G.height) :=
    ⟨_, hlag.trans (mul_comm _ _)⟩
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  refine ⟨e, ⟨n, fun m hm => (GlobalTheory.T.finrank_quot_kernelIdeal_eq_beyond_exponent p k G Q n m q q' h1 hm).trans he⟩, ?_⟩
  rintro e' ⟨N, hN⟩
  have h2 := hN (max N n) (le_max_left _ _)
  rw [GlobalTheory.T.finrank_quot_kernelIdeal_eq_beyond_exponent p k G Q n (max N n) q q' h1 (le_max_right _ _), he] at h2
  exact Nat.pow_right_injective hp.two_le h2.symm

end GlobalTheory.Dieu
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HilbFam.EBasis

theorem bijective_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : E →+* ℂ) (θ : E),
    (ψ θ).im ≠ 0 → Function.Bijective (fun x : Fin 2 → FR E ↦ (x 0 : E) * θ + (x 1 : E)) := by
  intro E _ _ _ ψ θ hθ
  let f : (Fin 2 → FR E) →ₗ[FR E] E :=
    { toFun := fun x ↦ (x 0 : E) * θ + (x 1 : E)
      map_add' := fun x y ↦ by simp only [Pi.add_apply, Subfield.coe_add]; ring
      map_smul' := fun c x ↦ by
        simp only [Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, RingHom.id_apply, Subfield.smul_def]
        ring }
  have hreal : ∀ a : FR E, (ψ (a : E)).im = 0 := fun a ↦ by
    have h : star (ψ (a : E)) = ψ (a : E) := a.2 ψ
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have e : (x 0 : E) * θ + (x 1 : E) = 0 := hx
    have e2 := congrArg ψ e
    rw [map_add (f := _), map_mul, map_zero] at e2
    have him := congrArg Complex.im e2
    simp only [Complex.add_im, Complex.mul_im, hreal, mul_zero, zero_mul, add_zero, Complex.zero_im] at him
    have h0re : (ψ (x 0 : E)).re = 0 := (mul_eq_zero.1 him).resolve_right hθ
    have h0 : ψ (x 0 : E) = 0 := Complex.ext h0re (hreal _)
    have hx0 : x 0 = 0 := Subtype.ext ((map_eq_zero ψ).1 h0)
    have hx1 : x 1 = 0 := by
      rw [hx0] at e
      simpa using e
    funext i
    fin_cases i
    · exact hx0
    · exact hx1
  have hdim : Module.finrank (FR E) (Fin 2 → FR E) = Module.finrank (FR E) E := by
    rw [Module.finrank_fin_fun, Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

end GlobalTheory.HilbFam.EBasis
end
end

section

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD)

namespace GlobalTheory.JetExp

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_mul {r r' : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r' y) : Sz l lam (r + r') (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have e : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [e, map_mul, norm_mul, Real.rpow_add hl]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (h : r ≤ r') (hx : Sz l lam r x) : Sz l lam r' x :=
  ⟨hx.1, hx.2.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) h)⟩

theorem sz_one : Sz l lam 0 1 := ⟨one_mem _, by
  have e : (⟨1, one_mem _⟩ : algebraicClosure ℚ ℂ) = 1 := rfl
  rw [e, map_one, norm_one, Real.rpow_zero]⟩

theorem sz_prod {ι : Type} (t : Finset ι) (r : ι → ℝ) (f : ι → ℂ) (h : ∀ i ∈ t, Sz l lam (r i) (f i)) :
    Sz l lam (∑ i ∈ t, r i) (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (sz_one (l := l) (lam := lam))
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact sz_mul (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem norm_factorial_inv_le (n : ℕ) : ‖((n.factorial : ℂ_[l]))‖⁻¹ ≤ (l : ℝ) ^ (n : ℝ) := by
  have hp : l.Prime := Fact.out
  have e1 : ((n.factorial : ℂ_[l])) = (((n.factorial : ℚ) : ℚ_[l]) : ℂ_[l]) := by simp
  rw [e1, PadicComplex.norm_extends', Padic.eq_padicNorm,
    padicNorm.eq_zpow_of_nonzero (by exact_mod_cast Nat.factorial_ne_zero n), padicValRat.of_nat]
  have hv : multiplicity l n.factorial ≤ n := multiplicity_factorial_le l n
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hp.one_lt.le
  rw [Rat.cast_zpow, Rat.cast_natCast, zpow_neg, inv_inv, zpow_natCast, Real.rpow_natCast]
  exact pow_le_pow_right₀ hl1 hv

theorem sz_factorial_inv (n : ℕ) : Sz l lam (n : ℝ) ((n.factorial : ℂ)⁻¹) := by
  have hm : ((n.factorial : ℂ)⁻¹) ∈ algebraicClosure ℚ ℂ := inv_mem (natCast_mem _ _)
  refine ⟨hm, ?_⟩
  have e : (⟨(n.factorial : ℂ)⁻¹, hm⟩ : algebraicClosure ℚ ℂ) = ((n.factorial : algebraicClosure ℚ ℂ))⁻¹ := by
    ext; simp
  rw [e, map_inv₀, map_natCast, norm_inv]
  exact norm_factorial_inv_le n

theorem expansion_of_jetInt : JetInt → Expansion := by
  classical
  intro hJ E _ _ _ _ I _ d φ s hφ hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ _ lam Ω hΩ
  obtain ⟨a, b, hab, hX⟩ := hJ E I d φ s hφ hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy lam Ω hΩ
  refine ⟨a, b, hab, fun g κ u hg hu => ?_⟩
  have h1 := hX g κ u hg hu
  have h2 : Sz l lam ((∑ i, κ i : ℕ) : ℝ) (∏ i, ((κ i).factorial : ℂ)⁻¹) := by
    rw [Nat.cast_sum]
    exact sz_prod _ _ _ fun i _ => sz_factorial_inv (κ i)
  have e : iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ))) =
      (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s))) * ∏ i, ((κ i).factorial : ℂ)⁻¹ := by
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_mul_eq_div_div, div_eq_mul_inv (_ / _)]
  rw [e]
  refine sz_mono ?_ (sz_mul h1 h2)
  have hK : (0 : ℝ) ≤ ((∑ i, κ i : ℕ) : ℝ) := Nat.cast_nonneg _
  split_ifs <;> nlinarith

end GlobalTheory.JetExp
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam

theorem isIntegral_coord_of_isIntegral (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ)
    (x : Fin 2 → FR E) (_hD : 0 < D) (hθ : IsIntegral ℤ θ)
    (hr : (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E))
    (hu : IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E))) (j : Fin 2) :
    IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  have hc : ∀ y : E, IsIntegral ℤ y → IsIntegral ℤ (IsCMField.complexConj E y) := fun y hy =>
    map_isIntegral_int (IsCMField.complexConj E) hy
  have hfix : ∀ y : FR E, IsCMField.complexConj E (y : E) = y := fun y =>
    IsCMField.complexConj_apply_eq_self E y
  set r := θ - IsCMField.complexConj E θ with hrdef
  have hri : IsIntegral ℤ r := hθ.sub (hc _ hθ)
  have h0 : IsIntegral ℤ ((x 0 : E) * r) := by
    have := hu.sub (hc _ hu)
    rw [map_add (f := _), map_mul, hfix, hfix] at this
    have e : (x 0 : E) * r = (x 0 : E) * θ + (x 1 : E) -
        ((x 0 : E) * IsCMField.complexConj E θ + (x 1 : E)) := by rw [hrdef]; ring
    rw [e]; exact this
  have h1 : IsIntegral ℤ ((x 1 : E) * r) := by
    have := (hu.mul hri).sub (h0.mul hθ)
    have e : (x 1 : E) * r = ((x 0 : E) * θ + (x 1 : E)) * r - (x 0 : E) * r * θ := by ring
    rw [e]; exact this
  have hj : IsIntegral ℤ ((x j : E) * r) := by
    fin_cases j
    · exact h0
    · exact h1
  have hD' : (D : E) = -r ^ 2 := by rw [hr]; ring
  have hinj : Function.Injective (algebraMap (FR E) E) := (algebraMap (FR E) E).injective
  have hx : algebraMap (FR E) E (x j) = (x j : E) := rfl
  constructor
  · rw [← (isIntegral_algebraMap_iff (B := E)), map_mul, map_pow, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) ^ 2 = -((x j : E) * r * ((x j : E) * r)) := by ring
    rw [e]; exact (hj.mul hj).neg
  · rw [← (isIntegral_algebraMap_iff (B := E)), map_mul, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) = -((x j : E) * r * r) := by ring
    rw [e]; exact (hj.mul hri).neg

end GlobalTheory.HilbFam
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.JSW.MirPatch

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def cell (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a) : Set (GA E a) :=
  {p | ∃ u ∈ NA (E := E) (a := a), ∃ k ∈ K, ∃ y : GL (Fin a) (Cinf E), p = u * q * finGL E a k * infGL E a y}

theorem self_mem_cell (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a) : q ∈ cell K q :=
  ⟨1, ⟨fun i j h => by simp [Matrix.one_apply_ne (Fin.ne_of_gt h)], fun i => by simp⟩, 1, K.one_mem, 1, by simp⟩

end GlobalTheory.JSW.MirPatch
end
end
