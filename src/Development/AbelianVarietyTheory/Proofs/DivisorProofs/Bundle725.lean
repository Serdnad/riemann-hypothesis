module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamTotalDifferentialOneFunctionPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle686
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem cupHyp_add_cupHyp_swap : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    ∀ a b : Hyp1 F, cupHyp F a b + cupHyp F b a = 0 := by
  intro R _ C _ F a b
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rw [cupHyp_mk, cupHyp_mk, ← map_add (f := _)]
  refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * b.1.1 T T' φ), 0), ?_⟩
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
  · simp only [cechDeRhamTotalDifferentialOne_functionPart, Submodule.coe_add, Prod.fst_add, Pi.add_apply, coe_cupZZ, cupTot_apply,
      cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_mul, map_neg]
    ring
  · simp only [dTot1_a, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, coe_cupZZ,
      cupTot_a, map_neg, Derivation.leibniz, Pi.zero_apply, map_zero]
    rw [cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]
    module
  · simp only [dTot1_η, Submodule.coe_add, Prod.snd_add, Pi.add_apply, coe_cupZZ, cupTot_η,
      Pi.zero_apply, map_zero]
    rw [wedge_swap (a.1.2 T), neg_add_cancel]

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.KunnethOne

theorem tensor_eq_zero_of_forall {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (t : V ⊗[K] W)
    (h : ∀ l : W →ₗ[K] K, TensorProduct.rid K V (LinearMap.lTensor V l t) = 0) : t = 0 := by
  classical
  let b := Module.Free.chooseBasis K W
  have key : ∀ (j : Module.Free.ChooseBasisIndex K W) (s : V ⊗[K] W),
      TensorProduct.equivFinsuppOfBasisRight b s j =
        TensorProduct.rid K V (LinearMap.lTensor V (b.coord j) s) := by
    intro j s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext j
  rw [key, h, map_zero, Finsupp.zero_apply]

section Contr

variable {K : Type} [Field K] {Q : Type} [Category.{0} Q] (G : Q ⥤ CommAlgCat.{0} K)
  [Fintype Q] [DecidableEq Q] [∀ T T' : Q, Fintype (T ⟶ T')] [∀ T T' : Q, DecidableEq (T ⟶ T')]

def coef (Λ : C1 G →ₗ[K] K) (T T' : Q) (φ : T ⟶ T') : G.obj T' →ₗ[K] K :=
  Λ ∘ₗ LinearMap.single K (fun T => ∀ (T' : Q) (_ : T ⟶ T'), G.obj T') T ∘ₗ
    LinearMap.single K (fun T' => (T ⟶ T') → G.obj T') T' ∘ₗ
    LinearMap.single K (fun _ : T ⟶ T' => G.obj T') φ

def contr (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K) :
    (∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') →ₗ[K] M :=
  ∑ T, ∑ T', ∑ φ : T ⟶ T', (TensorProduct.rid K M).toLinearMap ∘ₗ
    LinearMap.lTensor M (coef G Λ T T' φ) ∘ₗ
    LinearMap.proj (R := K) (φ := fun _ : T ⟶ T' => M ⊗[K] G.obj T') φ ∘ₗ
    LinearMap.proj (R := K) (φ := fun T' => (T ⟶ T') → M ⊗[K] G.obj T') T' ∘ₗ
    LinearMap.proj (R := K) (φ := fun T => ∀ (T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') T

theorem contr_apply (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K)
    (c : ∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :
    contr G M Λ c = ∑ T, ∑ T', ∑ φ : T ⟶ T',
      TensorProduct.rid K M (LinearMap.lTensor M (coef G Λ T T' φ) (c T T' φ)) := by
  simp [contr, LinearMap.sum_apply]

theorem contr_tmul (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K) (z : M)
    (h : C1 G) : contr G M Λ (fun T T' φ => z ⊗ₜ[K] h T T' φ) = Λ h • z := by
  rw [contr_apply]
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, ← Finset.sum_smul]
  congr 1

  simp only [coef, LinearMap.comp_apply, ← map_sum]
  congr 1
  simp only [LinearMap.single_apply, Finset.univ_sum_single]

theorem contr_natural (M N : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (Λ : C1 G →ₗ[K] K) (h : M →ₗ[K] N) (c : ∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :
    contr G N Λ (fun T T' φ => LinearMap.rTensor (G.obj T') h (c T T' φ)) = h (contr G M Λ c) := by

  simp only [contr_apply, map_sum]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun T' _ =>
    Finset.sum_congr rfl fun φ _ => ?_
  induction c T T' φ using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem kunneth_contraction_d0_vanishes (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K)
    (hΛ : ∀ g : C0 G, Λ (d0 G g) = 0) (w : ∀ T : Q, M ⊗[K] G.obj T) :
    contr G M Λ (fun T T' φ => LinearMap.lTensor M (mp G φ).toLinearMap (w T) - w T') = 0 := by
  let D : (∀ T : Q, M ⊗[K] G.obj T) →ₗ[K] (∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :=
    LinearMap.pi fun T => LinearMap.pi fun T' => LinearMap.pi fun φ =>
      LinearMap.lTensor M (mp G φ).toLinearMap ∘ₗ
        LinearMap.proj (R := K) (φ := fun T => M ⊗[K] G.obj T) T -
      LinearMap.proj (R := K) (φ := fun T => M ⊗[K] G.obj T) T'
  have hD : contr G M Λ ∘ₗ D = 0 := by
    refine LinearMap.pi_ext fun T₀ x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      have e : D (Pi.single T₀ (z ⊗ₜ[K] u)) =
          fun T T' φ => z ⊗ₜ[K] (-d0 G (Pi.single T₀ u : C0 G) T T' φ) := by
        funext T T' φ
        simp only [D, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.proj_apply, amitsur_d0_apply, neg_sub, TensorProduct.tmul_sub]
        by_cases h1 : T = T₀ <;> by_cases h2 : T' = T₀
        · subst h1; subst h2; simp
        · subst h1; simp [Pi.single_eq_of_ne h2]
        · subst h2; simp [Pi.single_eq_of_ne h1]
        · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
      have c := contr_tmul G M Λ z (-d0 G (Pi.single T₀ u : C0 G))
      simp only [Pi.neg_apply] at c
      rw [LinearMap.comp_apply, e, c, map_neg, hΛ, neg_zero, zero_smul, LinearMap.zero_apply]
    | add u v hu hv => simp only [Pi.single_add, map_add (f := _), hu, hv]
  exact LinearMap.congr_fun hD w

end Contr

end GlobalTheory.CatCoh.KunnethOne

namespace GlobalTheory.CatCoh.KunnethOne

theorem sum_tmul_eq_zero_of_cup : ∀ (K : Type) [Field K] (P Q : Type) [Category.{0} P] [Category.{0} Q] [Finite Q] [Quiver.IsThin Q] (F : P ⥤ CommAlgCat.{0} K) (G : Q ⥤ CommAlgCat.{0} K) (E : P × Q ⥤ CommAlgCat.{0} K) (i₁ : ∀ T : P × Q, F.obj T.1 →ₐ[K] E.obj T) (i₂ : ∀ T : P × Q, G.obj T.2 →ₐ[K] E.obj T), (∀ (T T' : P × Q) (a : T ⟶ T') (b : F.obj T.1), i₁ T' (mp F a.1 b) = mp E a (i₁ T b)) → (∀ (T T' : P × Q) (a : T ⟶ T') (b : G.obj T.2), i₂ T' (mp G a.2 b) = mp E a (i₂ T b)) → (∀ T, Function.Bijective (Algebra.TensorProduct.productMap (i₁ T) (i₂ T))) → ∀ (n : ℕ) (x : Fin n → Z1 F) (y : Fin n → Z1 G) (f : C1 E), (∀ (T T' T'' : P × Q) (a : T ⟶ T') (b : T' ⟶ T''), d1 E f T T' T'' a b = ∑ i, mp E b (i₁ T' ((x i).1 _ _ a.1)) * i₂ T'' ((y i).1 _ _ b.2)) → ∑ i, GlobalTheory.CatCoh.H1.mk F (x i) ⊗ₜ[K] GlobalTheory.CatCoh.H1.mk G (y i) = 0 := by
  intro K _ P Q _ _ _ _ F G E i₁ i₂ h₁ h₂ hb n x y f hf
  classical
  haveI := Fintype.ofFinite Q
  haveI : ∀ T T' : Q, Fintype (T ⟶ T') := fun _ _ => Fintype.ofFinite _
  apply tensor_eq_zero_of_forall
  intro l

  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend (l ∘ₗ H1.mk G)
  have hΛy : ∀ z : Z1 G, Λ z.1 = l (H1.mk G z) := fun z => LinearMap.congr_fun hΛ z
  have hΛd : ∀ g : C0 G, Λ (d0 G g) = 0 := fun g => by
    have e := hΛy ⟨d0 G g, commAlgFunctorCoboundaryZero_mem_cocyclesOne G g⟩
    rw [e, H1.mk_eq_zero.2 ⟨g, rfl⟩, map_zero]

  simp only [← hΛy, ← map_smul, ← map_sum]
  rw [H1.mk_eq_zero]
  let β : ∀ T : P × Q, F.obj T.1 ⊗[K] G.obj T.2 ≃ₐ[K] E.obj T :=
    fun T => AlgEquiv.ofBijective _ (hb T)
  have hβ : ∀ (T : P × Q) (z : F.obj T.1) (u : G.obj T.2), β T (z ⊗ₜ u) = i₁ T z * i₂ T u :=
    fun T z u => Algebra.TensorProduct.productMap_apply_tmul _ _ _ _
  have natL : ∀ (p p' : P) (T : Q) (a : p ⟶ p') (t : F.obj p ⊗[K] G.obj T),
      β (p', T) (LinearMap.rTensor (G.obj T) (mp F a).toLinearMap t) =
        mp E ((a, 𝟙 T) : (p, T) ⟶ (p', T)) (β (p, T) t) := by
    intro p p' T a t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      rw [LinearMap.rTensor_tmul, hβ, hβ, map_mul, ← h₁ (p, T) (p', T), ← h₂ (p, T) (p', T)]
      simp [mp_id]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  have natR : ∀ (p : P) (T T' : Q) (b : T ⟶ T') (t : F.obj p ⊗[K] G.obj T),
      β (p, T') (LinearMap.lTensor (F.obj p) (mp G b).toLinearMap t) =
        mp E ((𝟙 p, b) : (p, T) ⟶ (p, T')) (β (p, T) t) := by
    intro p T T' b t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      rw [LinearMap.lTensor_tmul, hβ, hβ, map_mul, ← h₁ (p, T) (p, T'), ← h₂ (p, T) (p, T')]
      simp [mp_id]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  refine ⟨fun p => contr G (F.obj p) Λ
    (fun T T' φ => (β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, φ) : (p, T) ⟶ (p, T')))), ?_⟩
  funext p p' a
  rw [amitsur_d0_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  have step : ∀ (T T' : Q) (b : T ⟶ T'),
      (β (p', T')).symm (f (p', T) (p', T') ((𝟙 p', b) : (p', T) ⟶ (p', T'))) -
        LinearMap.rTensor (G.obj T') (mp F a).toLinearMap
          ((β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, b) : (p, T) ⟶ (p, T')))) =
      ∑ i, (x i).1 p p' a ⊗ₜ[K] (y i).1 T T' b -
        (LinearMap.lTensor (F.obj p') (mp G b).toLinearMap
            ((β (p', T)).symm (f (p, T) (p', T) ((a, 𝟙 T) : (p, T) ⟶ (p', T)))) -
          (β (p', T')).symm (f (p, T') (p', T') ((a, 𝟙 T') : (p, T') ⟶ (p', T')))) := by
    intro T T' b
    apply (β (p', T')).injective
    have H1 := hf (p, T) (p', T) (p', T') (a, 𝟙 T) (𝟙 p', b)
    have H2 := hf (p, T) (p, T') (p', T') (𝟙 p, b) (a, 𝟙 T')
    rw [d1_apply] at H1 H2
    simp only [prod_comp, Category.comp_id, Category.id_comp] at H1 H2
    simp only [Z1.id, map_zero, zero_mul, Finset.sum_const_zero] at H2
    simp only [← h₁, mp_id] at H1

    simp only [map_sub, map_sum, AlgEquiv.apply_symm_apply, natL, natR, hβ]
    linear_combination H1 - H2
  have nat := contr_natural G (F.obj p) (F.obj p') Λ (mp F a).toLinearMap
    (fun T T' φ => (β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, φ) : (p, T) ⟶ (p, T'))))
  rw [AlgHom.toLinearMap_apply] at nat
  rw [← nat, ← map_sub]
  trans contr G (F.obj p') Λ ((∑ i, fun T T' φ => (x i).1 p p' a ⊗ₜ[K] (y i).1 T T' φ) -
    fun T T' φ => LinearMap.lTensor (F.obj p') (mp G φ).toLinearMap
        ((β (p', T)).symm (f (p, T) (p', T) ((a, 𝟙 T) : (p, T) ⟶ (p', T)))) -
      (β (p', T')).symm (f (p, T') (p', T') ((a, 𝟙 T') : (p, T') ⟶ (p', T'))))
  · congr 1
    funext T T' b
    simp only [Pi.sub_apply, Finset.sum_apply]
    exact step T T' b
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, kunneth_contraction_d0_vanishes _ _ _ hΛd, sub_zero, map_sum]
    simp only [contr_tmul]

end GlobalTheory.CatCoh.KunnethOne
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem cup_anticomm (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (a b : GlobalTheory.CatCoh.H1 F) : cup F a b = - cup F b a := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨a, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F b
  rw [cup_mk, cup_mk, ← map_add (f := _)]
  refine GlobalTheory.CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * b.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [d1_apply, Submodule.coe_add, Pi.add_apply, cupZ_apply, Z1.comp a, Z1.comp b, map_mul, map_neg]
  ring

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isAffineOpen_inf_preimage_of_isPullback {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y}
    {iX : X ⟶ S} {iY : Y ⟶ S} (H : IsPullback p q iX iY) [IsAffine S] {U : X.Opens}
    {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) := by
  have : IsAffine _ := isAffineOpen_top S
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V) (UX := U) le_top le_top
    rfl).isoPullback.hom

theorem appLE_appLE_of_comp {T X Y : Scheme.{0}} (f : T ⟶ X) (g : X ⟶ Y) (h : T ⟶ Y)
    (e : f ≫ g = h) {W : Y.Opens} {U : X.Opens} {N : T.Opens} (h1 : U ≤ g ⁻¹ᵁ W)
    (h2 : N ≤ f ⁻¹ᵁ U) (h3 : N ≤ h ⁻¹ᵁ W) (x : Γ(Y, W)) :
    (f.appLE U N h2).hom ((g.appLE W U h1).hom x) = (h.appLE W N h3).hom x := by
  subst e
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem functions_on_product_of_affine_opens : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (U : X.left.affineOpens) (V : Y.left.affineOpens), ∃ (W : (X ⊗ Y).left.affineOpens) (h₁ : W.1 ≤ (fst X Y).left ⁻¹ᵁ U.1) (h₂ : W.1 ≤ (snd X Y).left ⁻¹ᵁ V.1) (i₁ : Sec X.hom U.1 →ₐ[R] Sec (X ⊗ Y).hom W.1) (i₂ : Sec Y.hom V.1 →ₐ[R] Sec (X ⊗ Y).hom W.1), W.1 = (fst X Y).left ⁻¹ᵁ U.1 ⊓ (snd X Y).left ⁻¹ᵁ V.1 ∧ (∀ b, i₁ b = ((fst X Y).left.appLE U.1 W.1 h₁).hom b) ∧ (∀ b, i₂ b = ((snd X Y).left.appLE V.1 W.1 h₂).hom b) ∧ Function.Bijective (Algebra.TensorProduct.productMap i₁ i₂) := by
  intro R _ X Y U V
  have H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := .of_hasPullback _ _
  let W : (X ⊗ Y).left.affineOpens :=
    ⟨(fst X Y).left ⁻¹ᵁ U.1 ⊓ (snd X Y).left ⁻¹ᵁ V.1,
      isAffineOpen_inf_preimage_of_isPullback H U.2 V.2⟩
  have h₁ : W.1 ≤ (fst X Y).left ⁻¹ᵁ U.1 := inf_le_left
  have h₂ : W.1 ≤ (snd X Y).left ⁻¹ᵁ V.1 := inf_le_right
  let i₁ : Sec X.hom U.1 →ₐ[R] Sec (X ⊗ Y).hom W.1 :=
    { ((fst X Y).left.appLE U.1 W.1 h₁).hom with
      commutes' := fun r => by
        change ((fst X Y).left.appLE U.1 W.1 h₁).hom ((X.hom.appLE ⊤ U.1 le_top).hom _) =
          ((X ⊗ Y).hom.appLE ⊤ W.1 le_top).hom _
        exact appLE_appLE_of_comp _ _ _ (Over.w _) _ _ _ _ }
  let i₂ : Sec Y.hom V.1 →ₐ[R] Sec (X ⊗ Y).hom W.1 :=
    { ((snd X Y).left.appLE V.1 W.1 h₂).hom with
      commutes' := fun r => by
        change ((snd X Y).left.appLE V.1 W.1 h₂).hom ((Y.hom.appLE ⊤ V.1 le_top).hom _) =
          ((X ⊗ Y).hom.appLE ⊤ W.1 le_top).hom _
        exact appLE_appLE_of_comp _ _ _ (Over.w _) _ _ _ _ }
  refine ⟨W, h₁, h₂, i₁, i₂, rfl, fun b => rfl, fun b => rfl, ?_⟩
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := V.1) (UX := U.1) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) V.2 U.2)

  have po' : IsPushout (CommRingCat.ofHom (algebraMap R (Sec X.hom U.1)))
      (CommRingCat.ofHom (algebraMap R (Sec Y.hom V.1)))
      ((fst X Y).left.appLE U.1 W.1 h₁) ((snd X Y).left.appLE V.1 W.1 h₂) := by
    refine po.of_iso (Scheme.ΓSpecIso (CommRingCat.of R)) (Iso.refl (CommRingCat.of (Sec X.hom U.1)))
      (Iso.refl (CommRingCat.of (Sec Y.hom V.1)))
      (Iso.refl (CommRingCat.of (Sec (X ⊗ Y).hom W.1))) ?_ ?_ (by rfl) (by rfl)
    · ext r
      change (X.hom.appLE ⊤ U.1 le_top).hom r = (X.hom.appLE ⊤ U.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))
      congr 1
      simp
    · ext r
      change (Y.hom.appLE ⊤ V.1 le_top).hom r = (Y.hom.appLE ⊤ V.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))
      congr 1
      simp
  have h1 := CommRingCat.isPushout_tensorProduct R (Sec X.hom U.1) (Sec Y.hom V.1)
  let e := h1.isoIsPushout _ _ po'
  have he : e.hom = CommRingCat.ofHom (Algebra.TensorProduct.productMap i₁ i₂).toRingHom := by
    refine h1.hom_ext ?_ ?_
    · refine (h1.inl_isoIsPushout_hom _ _ po').trans ?_
      ext x
      exact (Algebra.TensorProduct.productMap_left_apply i₁ i₂ x).symm
    · refine (h1.inr_isoIsPushout_hom _ _ po').trans ?_
      ext x
      exact (Algebra.TensorProduct.productMap_right_apply i₁ i₂ x).symm
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  rw [he] at hb
  exact hb

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTan

theorem range_spMap_fst_eq (B M : Type) [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) = Set.univ := by
  refine Set.eq_univ_of_forall fun y ↦ ⟨spMap (TrivSqZeroExt.inlHom B M) y, ?_⟩
  change PrimeSpectrum.comap _ (PrimeSpectrum.comap _ y) = y
  apply PrimeSpectrum.ext
  ext x
  change (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) ∈ y.asIdeal ↔ x ∈ y.asIdeal
  have hm : (TrivSqZeroExt.inr x.snd : TrivSqZeroExt B M) ∈ y.asIdeal :=
    y.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact y.asIdeal.zero_mem)
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm
  constructor
  · intro h; rw [hx]; exact y.asIdeal.add_mem h hm
  · intro h
    have e : (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) = x - TrivSqZeroExt.inr x.snd := by
      rw [eq_sub_iff_add_eq]; exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x
    rw [e]; exact y.asIdeal.sub_mem h hm

theorem exists_unique_ringHom_of_sqZero (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (U : X.affineOpens) (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (ρ : Sec s U.1 →+* B) (z : Sp (TrivSqZeroExt B M) ⟶ X)
    (hz : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap ρ ≫ affPt s U) :
    ∃! c : Sec s U.1 →+* TrivSqZeroExt B M, spMap c ≫ affPt s U = z ∧ ∀ b, (c b).fst = ρ b := by
  have hr : Set.range z ⊆ Set.range (affPt s U) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ : y ∈ Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) := by
      rw [range_spMap_fst_eq]; trivial
    refine ⟨spMap ρ x, ?_⟩
    change (spMap ρ ≫ affPt s U) x = (spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z) x
    rw [hz]
  haveI : IsOpenImmersion (affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
  set g := IsOpenImmersion.lift (affPt s U) z hr with hg
  have hgf : g ≫ affPt s U = z := IsOpenImmersion.lift_fac _ _ _
  have hsp : ∀ c c' : Sec s U.1 →+* TrivSqZeroExt B M,
      spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c' := fun c c' h ↦ by
    have h' := (cancel_mono (affPt s U)).1 h
    have := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom this
  have hsp' : ∀ c c' : Sec s U.1 →+* B,
      spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c' := fun c c' h ↦ by
    have h' := (cancel_mono (affPt s U)).1 h
    have := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom this
  set c₀ : Sec s U.1 →+* TrivSqZeroExt B M := (Spec.preimage g).hom with hc₀
  have hc : spMap c₀ = g := Spec.map_preimage g
  have h₁ : spMap c₀ ≫ affPt s U = z := by rw [hc, hgf]
  refine ⟨c₀, ⟨h₁, ?_⟩, fun c hc' ↦ hsp _ _ (hc'.1.trans h₁.symm)⟩
  have e : spMap ((TrivSqZeroExt.fstHom B B M).toRingHom.comp c₀) ≫ affPt s U =
      spMap ρ ≫ affPt s U := by
    rw [← hz, ← h₁, ← Category.assoc, ← Spec.map_comp]; rfl
  intro b
  exact congrArg (fun f : Sec s U.1 →+* B ↦ f b) (hsp' _ _ e)

end GlobalTheory.AbTan
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem chart_ev_nmul_pow_self : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (i : Fin d), c.ev n (nmul c.μ (p ^ n) i) = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n i
  rw [GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c n (p ^ n) i, G.mulBy_pow_self n (c.x n i), c.aug n i, map_zero]

end GlobalTheory
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.coeff_quasiLogarithm_integral_low_degree : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ l : MvPowerSeries (Fin d) Q, QL μ ⊤ l → ∀ α : Fin d →₀ ℕ, α.degree ≤ p → (∀ i, α ≠ Finsupp.single i p) → ∃ b : B, coeff α l = algebraMap B Q b := by
  first | exact @GlobalTheory.QLogInt.coeff_integral_of_QL | exact GlobalTheory.QLogInt.coeff_integral_of_QL | (intros; apply GlobalTheory.QLogInt.coeff_integral_of_QL <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.ev_subst_natMultiple_prime_pow_constant : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, c.ev n (subst (nmul c.μ (p ^ n)) f) = algebraMap O _ (constantCoeff f)) ∧ (∀ s, c.ev₂ n (pull2 (nmul c.μ (p ^ n)) s) = algebraMap O _ (constantCoeff s)) ∧ ∀ f, c.ev (n + 1) (subst (nmul c.μ p) f) = G.mulP n (c.ev n f) := by
  first | exact @GlobalTheory.QLog.Chart.ev_nmul_pow | exact GlobalTheory.QLog.Chart.ev_nmul_pow | (intros; apply GlobalTheory.QLog.Chart.ev_nmul_pow <;> assumption)
end
