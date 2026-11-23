module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

namespace GlobalTheory.HomMumAdd

variable {S : Scheme.{0}}

theorem prod_mumford {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum G (x2 G) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  have e : ∀ I : ULift.{0} (Finset (Fin 2)), (lift x y).left ≫ (psum G (x2 G) I.down).left =
      (psum G ![x, y] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 G) I.down).trans
      (congrArg (fun q => psum G q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum G ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_neg, zpow_one]
  ac_rfl

variable {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]

theorem prod_pair (a b : H₁ ⟶ H₂) {T : Over S} (x y : T ⟶ H₁) {U : Type} [CommGroup U]
    (h : (T.left ⟶ H₁.left ⨿ H₂.left) → U) :
    ∏ I : MK, h ((lift x y).left ≫ mφ H₁ H₂ a b I) ^ mε I =
      (h (((x ≫ a) * (y ≫ b)).left ≫ coprod.inr) * (h ((x ≫ a).left ≫ coprod.inr))⁻¹ *
        (h ((y ≫ b).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ H₂).left ≫ coprod.inr)) *
      (h ((x * y).left ≫ coprod.inl) * (h (x.left ≫ coprod.inl))⁻¹ * (h (y.left ≫ coprod.inl))⁻¹ *
        h ((1 : T ⟶ H₁).left ≫ coprod.inl))⁻¹ := by
  refine prod_sum₂ _ ?_ ?_
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_)
      (prod_mumford (x ≫ a) (y ≫ b) fun q => h (q ≫ coprod.inr))
    have e : lift x y ≫ lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b) = lift (x ≫ a) (y ≫ b) := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
    refine congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card))) ?_
    rw [← e, Over.comp_left, Category.assoc, Category.assoc]
    rfl
  · refine Eq.trans ?_ (congrArg (·⁻¹) (prod_mumford x y fun q => h (q ≫ coprod.inl)))
    refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (Finset.prod_inv_distrib _)
    refine (zpow_neg _ _).trans (congrArg (fun q => (h q ^ ((-1 : ℤ) ^ (2 - I.down.card)))⁻¹) ?_)
    exact (Category.assoc _ _ _).symm

theorem pair_add_of_surj : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {L₁ : RigLB H₁} {L₂ : RigLB H₂} (c₁ : CubicalStr H₁ L₁) (c₂ : CubicalStr H₂ L₂), (join L₁.L L₂.L).IsLB → Function.Surjective (H₁ ⊗ H₁ ⊗ H₁).hom.appTop.hom → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (u : LB.Gen (LB.LinComb (join L₁.L L₂.L) (mφ H₁ H₂ a b) mε)), IsNrm u → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ H₁.left ⨿ H₂.left) → (join L₁.L L₂.L).ι), Good (join L₁.L L₂.L) z J → ∀ x x' y : T ⟶ H₁, val u (lift (x * x') y).left z J * cubV c₁ z (rl J) x x' y = cubV c₂ z (rr J) (x ≫ a) (x' ≫ a) (y ≫ b) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV c₁ z (rl J) y x x' = cubV c₂ z (rr J) (y ≫ a) (x ≫ b) (x' ≫ b) * (val u (lift y x).left z J * val u (lift y x').left z J) := by
  intro S H₁ H₂ _ _ _ _ L₁ L₂ c₁ c₂ hL sj f g _ _ u hu T z J hJ x x' y
  let p₀ := x3 H₁ 0
  let p₁ := x3 H₁ 1
  let p₂ := x3 H₁ 2
  have mf : ∀ {T : Over S} (a b : T ⟶ H₁), (a * b) ≫ f = (a ≫ f) * (b ≫ f) := fun a b => MonObj.mul_comp a b f
  have mg : ∀ {T : Over S} (a b : T ⟶ H₁), (a * b) ≫ g = (a ≫ g) * (b ≫ g) := fun a b => MonObj.mul_comp a b g
  have P₁ := isPart_inl L₁.L L₂.L
  have P₂ := isPart_inr L₁.L L₂.L
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good (join L₁.L L₂.L) z J → ∀ a b : T ⟶ H₁,
      val (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J :=
    fun ρ z J hJ a b => by rw [val_pull hJ, ← Over.comp_left, comp_lift]
  let e : 𝟙_ (Over S) ⟶ G3 H₁ := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have he : e.left ≫ (H₁ ⊗ H₁ ⊗ H₁).hom = 𝟙 _ := Over.w e
  let ρ : T ⟶ G3 H₁ := lift x (lift x' y)
  have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have gen : ∀ (a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ : G3 H₁ ⟶ H₁) (l₁ l₂ l₃ : G3 H₁ ⟶ H₂),
      (∀ (V : Type) [CommGroup V] (k : (G3 H₁ ⟶ H₁) → V) (l : (G3 H₁ ⟶ H₂) → V),
        (l (l₁ * l₂ * l₃) * (l (l₁ * l₂))⁻¹ * (l (l₁ * l₃))⁻¹ * (l (l₂ * l₃))⁻¹ * l l₁ * l l₂ * l l₃ * (l 1)⁻¹) *
          (((l ((a₁ ≫ f) * (b₁ ≫ g)) * (l (a₁ ≫ f))⁻¹ * (l (b₁ ≫ g))⁻¹ * l 1) *
              (k (a₁ * b₁) * (k a₁)⁻¹ * (k b₁)⁻¹ * k 1)⁻¹) *
            ((l ((a₂ ≫ f) * (b₂ ≫ g)) * (l (a₂ ≫ f))⁻¹ * (l (b₂ ≫ g))⁻¹ * l 1) *
              (k (a₂ * b₂) * (k a₂)⁻¹ * (k b₂)⁻¹ * k 1)⁻¹)) =
        ((l ((a ≫ f) * (b ≫ g)) * (l (a ≫ f))⁻¹ * (l (b ≫ g))⁻¹ * l 1) *
              (k (a * b) * (k a)⁻¹ * (k b)⁻¹ * k 1)⁻¹) *
          (k (k₁ * k₂ * k₃) * (k (k₁ * k₂))⁻¹ * (k (k₁ * k₃))⁻¹ * (k (k₂ * k₃))⁻¹ * k k₁ * k k₂ * k k₃ * (k 1)⁻¹)) →
      e ≫ a = 1 → e ≫ b = 1 → e ≫ a₁ = 1 → e ≫ b₁ = 1 → e ≫ a₂ = 1 → e ≫ b₂ = 1 → e ≫ k₁ = 1 → e ≫ l₁ = 1 →
      val u (lift (ρ ≫ a) (ρ ≫ b)).left z J * cubV c₁ z (rl J) (ρ ≫ k₁) (ρ ≫ k₂) (ρ ≫ k₃) =
        cubV c₂ z (rr J) (ρ ≫ l₁) (ρ ≫ l₂) (ρ ≫ l₃) *
          (val u (lift (ρ ≫ a₁) (ρ ≫ b₁)).left z J * val u (lift (ρ ≫ a₂) (ρ ≫ b₂)).left z J) := by
    intro a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ hF ha hb ha₁ hb₁ ha₂ hb₂ hk hl
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 H₁) {z : T'.left} {J}, Good (join L₁.L L₂.L) z J →
        val (LB.mulGen (join L₁.L L₂.L) _ _ _ _ (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a b).left)
          (P₁.gen (LB.pullGen L₁.L (thφ H₁ (x3 H₁)) thε c₁.t (lift k₁ (lift k₂ k₃)).left))) σ.left z J =
          val u (lift (σ ≫ a) (σ ≫ b)).left z J * cubV c₁ z (rl J) (σ ≫ k₁) (σ ≫ k₂) (σ ≫ k₃) ∧
        val (LB.mulGen (join L₁.L L₂.L) _ _ _ _
          (P₂.gen (LB.pullGen L₂.L (thφ H₂ (x3 H₂)) thε c₂.t (lift l₁ (lift l₂ l₃)).left))
          (LB.mulGen (join L₁.L L₂.L) _ _ _ _ (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a₁ b₁).left)
            (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a₂ b₂).left)))
          σ.left z J = cubV c₂ z (rr J) (σ ≫ l₁) (σ ≫ l₂) (σ ≫ l₃) *
            (val u (lift (σ ≫ a₁) (σ ≫ b₁)).left z J * val u (lift (σ ≫ a₂) (σ ≫ b₂)).left z J) := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _)
          ((P₁.val_gen _ _ z hJ).trans (val_cub c₁ σ (P₁.good hJ) _ _ _))),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((P₂.val_gen _ _ z hJ).trans (val_cub c₂ σ (P₂.good hJ) _ _ _))
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
    refine (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' hL (fun V _ k => ?_) _ e.left he sj
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu.1 _) (P₁.gen_isGen (pullGen_isGen _ _ _ _ c₁.isGen _)))
      (mulGen_isGen _ _ _ _ _ _ _ (P₂.gen_isGen (pullGen_isGen _ _ _ _ c₂.isGen _)) (mulGen_isGen _ _ _ _ _ _ _
        (pullGen_isGen _ _ _ _ hu.1 _) (pullGen_isGen _ _ _ _ hu.1 _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
    · exact (prod_sum₂ (K := thK) (K' := MK ⊕ MK) (U := V) _ (prod_cub l₁ l₂ l₃ fun q => k (q ≫ coprod.inr))
        (prod_sum₂ (K := MK) (K' := MK) (U := V) _ (prod_pair f g a₁ b₁ k) (prod_pair f g a₂ b₂ k))).trans
        ((hF V (fun q => k (q.left ≫ coprod.inl)) (fun q => k (q.left ≫ coprod.inr))).trans
          (prod_sum₂ (K := MK) (K' := thK) (U := V) _ (prod_pair f g a b k)
          (prod_cub k₁ k₂ k₃ fun q => k (q ≫ coprod.inl))).symm)
    · have C₁ : IsCub (cubV c₁ y (rl I)) := isCub_cubV c₁ (P₁.good hI)
      have C₂ : IsCub (cubV c₂ y (rr I)) := isCub_cubV c₂ (P₂.good hI)
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [ha, hb, ha₁, hb₁, ha₂, hb₂, hk, hl, hu.2 y I hI, C₁.face, C₂.face]
      simp
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  constructor
  · have := gen (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ p₂ (p₀ ≫ f) (p₁ ≫ f) (p₂ ≫ g) (fun V _ k l => by
      rw [mf]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) o₁ e₂ e₀ e₂ e₁ e₂ e₀ (by rw [← Category.assoc, e₀, MonObj.one_comp])
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this
  · have := gen p₂ (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ (p₂ ≫ f) (p₀ ≫ g) (p₁ ≫ g) (fun V _ k l => by
      rw [mg, _root_.mul_assoc p₂, _root_.mul_assoc (p₂ ≫ f)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) e₂ o₁ e₂ e₀ e₂ e₁ e₂ (by rw [← Category.assoc, e₂, MonObj.one_comp])
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this

end GlobalTheory.HomMumAdd
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchIntAlter

open Set

variable {k : Type} [CommRing k] {Y Y' : Scheme.{0}} [IsIntegral Y] [IsIntegral Y'] {q : Y ⟶ Sp k}
  {σ : k →+* ℂ}

theorem continuousOn_logNorm {L : LB Y} (φ : Weight q σ L) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (hφ : φ.IsCInf) :
    ContinuousOn (logNorm φ r) (offSupp q σ (divOfRatSec φ.isLB hr)) := by
  intro y hy
  have ho := isOpen_offSupp (q := q) (σ := σ) (divOfRatSec φ.isLB hr)
  have hi : y ∈ ptsIn q σ (L.U (pick φ.isLB y)) := mem_pick _ y
  have hu := hr.unitAt φ.isLB hy hi
  have hn : ptsIn q σ (L.U (pick φ.isLB y)) ∩ offSupp q σ (divOfRatSec φ.isLB hr) ∈ 𝓝 y :=
    inter_mem ((isOpen_ptsIn _).mem_nhds hi) (ho.mem_nhds hy)
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun z => Real.log ‖ratVal (r (pick φ.isLB y) : Y.functionField) z‖ -
      φ.φ (pick φ.isLB y) z / 2) y :=
    ((LogNormInt.continuousAt_ratVal hu.regAt).norm.log (norm_ne_zero_iff.2 (ratVal_ne_zero hu))).sub
      ((hφ _ y hi).continuousAt.div_const 2)
  refine hc.congr ?_
  filter_upwards [hn] with z hz
  exact (logNorm_eq φ hr hz.2 hz.1).symm

variable (M : HermLB q) (ρ : Y' ⟶ Y) (hη : ρ (genericPoint Y') ⤳ genericPoint Y)
  {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)

theorem mem_offSupp_pull {y : CxPts (ρ ≫ q) σ}
    (hy : y ∈ ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :
    y ∈ offSupp (ρ ≫ q) σ ((M.restr ρ).div (MultPull.isRatSec_pull_map ρ hη hr)) := by
  have hx : PtsOver.map ρ rfl _ y ∈ offSupp q σ (M.div hr) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  obtain ⟨c, hc⟩ := exists_chart (M.restr ρ).isLB (under y)
  have hc' : PtsOver.map ρ rfl _ y ∈ ptsIn q σ (M.B.U (c PUnit.unit)) :=
    mem_ptsIn.2 (Set.mem_iInter.1 hc PUnit.unit)
  have hu := hr.unitAt M.isLB hx hc'
  have hu' := FrameGlue.Pull.unitAt_fnMap ρ hη hu
  exact mem_offSupp.2 fun h => ((presents_divOfRatSec (M.restr ρ).isLB
    (MultPull.isRatSec_pull_map ρ hη hr)).isEqn c _ hc).mem_supp_iff.1 h hu'

theorem logNorm_pull {y : CxPts (ρ ≫ q) σ}
    (hy : y ∈ ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :
    logNorm ((M.restr ρ).φ σ) (fun c => Units.map (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom
      (r (c PUnit.unit))) y = logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y) := by
  have hx : PtsOver.map ρ rfl _ y ∈ offSupp q σ (M.div hr) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  have hj : y ∈ ptsIn _ σ ((M.restr ρ).B.U (pick ((M.restr ρ).φ σ).isLB y)) := mem_pick _ y
  have hj' : PtsOver.map ρ rfl _ y ∈
      ptsIn q σ (M.B.U (pick ((M.restr ρ).φ σ).isLB y PUnit.unit)) :=
    mem_ptsIn.2 (Set.mem_iInter.1 (mem_ptsIn.1 hj) PUnit.unit)
  have hu := hr.unitAt M.isLB hx hj'
  have hu' := FrameGlue.Pull.unitAt_fnMap ρ hη hu
  have e₁ : ((M.restr ρ).φ σ).φ (pick ((M.restr ρ).φ σ).isLB y) y =
      (M.φ σ).φ (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) (PtsOver.map ρ rfl _ y) :=
    (M.φ σ).pull_φ ρ rfl _ y
  have e₂ : ratVal ((Units.map (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom
      (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit)) : Y'.functionFieldˣ) : Y'.functionField) y =
      ratVal (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) : Y.functionField)
      (PtsOver.map ρ rfl _ y) := by
    show ratVal (TrueGeo.SmallSec.fnMap ρ hη (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) :
      Y.functionField)) y = _
    rw [TrueGeo.SmallSec.ratVal_eq_valAt y hu'.regAt, TrueGeo.SmallSec.valAt_fnMap ρ hη _ hu.regAt,
      TrueGeo.SmallSec.ratVal_eq_valAt _ hu.regAt]
    rfl
  rw [logNorm_eq (M.φ σ) hr hx hj', logNorm, e₁, e₂]

end GlobalTheory.ArchIntAlter

namespace GlobalTheory.ArchIntAlter

open Set

end GlobalTheory.ArchIntAlter
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

open GlobalTheory.FieldBaseChange

theorem phiRel_famExt : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (p : QkPt D.toPre (Kb R) N) (w : GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b) (p' : QkPt D.toPre F N) (w' : GlobalTheory.UT.Frm D.toPre F N p'.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p' w' → QkExt em.toRingHom p p' → ∀ s s₁, PhiRel D.toPre (Kb R) N p w s s₁ → PhiRel D.toPre F N p' w' (famExt D.toPre em N s) (famExt D.toPre em N s₁) := by
  intro R _ _ _ I hI D F _ _ _ em N hN p w p' w' hw hw' hp s s₁ H
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  have hL : GlobalTheory.UT.LL := ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1,
    GlobalTheory.allSixLaws.2.2.2.2.1⟩
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨hy, hb, hs⟩ := hp
  have hb' : p'.g.b = baseMap (R := R) (Kb R) F ≫ p.g.b := Over.OverMorphism.ext hb
  have hb2 : (baseMap (R := R) (Kb R) F).left ≫ p.g.b.left = p'.g.b.left := hb.symm
  have h0 : (baseMap (R := R) (Kb R) F).left ≫ (DegPre.zeroF D.toPre (Kb R)).left = (DegPre.zeroF D.toPre F).left :=
    congrArg (fun q : TF (R := R) F ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) (baseMap (R := R) (Kb R) F))
  have j1 : (baseMap (R := R) (Kb R) F).left ≫ jFK (R := R) (Kb R) = jFK (R := R) F := specMap_jFK (R := R) (Kb R) F
  have j2 : (baseMap (R := R) (Kb R) F).left ≫ (TF (R := R) (Kb R)).hom = (TF (R := R) F).hom := Over.w _
  obtain ⟨w'', hw'', hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F p'.g.b) (ε' := DegPre.lineε N)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) hb.symm)
    (LB.pullGen D.toPre.P.L _ _ w (baseMap (R := R) (Kb R) F).left) (pullGen_isGen _ _ _ _ hw.1 _)
  have hX : GlobalTheory.UT.TXFrame N p' w'' := by
    refine ⟨hw'', fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
    · have C : LB.Gen.Corr D.toPre.P.L _ _ _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ w 2)
          (LB.mulGen D.toPre.P.L _ _ _ _ (p.g.s p.y) (LB.pullGen D.toPre.P.L _ _ ν p.g.b.left)) :=
        corr_of_val D.toPre.P.isLB fun y J hJ => by
          rw [val_mul hJ, val_pull hJ, Category.id_comp]
          exact (map_pow _ _ _).trans (hw.2.1 ν hν y J hJ)
      have e := val_corr hJ C (baseMap (R := R) (Kb R) F).left
      rw [val_mul hJ, val_pull hJ, hb2] at e
      rw [hv _ _ z J hJ, val_pull hJ, val_corr hJ (hs p'.y), val_pull hJ, hy, Category.id_comp, Category.id_comp]
      exact (map_pow _ _ _).symm.trans e
    · have C : LB.Gen.Corr D.toPre.P.L _ _ _ _
          (LB.mulGen D.toPre.P.L _ _ _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ w N) (LB.pullGen D.toPre.P.L _ _ κ p.g.b.left))
          (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (D.toPre.psi p.y) (jFK (R := R) (Kb R)))
            (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig
              (TF (R := R) (Kb R)).hom)) :=
        corr_of_val D.toPre.P.isLB fun y J hJ => by
          rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp,
            Category.id_comp]
          exact (congrArg₂ (· * ·) (map_pow _ _ _) rfl).trans (hw.2.2 κ hκ y J hJ)
      have e := val_corr hJ C (baseMap (R := R) (Kb R) F).left
      rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, hb2, j1, j2] at e
      rw [hv _ _ z J hJ, val_pull hJ, Category.id_comp, hy]
      exact (congrArg₂ (· * ·) (map_pow _ _ _).symm rfl).trans e
  have Cw : LB.Gen.Corr D.toPre.P.L _ _ _ _ w' (LB.pullGen D.toPre.P.L _ _ w (baseMap (R := R) (Kb R) F).left) :=
    corr_of_val D.toPre.P.isLB fun y J hJ =>
      ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p').2 w'' w' hX hw' y J hJ).symm.trans (hv _ _ y J hJ)
  rw [phiRel_iff hG p w hw.1] at H
  refine (phiRel_iff hG p' w' hw'.1 _ _).2 ?_
  intro α β hβ T ρ z J hJ
  have e₁ : DegPre.trPt D.toPre F p'.g.b ≫ famMap D.toPre (Kb R) F =
      famMap D.toPre (Kb R) F ≫ DegPre.trPt D.toPre (Kb R) p.g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, famMap_fst, tr_fst, ← Category.assoc, tr_fst, famMap_fst]
    · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (famMap_snd D.toPre (Kb R) F)).trans (tr_pr D.toPre F _))).trans
        (Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D.toPre (Kb R) _)).trans ?_)))
      rw [MonObj.comp_mul, famMap_snd, ← Category.assoc, famMap_fst, hb', Category.assoc]
  have e₂ : ((ρ ≫ famMap D.toPre (Kb R) F) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (baseMap (R := R) (Kb R) F).left := by
    rw [Category.assoc, famMap_fst, ← Category.assoc]; rfl
  have e₃ : uVal D.toPre (Kb R) N α p.g.b (ρ ≫ famMap D.toPre (Kb R) F) z J = uVal D.toPre F N α p'.g.b ρ z J := by
    have : famMap D.toPre (Kb R) F ≫ fst _ _ ≫ p.g.b = fst _ _ ≫ p'.g.b := by
      rw [← Category.assoc, famMap_fst, hb', Category.assoc]
    simp only [uVal, Category.assoc, famMap_snd, this]
  refine (sval_pullOver _ _ _ _ hJ).trans ((H α β (hy ▸ hβ) T (ρ ≫ famMap D.toPre (Kb R) F) z J hJ).trans
    (congrArg₂ (· * ·) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm) (congrArg Units.val ?_)))
  · rw [Category.assoc, ← e₁, ← Category.assoc]; rfl
  · rw [e₃, val_mul hJ, val_mul hJ, val_corr hJ Cw, val_pull hJ, val_corr hJ (hs α), val_pull hJ, e₂]
    rfl

end GlobalTheory.Mum.Desc
end
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem pulled_back_lineBundle_transition_unit_eq_restriction {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j j' : PUnit.{1} → L.ι) :
    (L.pull f).g j j' = res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ => f) j' PUnit.unit)))
      (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
  have e : ∀ u : Γ(Y, L.wchart (fun _ => f) j ⊓ L.wchart (fun _ => f) j')ˣ, (∏ _k : PUnit.{1}, u ^ (1 : ℤ)) = u :=
    fun u => by simp
  exact e _

theorem pull_g_eq (h : IsGrpPullback H G x ψ) (j j' : ((hodge G g).pull x).ι) :
    ((hodge G g).pull x).g j j' =
      (isFrame_chart h j).detUnit (isFrame_chart h j') inf_le_left inf_le_right := by
  have frame_pb {X Y : Scheme.{0}} {I : Type} [Fintype I] (f : Y ⟶ X)
      {F : X.Modules} [F.IsQuasicoherent] {U : X.Opens} {e : I → Γ(F, U)} (he : IsFrame e)
      {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) : IsFrame fun i => pullbackSections f F h (e i) := by
    have k := (he.pullback f).res h
    exact (funext fun l => QCoh.res_pullbackSections f F le_rfl h (e l)) ▸ k
  have e₁ := IsFrame.detUnit_map_iso
    (frame_pb x (j PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
    (frame_pb x (j' PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
    (omegaBase h) (inf_le_left : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤ _)
    inf_le_right
  refine Eq.trans ?_ e₁.symm
  have hT : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤
      x ⁻¹ᵁ ((j PUnit.unit).U ⊓ (j' PUnit.unit).U) :=
    le_inf (inf_le_left.trans (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
  refine Eq.trans ?_ (GlobalTheory.Vert.DivPull.detUnit_congr _ _ ((j PUnit.unit).isFrame.pullback x)
    ((j' PUnit.unit).isFrame.pullback x) _ _ (hT.trans (x.preimage_mono inf_le_left))
    (hT.trans (x.preimage_mono inf_le_right))
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)).symm
  refine Units.ext ?_
  refine (congrArg Units.val (pulled_back_lineBundle_transition_unit_eq_restriction (hodge G g) x j j')).trans (Eq.trans ?_
    (IsFrame.val_detUnit_pullback (j PUnit.unit).isFrame (j' PUnit.unit).isFrame x inf_le_left inf_le_right hT).symm)
  rfl

theorem gen_isGen : ∀ {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a), (gen h ha).IsGen := by
  intro S' T G _ H _ x ψ _ g h a ha j j'
  refine (IsFrame.res_detUnit _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (pull_g_eq h j j').symm (IsFrame.res_detUnit _ _ _ _ _).symm)
  exact (IsFrame.detUnit_mul _ _ _ _ _ _).symm

end GlobalTheory.HodgeFrameGen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_isUnit_gs_of_frame_eq_sum : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁) (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ l, IsSecOver L O (s l)) → (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z ∈ O → ∃ l, ∀ k, (pullback.fst f (spMap ρ₁)) z ∈ L.U k → IsUnit (gs (𝟙 X) ((pullback.fst f (spMap ρ₁)) z) (O ⊓ L.U k) (s l k)) := by
  intro R R₁ _ _ ρ₁ d b X f L hL W O hOW τ s hs hτ z hz
  obtain ⟨k₀, hk₀⟩ := exists_chart hL ((pullback.fst f (spMap ρ₁)) z)
  have hm : (𝟙 (pullback f (spMap ρ₁) : Scheme.{0})) z ∈
      (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k₀ := ⟨hOW hz, hk₀⟩
  have hm' : (pullback.fst f (spMap ρ₁)) z ∈ O ⊓ L.U k₀ := ⟨hz, hk₀⟩
  have hu : IsUnit (gs (𝟙 (pullback f (spMap ρ₁))) z
      ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k₀) (τ k₀).val) := by
    rw [gs_unit _ z _ hm]
    exact Units.isUnit _
  rw [hτ z k₀ hz hk₀] at hu
  obtain ⟨l, -, hl⟩ := IsLocalRing.exists_of_isUnit_sum hu
  have hl2 := isUnit_of_mul_isUnit_right hl
  rw [gs_eq_map_gs _ z _ hm'] at hl2
  have hl3 := (isUnit_map_iff _ _).1 hl2
  refine ⟨l, fun k hk => ?_⟩
  rw [hs l _ k k₀ hz hk hk₀]
  exact (Units.isUnit _).mul hl3

end GlobalTheory.Mum
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum


theorem _root_.GlobalTheory.T.homMumfordGenerator_additive_cubicalStructures : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {L₁ : RigLB H₁} {L₂ : RigLB H₂} (c₁ : CubicalStr H₁ L₁) (c₂ : CubicalStr H₂ L₂), (join L₁.L L₂.L).IsLB → Function.Surjective (H₁ ⊗ H₁ ⊗ H₁).hom.appTop.hom → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (u : LB.Gen (LB.LinComb (join L₁.L L₂.L) (mφ H₁ H₂ a b) mε)), IsNrm u → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ H₁.left ⨿ H₂.left) → (join L₁.L L₂.L).ι), Good (join L₁.L L₂.L) z J → ∀ x x' y : T ⟶ H₁, val u (lift (x * x') y).left z J * cubV c₁ z (rl J) x x' y = cubV c₂ z (rr J) (x ≫ a) (x' ≫ a) (y ≫ b) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV c₁ z (rl J) y x x' = cubV c₂ z (rr J) (y ≫ a) (x ≫ b) (x' ≫ b) * (val u (lift y x).left z J * val u (lift y x').left z J) := by
  first | exact @GlobalTheory.HomMumAdd.pair_add_of_surj | exact GlobalTheory.HomMumAdd.pair_add_of_surj | (intros; apply GlobalTheory.HomMumAdd.pair_add_of_surj <;> assumption)

end
end
