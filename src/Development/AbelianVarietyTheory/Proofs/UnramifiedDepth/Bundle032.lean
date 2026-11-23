module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.DualLattices.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
private theorem invGenDescent_gs_appLE {Y Y' : Scheme.{0}} (τ : Y' ⟶ Y) (W : Y.Opens) (W' : Y'.Opens)
    (h : W' ≤ τ ⁻¹ᵁ W) (a : Γ(Y, W)) (x : Y') (hx : x ∈ W') :
    gs (𝟙 Y') x W' ((τ.appLE W W' h).hom a) = gs τ x W a := by
  have e := (gs_res (𝟙 Y') x h hx ((τ.app W).hom a)).trans (gs_pull (𝟙 Y') τ x W (h hx) a)
  rw [Category.id_comp] at e
  exact e


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
private theorem invariant_generator_descent {X Y Y' : Scheme.{0}} (m : Y' ⟶ Y) {T : Type} (τ : T → (Y' ⟶ Y'))
    (hτ : ∀ t, τ t ≫ m = m)
    (H : ∀ (V : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ V)),
      (∀ t, ∀ h : m ⁻¹ᵁ V ≤ τ t ⁻¹ᵁ (m ⁻¹ᵁ V), ((τ t).appLE _ _ h).hom a = a) →
      ∃! a' : Γ(Y, V), (m.app V).hom a' = a)
    (M : LB X) (hM : M.IsLB) (ψ : Y ⟶ X)
    (σ : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => m ≫ ψ) (fun _ => 1))) (hσ : σ.IsGen)
    (inv : ∀ t (z : Y') (J : (Y' ⟶ X) → M.1), Good M z J → val σ (𝟙 Y' ≫ τ t) z J = val σ (𝟙 Y') z J) :
    ∃ t : (M.pull ψ).Gen, t.IsGen := by
  have inj : ∀ V : Y.Opens, Function.Injective (m.app V).hom := by
    intro V a b e
    obtain ⟨c, -, hc⟩ := H V ((m.app V).hom a) (fun t h => fn_ext fun x hx => by
      rw [invGenDescent_gs_appLE (τ t) _ _ h _ x hx, gs_pull (τ t) m x V (h hx), gs_pull (𝟙 Y') m x V hx, hτ,
        Category.id_comp])
    exact (hc a rfl).trans (hc b e.symm).symm
  have injU : ∀ V : Y.Opens, Function.Injective (pullU m V) := fun V a b e =>
    Units.ext (inj V (congrArg Units.val e))
  have descU : ∀ (V : Y.Opens) (u : Γ(Y', m ⁻¹ᵁ V)ˣ),
      (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) → ∃ v : Γ(Y, V)ˣ, pullU m V v = u := by
    intro V u hu
    have key : ∀ u : Γ(Y', m ⁻¹ᵁ V)ˣ, (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) →
        ∃ a : Γ(Y, V), (m.app V).hom a = u.val := fun u hu =>
      (H V u.val (fun t h => fn_ext fun x hx => by
        rw [invGenDescent_gs_appLE (τ t) _ _ h _ x hx, gs_unit (τ t) x (m ⁻¹ᵁ V) (h hx),
          gs_unit (𝟙 Y') x (m ⁻¹ᵁ V) hx,
          hu t x hx])).exists
    obtain ⟨a, ha⟩ := key u hu
    obtain ⟨b, hb⟩ := key u⁻¹ (fun t x hx => by rw [map_inv, map_inv, hu t x hx])
    have e : a * b = 1 := inj V (by rw [map_mul, map_one, ha, hb]; exact u.mul_inv)
    exact ⟨⟨a, b, e, (mul_comm _ _).trans e⟩, Units.ext ha⟩
  have le : ∀ j : PUnit → M.ι, m ⁻¹ᵁ LB.wchart M (fun _ : PUnit => ψ) j ≤ LB.wchart M (fun _ : PUnit => m ≫ ψ) j :=
    fun j x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have loc : ∀ j : PUnit → M.ι, ∃ v : Γ(Y, LB.wchart M (fun _ : PUnit => ψ) j)ˣ,
      pullU m _ v = res (le j) (σ.s j) := by
    intro j
    refine descU _ _ fun t x hx => ?_
    have hx' : τ t x ∈ m ⁻¹ᵁ LB.wchart M (fun _ : PUnit => ψ) j :=
      (congrArg (fun q : Y' ⟶ Y => q x ∈ LB.wchart M (fun _ : PUnit => ψ) j) (hτ t)).mpr hx
    obtain ⟨J, hJ, e⟩ := exists_good M hM x (fun _ : PUnit => m ≫ ψ) j (fun a b _ => rfl)
      (fun k => Set.mem_iInter.1 (le j hx) k)
    have := inv t x J hJ
    rw [val_of σ _ x J j (fun k => by rw [Category.id_comp, ← Category.assoc, hτ]; exact e k),
      val_of σ _ x J j (fun k => by rw [Category.id_comp]; exact e k), Category.id_comp] at this
    exact (gm_res (τ t) x (le j) hx' _).trans (this.trans (gm_res (𝟙 Y') x (le j) hx _).symm)
  choose v hv using loc
  refine ⟨⟨v⟩, fun i j => injU _ (unit_ext fun x hx => ?_)⟩
  have hv' : ∀ j : PUnit → M.ι, m x ∈ LB.wchart M (fun _ : PUnit => ψ) j →
      gm (𝟙 Y' ≫ m) x _ (v j) = gm (𝟙 Y') x (LB.wchart M (fun _ : PUnit => m ≫ ψ) j) (σ.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m x _ hj _).symm.trans ((congrArg (gm (𝟙 Y') x _) (hv j)).trans (gm_res (𝟙 Y') x (le j) hj _))
  have hx' : (𝟙 Y' ≫ m) x ∈ LB.wchart M (fun _ : PUnit => ψ) i ⊓ LB.wchart M (fun _ : PUnit => ψ) j := hx
  refine (gm_pull (𝟙 Y') m x _ hx _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m x _ hx _).symm)
  refine (gm_res _ x _ hx' _).trans ((hv' i hx.1).trans ((gen_trans hσ (𝟙 Y') x (le i hx.1) (le j hx.2)).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_linComb M (fun _ : PUnit => ψ) (fun _ => 1) (𝟙 Y' ≫ m) x i j hx'.1 hx'.2).trans ?_)
      ((gm_res _ x _ hx' _).trans (hv' j hx.2)))))))
  simp only [trF, Category.assoc]

theorem invariantGenerator_descends_mulN :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (V : (G ⊗ Over.mk f).left.Opens) (a : Γ((G ⊗ Over.mk f).left, (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V)),
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ h : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V ≤ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left ⁻¹ᵁ ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V), ((lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left.appLE _ _ h).hom a = a) →
    ∃! a' : Γ((G ⊗ Over.mk f).left, V), ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left.app V).hom a' = a) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (X : Scheme.{0}) (M : ReciprocityTheory.ChartRestriction.G.Semi.LB X), M.IsLB → ∀ (ψ : (G ⊗ Over.mk f).left ⟶ X)
      (σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb M (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ ψ) (fun _ => 1))), σ.IsGen →
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ X) → M.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good M z J →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) → ∃ t : (M.pull ψ).Gen, t.IsGen) := by
  intro H S G _ _ K _ _ f N hN h₁ h₂ h₃ h₄ X M hM ψ σ hσ inv
  refine invariant_generator_descent (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left (T := {y : Over.mk f ⟶ G // y ^ N = 1})
    (fun y => (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y.1)) (snd G (Over.mk f))).left) (fun y => ?_)
    (fun V a ha => H S G K f N hN h₁ h₂ h₃ h₄ V a (fun y hy => ha ⟨y, hy⟩)) M hM ψ σ hσ
    (fun y z J hJ => inv y.1 y.2 _ (𝟙 _) z J hJ)
  rw [← Over.comp_left]
  congr 1
  ext1
  · rw [lift_whiskerRight, lift_fst, whiskerRight_fst, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
      Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.mul_one]
  · simp

end GlobalTheory
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem biext_pairing_nondegenerate_geometric_fibre :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (X : Scheme.{0}) (M : ReciprocityTheory.ChartRestriction.G.Semi.LB X), M.IsLB → ∀ (ψ : (G ⊗ Over.mk f).left ⟶ X)
      (σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb M (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ ψ) (fun _ => 1))), σ.IsGen →
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ X) → M.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good M z J →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) → ∃ t : (M.pull ψ).Gen, t.IsGen) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ) (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (x : Over.mk f ⟶ G), x ^ N = 1 →
    ∃ σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left) (fun _ => 1)), σ.IsGen ∧
      ∀ y : Over.mk f ⟶ G, y ^ N = 1 → (∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom →
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    (∀ x : Over.mk f ⟶ G, (∃ t : (P.pull (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : Over.mk f ⟶ G, x ^ N = 1 → (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
      ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) → x = 1) := by
  intro hD hS S G _ _ P β K _ _ f N hN hsm hfin hfl hsur hpr x hx hxy
  obtain ⟨σ, hσ, hinv⟩ := hS S G K f N P β x hx
  exact hpr x (hD S G K f N hN hsm hfin hfl hsur _ P β.isLB _ σ hσ
    (fun y hy => hinv y hy (hxy y hy)))

end GlobalTheory
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
private theorem biextVal_pull {S : Scheme.{0}} {G : Over S} {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → ((G ⊗ G ⊗ G).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J : (T'.left ⟶ X) → L.ι} (hJ : Good L z J) (x x' y : T ⟶ G) :
    val (LB.pullGen L φ ε t (lift x (lift x' y)).left) ρ.left z J =
      val t (lift (ρ ≫ x) (lift (ρ ≫ x') (ρ ≫ y))).left z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift]


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem biext_val_axioms :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) := by
  intro S G _ _ P β T z J hJ t₁ t₂ h₁ h₂
  have a₀ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 0 = a := fun a b c d => by simp [x4]
  have a₁ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 1 = b := fun a b c d => by simp [x4]
  have a₂ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 2 = c := fun a b c d => by simp [x4]
  have a₃ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 3 = d := fun a b c d => by simp [x4]
  have b₀ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 0) (x4 G 1) = a * b :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  have b₁ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 1) (x4 G 2) = b * c :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  have b₂ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 2) (x4 G 3) = c * d :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃])
  have c₀ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 0 = a := fun a b c => by simp [x3]
  have c₁ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 1 = b := fun a b c => by simp [x3]
  have c₂ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 2 = c := fun a b c => by simp [x3]
  simp only [h₁, h₂]
  refine ⟨fun x x' x'' y => ?_, fun x x' y => ?_, fun x y y' y'' => ?_, fun x y y' => ?_, fun x x' y y' => ?_⟩
  · have := val_corr hJ β.assoc1 (lift x (lift x' (lift x'' y))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _)
      (biextVal_pull _ _ hJ _ _ _))).symm.trans (this.trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₀, b₁, a₀, a₁, a₂, a₃] at e
  · have e := (val_corr hJ β.comm1 (lift x (lift x' y)).left).trans (biextVal_pull _ _ hJ _ _ _)
    rwa [c₀, c₁, c₂] at e
  · have := val_corr hJ β.assoc2 (lift x (lift y (lift y' y''))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _)
      (biextVal_pull _ _ hJ _ _ _))).symm.trans (this.trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₁, b₂, a₀, a₁, a₂, a₃] at e
  · have e := (val_corr hJ β.comm2 (lift x (lift y y')).left).trans (biextVal_pull _ _ hJ _ _ _)
    rwa [c₀, c₁, c₂] at e
  · have := val_corr hJ β.compat (lift x (lift x' (lift y y'))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))) (biextVal_pull _ _ hJ _ _ _))).symm.trans
      (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₀, b₂, a₀, a₁, a₂, a₃] at e

end GlobalTheory
end
