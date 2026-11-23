module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLineBundlePowerIsoGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle577
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

theorem _root_.GlobalTheory.T.power_pullback_section_exists : ∀ {X Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (a : ℤ) (α : LB.Gen (LB.div (powPull M g a) (powPull L f a))), α.IsGen → L.IsLB → M.IsLB → ∀ σ : LB.Sec (powPull M g a), ∃ s : LB.Sec (powPull L f a), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (X.presheaf.map (homOfLE (inf_le_left : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart M (fun _ : Fin 1 => g) p.1)).op).hom (σ.f p.1) = (show Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) from (α.s p).val) * (X.presheaf.map (homOfLE (inf_le_right : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s.f p.2) := by
  first | exact @GlobalTheory.HomFixMat.divSec_exists | exact GlobalTheory.HomFixMat.divSec_exists | (intros; apply GlobalTheory.HomFixMat.divSec_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

theorem _root_.GlobalTheory.T.exists_lineBundlePower_iso_reindexed_charts : ∀ {X Y Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (h : X ⟶ Y) (m : Y ⟶ Z₂) (k : ℕ) (w : LB.Gen (LB.div ((M.pull m).pull h) (L.pull f))), w.IsGen → ∃ α : LB.Gen (LB.div (powPull M (h ≫ m) (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen := by
  first | (exact @GlobalTheory.PowIsoRe.exists_powIso) | (exact GlobalTheory.PowIsoRe.exists_powIso) | (intros; apply GlobalTheory.PowIsoRe.exists_powIso  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

theorem _root_.GlobalTheory.T.exists_rescaled_lineBundlePower_iso_generator : ∀ {T X Z₀ Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (eL : Z₀ ⟶ Z₁) (eM : Z₀ ⟶ Z₂) (t : T ⟶ Z₀) (z : T ⟶ X) (π : X ⟶ T) (k : ℕ) (eA : LB.Gen (L.pull eL)) (eB : LB.Gen (M.pull eM)) (α₀ : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ)))), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → α₀.IsGen → z ≫ π = 𝟙 T → z ≫ f = t ≫ eL → z ≫ g = t ≫ eM → ∃ α : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen ∧ ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (z.appLE ((LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_left)).hom (α.s p).val * ((t.appLE (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k = ((t.appLE (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  first | (exact @GlobalTheory.RigNorm.exists_rescaled_gen) | (exact GlobalTheory.RigNorm.exists_rescaled_gen) | (intros; apply GlobalTheory.RigNorm.exists_rescaled_gen  <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Mum

variable {X Y Z : Scheme.{0}} {L : LB X} {k k' : ℕ}

abbrev secGerm (u : Y ⟶ X) (y : Y) (s : H0 L k) (i : Fin 1 → L.ι) : Y.presheaf.stalk y :=
  gs u y (secChart L i) (s.f i)

theorem secRatioEq_iff_germ {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'} :
    SecRatioEq L u v s₁ s₂ t₁ t₂ ↔ ∀ (y : Y) (i i' : Fin 1 → L.ι), u y ∈ secChart L i → v y ∈ secChart L i' →
      secGerm u y s₁ i * secGerm v y t₂ i' = secGerm u y s₂ i * secGerm v y t₁ i' := by
  have key : ∀ (y : Y) (i i' : Fin 1 → L.ι) (hi : u y ∈ secChart L i) (hi' : v y ∈ secChart L i') (s : H0 L k)
      (t : H0 L k'), gs (𝟙 Y) y (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
        ((Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
          ((u.app (secChart L i)).hom (s.f i)) *
        (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
          ((v.app (secChart L i')).hom (t.f i'))) = secGerm u y s i * secGerm v y t i' := by
    intro y i i' hi hi' s t
    have hy : (𝟙 Y : Y ⟶ Y) y ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := ⟨hi, hi'⟩
    rw [gs_mul _ _ _ hy, gs_res _ _ _ hy, gs_res _ _ _ hy]
    exact congrArg₂ (· * ·) (gs_pull (𝟙 Y) u y _ hi _) (gs_pull (𝟙 Y) v y _ hi' _)
  refine ⟨fun h y i i' hi hi' => ?_, fun h i i' => fn_ext fun y hy => ?_⟩
  · rw [← key y i i' hi hi', ← key y i i' hi hi', h i i']
  · rw [key y i i' hy.1 hy.2, key y i i' hy.1 hy.2]
    exact h y i i' hy.1 hy.2

theorem exists_unit_secGerm (k : ℕ) (u : Y ⟶ X) (y : Y) {i j : Fin 1 → L.ι} (hi : u y ∈ secChart L i)
    (hj : u y ∈ secChart L j) :
    ∃ c : (Y.presheaf.stalk y)ˣ, ∀ s : H0 L k, secGerm u y s i = c.val * secGerm u y s j := by
  have hy : u y ∈ secChart L i ⊓ secChart L j := ⟨hi, hj⟩
  refine ⟨gm u y (secChart L i ⊓ secChart L j)
    ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))).g i j), fun s => ?_⟩
  have h := congrArg (gs u y (secChart L i ⊓ secChart L j)) (s.compat i j)
  refine (gs_res u y inf_le_left hy _).symm.trans (h.trans ((gs_mul u y _ hy _ _).trans ?_))
  exact congrArg₂ (· * ·) (gs_unit u y _ hy _) (gs_res u y inf_le_right hy _)

theorem secRatioEq_of_exists_germ {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'}
    (h : ∀ y : Y, ∃ i i' : Fin 1 → L.ι, u y ∈ secChart L i ∧ v y ∈ secChart L i' ∧
      secGerm u y s₁ i * secGerm v y t₂ i' = secGerm u y s₂ i * secGerm v y t₁ i') :
    SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  refine secRatioEq_iff_germ.2 fun y j j' hj hj' => ?_
  obtain ⟨i, i', hi, hi', e⟩ := h y
  obtain ⟨c, hc⟩ := exists_unit_secGerm k u y hj hi
  obtain ⟨c', hc'⟩ := exists_unit_secGerm k' v y hj' hi'
  rw [hc, hc, hc', hc']
  linear_combination (c.val * c'.val) * e

theorem secGerm_comp (w : Z ⟶ Y) (u : Y ⟶ X) (z : Z) (s : H0 L k) {i : Fin 1 → L.ι} (hi : u (w z) ∈ secChart L i) :
    secGerm (w ≫ u) z s i = (w.stalkMap z).hom (secGerm u (w z) s i) := by
  have key : ∀ a : Γ(X, secChart L i), gs (w ≫ u) z _ a = (w.stalkMap z).hom (gs u (w z) _ a) := fun a => by
    rw [gs_eq u (w z) _ hi, ← gs_pull w u z _ hi, gs_eq w z _ hi]
    exact (Scheme.Hom.germ_stalkMap_apply w _ z hi _).symm
  exact key _

theorem SecRatioEq.comp {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'} (h : SecRatioEq L u v s₁ s₂ t₁ t₂)
    (w : Z ⟶ Y) : SecRatioEq L (w ≫ u) (w ≫ v) s₁ s₂ t₁ t₂ := by
  refine secRatioEq_iff_germ.2 fun z i i' hi hi' => ?_
  rw [secGerm_comp w u z _ hi, secGerm_comp w u z _ hi, secGerm_comp w v z _ hi', secGerm_comp w v z _ hi',
    ← map_mul, ← map_mul, secRatioEq_iff_germ.1 h (w z) i i' hi hi']

theorem app_injective_of_isDominant [IsReduced Y] (w : Z ⟶ Y) [IsDominant w] (W : Y.Opens) :
    Function.Injective (w.app W).hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  apply eq_zero_of_basicOpen_eq_bot
  by_contra hne
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  obtain ⟨z, hz⟩ := w.denseRange.exists_mem_open (Y.basicOpen a).isOpen ⟨y, hy⟩
  have hz' : z ∈ w ⁻¹ᵁ Y.basicOpen a := hz
  rw [Scheme.preimage_basicOpen, ha, Scheme.basicOpen_zero] at hz'
  exact hz'

theorem SecRatioEq.of_isDominant [IsReduced Y] (w : Z ⟶ Y) [IsDominant w] {u v : Y ⟶ X} {s₁ s₂ : H0 L k}
    {t₁ t₂ : H0 L k'} (h : SecRatioEq L (w ≫ u) (w ≫ v) s₁ s₂ t₁ t₂) : SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  intro i i'
  apply app_injective_of_isDominant w
  refine fn_ext fun z hz => ?_
  have hz' : w z ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := hz
  rw [gs_pull (𝟙 Z) w z _ hz', gs_pull (𝟙 Z) w z _ hz', Category.id_comp, gs_mul _ _ _ hz', gs_mul _ _ _ hz',
    gs_res _ _ _ hz', gs_res _ _ _ hz', gs_res _ _ _ hz', gs_res _ _ _ hz']
  exact (congrArg₂ (· * ·) (gs_pull w u z _ hz'.1 _) (gs_pull w v z _ hz'.2 _)).trans
    ((secRatioEq_iff_germ.1 h z i i' hz'.1 hz'.2).trans
      (congrArg₂ (· * ·) (gs_pull w u z _ hz'.1 _) (gs_pull w v z _ hz'.2 _)).symm)

def VeryAmpleAlong {K : Type} [CommRing K] {A : Scheme.{0}} (p : A ⟶ Spec (CommRingCat.of K)) (π : A ⟶ X)
    (L : LB X) {k m : ℕ} (σ : Fin (m + 1) → H0 L k) : Prop :=
  (⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) = ⊤) ∧ ∀ i, IsAffineOpen (π ⁻¹ᵁ nonzeroLocus (σ i)) ∧
    ∃ r : Fin (m + 1) → Γ(A, π ⁻¹ᵁ nonzeroLocus (σ i)),
      (∀ (j : Fin (m + 1)) (c : Fin 1 → L.ι) (a : A), π a ∈ nonzeroLocus (σ i) → π a ∈ secChart L c →
        secGerm π a (σ j) c = gs (𝟙 A) a (π ⁻¹ᵁ nonzeroLocus (σ i)) (r j) * secGerm π a (σ i) c) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) r)

end GlobalTheory.Mum
end
end

section

open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

section Scal

variable {B K : Type} [CommRing B] [CommRing K] {n : ℕ} (g : B →+* K) (v : Fin n → K)

theorem algebraMap_map_mulVec (x : B) :
    (algebraMap B (Matrix (Fin n) (Fin n) B) x).map g *ᵥ v = g x • v := by
  ext k
  simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

theorem map_mul_mulVec_of_scal {X Y : Matrix (Fin n) (Fin n) B} {c d : K}
    (hX : X.map g *ᵥ v = c • v) (hY : Y.map g *ᵥ v = d • v) : (X * Y).map g *ᵥ v = (c * d) • v := by
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hY, Matrix.mulVec_smul, hX, smul_smul, mul_comm]

theorem map_sub_mulVec_of_scal {X Y : Matrix (Fin n) (Fin n) B} {c d : K}
    (hX : X.map g *ᵥ v = c • v) (hY : Y.map g *ᵥ v = d • v) : (X - Y).map g *ᵥ v = (c - d) • v := by
  rw [Matrix.map_sub _ (map_sub g), Matrix.sub_mulVec, hX, hY, sub_smul]

theorem map_sum_mulVec_of_scal {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin n) (Fin n) B) (c : ι → K)
    (h : ∀ x ∈ s, (X x).map g *ᵥ v = c x • v) : (∑ x ∈ s, X x).map g *ᵥ v = (∑ x ∈ s, c x) • v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.map_add _ (map_add g), Matrix.add_mulVec,
      h a (Finset.mem_insert_self _ _), ih (fun x hx => h x (Finset.mem_insert_of_mem hx)), add_smul]

theorem map_list_prod_mulVec_of_fix (L : List (Matrix (Fin n) (Fin n) B))
    (h : ∀ X ∈ L, X.map g *ᵥ v = v) : L.prod.map g *ᵥ v = v := by
  induction L with
  | nil => rw [List.prod_nil, Matrix.map_one _ (map_zero g) (map_one g), Matrix.one_mulVec]
  | cons X L ih =>
    rw [List.prod_cons, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      ih (fun Y hY => h Y (List.mem_cons_of_mem _ hY)), h X (by simp)]

end Scal

theorem projMat_map_mulVec_of_eig : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K)
    (i : Fin D.a) (v : Fin n → K), (∀ c : 𝓞 D.F, (M c).map g *ᵥ v = g (βB (b.t i c)) • v) →
      (projMat b βB M i).map g *ᵥ v = v := by
  intro p _ D R _ b B _ βB n M K _ g i v hv
  have hα : ∀ j, j ≠ i → (alphaMat b βB M i j).map g *ᵥ v = v := by
    intro j hj
    have hij : i ≠ j := fun h => hj h.symm
    unfold alphaMat
    rw [Finsupp.sum, map_sum_mulVec_of_scal g v _ _
      (fun x => g (βB (comaxC b i j x)) * (g (βB (b.t i x)) - g (βB (b.t j x))))
      (fun x _ => map_mul_mulVec_of_scal g v (algebraMap_map_mulVec g v _)
        (map_sub_mulVec_of_scal g v (hv x) (algebraMap_map_mulVec g v _)))]
    have hs := congrArg (fun y => g (βB y)) (comaxC_spec b hij)

    simp only [Finsupp.sum, map_sum, map_mul, map_sub, map_one] at hs
    rw [hs, one_smul]
  have hlast := map_mul_mulVec_of_scal g v (algebraMap_map_mulVec g v (βB (uInv b)))
    (map_sub_mulVec_of_scal g v (hv D.ω) (algebraMap_map_mulVec g v (βB ((D.tr : R) - b.ρ))))
  have h1 : g (βB (uInv b)) * (g (βB (b.t i D.ω)) - g (βB ((D.tr : R) - b.ρ))) = 1 := by
    have hu := congrArg (fun y => g (βB y)) (uInv_mul b)
    simp only [map_mul, map_sub, map_one, map_intCast, map_ofNat] at hu ⊢
    rw [b.t_ω]
    linear_combination hu
  rw [h1, one_smul] at hlast
  unfold projMat
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hlast]
  refine map_list_prod_mulVec_of_fix g v _ ?_
  intro X hX
  rw [List.mem_ofFn] at hX
  obtain ⟨j, rfl⟩ := hX
  split_ifs with h
  · rw [Matrix.map_one _ (map_zero g) (map_one g), Matrix.one_mulVec]
  · exact hα j h

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem heckeSub_finite_free : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), Finite (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A), h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N → toUnit (Over.mk x) ≫ h = 1 → h = 1 := by
  intro p _ D R _ b g k N hk hN hkp hNp S s o
  refine ⟨?_, ?_⟩
  · haveI := D.finLa
    let K : Submodule ℤ D.La := LinearMap.range ((k : ℤ) • LinearMap.id)
    haveI : Finite (D.La ⧸ K) := by
      apply Module.finite_of_fg_torsion
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K q
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, by simp⟩
    let σ := Function.surjInv (Submodule.Quotient.mk_surjective K)
    refine Finite.of_surjective (fun q : D.La ⧸ K => (⟨o.eta (N • g (σ q)), mem_heckeSub o g N _⟩ : heckeSub o g N)) ?_
    rintro ⟨h, x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩
    have e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K) :=
      Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at e
    obtain ⟨z, hz⟩ := e
    have hz' : σ (Submodule.Quotient.mk x) = x + k • z := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz
      rw [hz]; abel
    show o.eta (N • g (σ (Submodule.Quotient.mk x))) = o.eta (N • g x)
    rw [hz', map_add (f := _), map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]
  · intro κ _ _ x h hh h1
    obtain ⟨x0, rfl⟩ := hh
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
    obtain ⟨I, hI⟩ := o.geom κ x _ hβ
    have h2 : I.ev (N * k) (N • g x0) = 1 := by rw [← hI]; exact h1
    obtain ⟨y, hy⟩ := (I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul_left hNp hkp) _).1 h2
    rw [hy, o.eta_ker]

end GlobalTheory.UPel.HT.Hecke
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.ProdGalois
variable {S : Scheme.{0}}

theorem transl_lift_fst {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A) ≫ fst A A = fst A A ≫ transl h₁ := by
  rw [transl, transl, mul_comp, comp_mul, Category.id_comp, Category.comp_id, Category.assoc, lift_fst,
    ← Category.assoc, toUnit_unique (fst A A ≫ toUnit A) (toUnit _)]

theorem transl_lift_snd {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A) ≫ snd A A = snd A A ≫ transl h₂ := by
  rw [transl, transl, mul_comp, comp_mul, Category.id_comp, Category.comp_id, Category.assoc, lift_snd,
    ← Category.assoc, toUnit_unique (snd A A ≫ toUnit A) (toUnit _)]

theorem transl_lift_fst_left {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    (transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A)).left ≫ (fst A A).left = (fst A A).left ≫ (transl h₁).left := by
  rw [← Over.comp_left, transl_lift_fst, Over.comp_left]

theorem transl_lift_snd_left {A : Over S} [GrpObj A] [IsCommMonObj A] (h₁ h₂ : 𝟙_ (Over S) ⟶ A) :
    (transl (lift h₁ h₂ : 𝟙_ (Over S) ⟶ G2 A)).left ≫ (snd A A).left = (snd A A).left ≫ (transl h₂).left := by
  rw [← Over.comp_left, transl_lift_snd, Over.comp_left]

theorem grpScheme_square_hom_ext_fst_snd {A : Over S} {X : Scheme.{0}} {a b : X ⟶ (G2 A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem grpSchemeSquareProductMap_comp_fst {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem grpSchemeSquareProductMap_eq_pullback_map {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ = pullback.map A.hom A.hom A'.hom A'.hom ψ.left ψ.left (𝟙 S) (by simp) (by simp) := by
  apply grpScheme_square_hom_ext_fst_snd
  · rw [grpSchemeSquareProductMap_comp_fst]; exact (pullback.lift_fst _ _ _).symm
  · rw [grpSchemeSquareProductMap_comp_snd]; exact (pullback.lift_snd _ _ _).symm

end GlobalTheory.UPel.HT.Hecke.ProdGalois


open GlobalTheory.UPel.HT.Hecke.ProdGalois in
theorem GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → GlobalTheory.ZM.IsGaloisCover (G × G) (fun h => (GlobalTheory.UPel.HT.Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left) (GlobalTheory.UPel.HT.Hecke.sq2 ψ) := by
  intro S A A' _ _ _ _ G ψ _ hψ
  have := hψ.finite
  have hfin := hψ.fin
  have het := hψ.etale
  have hon := hψ.onto
  refine
    { finite := inferInstance
      one := ?_
      mul := ?_
      inv := ?_
      fin := ?_
      etale := ?_
      onto := ?_
      fibre := ?_ }
  · apply grpScheme_square_hom_ext_fst_snd
    · rw [transl_lift_fst_left, Category.id_comp]
      have e := hψ.one
      rw [show ((1 : G × G).1 : 𝟙_ (Over S) ⟶ A) = ((1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e, Category.comp_id]
    · rw [transl_lift_snd_left, Category.id_comp]
      have e := hψ.one
      rw [show ((1 : G × G).2 : 𝟙_ (Over S) ⟶ A) = ((1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e, Category.comp_id]
  · intro a c
    apply grpScheme_square_hom_ext_fst_snd
    · rw [transl_lift_fst_left, Category.assoc, transl_lift_fst_left, reassoc_of% transl_lift_fst_left]
      have e := hψ.mul a.1 c.1
      rw [show ((a * c).1 : 𝟙_ (Over S) ⟶ A) = ((a.1 * c.1 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e]
    · rw [transl_lift_snd_left, Category.assoc, transl_lift_snd_left, reassoc_of% transl_lift_snd_left]
      have e := hψ.mul a.2 c.2
      rw [show ((a * c).2 : 𝟙_ (Over S) ⟶ A) = ((a.2 * c.2 : G) : 𝟙_ (Over S) ⟶ A) from rfl, e]
  · intro a
    apply grpScheme_square_hom_ext_fst_snd
    · rw [Category.assoc, grpSchemeSquareProductMap_comp_fst, reassoc_of% transl_lift_fst_left, hψ.inv a.1]
    · rw [Category.assoc, grpSchemeSquareProductMap_comp_snd, reassoc_of% transl_lift_snd_left, hψ.inv a.2]
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    exact MorphismProperty.pullbackMap (P := @IsFinite) hfin hfin (Over.w ψ).symm (Over.w ψ).symm
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    haveI : MorphismProperty.IsStableUnderComposition @Etale.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
    exact MorphismProperty.pullbackMap (P := @Etale) het het (Over.w ψ).symm (Over.w ψ).symm
  · rw [grpSchemeSquareProductMap_eq_pullback_map]
    haveI : MorphismProperty.IsStableUnderComposition @Surjective.{0} := ⟨fun _ _ _ _ ↦ inferInstance⟩
    exact MorphismProperty.pullbackMap (P := @Surjective) hon hon (Over.w ψ).symm (Over.w ψ).symm
  · intro K _ _ y y' e
    have e₁ : (y ≫ (fst A A).left) ≫ ψ.left = (y' ≫ (fst A A).left) ≫ ψ.left := by
      rw [Category.assoc, Category.assoc, ← grpSchemeSquareProductMap_comp_fst, reassoc_of% e]
    have e₂ : (y ≫ (snd A A).left) ≫ ψ.left = (y' ≫ (snd A A).left) ≫ ψ.left := by
      rw [Category.assoc, Category.assoc, ← grpSchemeSquareProductMap_comp_snd, reassoc_of% e]
    obtain ⟨a₁, ha₁, hu₁⟩ := hψ.fibre K _ _ e₁
    obtain ⟨a₂, ha₂, hu₂⟩ := hψ.fibre K _ _ e₂
    refine ⟨(a₁, a₂), ?_, ?_⟩
    · apply grpScheme_square_hom_ext_fst_snd
      · rw [Category.assoc, transl_lift_fst_left, ← Category.assoc]; exact ha₁
      · rw [Category.assoc, transl_lift_snd_left, ← Category.assoc]; exact ha₂
    · intro b hb
      refine Prod.ext (hu₁ b.1 ?_) (hu₂ b.2 ?_)
      · show (y ≫ (fst A A).left) ≫ (transl (b.1 : 𝟙_ (Over S) ⟶ A)).left = y' ≫ (fst A A).left
        rw [Category.assoc, ← transl_lift_fst_left _ (b.2 : 𝟙_ (Over S) ⟶ A), ← Category.assoc]
        exact congrArg (· ≫ (fst A A).left) hb
      · show (y ≫ (snd A A).left) ≫ (transl (b.2 : 𝟙_ (Over S) ⟶ A)).left = y' ≫ (snd A A).left
        rw [Category.assoc, ← transl_lift_snd_left (b.1 : 𝟙_ (Over S) ⟶ A), ← Category.assoc]
        exact congrArg (· ≫ (snd A A).left) hb
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem isPushout_sec (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (U : X₀.affineOpens) :
    IsPushout (secMap s₀ U.1) (CommRingCat.ofHom (algebraMap R₀ R₁)) (pr.appLE U.1 (pr ⁻¹ᵁ U.1) le_rfl)
      (secMap s₁ (pr ⁻¹ᵁ U.1)) := by
  have po := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := U.1) (UY := pr ⁻¹ᵁ U.1) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) U.2)
  refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, ← Iso.inv_comp_eq]
    rfl
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp
  · rw [Iso.refl_hom, Category.comp_id, ← Iso.inv_comp_eq]
    rfl

theorem tensHom_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)), Function.Bijective (GlobalTheory.Obs.BC.tensHom hp.w U hU) := by
  intro R₀ R₁ _ _ _ X₀ X₁ s₀ s₁ pr hp U hU
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) := (prSec hp.w U hU).toAlgebra
  haveI : IsScalarTower R₀ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun r ↦
    ((semiHom_secPull hp.w (⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩ : Pair pr)).map_algebraMap r).symm
  have hpo : Algebra.IsPushout R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_sec R₀ R₁ X₀ X₁ s₀ s₁ pr hp U).flip
  have e : ∀ x, tensHom hp.w U hU x = Algebra.IsPushout.equiv R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1)) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r b => rw [tensHom_tmul, Algebra.IsPushout.equiv_tmul]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have : ⇑(tensHom hp.w U hU) = ⇑(Algebra.IsPushout.equiv R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1))) := funext e
  rw [this]
  exact (Algebra.IsPushout.equiv R₀ R₁ (Sec s₀ U.1) (Sec s₁ (pr ⁻¹ᵁ U.1))).bijective

end GlobalTheory.Obs.BC
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ), Desc.HasLoc F → Desc.HasLoc (FormExtJ.omjExt F j) := by
  first | exact @GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt | exact GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt | (intros; apply GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt <;> assumption)
end
