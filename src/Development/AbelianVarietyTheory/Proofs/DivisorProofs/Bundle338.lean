module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle261
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.BcLevel

set_option synthInstance.maxHeartbeats 200000 in
def bcIsoOfIso {E E' : Spc} {S : Scheme.{0}} (α : E ≅ E') (p : E' ⟶ sch.obj S) : bc (α.hom ≫ p) ≅ bc p :=
  haveI : ∀ U, IsIso ((bcMap α.hom p).app U) := fun U => by
    dsimp only [bcMap]; exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  haveI : IsIso (bcMap α.hom p) := NatIso.isIso_of_isIso_app _
  asIso (bcMap α.hom p)

def dq {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) : disc.obj (E.obj k) ⟶ sch.obj S :=
  disc.map (p.app k)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.BcLevel.isPullback_lv {E : _root_.GlobalTheory.EtC.Spc} {S : Scheme.{0}}
    (p : E ⟶ _root_.GlobalTheory.EtC.sch.obj S) (k : SimplexCategoryᵒᵖ) (U : Over S) :
    IsPullback (_root_.GlobalTheory.EtC.disc.map ((pullback.fst p (_root_.GlobalTheory.EtC.sch.map U.hom)).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.disc.obj (E.obj k))
      (_root_.GlobalTheory.EtC.disc.map ((pullback.snd p (_root_.GlobalTheory.EtC.sch.map U.hom)).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.sch.obj U.left)
      (_root_.GlobalTheory.EtC.BcLevel.dq p k) (_root_.GlobalTheory.EtC.sch.map U.hom) := by
  have h := (IsPullback.of_hasPullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).map
    ((evaluation SimplexCategoryᵒᵖ _root_.GlobalTheory.EtC.PSh).obj k)
  exact h.map _root_.GlobalTheory.EtC.disc

def lvIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) (U : Over S) :
    disc.obj ((pullback p (sch.map U.hom)).obj k) ≅ pullback (dq p k) (sch.map U.hom) :=
  (isPullback_lv p k U).isoPullback

set_option synthInstance.maxHeartbeats 200000 in
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.BcLevel.lv_nat {E : _root_.GlobalTheory.EtC.Spc} {S : Scheme.{0}}
    (p : E ⟶ _root_.GlobalTheory.EtC.sch.obj S) (k : SimplexCategoryᵒᵖ) {U V : Over S} (g : U ⟶ V) :
    (_root_.GlobalTheory.EtC.disc.map (((_root_.GlobalTheory.EtC.bc p).map g).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map V.hom)).obj k)) ≫
      (_root_.GlobalTheory.EtC.BcLevel.lvIso p k V).hom = (_root_.GlobalTheory.EtC.BcLevel.lvIso p k U).hom ≫ (_root_.GlobalTheory.EtC.bc (_root_.GlobalTheory.EtC.BcLevel.dq p k)).map g := by
  have hV₁ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k V).isoPullback_hom_fst
  have hV₂ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k V).isoPullback_hom_snd
  have hU₁ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k U).isoPullback_hom_fst
  have hU₂ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k U).isoPullback_hom_snd
  unfold _root_.GlobalTheory.EtC.BcLevel.lvIso
  dsimp only [_root_.GlobalTheory.EtC.bc]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    erw [hV₁, pullback.lift_fst, Category.comp_id, hU₁]
    rw [← Functor.map_comp, ← NatTrans.comp_app, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, Category.assoc]
    erw [hV₂, pullback.lift_snd, ← Category.assoc, hU₂]
    change _ = _root_.GlobalTheory.EtC.disc.map _ ≫
      _root_.GlobalTheory.EtC.disc.map ((_root_.GlobalTheory.EtC.sch.map g.left).app k)
    rw [← Functor.map_comp]
    erw [← Functor.map_comp]
    congr 1
    rw [← NatTrans.comp_app]
    erw [← NatTrans.comp_app, pullback.lift_snd]

def bcDiscIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) :
    bc p ⋙ (evaluation _ PSh).obj k ⋙ disc ≅ bc (dq p k) :=
  NatIso.ofComponents (lvIso p k) (fun g => lv_nat p k g)

theorem bc_level : ∀ (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) (X : Scheme.{0}) (r : X ⟶ S)
    (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r →
    Nonempty (bc (sch.map r) ≅ bc p ⋙ (evaluation _ PSh).obj k ⋙ disc) := by
  intro S E p k X r e h
  have heq : sch.map r = (disc.mapIso e : sch.obj X ≅ disc.obj (E.obj k)).hom ≫ dq p k := by
    change disc.map (yoneda.map r) = disc.map e.hom ≫ disc.map (p.app k)
    rw [← h]
    exact disc.map_comp _ _
  rw [heq]
  exact ⟨bcIsoOfIso _ (dq p k) ≪≫ (bcDiscIso p k).symm⟩

end GlobalTheory.EtC.BcLevel
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem ContCone.iff_of_eqv (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I]
    (G G' : I ⥤ Spc) (c : Cone G) (c' : Cone G') (α : G ⟶ G') (β : c.pt ⟶ c'.pt)
    (h : ∀ i, c.π.app i ≫ α.app i = β ≫ c'.π.app i) (hα : ∀ i, Eqv R (α.app i) F) (hβ : Eqv R β F) :
    ContCone R F c ↔ ContCone R F c' := by
  have hsq : ∀ n i (y' : H R (G'.obj i) F n),
      pull R (c.π.app i) F n (pull R (α.app i) F n y') = pull R β F n (pull R (c'.π.app i) F n y') := by
    intro n i y'
    rw [← pull_comp, ← pull_comp, h i]
  have hnat : ∀ n {k i : I} (f : k ⟶ i) (y' : H R (G'.obj i) F n),
      pull R (G.map f) F n (pull R (α.app i) F n y') = pull R (α.app k) F n (pull R (G'.map f) F n y') := by
    intro n k i f y'
    rw [← pull_comp, ← pull_comp, α.naturality f]
  constructor
  · intro hc n
    refine ⟨fun x' => ?_, fun i y' hy' => ?_⟩
    · obtain ⟨i, y, hy⟩ := (hc n).1 (pull R β F n x')
      obtain ⟨y', rfl⟩ := (hα i n).2 y
      refine ⟨i, y', (hβ n).1 ?_⟩
      rw [← hsq, hy]
    · obtain ⟨k, f, hf⟩ := (hc n).2 i (pull R (α.app i) F n y') (by rw [hsq, hy', map_zero])
      refine ⟨k, f, (hα k n).1 ?_⟩
      rw [← hnat, hf, map_zero]
  · intro hc n
    refine ⟨fun x => ?_, fun i y hy => ?_⟩
    · obtain ⟨x', rfl⟩ := (hβ n).2 x
      obtain ⟨i, y', hy'⟩ := (hc n).1 x'
      exact ⟨i, pull R (α.app i) F n y', by rw [hsq, hy']⟩
    · obtain ⟨y', rfl⟩ := (hα i n).2 y
      have h0 : pull R (c'.π.app i) F n y' = 0 := (hβ n).1 (by rw [← hsq, hy, map_zero])
      obtain ⟨k, f, hf⟩ := (hc n).2 i y' h0
      exact ⟨k, f, by rw [hnat, hf, map_zero]⟩

end GlobalTheory.EtC
end

section

open TensorProduct GlobalTheory.EtC

namespace GlobalTheory.DescTop

theorem top_mul_descMod_eq_top (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (u : (B ⊗[A] B)ˣ) (hu : UCoc A B u) : (⊤ : Submodule A B) * descMod A B u = ⊤ := by
  set F : B →ₗ[A] B ⊗[A] B := (LinearMap.mulLeft A (u : B ⊗[A] B)) ∘ₗ
    (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap with hF
  set G : B →ₗ[A] B ⊗[A] B := (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap with hG
  set f13 := Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  set f12 := Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)
  set f23 := (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))
  have hD : descMod A B u = LinearMap.ker (F - G) := by
    rw [← LinearMap.eqLocus_eq_ker_sub]; rfl
  have hLF : LinearMap.lTensor B F = (LinearMap.mulLeft A (f23 (u : B ⊗[A] B))) ∘ₗ f13.toLinearMap := by
    apply TensorProduct.ext'
    intro c b
    simp [hF, f23, f13, Algebra.TensorProduct.tmul_mul_tmul]
  have hLG : LinearMap.lTensor B G = f12.toLinearMap := by
    apply TensorProduct.ext'
    intro c b
    simp [hG, f12]

  have hinv : f23 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) := by
    have h1 : f13 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : f12 (u : B ⊗[A] B) * f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hc : f13 (u : B ⊗[A] B) = f12 (u : B ⊗[A] B) * f23 (u : B ⊗[A] B) := hu
    calc f23 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)
        = f23 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) *
            (f12 (u : B ⊗[A] B) * f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)) := by rw [h2, mul_one]
      _ = (f13 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)) * f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) := by
            rw [hc]; ring
      _ = f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) := by rw [h1, one_mul]
  have hex := Module.Flat.lTensor_exact B (LinearMap.exact_subtype_ker_map (F - G))
  have hy : ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) ∈
      LinearMap.range (LinearMap.lTensor B (LinearMap.ker (F - G)).subtype) := by
    rw [← hex.linearMap_ker_eq, LinearMap.mem_ker, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero,
      hLF, hLG]
    simpa using hinv
  obtain ⟨z, hz⟩ := hy
  have hmem : ∀ w : B ⊗[A] LinearMap.ker (F - G),
      Algebra.TensorProduct.lmul' A (LinearMap.lTensor B (LinearMap.ker (F - G)).subtype w) ∈
        (⊤ : Submodule A B) * descMod A B u := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul c m =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
      exact Submodule.mul_mem_mul Submodule.mem_top (by rw [hD]; exact m.2)
    | add x y hx hy =>
      simp only [map_add]
      exact Submodule.add_mem _ hx hy
  have hv := hmem z
  rw [hz] at hv
  set v := Algebra.TensorProduct.lmul' A (((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)) with hvdef
  have hvu : IsUnit v := (Units.isUnit (u⁻¹)).map (Algebra.TensorProduct.lmul' A (S := B))
  obtain ⟨w, hw⟩ := hvu.exists_left_inv
  have hle : (⊤ : Submodule A B) * ((⊤ : Submodule A B) * descMod A B u) ≤ (⊤ : Submodule A B) * descMod A B u := by
    rw [← mul_assoc]; first
      | exact Submodule.mul_le_mul le_top le_rfl
      | exact mul_le_mul_right' le_top _
      | (gcongr; exact le_top)
  rw [eq_top_iff]
  intro b _
  have : b = (b * w) * v := by rw [mul_assoc, hw, mul_one]
  rw [this]
  exact hle (Submodule.mul_mem_mul Submodule.mem_top hv)

end GlobalTheory.DescTop
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

section QuotEtale

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {B : La} {t0 : ι → Y → ℂ} {t : Fin n → ι → Y → ℂ}

end QuotEtale

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] in
private lemma sec_eq_transition_mul {A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La} {B : La} {s : ι → Y → ℂ}
    (hs : A.IsSec B s) {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : s i y = A.g B i j y * s j y := by
  have h := hs
  unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at h
  exact h.2 i j y (Set.mem_univ y) hi hj

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.etale_zmap_main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (U : Set Y),
    A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → IsOpen U →
    (∀ y ∈ U, t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y) → _root_.GlobalTheory.OTY.Etale A U (A.zmap t0 t) := by
  intro n Y _ _ _ _ _ ι La _ A B t0 t U h0 ht hU hcoord
  have hne : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source → t0 i y ≠ 0 := by
    intro i y hy hi
    rw [sec_eq_transition_mul h0 hi (A.mem_pick y)]
    exact mul_ne_zero (A.g_ne B i _ y hi (A.mem_pick y)) (hcoord y hy).1
  have hz : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source →
      A.zmap t0 t y = A.zLoc t0 t i (A.chart i y) := by
    intro i y hy hi
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zmap _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc
    rw [(A.chart i).left_inv hi]
    congr 1
    funext k
    rw [sec_eq_transition_mul (ht k) hi (A.mem_pick y),
      sec_eq_transition_mul h0 hi (A.mem_pick y)]
    exact (mul_div_mul_left _ _ (A.g_ne B i _ y hi (A.mem_pick y))).symm
  have hloc : ∀ i, DifferentiableOn ℂ (A.zLoc t0 t i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
    intro i
    apply (differentiableOn_piLp (𝕜 := ℂ) 2).2
    intro k
    have hk := ht k
    have h0' := h0
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at hk h0'
    have hsub : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆
        (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ := fun v hv => ⟨hv.1, Set.mem_univ _⟩
    have hnum : DifferentiableOn ℂ (fun v => t k i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (hk.1 i).mono hsub
    have hden : DifferentiableOn ℂ (fun v => t0 i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (h0'.1 i).mono hsub
    have hdiv : DifferentiableOn ℂ
        (fun v => t k i ((A.chart i).symm v) / t0 i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
      simp only [div_eq_mul_inv]
      exact hnum.mul (hden.inv fun v hv => hne i _ hv.2 ((A.chart i).map_target hv.1))
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc
    exact hdiv
  refine ⟨hU, ?_, ?_⟩
  · intro i
    refine (hloc i).congr ?_
    intro v hv
    simp only [Function.comp_apply]
    rw [hz i _ hv.2 ((A.chart i).map_target hv.1), (A.chart i).right_inv hv.1]
  · intro i y hy hi
    unfold _root_.GlobalTheory.OTY.jdet _root_.GlobalTheory.OTY.jz
    set j := A.pick y with hj_def
    have hj : y ∈ (A.chart j).source := A.mem_pick y
    have hV : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ (A.chart j).source) ∈
        𝓝 (A.chart i y) := by
      refine ((A.chart i).isOpen_inter_preimage_symm (hU.inter (A.chart j).open_source)).mem_nhds ?_
      refine ⟨(A.chart i).map_source hi, ?_⟩
      simp only [Set.mem_preimage, (A.chart i).left_inv hi]
      exact ⟨hy, hj⟩
    have heq : A.zmap t0 t ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        A.zLoc t0 t j ∘ ((A.chart j) ∘ (A.chart i).symm) := by
      filter_upwards [hV] with v hv
      simp only [Function.comp_apply]
      exact hz j _ hv.2.1 hv.2.2
    rw [heq.fderiv_eq]
    have hT : DifferentiableAt ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) := by
      refine (A.holo_trans i j).differentiableAt ?_
      have ho : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
      refine ho.mem_nhds ?_
      refine ⟨(A.chart i).map_source hi, ?_⟩
      simp only [Set.mem_preimage, (A.chart i).left_inv hi]
      exact hj
    have hTy : ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
    have hL : DifferentiableAt ℂ (A.zLoc t0 t j) (((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hTy]
      refine (hloc j).differentiableAt ?_
      refine ((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ?_
      refine ⟨(A.chart j).map_source hj, ?_⟩
      simp only [Set.mem_preimage, (A.chart j).left_inv hj]
      exact hy
    rw [fderiv_comp _ hL hT, hTy]
    have hdet : LinearMap.det (((fderiv ℂ (A.zLoc t0 t j) (A.chart j y)).comp
        (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) :
          _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) =
        LinearMap.det (fderiv ℂ (A.zLoc t0 t j) (A.chart j y) : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) *
          LinearMap.det (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) :
            _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) :=
      LinearMap.det_comp _ _
    rw [ContinuousLinearMap.det, hdet]
    refine mul_ne_zero ?_ ?_
    · have hc := (hcoord y hy).2
      unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsCoordAt at hc
      exact hc
    · have hk := A.g_kap i j y hi hj
      have hg := A.g_ne A.kap i j y hi hj
      rw [hk] at hg
      exact hg

end GlobalTheory.OTY
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FreeHom

variable {R : Type} [CommRing R]

theorem val_eq {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    val s U x = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom).app (op U)).hom
      (ModuleCat.freeMk (ULift.up x)) := rfl

theorem freePresheaf_map_freeMk (P : PSh) {U V : Scheme.{0}ᵒᵖ} (g : U ⟶ V) (x : P.obj U) :
    (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
  change ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (P.map g))).hom (ModuleCat.freeMk (ULift.up x)) = _
  exact ModuleCat.free_map_apply _ _

theorem freePresheaf_map_app_freeMk {P P' : PSh} (f : P' ⟶ P) (U : Scheme.{0}ᵒᵖ) (x : P'.obj U) :
    (((freeP R).map f).app U).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (f.app U x)) := by
  change ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (f.app U))).hom (ModuleCat.freeMk (ULift.up x)) = _
  exact ModuleCat.free_map_apply _ _

theorem ext {P : PSh} {G : Shv R} (s s' : (free R).obj P ⟶ G) (h : ∀ U x, val s U x = val s' U x) : s = s' := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  apply NatTrans.ext
  funext U
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have hx := h U.unop x
  rw [val_eq, val_eq] at hx
  exact hx

def descP (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom fun x => φ U.unop x.down)
  naturality U V g := by
    apply ModuleCat.free_hom_ext
    rintro ⟨x⟩
    change (ModuleCat.freeDesc _).hom ((((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x))) =
      (G.obj.map g).hom ((ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up x)))
    rw [freePresheaf_map_freeMk]
    erw [ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact hφ V.unop U.unop g.unop x

def desc (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) :
    (free R).obj P ⟶ G :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).symm (descP P G φ hφ)

theorem val_desc (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x))
    (U : Scheme.{0}) (x : P.obj (op U)) : val (desc P G φ hφ) U x = φ U x := by
  rw [val_eq]
  have key : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ (desc P G φ hφ).hom = descP P G φ hφ := by
    have hs := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply
      (descP P G φ hφ)
    rw [Adjunction.homEquiv_unit] at hs
    exact hs
  rw [key]
  change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up x)) = _
  erw [ModuleCat.freeDesc_apply]
  rfl

private theorem val_nat_lemma {P : PSh} {F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (η : (freeP R).obj P ⟶ F)
    {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op x))) =
      (F.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up x))) :=
  calc (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op x)))
      = (η.app (op V)).hom ((((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x))) :=
        congrArg (η.app (op V)).hom (freePresheaf_map_freeMk P g.op x).symm
    _ = _ := congrArg (fun k => k.hom (ModuleCat.freeMk (ULift.up x))) (η.naturality g.op)

theorem val_nat {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)) :
    val s V (P.map g.op x) = Sec.res g (val s U x) := by
  rw [val_eq, val_eq]
  exact val_nat_lemma _ g x

theorem val_free_map {P P' : PSh} (f : P' ⟶ P) {G : Shv R} (s : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P'.obj (op U)) :
    val ((free R).map f ≫ s) U x = val s U (f.app (op U) x) := by
  rw [val_eq, val_eq]
  have hn : toSheafify Scheme.etaleTopology ((freeP R).obj P') ≫ ((free R).map f ≫ s).hom
      = (freeP R).map f ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom :=
    (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map f) s.hom).symm
  rw [hn]
  change ((toSheafify _ _ ≫ s.hom).app (op U)).hom ((((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) = _
  rw [freePresheaf_map_app_freeMk]

theorem val_comp {P : PSh} {G G' : Shv R} (s : (free R).obj P ⟶ G) (ψ : G ⟶ G') (U : Scheme.{0}) (x : P.obj (op U)) :
    val (s ≫ ψ) U x = Sec.map ψ (val s U x) := rfl

theorem val_add {P : PSh} {G : Shv R} (s s' : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    val (s + s') U x = val s U x + val s' U x := rfl

def valHom (P : PSh) (G : Shv R) (U : Scheme.{0}) (x : P.obj (op U)) : ((free R).obj P ⟶ G) →+ Sec G U :=
  AddMonoidHom.mk' (fun s => val s U x) (fun s s' => val_add s s' U x)

theorem val_zsmul {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (m : ℤ) (U : Scheme.{0}) (x : P.obj (op U)) :
    val (m • s) U x = m • val s U x := by
  exact map_zsmul (valHom P G U x) m s

theorem main : ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R), (∀ s s' : (free R).obj P ⟶ G, (∀ U x, val s U x = val s' U x) → s = s') ∧ (∀ φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) → ∃ s : (free R).obj P ⟶ G, ∀ U x, val s U x = φ U x) ∧ (∀ (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), val s V (P.map g.op x) = Sec.res g (val s U x)) ∧ (∀ (P' : PSh) (f : P' ⟶ P) (s : (free R).obj P ⟶ G) U x, val ((free R).map f ≫ s) U x = val s U (f.app (op U) x)) ∧ (∀ (G' : Shv R) (ψ : G ⟶ G') (s : (free R).obj P ⟶ G) U x, val (s ≫ ψ) U x = Sec.map ψ (val s U x)) ∧ ∀ (s s' : (free R).obj P ⟶ G) (m : ℤ) U x, val (s + s') U x = val s U x + val s' U x ∧ val (m • s) U x = m • val s U x := by
  intro R _ P G
  exact ⟨fun s s' h => ext s s' h, fun φ hφ => ⟨desc P G φ hφ, val_desc P G φ hφ⟩,
    fun s V U g x => val_nat s V U g x, fun P' f s U x => val_free_map f s U x,
    fun G' ψ s U x => val_comp s ψ U x, fun s s' m U x => ⟨val_add s s' U x, val_zsmul s m U x⟩⟩

end GlobalTheory.EtC.FreeHom
end
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.exists_parameter_function_of_fibreDeriv_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ (a : ∀ k, Hol (K.W k)), (∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k') → (∀ k i, dw i (a k) = 0) → ∃ p : Hol F.V, ∀ k, a k = K.cst k p := by
  exact @GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero
end

section

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

theorem _root_.GlobalTheory.T.fibreCoordinatePartialDerivation_comm : ∀ (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W), dw a (dw b x) = dw b (dw a x) := by
  first | exact @GlobalTheory.AnPer.dw_comm | exact GlobalTheory.AnPer.dw_comm | (intros; apply GlobalTheory.AnPer.dw_comm <;> assumption)
end
