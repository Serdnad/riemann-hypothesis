module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle577
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open scoped Pointwise

theorem prod_mul_eq_zero_of_mem_span {S X ι : Type} [CommRing S] [Fintype ι] (N : ι → X → S) (W : S)
    (h : ∀ c : ι → X, (∏ j, N j (c j)) * W = 0) (f : ι → S)
    (hf : ∀ j, f j ∈ Ideal.span (Set.range (N j))) : (∏ j, f j) * W = 0 := by
  classical
  have hmem : (∏ j, f j) ∈ Ideal.span (∏ j, Set.range (N j)) := by
    rw [← Ideal.prod_span]
    exact Ideal.prod_mem_prod fun j _ => hf j
  refine Submodule.span_induction (p := fun x _ => x * W = 0) ?_ ?_ ?_ ?_ hmem
  · intro x hx
    obtain ⟨e, he, rfl⟩ := (Set.mem_fintype_prod (fun j => Set.range (N j)) x).1 hx
    choose c hc using he
    simpa [hc] using h c
  · simp
  · intro x y _ _ hx hy; rw [add_mul, hx, hy, add_zero]
  · intro a x _ hx; rw [smul_eq_mul, mul_assoc, hx, mul_zero]

end GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

theorem mapMatrix_algebraMap_fin {B K : Type} [CommRing B] [CommRing K] (g : B →+* K) {n : ℕ} (x : B) :
    g.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) x) = algebraMap K (Matrix (Fin n) (Fin n) K) (g x) := by
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

theorem map_mul_projMat_eq_smul (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (B : Type) [CommRing B] (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K]
    (g : B →+* K) :
    lieIdeal b βB M ≤ RingHom.ker g → ∀ (i : Fin D.a) (c : 𝓞 D.F),
      (M c).map g * (projMat b βB M i).map g = g (βB (b.t i c)) • (projMat b βB M i).map g := by
  intro hI i c
  classical
  set M' : 𝓞 D.F →+* Matrix (Fin n) (Fin n) K := g.mapMatrix.comp M with hM'
  have hcomm : ∀ a ∈ Set.range M', ∀ a' ∈ Set.range M', a * a' = a' * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; rw [← map_mul, ← map_mul, mul_comm]
  let S := Algebra.adjoin K (Set.range M')
  let : IsMulCommutative S := Algebra.isMulCommutative_adjoin K fun a ha a' ha' _ =>
    hcomm a ha a' ha'
  let : CommRing S := open scoped IsMulCommutative in inferInstance
  let m : 𝓞 D.F → S := fun x => ⟨M' x, Algebra.subset_adjoin ⟨x, rfl⟩⟩
  let sc : R → S := fun r => algebraMap K S (g (βB r))
  let N : Fin D.a → 𝓞 D.F → S := fun j x => m x - sc (b.t j x)
  let WS : S := m D.ω - sc ((D.tr : R) - b.ρ)
  let α : Fin D.a → S := fun j => (comaxC b i j).sum fun x r => sc r * N j x
  let PS : S := (List.ofFn fun j => if j = i then 1 else α j).prod * (sc (uInv b) * WS)
  have hsc : ∀ r, S.val (sc r) = g.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) (βB r)) := by
    intro r; rw [AlgHom.commutes, mapMatrix_algebraMap_fin]
  have hm : ∀ x, S.val (m x) = g.mapMatrix (M x) := fun _ => rfl
  have hN : ∀ j x, S.val (N j x) =
      g.mapMatrix (M x - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t j x))) := by
    intro j x; simp only [N, map_sub, hm, hsc]
  have hW : S.val WS = g.mapMatrix (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ))) := by
    simp only [WS, map_sub, hm, hsc]
  have hα : ∀ j, S.val (α j) = g.mapMatrix (alphaMat b βB M i j) := by
    intro j; simp only [α, alphaMat, Finsupp.sum, map_sum, map_mul, hsc, hN]
  have hP : S.val PS = g.mapMatrix (projMat b βB M i) := by
    have hfactor (j : Fin D.a) : S.val (if j = i then 1 else α j) =
        g.mapMatrix (if j = i then 1 else alphaMat b βB M i j) := by
      by_cases hj : j = i <;> simp [hj, hα]
    simp only [PS, projMat, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, hsc, hW,
      hfactor]
  have hlie : ∀ c' : Fin D.a → 𝓞 D.F, (∏ j, N j (c' j)) * WS = 0 := by
    intro c'
    have h0 : g.mapMatrix (lieMat b βB M c') = 0 := by
      ext k l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
      exact hI (Ideal.subset_span ⟨c', k, l, rfl⟩)
    rw [← List.prod_ofFn]
    refine (map_eq_zero_iff S.val Subtype.val_injective).1 ?_
    rw [← h0]
    simp only [lieMat, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, hN, hW]
  have hkey : N i c * PS = 0 := by
    have hf : ∀ j, (if j = i then N i c else α j) ∈ Ideal.span (Set.range (N j)) := by
      intro j; split_ifs with hj
      · subst hj; exact Ideal.subset_span ⟨c, rfl⟩
      · exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)
    have h1 := prod_mul_eq_zero_of_mem_span N WS hlie _ hf
    have h2 : N i c * (∏ j, if j = i then (1 : S) else α j) = ∏ j, if j = i then N i c else α j := by
      rw [show (∏ j, if j = i then N i c else α j) =
          ∏ j, ((if j = i then N i c else 1) * if j = i then 1 else α j) from
          Finset.prod_congr rfl fun j _ => by split_ifs <;> simp, Finset.prod_mul_distrib, Finset.prod_ite_eq']
      simp
    simp only [PS, List.prod_ofFn]
    rw [← mul_assoc, h2, mul_left_comm, h1, mul_zero]
  have h3 := congrArg S.val hkey
  rw [map_mul, map_zero, hN, hP, map_sub, mapMatrix_algebraMap_fin, sub_mul] at h3
  change g.mapMatrix (M c) * g.mapMatrix (projMat b βB M i) = _
  rw [Algebra.smul_def, ← sub_eq_zero]
  exact h3

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.GrpTangentPt

noncomputable section

namespace GlobalTheory.TanPtMod

variable {S : Scheme.{0}} {k : Type} [CommRing k] (x : Sp k ⟶ S)

def epsZeroPt : Over.mk x ⟶ epsPtR x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = x
    rw [← Category.assoc, ← Spec.map_comp]
    conv_rhs => rw [← Category.id_comp x]
    congr 1
    rw [← Spec.map_id]
    congr 1)

@[reassoc]
lemma epsZeroPt_epsScalePt (c : k) : epsZeroPt x ≫ epsScalePt x c = epsZeroPt x := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  simp

lemma epsScalePt_mul (a b : k) : epsScalePt x a ≫ epsScalePt x b = epsScalePt x (a * b) := by
  rw [sqZeroMapPt_comp]
  congr 1
  refine LinearMap.ext_ring ?_
  simp

variable (G : Over S) [GrpObj G] [IsCommMonObj G]

def tanSub : Subgroup (epsPtR x ⟶ G) where
  carrier := {w | epsZeroPt x ≫ w = 1}
  one_mem' := comp_one _
  mul_mem' {a b} ha hb := by
    change epsZeroPt x ≫ (a * b) = 1
    rw [comp_mul, ha, hb, _root_.one_mul]
  inv_mem' {a} ha := by
    change epsZeroPt x ≫ a⁻¹ = 1
    rw [GrpObj.comp_inv, ha, _root_.inv_one]

lemma mem_tanSub_iff (w : epsPtR x ⟶ G) :
    w ∈ tanSub x G ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left := by
  change epsZeroPt x ≫ w = 1 ↔ _
  exact ⟨fun h => congrArg Over.Hom.left h, fun h => Over.OverMorphism.ext h⟩

abbrev Tan : Type := Additive (tanSub x G)

variable {x G}

def Tan.hom (v : Tan x G) : epsPtR x ⟶ G := (Additive.toMul v : tanSub x G).1

def Tan.mk (w : epsPtR x ⟶ G) (hw : w ∈ tanSub x G) : Tan x G := Additive.ofMul ⟨w, hw⟩

lemma Tan.hom_mem (v : Tan x G) : v.hom ∈ tanSub x G := (Additive.toMul v : tanSub x G).2

@[ext] lemma Tan.ext {v w : Tan x G} (h : v.hom = w.hom) : v = w :=
  Additive.toMul.injective (Subtype.ext h)

def Tan.homAdd : Tan x G →+ Additive (epsPtR x ⟶ G) := (tanSub x G).subtype.toAdditive

lemma Tan.hom_sum {I : Type} (s : Finset I) (v : I → Tan x G) : (∑ i ∈ s, v i).hom = ∏ i ∈ s, (v i).hom := by
  have := map_sum (Tan.homAdd (x := x) (G := G)) v s
  exact congrArg Additive.toMul this

instance : Module k (Tan x G) where
  smul c v := Tan.mk (epsScalePt x c ≫ v.hom) (by
    change epsZeroPt x ≫ _ = 1
    rw [epsZeroPt_epsScalePt_assoc]; exact v.hom_mem)
  one_smul v := Tan.ext (by
    change epsScalePt x 1 ≫ v.hom = _
    rw [epsScalePt_one, Category.id_comp])
  mul_smul a b v := Tan.ext (by
    change epsScalePt x (a * b) ≫ v.hom = epsScalePt x a ≫ epsScalePt x b ≫ v.hom
    rw [← Category.assoc, epsScalePt_mul])
  smul_zero c := Tan.ext (comp_one _)
  smul_add c v w := Tan.ext (comp_mul _ _ _)
  add_smul a b v := Tan.ext (epsScalePt_add_comp x a b ((mem_tanSub_iff x G _).mp v.hom_mem))
  zero_smul v := Tan.ext (epsScalePt_zero_comp x ((mem_tanSub_iff x G _).mp v.hom_mem))

@[simp] lemma Tan.hom_smul (c : k) (v : Tan x G) : (c • v).hom = epsScalePt x c ≫ v.hom := rfl

def Tan.map (f : G ⟶ G) [IsMonHom f] : Tan x G →ₗ[k] Tan x G where
  toFun v := Tan.mk (v.hom ≫ f) (by
    change epsZeroPt x ≫ _ = 1
    rw [← Category.assoc, v.hom_mem, one_comp])
  map_add' v w := Tan.ext (mul_comp _ _ _)
  map_smul' c v := Tan.ext (Category.assoc _ _ _)

def actEnd {O : Type} [Ring O] (a : OActN O G) : O →+* Module.End k (Tan x G) where
  toFun b := haveI := a.hom b; Tan.map (a.act b)
  map_one' := by
    refine LinearMap.ext fun v => Tan.ext ?_
    change v.hom ≫ a.act 1 = v.hom
    rw [a.one, Category.comp_id]
  map_mul' b c := by
    refine LinearMap.ext fun v => Tan.ext ?_
    change v.hom ≫ a.act (b * c) = (v.hom ≫ a.act c) ≫ a.act b
    rw [a.mul, Category.assoc]
  map_zero' := by
    have h : a.act 0 = 1 := by
      have := a.add 0 0
      rw [add_zero] at this
      exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
    refine LinearMap.ext fun v => Tan.ext ?_
    change v.hom ≫ a.act 0 = 1
    rw [h, comp_one]
  map_add' b c := by
    refine LinearMap.ext fun v => Tan.ext ?_
    change v.hom ≫ a.act (b + c) = (v.hom ≫ a.act b) * (v.hom ≫ a.act c)
    rw [a.add, comp_mul]

end GlobalTheory.TanPtMod
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem exists_affineOpen_nhds_le {X : Scheme.{0}} (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (W : Set X) from hx) W.isOpen
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

theorem pairBC_fst_basis : ∀ (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (e : f₁ ≫ pr = pr' ≫ f₀), (∀ U : Y₁.Opens, ∃ V : Y₀.Opens, pr' ⁻¹ᵁ V = U) → (∀ (x : Y₁) (U : Y₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : Y₁) (U : Y₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ≤ U) := by
  intro X₀ X₁ Y₀ Y₁ pr pr' _ _ f₀ f₁ e hsurj
  constructor
  · intro x U hx
    obtain ⟨W₀, rfl⟩ := hsurj U
    have hy : pr' x ∈ W₀ := hx
    obtain ⟨V, hfV, -⟩ := exists_affineOpen_nhds_le (f₀ (pr' x)) ⊤ trivial
    obtain ⟨U', hU', hU'le⟩ := exists_affineOpen_nhds_le (pr' x) (W₀ ⊓ f₀ ⁻¹ᵁ V.1) ⟨hy, hfV⟩
    refine ⟨Opposite.op (⟨(U', V), hU'le.trans inf_le_right⟩ : Pair f₀), ?_, ?_⟩
    · show pr' x ∈ U'.1
      exact hU'
    · show pr' ⁻¹ᵁ U'.1 ≤ pr' ⁻¹ᵁ W₀
      exact pr'.preimage_mono (hU'le.trans inf_le_left)
  · intro t₁ t₂ x U hx h₁ h₂
    obtain ⟨W₀, rfl⟩ := hsurj U
    have hy : pr' x ∈ W₀ := hx
    have hy₁ : pr' x ∈ t₁.unop.1.1.1 := h₁
    have hy₂ : pr' x ∈ t₂.unop.1.1.1 := h₂
    have hf₁ : f₀ (pr' x) ∈ t₁.unop.1.2.1 := t₁.unop.2 hy₁
    have hf₂ : f₀ (pr' x) ∈ t₂.unop.1.2.1 := t₂.unop.2 hy₂
    obtain ⟨V, hfV, hVle⟩ := exists_affineOpen_nhds_le (f₀ (pr' x)) (t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨hf₁, hf₂⟩
    obtain ⟨U', hU', hU'le⟩ := exists_affineOpen_nhds_le (pr' x)
      (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1 ⊓ W₀ ⊓ f₀ ⁻¹ᵁ V.1) ⟨⟨⟨hy₁, hy₂⟩, hy⟩, hfV⟩
    let p : Pair f₀ := ⟨(U', V), hU'le.trans inf_le_right⟩
    have hp₁ : p ≤ t₁.unop := Subtype.coe_le_coe.1 (Prod.mk_le_mk.2
      ⟨hU'le.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)), hVle.trans inf_le_left⟩)
    have hp₂ : p ≤ t₂.unop := Subtype.coe_le_coe.1 (Prod.mk_le_mk.2
      ⟨hU'le.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)), hVle.trans inf_le_right⟩)
    refine ⟨Opposite.op p, ⟨(homOfLE hp₁).op⟩, ⟨(homOfLE hp₂).op⟩, ?_, ?_⟩
    · show pr' x ∈ U'.1
      exact hU'
    · show pr' ⁻¹ᵁ U'.1 ≤ pr' ⁻¹ᵁ W₀
      exact pr'.preimage_mono (hU'le.trans (inf_le_left.trans inf_le_right))

end GlobalTheory.Obs.BC
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem preAff_basis : ∀ (X₀ X₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) [IsAffineHom pr], (∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U) → (∀ (x : X₁) (U : X₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : X₁) (U : X₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ≤ U) := by
  intro X₀ X₁ pr _ hsurj
  refine ⟨?_, ?_⟩
  · intro x U hx
    obtain ⟨V, rfl⟩ := hsurj U
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open (show pr.base x ∈ V from hx) V.isOpen
    exact ⟨Opposite.op ⟨W, hW⟩, hxW, pr.preimage_mono hWV⟩
  · intro t₁ t₂ x U hx h₁ h₂
    obtain ⟨V, rfl⟩ := hsurj U
    have hmem : pr.base x ∈ t₁.unop.1 ⊓ t₂.unop.1 ⊓ V := ⟨⟨h₁, h₂⟩, hx⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X₀.isBasis_affineOpens.exists_subset_of_mem_open hmem (t₁.unop.1 ⊓ t₂.unop.1 ⊓ V).isOpen
    have hWV' : W ≤ t₁.unop.1 ⊓ t₂.unop.1 ⊓ V := hWV
    exact ⟨Opposite.op ⟨W, hW⟩, ⟨(homOfLE (show (⟨W, hW⟩ : X₀.affineOpens) ≤ t₁.unop from
        (le_trans hWV' (le_trans inf_le_left inf_le_left) : W ≤ t₁.unop.1))).op⟩,
      ⟨(homOfLE (show (⟨W, hW⟩ : X₀.affineOpens) ≤ t₂.unop from
        (le_trans hWV' (le_trans inf_le_left inf_le_right) : W ≤ t₂.unop.1))).op⟩, hxW,
      pr.preimage_mono (le_trans hWV' inf_le_right)⟩

end GlobalTheory.Obs.BC
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open Opposite
namespace GlobalTheory.Obs.BC

theorem tensPair_extMap_pairPull : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀) (p : (Pair f₀)ᵒᵖ) (b : (ext R₁ (OAff s₀)).obj ((pairSnd f₀).obj p)), (GlobalTheory.Obs.BC.tensPair w' e).α p ((extMap R₁ (pairPull h₀)).α p b) = (pairPull h₁).α ((GlobalTheory.Obs.BC.pairBC pr pr' e).obj p) ((GlobalTheory.Obs.BC.tensCoef w).α ((pairSnd f₀).obj p) b) := by
  intro R₀ R₁ _ _ _ X₀ X₁ Y₀ Y₁ s₀ s₁ pr t₀ t₁ pr' _ _ w w' f₀ f₁ h₀ h₁ e p b
  have key : ∀ (g g' : Y₁ ⟶ X₀) (_ : g = g') (U : X₀.Opens) (V : Y₁.Opens) (k : V ≤ g ⁻¹ᵁ U) (k' : V ≤ g' ⁻¹ᵁ U),
      g.appLE U V k = g'.appLE U V k' := by
    rintro g _ rfl U V k k'; rfl
  change tensHom w' (unop ((pairFst f₀).obj p)) _ (extHom R₁ (coefHom (pairPull h₀) p) b) =
    GlobalTheory.CechDR.secPull s₁ t₁ (pairBCObj pr pr' e p.unop) (tensHom w (unop ((pairSnd f₀).obj p)) _ b)
  induction b using TensorProduct.induction_on with
  | zero => repeat erw [map_zero]
            all_goals exact rfl
  | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]; exact rfl
  | tmul r x =>
    refine (congrArg (tensHom w' _ _) (Algebra.TensorProduct.map_tmul _ _ r x)).trans ?_
    refine (tensHom_tmul w' _ _ r _).trans ?_
    have h2 := congrArg (GlobalTheory.CechDR.secPull s₁ t₁ (pairBCObj pr pr' e p.unop))
      (tensHom_tmul w (unop ((pairSnd f₀).obj p)) ((isAffine_aff _).preimage pr) r x)
    refine Eq.trans ?_ h2.symm
    refine Eq.trans ?_ (map_mul _ _ _).symm
    congr 1
    · exact ((semiHom_secPull h₁ (pairBCObj pr pr' e p.unop)).map_algebraMap r).symm
    · change (pr'.appLE _ _ _).hom ((f₀.appLE _ _ _).hom x) = (f₁.appLE _ _ _).hom ((pr.appLE _ _ _).hom x)
      have c1 := Scheme.Hom.appLE_comp_appLE pr' f₀ p.unop.1.2.1 p.unop.1.1.1 (pr' ⁻¹ᵁ p.unop.1.1.1) p.unop.2 le_rfl
      have c2 := Scheme.Hom.appLE_comp_appLE f₁ pr p.unop.1.2.1 (pr ⁻¹ᵁ p.unop.1.2.1) (pr' ⁻¹ᵁ p.unop.1.1.1) le_rfl
        (pairBCObj pr pr' e p.unop).2
      rw [key (pr' ≫ f₀) (f₁ ≫ pr) e.symm _ _ _ (by rw [e]; exact pr'.preimage_mono p.unop.2)] at c1
      exact (congrArg (fun t ↦ t.hom x) c1).trans (congrArg (fun t ↦ t.hom x) c2).symm

end GlobalTheory.Obs.BC
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.BC

theorem natCoef_pull1_bijective (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F F' : C ⥤ CommAlgCat.{0} R)
    (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) :
    (∀ T, Function.Bijective (α T)) → Function.Bijective (GlobalTheory.Obs.BC.natCoef α nat smul).pull1 := by
  intro hb
  let β : ∀ T, F'.obj T →+* F.obj T := fun T ↦ (RingEquiv.ofBijective (α T) (hb T)).symm.toRingHom
  have hαβ : ∀ T (b : F'.obj T), α T (β T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).apply_symm_apply b
  have hβα : ∀ T (b : F.obj T), β T (α T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).symm_apply_apply b
  have natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b) := by
    intro T T' a b
    apply (hb T').1
    rw [hαβ, nat, hαβ]
  have smulβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b := by
    intro T r b
    apply (hb T).1
    rw [hαβ, smul, hαβ]
  let m := GlobalTheory.Obs.BC.natCoef α nat smul
  let n := GlobalTheory.Obs.BC.natCoef β natβ smulβ
  have left : ∀ c, n.pull1 (m.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hβα T' _
  have right : ∀ c, m.pull1 (n.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F' c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hαβ T' _
  exact ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩

end GlobalTheory.Obs.BC
end
end

section

open GlobalTheory.SliceSchwartz

theorem _root_.GlobalTheory.T.schwartz_tensor_right_operator : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type)
    [Fintype κ] [Fintype κ'] [Fintype κ₁'] (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ),
    ∃ Q : SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ₁' → V) ℂ,
      ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V), Q f s = P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr) := by
  first | exact @GlobalTheory.SliceOp.exists_tensor_clm | exact GlobalTheory.SliceOp.exists_tensor_clm | (intros; apply GlobalTheory.SliceOp.exists_tensor_clm <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → (F).obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp (F) u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (F).obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp (F) u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt <;> assumption)
end

section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.mem_symmetricCocycles_of_pullback_mulP : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (c : G.A n ⊗[R] G.A n), pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1)) → c ∈ symCocycles R (G.A n) := by
  first | exact @GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP | exact GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP | (intros; apply GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP <;> assumption)
end
