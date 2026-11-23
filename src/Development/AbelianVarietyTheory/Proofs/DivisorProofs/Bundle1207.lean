module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle484
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

open TopologicalSpace

theorem exists_pic_of_glue_units {X X₁ X₂ : Scheme.{0}} (p₁ : X₁ ⟶ X) (p₂ : X₂ ⟶ X) [IsClosedImmersion p₂]
    [Surjective p₂] (D : LB X₂) (hD : D.IsLB)
    (inj : ∀ (W : X.Opens) (a b : Γ(X, W)ˣ), pullU p₁ W a = pullU p₁ W b → pullU p₂ W a = pullU p₂ W b → a = b)
    (glue : ∀ (W : X.Opens) (a b : D.ι) (h : p₂ ⁻¹ᵁ W ≤ D.U a ⊓ D.U b),
      ∃ v : Γ(X, W)ˣ, pullU p₁ W v = 1 ∧ pullU p₂ W v = res h (D.g a b)) :
    ∃ c : Pic X, GlobalTheory.CechPic.pull p₁ c = 0 ∧ GlobalTheory.CechPic.pull p₂ c = cls D hD := by
  have hW : ∀ a : D.ι, ∃ W : X.Opens, ∀ y : X₂, p₂ y ∈ W ↔ y ∈ D.U a := fun a => by
    obtain ⟨t, ht, e⟩ := (p₂.isClosedEmbedding.isInducing.isOpen_iff).1 (D.U a).isOpen
    exact ⟨⟨t, ht⟩, fun y => Set.ext_iff.1 e y⟩
  choose W hW using hW
  have hle : ∀ a b, p₂ ⁻¹ᵁ (W a ⊓ W b) ≤ D.U a ⊓ D.U b := fun a b y hy => ⟨(hW a y).1 hy.1, (hW b y).1 hy.2⟩
  choose v hv₁ hv₂ using fun a b => glue (W a ⊓ W b) a b (hle a b)
  have g₁ : ∀ (y : X₁) a b, p₁ y ∈ W a → p₁ y ∈ W b → gm (𝟙 X₁ ≫ p₁) y (W a ⊓ W b) (v a b) = 1 :=
    fun y a b ha hb => by
      rw [← gm_pull (𝟙 X₁) p₁ y (W a ⊓ W b) ⟨ha, hb⟩, hv₁, map_one]
  have g₂ : ∀ (y : X₂) a b, p₂ y ∈ W a → p₂ y ∈ W b →
      gm (𝟙 X₂ ≫ p₂) y (W a ⊓ W b) (v a b) = gm (𝟙 X₂) y _ (D.g a b) :=
    fun y a b ha hb => by
      rw [← gm_pull (𝟙 X₂) p₂ y (W a ⊓ W b) ⟨ha, hb⟩, hv₂, gm_res (𝟙 X₂) y (hle a b) ⟨ha, hb⟩]
  have ext : ∀ (V : X.Opens) (a b : Γ(X, V)ˣ),
      (∀ y : X₁, p₁ y ∈ V → gm (𝟙 X₁ ≫ p₁) y V a = gm (𝟙 X₁ ≫ p₁) y V b) →
      (∀ y : X₂, p₂ y ∈ V → gm (𝟙 X₂ ≫ p₂) y V a = gm (𝟙 X₂ ≫ p₂) y V b) → a = b := fun V a b h₁ h₂ =>
    inj V a b
      (unit_ext fun y hy => by rw [gm_pull (𝟙 X₁) p₁ y V hy, gm_pull (𝟙 X₁) p₁ y V hy]; exact h₁ y hy)
      (unit_ext fun y hy => by rw [gm_pull (𝟙 X₂) p₂ y V hy, gm_pull (𝟙 X₂) p₂ y V hy]; exact h₂ y hy)
  let E : LB X := ⟨D.ι, W, v⟩
  have hE : E.IsLB :=
    { cover := by
        rw [eq_top_iff]
        intro x _
        obtain ⟨y, rfl⟩ := Surjective.surj (f := p₂) x
        obtain ⟨a, ha⟩ := exists_chart hD y
        exact Opens.mem_iSup.2 ⟨a, (hW a y).2 ha⟩
      g_self := fun a => ext _ _ _
        (fun y hy => by
          rw [gm_res (𝟙 X₁ ≫ p₁) y _ hy, map_one]
          exact g₁ y a a hy hy)
        (fun y hy => by
          rw [gm_res (𝟙 X₂ ≫ p₂) y _ hy, map_one]
          exact (g₂ y a a hy hy).trans (gm_self hD (𝟙 X₂) y ((hW a y).1 hy)))
      cocycle := fun a b c => ext _ _ _
        (fun y hy => by
          rw [map_mul, gm_res (𝟙 X₁ ≫ p₁) y _ hy, gm_res (𝟙 X₁ ≫ p₁) y _ hy, gm_res (𝟙 X₁ ≫ p₁) y _ hy]
          exact (congrArg₂ (· * ·) (g₁ y a b hy.1.1 hy.1.2) (g₁ y b c hy.1.2 hy.2)).trans
            ((_root_.mul_one _).trans (g₁ y a c hy.1.1 hy.2).symm))
        (fun y hy => by
          rw [map_mul, gm_res (𝟙 X₂ ≫ p₂) y _ hy, gm_res (𝟙 X₂ ≫ p₂) y _ hy, gm_res (𝟙 X₂ ≫ p₂) y _ hy]
          exact (congrArg₂ (· * ·) (g₂ y a b hy.1.1 hy.1.2) (g₂ y b c hy.1.2 hy.2)).trans
            ((gm_cocycle hD (𝟙 X₂) y ((hW a y).1 hy.1.1) ((hW b y).1 hy.1.2) ((hW c y).1 hy.2)).trans
              (g₂ y a c hy.1.1 hy.2).symm)) }
  refine ⟨cls E hE, ?_, ?_⟩
  · rw [← cls_pull hE p₁ (pull_isLB hE p₁), cls_eq_zero_iff]
    refine ⟨⟨fun _ => 1⟩, (isGen_iff_germ _).2 fun y J J' hJ hJ' => ?_⟩
    rw [map_one, map_one, _root_.mul_one]
    exact ((gm_pull_g E p₁ (𝟙 _) y J J' hJ hJ').trans (g₁ y _ _ (mem_pull.1 hJ) (mem_pull.1 hJ'))).symm
  · rw [← cls_pull hE p₂ (pull_isLB hE p₂)]
    refine Eq.symm ((cls_eq_iff hD (pull_isLB hE p₂)).2 (iso_of_chart (pull_isLB hE p₂) ?_))
    exact
      { idx := fun a _ => a
        le := fun a y hy => mem_pull.2 ((hW a y).2 hy)
        g := fun y a b ha hb => Eq.symm ((gm_pull_g E p₂ (𝟙 _) y (fun _ => a) (fun _ => b)
          (mem_pull.2 ((hW a y).2 ha)) (mem_pull.2 ((hW b y).2 hb))).trans
          (g₂ y a b ((hW a y).2 ha) ((hW b y).2 hb))) }

theorem isPullback_whiskerLeft_left {S : Scheme.{0}} (A : Over S) {T T' : Over S} (j : T' ⟶ T) :
    IsPullback (A ◁ j).left (snd A T').left (snd A T).left j.left := by
  have P : IsPullback (A ◁ j) (snd A T') (snd A T) j := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.fst ≫ fst A T) s.snd) ?_ ?_ ?_⟩⟩
    · intro s
      ext <;> simp [s.condition]
    · intro s
      simp
    · intro s m h₁ h₂
      ext <;> simp [← h₁, ← h₂]
  exact P.map (Over.forget S)

theorem exists_pic_extend_of_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → IsClosedImmersion j₂.left → Surjective j₂.left → Surjective k₂.left → ∀ c₂ : Pic (A ⊗ T₂).left, GlobalTheory.CechPic.pull (A ◁ k₂).left c₂ = 0 → ∃ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (A ◁ j₁).left c = 0 ∧ GlobalTheory.CechPic.pull (A ◁ j₂).left c = c₂ := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ hM hj hj' hk' c₂ hc
  have hk := hM.closed
  haveI : IsClosedImmersion (A ◁ j₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A j₂).flip hj
  haveI : Surjective (A ◁ j₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A j₂).flip hj'
  haveI : IsClosedImmersion (A ◁ k₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A k₂).flip hk
  haveI : Surjective (A ◁ k₂).left :=
    MorphismProperty.of_isPullback (isPullback_whiskerLeft_left A k₂).flip hk'
  have w₀ : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext hM.w
  have w : (A ◁ k₁).left ≫ (A ◁ j₁).left = (A ◁ k₂).left ≫ (A ◁ j₂).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, w₀]
  obtain ⟨D, hD, rfl, h1⟩ := GlobalTheory.T.exists_cechCocycle_one_on_thickening _ _ (A ◁ k₂).left c₂ hc
  have H := GlobalTheory.T.sections_flat_baseChange_affineMilnorSquare_open S A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ hM
  generalize (A ◁ j₁).left = p₁ at *
  generalize (A ◁ j₂).left = p₂ at *
  generalize (A ◁ k₁).left = q₁ at *
  generalize (A ◁ k₂).left = q₂ at *
  have inj : ∀ (W : (A ⊗ T).left.Opens) (a b : Γ((A ⊗ T).left, W)ˣ), pullU p₁ W a = pullU p₁ W b →
      pullU p₂ W a = pullU p₂ W b → a = b := fun W a b h₁ h₂ =>
    Units.ext ((H W).1 _ _ (congrArg Units.val h₁) (congrArg Units.val h₂))
  refine exists_pic_of_glue_units p₁ p₂ D hD inj fun W a b h => ?_
  have e : q₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W) = q₂ ⁻¹ᵁ (p₂ ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  have lift : ∀ u : Γ((A ⊗ T₂).left, p₂ ⁻¹ᵁ W)ˣ, pullU q₂ _ u = 1 →
      ∃ s : Γ((A ⊗ T).left, W), p₁.app W s = 1 ∧ p₂.app W s = u.val := fun u hu =>
    (H W).2 _ e.ge le_rfl e.le 1 u.val (by
      rw [map_one, Scheme.Hom.appLE_eq_app]
      exact (congrArg Units.val hu).symm)
  have hu : pullU q₂ _ (res h (D.g a b)) = 1 := unit_ext fun y hy => by
    rw [gm_pull (𝟙 _) q₂ y _ hy, gm_res (𝟙 _ ≫ q₂) y h hy, ← gm_pull (𝟙 _) q₂ y _ (h hy), h1, map_one, map_one]
  obtain ⟨s, hs₁, hs₂⟩ := lift _ hu
  obtain ⟨t, ht₁, ht₂⟩ := lift (res h (D.g a b))⁻¹ (by rw [map_inv, hu, inv_one])
  have st : s * t = 1 := (H W).1 _ _ (by rw [map_mul, hs₁, ht₁, map_one, _root_.mul_one])
    (by rw [map_mul, hs₂, ht₂, map_one, Units.mul_inv])
  exact ⟨⟨s, t, st, (mul_comm _ _).trans st⟩, Units.ext hs₁, Units.ext hs₂⟩

end GlobalTheory.DualOpen
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

noncomputable section

namespace GlobalTheory.SqConj

lemma wp_eq_of_sub_mem (L : PeriodPair) {z w : ℂ} (h : z - w ∈ L.lattice) :
    L.weierstrassP z = L.weierstrassP w := by
  have := L.weierstrassP_add_coe w ⟨z - w, h⟩
  simpa using this

lemma dwp_eq_of_sub_mem (L : PeriodPair) {z w : ℂ} (h : z - w ∈ L.lattice) :
    L.derivWeierstrassP z = L.derivWeierstrassP w := by
  have := L.derivWeierstrassP_add_coe w ⟨z - w, h⟩
  simpa using this

theorem sqProd_conj : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → (σ (sqProd p L t) = sqProd p L t ∧ ∃ e : Sq p ≃ Sq p, ∀ k, GlobalTheory.ConjPoint.IsConj L L σ (sqPt p t k) (sqPt p t (e k))) ∨ σ (sqProd p L t) = -sqProd p L t := by
  intro p F L t hp hp4 hp3 hD σ hσ
  obtain ⟨c, hpc, hc⟩ := GlobalTheory.T.exists_conj_kernel_mul' p F L t hp hp4 hp3 hD σ hσ
  obtain ⟨e, ε, hε, he⟩ := GlobalTheory.T.nonzeroSquaresModPrime_mul_perm_up_to_sign p c hp hp4 hpc
  have hker := (GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp hp4 hp3 hD).1
  obtain ⟨hne, -⟩ := GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp hp4 hp3 hD
  obtain ⟨-, hodd⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp hp4
  have hmem : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) - (ε : ℂ) * sqPt p t (e k) ∈ L.lattice := by
    intro k
    have := (hker _).2 (he k)
    convert this using 1
    simp only [sqPt]
    push_cast
    ring
  have hconj : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) ∉ L.lattice ∧
      L.weierstrassP (((k.1 : ℕ) : ℂ) * ((c : ℂ) * t)) = σ (L.weierstrassP (sqPt p t k)) ∧
      L.derivWeierstrassP (((k.1 : ℕ) : ℂ) * ((c : ℂ) * t)) = σ (L.derivWeierstrassP (sqPt p t k)) := by
    intro k
    rcases hc k.1 with h | h
    · exact absurd h.1 (hne k).1
    · exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  have hσprod : σ (sqProd p L t) = ∏ k : Sq p, L.derivWeierstrassP (((k.1 : ℕ) : ℂ) * ((c : ℂ) * t)) := by
    simp only [sqProd, map_prod]
    exact Finset.prod_congr rfl fun k _ => (hconj k).2.2.symm
  rcases hε with rfl | rfl
  · left
    have hm : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) - sqPt p t (e k) ∈ L.lattice := by
      intro k; simpa using hmem k
    refine ⟨?_, e, fun k => ?_⟩
    · rw [hσprod]
      simp only [dwp_eq_of_sub_mem L (hm _)]
      exact Equiv.prod_comp e (fun k => L.derivWeierstrassP (sqPt p t k))
    · right
      refine ⟨(hne k).1, (hne (e k)).1, ?_, ?_⟩
      · rw [← wp_eq_of_sub_mem L (hm k)]; exact (hconj k).2.1
      · rw [← dwp_eq_of_sub_mem L (hm k)]; exact (hconj k).2.2
  · right
    have hm : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) - (-sqPt p t (e k)) ∈ L.lattice := by
      intro k; simpa using hmem k
    rw [hσprod]
    simp only [dwp_eq_of_sub_mem L (hm _), PeriodPair.derivWeierstrassP_neg]
    rw [Finset.prod_neg, Equiv.prod_comp e (fun k => L.derivWeierstrassP (sqPt p t k)),
      Finset.card_univ, hodd.neg_one_pow, sqProd]
    ring

end GlobalTheory.SqConj
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

open TopologicalSpace

theorem exists_units_of_pull_eq_zero {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    (h : CechPic.pull f (cls L hL) = 0) : ∃ b : ∀ i, Γ(Y, f ⁻¹ᵁ L.U i)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : L.ι), f (r z) ∈ L.U i → f (r z) ∈ L.U j →
        gm r z _ (b i) = gm (r ≫ f) z _ (L.g i j) * gm r z _ (b j) := by
  rw [← cls_pull hL f (pull_isLB hL f)] at h
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 h
  have le : ∀ i, f ⁻¹ᵁ L.U i ≤ (L.pull f).U (fun _ ↦ i) := fun i y hy ↦ mem_pull.2 hy
  refine ⟨fun i ↦ res (le i) (t.s fun _ ↦ i), fun Z r z i j hi hj ↦ ?_⟩
  have mi : r z ∈ (L.pull f).U (fun _ ↦ i) := mem_pull.2 hi
  have mj : r z ∈ (L.pull f).U (fun _ ↦ j) := mem_pull.2 hj
  have hm : r z ∈ (L.pull f).U (fun _ ↦ i) ⊓ (L.pull f).U (fun _ ↦ j) := ⟨mi, mj⟩
  have e := congrArg (gm r z _) (ht (fun _ ↦ i) (fun _ ↦ j))
  rw [map_mul, gm_res r z _ hm, gm_res r z _ hm, gm_pull_g L f r z _ _ mi mj] at e
  rw [gm_res r z (le i) hi, gm_res r z (le j) hj]
  exact e

theorem eq_zero_of_square {X X₁ X₂ X₀ : Scheme.{0}} (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (g₁ : X₀ ⟶ X₁) (g₂ : X₀ ⟶ X₂)
    (w : g₁ ≫ f₁ = g₂ ≫ f₂)
    (inj : ∀ (W : X.Opens) (a b : Γ(X, W)), f₁.app W a = f₁.app W b → f₂.app W a = f₂.app W b → a = b)
    (ex : ∀ (W : X.Opens) (h₂ : g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W)) (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W))
      (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)), g₁.appLE _ _ le_rfl a₁ = g₂.appLE _ _ h₂ a₂ →
        ∃ a : Γ(X, W), f₁.app W a = a₁ ∧ f₂.app W a = a₂)
    (lift : Function.Surjective (Units.map g₂.appTop.hom.toMonoidHom))
    (c : Pic X) (h₁ : CechPic.pull f₁ c = 0) (h₂ : CechPic.pull f₂ c = 0) : c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨b₁, hb₁⟩ := exists_units_of_pull_eq_zero hL f₁ h₁
  obtain ⟨b₂, hb₂⟩ := exists_units_of_pull_eq_zero hL f₂ h₂
  have le : ∀ W : X.Opens, g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ W) ≤ g₂ ⁻¹ᵁ (f₂ ⁻¹ᵁ W) := fun W ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  have injU : ∀ (W : X.Opens) (a b : Γ(X, W)ˣ), pullU f₁ W a = pullU f₁ W b → pullU f₂ W a = pullU f₂ W b → a = b :=
    fun W a b e₁ e₂ ↦ Units.ext (inj W _ _ (congrArg Units.val e₁) (congrArg Units.val e₂))
  have exU : ∀ (W : X.Opens) (a₁ : Γ(X₁, f₁ ⁻¹ᵁ W)ˣ) (a₂ : Γ(X₂, f₂ ⁻¹ᵁ W)ˣ),
      res le_rfl (pullU g₁ _ a₁) = res (le W) (pullU g₂ _ a₂) →
        ∃ a : Γ(X, W)ˣ, pullU f₁ W a = a₁ ∧ pullU f₂ W a = a₂ := fun W a₁ a₂ e ↦ by
    have e' : res le_rfl (pullU g₁ _ a₁⁻¹) = res (le W) (pullU g₂ _ a₂⁻¹) := by
      rw [map_inv, map_inv, map_inv, map_inv, e]
    obtain ⟨a, p₁, p₂⟩ := ex W (le W) a₁.val a₂.val (congrArg Units.val e)
    obtain ⟨a', q₁, q₂⟩ := ex W (le W) (a₁⁻¹).val (a₂⁻¹).val (congrArg Units.val e')
    have k : a * a' = 1 := inj W _ _ (by rw [map_mul, map_one, p₁, q₁, Units.mul_inv])
      (by rw [map_mul, map_one, p₂, q₂, Units.mul_inv])
    exact ⟨⟨a, a', k, (mul_comm _ _).trans k⟩, Units.ext p₁, Units.ext p₂⟩
  have key : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * (a * y)⁻¹ = x * y⁻¹ := fun a x y ↦ by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  let V : L.ι → X₀.Opens := fun i ↦ g₁ ⁻¹ᵁ (f₁ ⁻¹ᵁ L.U i)
  let q : ∀ i, Γ(X₀, V i)ˣ := fun i ↦ pullU g₁ _ (b₁ i) * (res (le _) (pullU g₂ _ (b₂ i)))⁻¹
  have gq : ∀ i x, x ∈ V i → gm (𝟙 X₀) x (V i) (q i) = gm g₁ x _ (b₁ i) * (gm g₂ x _ (b₂ i))⁻¹ := fun i x hx ↦ by
    have e₁ := gm_pull (𝟙 X₀) g₁ x _ hx (b₁ i)
    have e₂ := (gm_res (𝟙 X₀) x (le (L.U i)) hx _).trans (gm_pull (𝟙 X₀) g₂ x _ (le _ hx) (b₂ i))
    rw [Category.id_comp] at e₁ e₂
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) e₁ ((map_inv _ _).trans (congrArg (·⁻¹) e₂)))
  obtain ⟨F, hF⟩ := glue_unit ⊤ V (fun _ ↦ le_top) (fun x _ ↦ by
      obtain ⟨i, hi⟩ := exists_chart hL (f₁ (g₁ x))
      exact Opens.mem_iSup.2 ⟨i, hi⟩) q (fun i j x hx ↦ by
      rw [gq i x hx.1, gq j x hx.2, hb₁ _ g₁ x i j hx.1 hx.2, hb₂ _ g₂ x i j (le _ hx.1) (le _ hx.2), w, key])
  obtain ⟨u, hu⟩ := lift F
  have hu' : pullU g₂ ⊤ u = F := hu
  have loc : ∀ i, ∃ s : Γ(X, L.U i)ˣ, pullU f₁ _ s = b₁ i ∧ pullU f₂ _ s = b₂ i * res le_top u := fun i ↦
    exU _ _ _ (unit_ext fun x hx ↦ by
      have e := congrArg (gm (𝟙 X₀) x (V i)) (hF i)
      rw [gm_res (𝟙 X₀) x _ hx, gq i x hx, ← hu'] at e
      have e₀ := gm_pull (𝟙 X₀) g₂ x ⊤ trivial u
      have e₁ := gm_pull (𝟙 X₀) g₁ x _ hx (b₁ i)
      have e₂ := gm_pull (𝟙 X₀) g₂ x _ (le _ hx) (b₂ i * res le_top u)
      rw [Category.id_comp] at e₀ e₁ e₂
      rw [gm_res (𝟙 X₀) x _ hx, gm_res (𝟙 X₀) x _ hx, e₁, e₂, map_mul, gm_res g₂ x _ (le _ hx), ← e₀]
      exact (mul_inv_eq_iff_eq_mul.1 e.symm).trans (mul_comm _ _))
  choose s hs₁ hs₂ using loc
  have gp : ∀ {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (W : X.Opens) (a : Γ(X, W)ˣ), f y ∈ W →
      gm (𝟙 Y) y (f ⁻¹ᵁ W) (pullU f W a) = gm f y W a := fun f y W a hy ↦
    (gm_pull (𝟙 _) f y W hy a).trans (by rw [Category.id_comp])
  refine (cls_eq_zero_iff hL).2 ⟨⟨s⟩, fun i j ↦ injU _ _ _ (unit_ext fun y hy ↦ ?_) (unit_ext fun y hy ↦ ?_)⟩
  · have e := hb₁ _ (𝟙 _) y i j hy.1 hy.2
    rw [Category.id_comp, ← hs₁, ← hs₁, gp f₁ y _ _ hy.1, gp f₁ y _ _ hy.2] at e
    rw [gp f₁ y _ _ hy, gp f₁ y _ _ hy, map_mul, gm_res f₁ y _ hy, gm_res f₁ y _ hy]
    exact e
  · have e := hb₂ _ (𝟙 _) y i j hy.1 hy.2
    rw [Category.id_comp] at e
    have k : ∀ i, f₂ y ∈ L.U i → gm f₂ y _ (s i) = gm (𝟙 _) y _ (b₂ i) * gm (𝟙 _) y ⊤ u := fun i hi ↦ by
      rw [← gp f₂ y _ _ hi, hs₂, map_mul, gm_res (𝟙 _) y _ hi]
    rw [gp f₂ y _ _ hy, gp f₂ y _ _ hy, map_mul, gm_res f₂ y _ hy, gm_res f₂ y _ hy]
    exact (k i hy.1).trans (by rw [e, k j hy.2, _root_.mul_assoc])

theorem pic_eq_zero_of_milnor : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T)
    (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left →
    Function.Surjective (Units.map (A ◁ k₂).left.appTop.hom.toMonoidHom) →
    ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (A ◁ j₁).left c = 0 → GlobalTheory.CechPic.pull (A ◁ j₂).left c = 0 → c = 0 := by
  intro S A T T₁ T₂ T₀ _ j₁ j₂ k₁ k₂ h hs
  have H := GlobalTheory.T.sections_flat_baseChange_affineMilnorSquare_open S A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ h
  have w : k₁ ≫ j₁ = k₂ ≫ j₂ := Over.OverMorphism.ext h.w
  refine eq_zero_of_square _ _ (A ◁ k₁).left (A ◁ k₂).left ?_ (fun W ↦ (H W).1)
    (fun W h₂ ↦ (H W).2 _ le_rfl h₂ le_rfl) hs
  rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, w]

end GlobalTheory.DualOpen
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mulStable_intCast_add_sub (L : PeriodPair) (s : ℂ) (a : ℤ) (h : MulStable L s) :
    MulStable L (a + s) ∧ MulStable L (a - s) := by
  have ha : ∀ ω ∈ L.lattice, (a : ℂ) * ω ∈ L.lattice := fun ω hω => by
    have := L.lattice.smul_mem a hω
    rwa [zsmul_eq_mul] at this
  refine ⟨fun ω hω => ?_, fun ω hω => ?_⟩
  · rw [add_mul]; exact add_mem (ha ω hω) (h ω hω)
  · rw [sub_mul]; exact sub_mem (ha ω hω) (h ω hω)

theorem normSq_natCast_add_sub_sqrtNegNat (p a : ℕ) :
    Complex.normSq (((a : ℤ) : ℂ) + sqrtNegNat p) = ((a ^ 2 + p : ℕ) : ℝ) ∧
      Complex.normSq (((a : ℤ) : ℂ) - sqrtNegNat p) = ((a ^ 2 + p : ℕ) : ℝ) := by
  have h : √(p : ℝ) * √(p : ℝ) = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  constructor <;> simp [sqrtNegNat, Complex.normSq_apply, h, sq]

theorem exists_stable_family_ker : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ, ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (T : ι → ℂ), Odd N ∧ N % 3 = 2 ∧ V.valuation (N : ℂ) = 1 ∧ Fintype.card ι = 2 * (N - 1) ∧ Stable L F T ∧ ∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice := by
  intro p F L t hp _ h3 hD V
  obtain ⟨a, N, hN, hodd, hmod, hv⟩ := GlobalTheory.T.exists_sq_add_prime_odd_mod_three_valuation_one p V hp h3
  obtain ⟨hs, hs'⟩ := mulStable_intCast_add_sub L (sqrtNegNat p) (a : ℤ) hD.mul
  obtain ⟨hn, hn'⟩ := normSq_natCast_add_sub_sqrtNegNat p a
  rw [← hN] at hn hn'
  have hN0 : (N : ℝ) ≠ 0 := by
    have : N ≠ 0 := by omega
    exact_mod_cast this
  have h0 : ((a : ℤ) : ℂ) + sqrtNegNat p ≠ 0 := fun h => hN0 (by rw [← hn, h, map_zero])
  have h0' : ((a : ℤ) : ℂ) - sqrtNegNat p ≠ 0 := fun h => hN0 (by rw [← hn', h, map_zero])
  obtain ⟨S, hS⟩ := kerRepsExist L _ h0 hs
  obtain ⟨S', hS'⟩ := kerRepsExist L _ h0' hs'
  have hc := kerRepsCard L _ S h0 hs hS
  have hc' := kerRepsCard L _ S' h0' hs' hS'
  rw [hn] at hc
  rw [hn'] at hc'
  have hc1 : S.card + 1 = N := by exact_mod_cast hc
  have hc1' : S'.card + 1 = N := by exact_mod_cast hc'
  have hfac : (N : ℂ) = (((a : ℤ) : ℂ) - sqrtNegNat p) * (((a : ℤ) : ℂ) + sqrtNegNat p) := by
    have := sqrtNegNat_sq p
    rw [hN]; push_cast
    linear_combination this
  refine ⟨N, S ⊕ S', inferInstance, Sum.elim (fun t : S => (t : ℂ)) (fun t : S' => (t : ℂ)), hodd, hmod, hv,
    ?_, GlobalTheory.T.stable_sum_elim_of_isKerReps_add_sub_sqrtNegNat p F L a S S' hD.g₂_mem hD.g₃_mem hD.mul hS hS', ?_⟩
  · rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]; omega
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · refine ⟨(hS.1 x hx).2, ?_⟩
      show (N : ℂ) * x ∈ _
      rw [hfac, mul_assoc]
      exact hs' _ (hS.1 x hx).1
    · refine ⟨(hS'.1 x hx).2, ?_⟩
      show (N : ℂ) * x ∈ _
      rw [hfac, mul_comm (_ - _), mul_assoc]
      exact hs _ (hS'.1 x hx).1

end GlobalTheory.CMModel
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction : ∀ (K : Type) [Field K] (C : Scheme.{0}) [IsIntegral C] (x : Sp K ⟶ C), IsGen x → ∀ V : C.Opens, (V : Set C).Nonempty → ∃ h : ⊤ ≤ x ⁻¹ᵁ V, Function.Injective (evAt x h) ∧ (IsAffineOpen V → ∀ z : K, ∃ a b : Γ(C, V), b ≠ 0 ∧ z * evAt x h b = evAt x h a) := by
  first | exact @GlobalTheory.Nef.isGen_evAt_frac | exact GlobalTheory.Nef.isGen_evAt_frac | (intros; apply GlobalTheory.Nef.isGen_evAt_frac <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk : (∀ (R R' : Type) [CommRing R] [CommRing R'] (X : Scheme.{0}) (φ : R →+* R') (b : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ b) ⁻¹ᵁ U) (f : Γ(X, U)), evAt (spMap φ ≫ b) h' f = φ (evAt b h f)) ∧ (∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (b : Sp R ⟶ X) (g : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (b ≫ g) ⁻¹ᵁ V) (e : U ≤ g ⁻¹ᵁ V) (f : Γ(Y, V)), evAt (b ≫ g) h' f = evAt b h (g.appLE V U e f)) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U U' : X.Opens) (e : U' ≤ U) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U') (f : Γ(X, U)), evAt b h' (X.presheaf.map (homOfLE e).op f) = evAt b h f) ∧ (∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U : X.Opens), ⊤ ≤ b ⁻¹ᵁ U ↔ b (IsLocalRing.closedPoint R) ∈ U) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b b' : Sp R ⟶ X) (U : X.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U), evAt b h = evAt b' h' → b = b') ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ φ : Γ(X, U) →+* R, ∃ (b : Sp R ⟶ X) (h : ⊤ ≤ b ⁻¹ᵁ U), evAt b h = φ) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X) (φ : X.presheaf.stalk p →+* R) (U : X.Opens) (hp : p ∈ U), ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) ⁻¹ᵁ U, ∀ f, evAt (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) h f = φ (X.presheaf.germ U p hp f)) := by
  first | exact @GlobalTheory.Nef.evAt_calculus | exact GlobalTheory.Nef.evAt_calculus | (intros; apply GlobalTheory.Nef.evAt_calculus <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ p : Place k E, ∃! b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x := by
  first | exact @GlobalTheory.Nef.existsUnique_centre | exact GlobalTheory.Nef.existsUnique_centre | (intros; apply GlobalTheory.Nef.existsUnique_centre <;> assumption)
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.dualWeylTensorEvaluation_translate_kronecker : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K S : Type) [Field K] [CharZero K] [CommRing S] (φ : K →+* S) (x : TIdx la → K) (g : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), tval la (fun I => φ (x I)) (fun t => (g t).map φ * y t) = tval la (fun I => φ (((kron fun t => rhoMat (la t) (g t)) *ᵥ x) I)) y := by
  first | exact @GlobalTheory.DefPt.tval_translate | exact GlobalTheory.DefPt.tval_translate | (intros; apply GlobalTheory.DefPt.tval_translate <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.exists_groupSchemeUnitStalkData : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ s : S, ∃ π ε m, StalkData G s π ε m ∧ ε.comp π = RingHom.id _ ∧ m.comp π = π ∧ ε.comp m = ε := by
  first | exact @GlobalTheory.Nef.stalkData_exists | exact GlobalTheory.Nef.stalkData_exists | (intros; apply GlobalTheory.Nef.stalkData_exists <;> assumption)
end
