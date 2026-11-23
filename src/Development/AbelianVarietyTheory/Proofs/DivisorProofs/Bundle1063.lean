module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyTrivialOfIsoPull
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle376
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle104
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Valuation.LocalSubring
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

@[expose] public section

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem modelAt_shortTwist_four_mul_add_one : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ D : ℂ) (k : ℤ), a₄ ∈ F → a₆ ∈ F → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D → ModelAt V F (shortTwist (4 * (k : ℂ) + 1) a₄ a₆) ((4 * (k : ℂ) + 1) ^ 6 * D) := by
  intro V F a₄ a₆ D k _ _ h
  obtain ⟨C, hu, hr, hs, ht, ⟨h1, h2, h3, h4, h6⟩, hΔ⟩ := h
  set d : ℂ := 4 * (k : ℂ) + 1 with hd
  have hkV : (k : ℂ) ∈ V := intCast_mem V k
  have hdV : d ∈ V := add_mem (mul_mem (by exact_mod_cast intCast_mem V 4 : (4 : ℂ) ∈ V) hkV) (one_mem V)
  have hkF : (k : ℂ) ∈ F := by simpa using IntermediateField.intCast_mem F k
  have hdF : d ∈ F := F.add_mem (F.mul_mem (by simpa using IntermediateField.intCast_mem F 4) hkF) F.one_mem
  let W₀ : WeierstrassCurve ℂ := ⟨0, 0, 0, a₄, a₆⟩
  let C' : VariableChange ℂ := ⟨C.u, d * C.r, C.s, d * C.t⟩
  refine ⟨C', hu, F.mul_mem hdF hr, hs, F.mul_mem hdF ht, ?_, ?_⟩
  · have e1 : (C' • shortTwist d a₄ a₆).a₁ = (C • W₀).a₁ := by
      simp only [variableChange_a₁, shortTwist, W₀, C']
    have e2 : (C' • shortTwist d a₄ a₆).a₂ = d * (C • W₀).a₂ + k * (C • W₀).a₁ ^ 2 := by
      simp only [variableChange_a₁, variableChange_a₂, shortTwist, W₀, C', hd]; ring
    have e3 : (C' • shortTwist d a₄ a₆).a₃ = d * (C • W₀).a₃ := by
      simp only [variableChange_a₃, shortTwist, W₀, C']; ring
    have e4 : (C' • shortTwist d a₄ a₆).a₄ = d ^ 2 * (C • W₀).a₄ + 2 * k * d * (C • W₀).a₁ * (C • W₀).a₃ := by
      simp only [variableChange_a₁, variableChange_a₃, variableChange_a₄, shortTwist, W₀, C', hd]; ring
    have e6 : (C' • shortTwist d a₄ a₆).a₆ = d ^ 3 * (C • W₀).a₆ + k * d ^ 2 * (C • W₀).a₃ ^ 2 := by
      simp only [variableChange_a₃, variableChange_a₆, shortTwist, W₀, C', hd]; ring
    have h2V : (2 : ℂ) ∈ V := by simpa using intCast_mem V 2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e1]; exact h1
    · rw [e2]; exact add_mem (mul_mem hdV h2) (mul_mem hkV (pow_mem h1 2))
    · rw [e3]; exact mul_mem hdV h3
    · rw [e4]; exact add_mem (mul_mem (pow_mem hdV 2) h4)
        (mul_mem (mul_mem (mul_mem (mul_mem h2V hkV) hdV) h1) h3)
    · rw [e6]; exact add_mem (mul_mem (pow_mem hdV 3) h6)
        (mul_mem (mul_mem hkV (pow_mem hdV 2)) (pow_mem h3 2))
  · have eΔ : (C' • shortTwist d a₄ a₆).Δ = d ^ 6 * (C • W₀).Δ := by
      rw [variableChange_Δ, variableChange_Δ]
      simp only [C', W₀, shortTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [eΔ, map_mul, map_mul, hΔ]

end GlobalTheory.CMModel
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem bijective_app_iso_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) (V : Z.Opens)
    (h : Function.Bijective (g.app V).hom) : Function.Bijective ((f ≫ g).app V).hom := by
  have : IsIso (g.app V) := (ConcreteCategory.isIso_iff_bijective _).2 h
  have : IsIso (f.app (g ⁻¹ᵁ V)) := inferInstance
  have : IsIso ((f ≫ g).app V) := by
    rw [Scheme.Hom.comp_app]; exact IsIso.comp_isIso' ‹_› ‹_›
  exact ConcreteCategory.bijective_of_isIso _

theorem fnBij_snd : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → FnBij (snd A T).left := by
  intro S A T _ hA V
  have e : (snd A T).left = (β_ A T).hom.left ≫ (fst T A).left := by
    rw [← Over.comp_left, braiding_hom_fst]
  have : IsIso (β_ A T).hom.left := inferInstanceAs (IsIso ((Over.forget S).map (β_ A T).hom))
  rw [e]
  exact bijective_app_iso_comp _ _ V
    (GlobalTheory.CubeLawCompare.bijective_app_fst GlobalTheory.SemiRigid.globalFns hA T V)

end GlobalTheory.PicGlue
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem stable_sym_mem (F : IntermediateField ℚ ℂ) (L : PeriodPair) (ι : Type) [Fintype ι] (T : ι → ℂ) :
    L.g₂ ∈ F → L.g₃ ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice) →
    (∑ i, L.weierstrassP (T i)) ∈ F ∧ (∑ i, L.derivWeierstrassP (T i) / 2) ∈ F ∧
    (∑ i, (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2))) ∈ F ∧
    ((∀ i, 2 * T i ∉ L.lattice) → (∏ i, (L.weierstrassP (T i) - L.weierstrassP (2 * T i))) ∈ F) := by
  intro h₂ h₃ hS hT
  have key : ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ e : ι ≃ ι,
      (∀ i, σ (L.weierstrassP (T i)) = L.weierstrassP (T (e i))) ∧
      (∀ i, σ (L.derivWeierstrassP (T i)) = L.derivWeierstrassP (T (e i))) ∧
      ((∀ i, 2 * T i ∉ L.lattice) → ∀ i, σ (L.weierstrassP (2 * T i)) = L.weierstrassP (2 * T (e i))) ∧
      σ L.g₂ = L.g₂ := by
    intro σ hσ
    obtain ⟨e, he⟩ := hS σ hσ
    have g₂e : L.g₂ = σ L.g₂ := (hσ _ h₂).symm
    have g₃e : L.g₃ = σ L.g₃ := (hσ _ h₃).symm
    refine ⟨e, fun i ↦ ?_, fun i ↦ ?_, fun h2 i ↦ ?_, hσ _ h₂⟩
    · exact (((he i).resolve_left fun h ↦ hT i h.1).2.2.1).symm
    · exact (((he i).resolve_left fun h ↦ hT i h.1).2.2.2).symm
    · have := GlobalTheory.ConjPoint.IsConj.add g₂e g₃e (he i) (he i)
      rw [← two_mul, ← two_mul] at this
      exact ((this.resolve_left fun h ↦ h2 i h.1).2.2.1).symm
  refine ⟨GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_, GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_,
    GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_, fun h2 ↦ GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_⟩
  · obtain ⟨e, a, -, -, -⟩ := key σ hσ

    rw [map_sum]; simp only [a]; exact Equiv.sum_comp e (fun i ↦ L.weierstrassP (T i))
  · obtain ⟨e, -, b, -, -⟩ := key σ hσ

    rw [map_sum]; simp only [map_div₀, map_ofNat, b]
    exact Equiv.sum_comp e (fun i ↦ L.derivWeierstrassP (T i) / 2)
  · obtain ⟨e, a, b, -, g⟩ := key σ hσ

    rw [map_sum]
    simp only [map_div₀, map_add (f := _), map_mul, map_pow, map_neg, map_ofNat, a, b, g]
    exact Equiv.sum_comp e (fun i ↦ (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2)))
  · obtain ⟨e, a, -, c, -⟩ := key σ hσ
    rw [map_prod]; simp only [map_sub, a, c h2]
    exact Equiv.prod_comp e (fun i ↦ L.weierstrassP (T i) - L.weierstrassP (2 * T i))

end GlobalTheory.CMModel
end

section

open WeierstrassCurve

namespace GlobalTheory.CMModel

theorem exists_intV_variableChange (W : WeierstrassCurve ℂ) [W.IsElliptic] (V : ValuationSubring ℂ)
    (u : ℂˣ) (hj : W.j ∈ V) (hu : V.valuation (u : ℂ) ^ 12 = V.valuation W.Δ) :
    ∃ r s t : ℂ, IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • W) := by
  have : IsIntegrallyClosedIn V ℂ := (isIntegrallyClosed_iff_isIntegrallyClosedIn ℂ).1 inferInstance
  have ht : HasRationalTorsion W ℂ 12 := by
    intro x y h hn
    exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  obtain ⟨C, W₀, e, h₀⟩ := exists_integral_model V (L := ℂ) (W := W) ⟨⟨W.j, hj⟩, rfl⟩ ht
  have hΔ : ((C.u⁻¹ : ℂˣ) : ℂ) ^ 12 * W.Δ = 1 := by
    rw [← variableChange_Δ, e, WeierstrassCurve.baseChange, map_Δ, h₀, map_one]
  have hCu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have hu0 : (u : ℂ) ≠ 0 := u.ne_zero
  have hΔ' : W.Δ = (C.u : ℂ) ^ 12 := by
    rw [Units.val_inv_eq_inv_val] at hΔ
    field_simp at hΔ
    exact hΔ
  have hv : V.valuation (u : ℂ) = V.valuation (C.u : ℂ) := by
    rw [hΔ', map_pow] at hu
    exact (pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu
  have hw : (C.u : ℂ) / u ∈ V := by
    rw [← V.valuation_le_one_iff, map_div₀, hv, div_self]
    exact (map_ne_zero _).2 hCu
  have h1 : (C • W).a₁ ∈ V := by rw [e]; exact W₀.a₁.2
  have h2 : (C • W).a₂ ∈ V := by rw [e]; exact W₀.a₂.2
  have h3 : (C • W).a₃ ∈ V := by rw [e]; exact W₀.a₃.2
  have h4 : (C • W).a₄ ∈ V := by rw [e]; exact W₀.a₄.2
  have h6 : (C • W).a₆ ∈ V := by rw [e]; exact W₀.a₆.2
  refine ⟨C.r, C.s, C.t, ?_, ?_, ?_, ?_, ?_⟩
  · convert V.mul_mem _ _ hw h1 using 1
    simp only [variableChange_a₁, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 2) h2 using 1
    simp only [variableChange_a₂, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 3) h3 using 1
    simp only [variableChange_a₃, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 4) h4 using 1
    simp only [variableChange_a₄, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 6) h6 using 1
    simp only [variableChange_a₆, Units.val_inv_eq_inv_val]; field_simp

end GlobalTheory.CMModel
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mem_of_duplication_eq :
    ∀ (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) (x y δ : ℂ), IntV V W →
      W.toAffine.Equation x y → 2 * y + W.a₁ * x + W.a₃ ∈ V → δ ∈ V →
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ = (2 * y + W.a₁ * x + W.a₃) ^ 2 * (x + δ) →
      x ∈ V ∧ y ∈ V := by
  intro V W x y δ hW hE hl hδ h
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  have hr : ∀ z : ℂ, z ∈ V → z ∈ (algebraMap V ℂ).range := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  have hr' : ∀ z : ℂ, z ∈ (algebraMap V ℂ).range → z ∈ V := by
    rintro z ⟨w, rfl⟩; exact w.2
  have hb₄ : W.b₄ ∈ V := by
    rw [WeierstrassCurve.b₄]
    exact add_mem (mul_mem (ofNat_mem V 2) h₄) (mul_mem h₁ h₃)
  have hb₆ : W.b₆ ∈ V := by
    rw [WeierstrassCurve.b₆]
    exact add_mem (pow_mem h₃ 2) (mul_mem (ofNat_mem V 4) h₆)
  have hb₈ : W.b₈ ∈ V := by
    rw [WeierstrassCurve.b₈]
    refine sub_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
    · exact mul_mem (pow_mem h₁ 2) h₆
    · exact mul_mem (mul_mem (ofNat_mem V 4) h₂) h₆
    · exact mul_mem (mul_mem h₁ h₃) h₄
    · exact mul_mem h₂ (pow_mem h₃ 2)
    · exact pow_mem h₄ 2
  set l := 2 * y + W.a₁ * x + W.a₃ with hl_def
  have hx : x ∈ V := by
    refine hr' x (GlobalTheory.mem_range_of_quartic (A := V) (c₀ := -(W.b₈ + l ^ 2 * δ))
      (c₁ := -(2 * W.b₆ + l ^ 2)) (c₂ := -W.b₄) (c₃ := 0) (hr _ ?_) (hr _ ?_) (hr _ ?_) (hr _ ?_) ?_)
    · exact neg_mem (add_mem hb₈ (mul_mem (pow_mem hl 2) hδ))
    · exact neg_mem (add_mem (mul_mem (ofNat_mem V 2) hb₆) (pow_mem hl 2))
    · exact neg_mem hb₄
    · exact zero_mem V
    · linear_combination h
  refine ⟨hx, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  refine hr' y (GlobalTheory.mem_range_of_quartic (A := V) (c₀ := 0) (c₁ := 0)
    (c₂ := -(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) (c₃ := W.a₁ * x + W.a₃)
    (hr _ (zero_mem V)) (hr _ (zero_mem V)) (hr _ ?_) (hr _ ?_) ?_)
  · exact neg_mem (add_mem (add_mem (add_mem (pow_mem hx 3)
      (mul_mem h₂ (pow_mem hx 2))) (mul_mem h₄ hx)) h₆)
  · exact add_mem (mul_mem h₁ hx) h₃
  · linear_combination y ^ 2 * hE

end GlobalTheory.CMModel
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue.OpenExt

variable {X X' : Scheme.{0}} (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X')

theorem image_inf_le (a b : L.ι) : f ''ᵁ L.U a ⊓ f ''ᵁ L.U b ≤ f ''ᵁ (L.U a ⊓ L.U b) := fun x hx ↦ by
  obtain ⟨w, hw, rfl⟩ := hx.1
  exact f.apply_mem_image_iff.2 ⟨hw, f.apply_mem_image_iff.1 hx.2⟩

def extLB : LB X :=
  ⟨L.ι, fun a ↦ f ''ᵁ L.U a, fun a b ↦ res (image_inf_le f L a b) (GlobalTheory.GlueLineBundle.imU f _ (L.g a b))⟩

theorem gm_ext_g {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (a b : L.ι) (ha : r z ∈ L.U a) (hb : r z ∈ L.U b) :
    gm (r ≫ f) z ((extLB f L).U a ⊓ (extLB f L).U b) ((extLB f L).g a b) = gm r z (L.U a ⊓ L.U b) (L.g a b) := by
  have hm : (r ≫ f) z ∈ f ''ᵁ L.U a ⊓ f ''ᵁ L.U b := ⟨f.apply_mem_image_iff.2 ha, f.apply_mem_image_iff.2 hb⟩
  exact (gm_res (r ≫ f) z (image_inf_le f L a b) hm _).trans
    (GlobalTheory.GlueLineBundle.gm_imU f r z (L.U a ⊓ L.U b) ⟨ha, hb⟩ _)


variable {f} in
theorem gm_eq_map {Y : Scheme.{0}} (g : Y ⟶ X) (y : Y) (U : X.Opens) (h : g y ∈ U) (a : Γ(X, U)ˣ) :
    gm g y U a = Units.map (g.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (g y) U a) := by
  apply Units.ext
  rw [Units.coe_map, gm_val g y U h, GlobalTheory.GlueLineBundle.gm_id_val h]
  exact (Scheme.Hom.germ_stalkMap_apply g U y h a.val).symm

end GlobalTheory.PicGlue.OpenExt

namespace GlobalTheory.PicGlue.OpenExt

variable {X X' : Scheme.{0}} (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X')

theorem isOn_extLB (hL : L.IsLB) : IsOn f.opensRange (extLB f L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a x hx
    obtain ⟨w, -, rfl⟩ := hx
    exact ⟨w, rfl⟩
  · intro x hx
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨a, ha⟩ := exists_chart hL w
    exact ⟨a, f.apply_mem_image_iff.2 ha⟩
  · intro x a b c hxa hxb hxc
    obtain ⟨w, ha, rfl⟩ := hxa
    have hb : w ∈ L.U b := f.apply_mem_image_iff.1 hxb
    have hc : w ∈ L.U c := f.apply_mem_image_iff.1 hxc
    have e : ∀ (d d' : L.ι) (hd : w ∈ L.U d) (hd' : w ∈ L.U d'),
        Units.map (f.stalkMap w).hom.toMonoidHom (gm (𝟙 X) (f w) _ ((extLB f L).g d d')) =
          gm (𝟙 X') w (L.U d ⊓ L.U d') (L.g d d') := by
      intro d d' hd hd'
      rw [← gm_eq_map f w ((extLB f L).U d ⊓ (extLB f L).U d') ⟨f.apply_mem_image_iff.2 hd, f.apply_mem_image_iff.2 hd'⟩]
      have k := gm_ext_g f L (𝟙 X') w d d' hd hd'
      rwa [Category.id_comp] at k
    apply Units.map_injective (f := (f.stalkMap w).hom.toMonoidHom)
      (fun u v h ↦ (ConcreteCategory.bijective_of_isIso (f.stalkMap w)).1 h)
    refine (MonoidHom.map_mul _ _ _).trans ?_
    exact (congrArg₂ (· * ·) (e a b ha hb) (e b c hb hc)).trans
      ((gm_cocycle hL (𝟙 X') w ha hb hc).trans (e a c ha hc).symm)

end GlobalTheory.PicGlue.OpenExt


open GlobalTheory.PicGlue.OpenExt in
theorem GlobalTheory.PicGlue.exists_isOn_of_openImmersion : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X'),
    L.IsLB → ∃ L' : LB X, IsOn f.opensRange L' ∧ LBIso (L'.pull f) L := by
  intro X X' f _ L hL
  refine ⟨extLB f L, isOn_extLB f L hL, iso_of_chart hL ⟨fun J ↦ J PUnit.unit, ?_, ?_⟩⟩
  · intro J y hy
    exact f.apply_mem_image_iff.1 (mem_pull.1 hy)
  · intro y J J' hj hj'
    exact (gm_pull_g (extLB f L) f (𝟙 X') y J J' hj hj').trans
      (gm_ext_g f L (𝟙 X') y _ _ (f.apply_mem_image_iff.1 (mem_pull.1 hj)) (f.apply_mem_image_iff.1 (mem_pull.1 hj')))
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem gm_eq_map_stalk {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U h, Units.coe_map, gm_val _ (f y) U h, ← Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem isoOn_of_lbIso (X : Scheme.{0}) (W : X.Opens) (L M : LB X) (h : LBIso (L.pull W.ι) (M.pull W.ι)) :
    ∃ w : Cmp W L M, IsoOn W L M w := by
  obtain ⟨s, hs⟩ := h
  have hle : ∀ (a : L.ι) (b : M.ι), W ⊓ (L.U a ⊓ M.U b) ≤
      W.ι ''ᵁ ((M.pull W.ι).U (fun _ => b) ⊓ (L.pull W.ι).U (fun _ => a)) := by
    intro a b x hx
    obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx.1⟩, rfl⟩
    exact W.ι.apply_mem_image_iff.2 ⟨mem_pull.2 hx.2.2, mem_pull.2 hx.2.1⟩
  refine ⟨fun a b => (res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹, ?_⟩
  intro x hx a a' b b' ha ha' hb hb'
  obtain ⟨y, rfl⟩ : ∃ y : W.toScheme, W.ι y = x := ⟨⟨x, hx⟩, rfl⟩
  have E : ∀ (a : L.ι) (b : M.ι), W.ι y ∈ L.U a → W.ι y ∈ M.U b →
      gm W.ι y (W ⊓ (L.U a ⊓ M.U b))
        ((res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹) =
      (gm (𝟙 _) y _ (s.s (fun _ => b, fun _ => a)))⁻¹ := by
    intro a b ha hb
    have hm : W.ι y ∈ W ⊓ (L.U a ⊓ M.U b) := ⟨hx, ha, hb⟩
    have hv : (𝟙 W.toScheme) y ∈ (M.pull W.ι).U (fun _ => b) ⊓ (L.pull W.ι).U (fun _ => a) :=
      ⟨mem_pull.2 hb, mem_pull.2 ha⟩
    have e := GlobalTheory.GlueLineBundle.gm_imU W.ι (𝟙 _) y _ hv (s.s (fun _ => b, fun _ => a))
    rw [Category.id_comp] at e
    rw [map_inv, gm_res W.ι y (hle a b) hm, e]
    rfl
  have EL : ∀ (a a' : L.ι), W.ι y ∈ L.U a → W.ι y ∈ L.U a' →
      gm W.ι y (L.U a ⊓ L.U a') (L.g a a') = gm (𝟙 _) y _ ((L.pull W.ι).g (fun _ => a) (fun _ => a')) := by
    intro a a' ha ha'
    have e := gm_pull_g L W.ι (𝟙 _) y (fun _ => a) (fun _ => a') (mem_pull.2 ha) (mem_pull.2 ha')
    rw [Category.id_comp] at e
    exact e.symm
  have EM : ∀ (b b' : M.ι), W.ι y ∈ M.U b → W.ι y ∈ M.U b' →
      gm W.ι y (M.U b ⊓ M.U b') (M.g b b') = gm (𝟙 _) y _ ((M.pull W.ι).g (fun _ => b) (fun _ => b')) := by
    intro b b' hb hb'
    have e := gm_pull_g M W.ι (𝟙 _) y (fun _ => b) (fun _ => b') (mem_pull.2 hb) (mem_pull.2 hb')
    rw [Category.id_comp] at e
    exact e.symm
  have hp : y ∈ (LB.div (M.pull W.ι) (L.pull W.ι)).U (fun _ => b, fun _ => a) := ⟨mem_pull.2 hb, mem_pull.2 ha⟩
  have hq : y ∈ (LB.div (M.pull W.ι) (L.pull W.ι)).U (fun _ => b', fun _ => a') := ⟨mem_pull.2 hb', mem_pull.2 ha'⟩
  have G := (isGen_iff_germ s).1 hs y _ _ hp hq
  rw [gm_div' (M.pull W.ι) (L.pull W.ι) (𝟙 _) y _ _ hp hq] at G
  have alg : ∀ {Gp : Type} [CommGroup Gp] (S Mg large₂ S' : Gp), S = Mg * large₂⁻¹ * S' → S⁻¹ * Mg = large₂ * S'⁻¹ := by
    intro Gp _ S Mg large₂ S' e
    rw [e, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, _root_.mul_assoc, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
    exact _root_.mul_comm _ _
  have key : gm W.ι y (W ⊓ (L.U a ⊓ M.U b))
        ((res (hle a b) (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b, fun _ => a))))⁻¹) *
        gm W.ι y (M.U b ⊓ M.U b') (M.g b b') =
      gm W.ι y (L.U a ⊓ L.U a') (L.g a a') * gm W.ι y (W ⊓ (L.U a' ⊓ M.U b'))
        ((res (hle a' b') (GlobalTheory.GlueLineBundle.imU W.ι _ (s.s (fun _ => b', fun _ => a'))))⁻¹) := by
    rw [E a b ha hb, E a' b' ha' hb', EL a a' ha ha', EM b b' hb hb']
    exact alg _ _ _ _ G
  have hinj : Function.Injective (Units.map (W.ι.stalkMap y).hom.toMonoidHom) := fun u v e =>
    Units.ext ((ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1 (congrArg Units.val e))
  apply hinj
  rw [map_mul, map_mul, ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ W ⊓ (L.U a ⊓ M.U b) from ⟨hx, ha, hb⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ M.U b ⊓ M.U b' from ⟨hb, hb'⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ L.U a ⊓ L.U a' from ⟨ha, ha'⟩),
    ← gm_eq_map_stalk W.ι y _ (show W.ι y ∈ W ⊓ (L.U a' ⊓ M.U b') from ⟨hx, ha', hb'⟩)]
  exact key

end GlobalTheory.PicGlue
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PicGlue

theorem stalkMap_gm {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (u : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U u) = gm (f ≫ g) z U u := by
  by_cases h : g (f z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val g (f z) U h, gm_val (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).trans rfl
  · have h' : (f ≫ g) z ∉ U := h
    simp only [gm, dif_neg h, dif_neg h', MonoidHom.one_apply, map_one]

theorem rigOn_of_triv_open : ∀ (X Y : Scheme.{0}) (e : Y ⟶ X) (V : Y.Opens) (L : LB X),
    (∀ (a : L.ι) (y : Y), e y ∈ L.U a → y ∈ V) → Triv (L.pull (V.ι ≫ e)) → ∃ r : RigD e L, RigOn e L r := by
  intro X Y e V L hV ⟨t, ht⟩
  have hle : ∀ a : L.ι, e ⁻¹ᵁ L.U a ≤ V.ι ''ᵁ (L.pull (V.ι ≫ e)).U (fun _ => a) := by
    intro a y hy
    obtain ⟨v, rfl⟩ : y ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hV a y hy
    exact V.ι.apply_mem_image_iff.2 (mem_pull.2 hy)
  refine ⟨fun a => res (hle a) (GlobalTheory.GlueLineBundle.imU V.ι _ (t.s fun _ => a)), ?_⟩
  intro y a b ha hb
  obtain ⟨v, rfl⟩ : y ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hV a y ha
  have key : ∀ c : L.ι, e (V.ι v) ∈ L.U c →
      gm V.ι v (e ⁻¹ᵁ L.U c) (res (hle c) (GlobalTheory.GlueLineBundle.imU V.ι _ (t.s fun _ => c))) =
        gm (𝟙 V.toScheme) v _ (t.s fun _ => c) := by
    intro c hc
    have hm : (𝟙 V.toScheme) v ∈ (L.pull (V.ι ≫ e)).U (fun _ => c) := mem_pull.2 hc
    rw [gm_res V.ι v (hle c) (show V.ι v ∈ e ⁻¹ᵁ L.U c from hc)]
    have := GlobalTheory.GlueLineBundle.gm_imU V.ι (𝟙 V.toScheme) v _ hm (t.s fun _ => c)
    rwa [Category.id_comp] at this
  have hinj : Function.Injective (Units.map (V.ι.stalkMap v).hom.toMonoidHom) :=
    Units.map_injective (asIso (V.ι.stalkMap v)).commRingCatIsoToRingEquiv.injective
  apply hinj
  rw [map_mul, stalkMap_gm, stalkMap_gm, stalkMap_gm, Category.comp_id]
  beta_reduce
  rw [key a ha, key b hb,
    (isGen_iff_germ t).1 ht v (fun _ => a) (fun _ => b) (mem_pull.2 ha) (mem_pull.2 hb),
    gm_pull_g L (V.ι ≫ e) (𝟙 V.toScheme) v (fun _ => a) (fun _ => b) (mem_pull.2 ha) (mem_pull.2 hb),
    Category.id_comp]

end GlobalTheory.PicGlue
end
end
