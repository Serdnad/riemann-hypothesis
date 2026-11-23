module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem app_res {X Y : Scheme.{0}} (f : Y ⟶ X) {W W' : X.Opens} (h : W' ≤ W) (s : Γ(X, W)) :
    (f.app W').hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (Y.presheaf.map ((Opens.map f.base).map (homOfLE h)).op).hom ((f.app W).hom s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

theorem compat_res {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    {W W' : X.Opens} (h : W' ≤ W) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W))
    (hab : (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b) :
    (i'.appLE (p ⁻¹ᵁ W') (i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W')) inf_le_left).hom
        ((X'.presheaf.map ((Opens.map p.base).map (homOfLE h)).op).hom a) =
      (p'.appLE (i ⁻¹ᵁ W') (i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W')) inf_le_right).hom
        ((Z.presheaf.map ((Opens.map i.base).map (homOfLE h)).op).hom b) := by
  have hV : i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W') ≤ i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W) :=
    fun x hx => ⟨h hx.1, h hx.2⟩
  have := congrArg (Z'.presheaf.map (homOfLE hV).op).hom hab
  simp only [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] at this ⊢
  exact this

theorem unique_of_basis {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    (B : Set X.Opens) (hbasis : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W)
    (hB : ∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
      (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
        (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
      ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b)
    (W : X.Opens) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W))
    (hab : (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b)
    (s s' : Γ(X, W)) (hs : (p.app W).hom s = a ∧ (i.app W).hom s = b)
    (hs' : (p.app W).hom s' = a ∧ (i.app W).hom s' = b) : s = s' := by
  have hcover : W ≤ ⨆ j : {W' : X.Opens // W' ∈ B ∧ W' ≤ W}, j.1 := by
    intro x hx
    obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W x hx
    exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
  refine X.sheaf.eq_of_locally_eq' (fun j : {W' : X.Opens // W' ∈ B ∧ W' ≤ W} => j.1) W
    (fun j => homOfLE j.2.2) hcover s s' fun j => ?_
  have hc := compat_res p i i' p' j.2.2 a b hab
  refine (hB j.1 j.2.1 _ _ hc).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · exact (app_res p j.2.2 s).trans (congrArg _ hs.1)
  · exact (app_res i j.2.2 s).trans (congrArg _ hs.2)
  · exact (app_res p j.2.2 s').trans (congrArg _ hs'.1)
  · exact (app_res i j.2.2 s').trans (congrArg _ hs'.2)

theorem glues_of_basis : ∀ {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    (B : Set X.Opens), (∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W) →
    (∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
      (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
        (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
      ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b) → GlobalTheory.PinchLift.Glues p i i' p' := by
  intro X X' Z Z' p i i' p' B hbasis hB W a b hab
  let I := {W' : X.Opens // W' ∈ B ∧ W' ≤ W}
  have hcover : W ≤ ⨆ j : I, j.1 := by
    intro x hx
    obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W x hx
    exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
  choose t ht using fun j : I => (hB j.1 j.2.1 _ _ (compat_res p i i' p' j.2.2 a b hab)).exists
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun j : I => j.1) t := by
    intro j k
    have hjk : j.1 ⊓ k.1 ≤ W := inf_le_left.trans j.2.2
    refine unique_of_basis p i i' p' B hbasis hB (j.1 ⊓ k.1) _ _ (compat_res p i i' p' hjk a b hab) _ _
      ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · refine (app_res p inf_le_left (t j)).trans ?_
      rw [(ht j).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res i inf_le_left (t j)).trans ?_
      rw [(ht j).2, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res p inf_le_right (t k)).trans ?_
      rw [(ht k).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res i inf_le_right (t k)).trans ?_
      rw [(ht k).2, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun j : I => j.1) W (fun j => homOfLE j.2.2)
    hcover t hcompat
  have key : (p.app W).hom s = a ∧ (i.app W).hom s = b := by
    constructor
    · have hcov' : p ⁻¹ᵁ W ≤ ⨆ j : I, p ⁻¹ᵁ j.1 := by
        intro x hx
        obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W (p.base x) hx
        exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
      refine X'.sheaf.eq_of_locally_eq' (fun j : I => p ⁻¹ᵁ j.1) (p ⁻¹ᵁ W)
        (fun j => (Opens.map p.base).map (homOfLE j.2.2)) hcov' _ _ fun j => ?_
      refine (app_res p j.2.2 s).symm.trans ?_
      rw [show (X.presheaf.map (homOfLE j.2.2).op).hom s = t j from hs j]
      exact (ht j).1
    · have hcov' : i ⁻¹ᵁ W ≤ ⨆ j : I, i ⁻¹ᵁ j.1 := by
        intro x hx
        obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W (i.base x) hx
        exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
      refine Z.sheaf.eq_of_locally_eq' (fun j : I => i ⁻¹ᵁ j.1) (i ⁻¹ᵁ W)
        (fun j => (Opens.map i.base).map (homOfLE j.2.2)) hcov' _ _ fun j => ?_
      refine (app_res i j.2.2 s).symm.trans ?_
      rw [show (X.presheaf.map (homOfLE j.2.2).op).hom s = t j from hs j]
      exact (ht j).2
  exact ⟨s, key, fun s' hs' => unique_of_basis p i i' p' B hbasis hB W a b hab s' s hs' key⟩

end GlobalTheory.PinchLift
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder FourierTransform

namespace GlobalTheory.RealWeil

theorem pow_mul_norm_gau_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (m : ℕ) (v : V) :
    ‖v‖ ^ m * ‖gau v‖ ≤ m.factorial * Real.exp 1 := by
  rw [norm_gau]
  have hx0 : 0 ≤ ‖v‖ := norm_nonneg v
  have h1 : ‖v‖ ^ m ≤ m.factorial * Real.exp ‖v‖ := by
    have := Real.pow_div_factorial_le_exp _ hx0 m
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < m.factorial)] at this
    linarith [mul_comm (Real.exp ‖v‖) (m.factorial : ℝ)]
  have h2 : ‖v‖ + (-(π / 2) * ‖v‖ ^ 2) ≤ 1 := by
    nlinarith [Real.pi_gt_three, sq_nonneg ‖v‖, sq_nonneg (‖v‖ - 1 / 3)]
  calc ‖v‖ ^ m * Real.exp (-(π / 2) * ‖v‖ ^ 2)
      ≤ (m.factorial * Real.exp ‖v‖) * Real.exp (-(π / 2) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = m.factorial * Real.exp (‖v‖ + (-(π / 2) * ‖v‖ ^ 2)) := by rw [Real.exp_add]; ring
    _ ≤ m.factorial * Real.exp 1 := by gcongr

theorem gau_add {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (v t : V) :
    gau (v + t) = gau v * gau t * cexp (-(π : ℂ) * (⟪v, t⟫ : ℝ)) := by
  unfold gau
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h' : ((‖v + t‖ : ℝ) : ℂ) ^ 2 = ((‖v‖ ^ 2 + 2 * ⟪v, t⟫ + ‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← norm_add_sq_real v t]; push_cast; ring
  rw [h']
  push_cast
  ring

theorem contDiff_gau {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    ContDiff ℝ ∞ (gau : V → ℂ) := by
  have e : (gau : V → ℂ) = fun u => cexp (-(π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u
    simp only [gau]
    push_cast
    rfl
  rw [e]
  have hn : ContDiff ℝ ∞ (fun u : V => ‖u‖ ^ 2) := contDiff_norm_sq ℝ
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hn))

theorem exists_shift_form {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (J : V ≃ₗᵢ[ℝ] V) (v : V) :
    ∃ l : V →L[ℝ] ℂ, ‖l‖ ≤ 2 * π * ‖v‖ ∧
      ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (omJ J v t : ℂ) := by
  let l : V →L[ℝ] ℂ := (-(π : ℂ)) • (Complex.ofRealCLM.comp (innerSL ℝ v)) -
      ((π : ℂ) * I) • (Complex.ofRealCLM.comp ((innerSL ℝ v).comp (J : V →L[ℝ] V)))
  have hl : ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ) := fun t => by
    simp [l]
  refine ⟨l, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_, fun t => by
    rw [hl t]; rfl⟩
  rw [hl t]
  calc ‖-(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ)‖
      ≤ ‖-(π : ℂ) * (⟪v, t⟫ : ℝ)‖ + ‖(π : ℂ) * I * (⟪v, J t⟫ : ℝ)‖ := norm_sub_le _ _
    _ = π * |⟪v, t⟫| + π * |⟪v, J t⟫| := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    _ ≤ π * (‖v‖ * ‖t‖) + π * (‖v‖ * ‖t‖) := by
        gcongr
        · exact abs_real_inner_le_norm _ _
        · exact (abs_real_inner_le_norm v (J t)).trans (by rw [J.norm_map])
    _ = 2 * π * ‖v‖ * ‖t‖ := by ring

theorem decay_gau_smul {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
    (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (k n : ℕ) :
    ∃ C, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun u => gau u • ρ u f) v‖ ≤ C := by
  set F : V → B := fun u => gau u • ρ u f with hF
  have hFs : ContDiff ℝ ∞ F := contDiff_gau.smul hf
  have hE : ContDiff ℝ ∞ (fun z : ℂ => cexp z) := Complex.contDiff_exp
  have hN : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) *
      ‖iteratedFDeriv ℝ (n - i) F 0‖ * ((k + i).factorial * Real.exp 1), fun v => ?_⟩
  obtain ⟨l, hl, hlt⟩ := exists_shift_form J v
  have hshift : (fun t => F (t + v)) = fun t => (gau v • ρ v) (cexp (l t) • F t) := by
    funext t
    simp only [hF, _root_.smul_apply, map_smul, smul_smul]
    rw [add_comm t v, h.2.1 v t f, smul_smul]
    congr 1
    have key : cexp (-(π : ℂ) * (⟪v, t⟫ : ℝ)) = cexp (l t) * cexp (π * I * (omJ J v t : ℂ)) := by
      rw [hlt t, ← Complex.exp_add]; congr 1; ring
    rw [gau_add, key]
    ring
  have hG : ContDiff ℝ ∞ (fun t => cexp (l t)) := hE.comp l.contDiff
  have hρ1 : ‖ρ v‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [h.2.2.1, one_mul]
  have hL : ‖(gau v • ρ v).restrictScalars ℝ‖ ≤ ‖gau v‖ := by
    rw [ContinuousLinearMap.norm_restrictScalars]
    calc ‖gau v • ρ v‖ ≤ ‖gau v‖ * ‖ρ v‖ := norm_smul_le _ _
      _ ≤ ‖gau v‖ * 1 := by gcongr
      _ = ‖gau v‖ := mul_one _
  have hexp : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (fun t => cexp (l t)) 0‖ ≤
      ‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i := by
    intro i
    have e1 : (fun t => cexp (l t)) = (fun z : ℂ => cexp z) ∘ (l : V → ℂ) := rfl
    rw [e1, l.iteratedFDeriv_comp_right hE 0 (by exact_mod_cast le_top), map_zero]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
  have hD : ‖iteratedFDeriv ℝ n F v‖ ≤ ‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) *
      ‖iteratedFDeriv ℝ (n - i) F 0‖ := by
    have e0 : iteratedFDeriv ℝ n F v = iteratedFDeriv ℝ n (fun t => F (t + v)) 0 := by
      rw [iteratedFDeriv_comp_add_right, zero_add]
    have e2 : (fun t => (gau v • ρ v) (cexp (l t) • F t)) =
        ((gau v • ρ v).restrictScalars ℝ) ∘ (fun t => cexp (l t) • F t) := rfl
    rw [e0, hshift, e2]
    refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hG.smul hFs).contDiffAt hN).trans ?_
    refine mul_le_mul hL ?_ (norm_nonneg _) (norm_nonneg _)
    refine (norm_iteratedFDeriv_smul_le hG hFs 0 hN).trans (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp i) (by positivity))
      (norm_nonneg _)
  calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ n F v‖
      ≤ ‖v‖ ^ k * (‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) *
        ‖iteratedFDeriv ℝ (n - i) F 0‖) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) *
        ‖iteratedFDeriv ℝ (n - i) F 0‖ * (‖v‖ ^ (k + i) * ‖gau v‖) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, pow_add]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (pow_mul_norm_gau_le _ _) (by positivity)

theorem Sm.good : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ f : B,
    Sm ρ f → Good h f := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h f hf
  let ψ : SchwartzMap V B := ⟨fun u => gau u • ρ u f, contDiff_gau.smul hf, fun k n => decay_gau_smul h hf k n⟩
  have hψ : ((𝓕 ψ : SchwartzMap V B) : V → B) = 𝓕 (fun u => gau u • ρ u f) := SchwartzMap.fourier_coe ψ
  intro n
  have hint := (𝓕 ψ).integrable_pow_mul volume n
  refine (J.measurePreserving.integrable_comp_of_integrable hint).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, LinearIsometryEquiv.norm_map, proj_translate hJ h f w, h.2.2.1, hψ]

end GlobalTheory.RealWeil
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}

theorem integral_gau_twisted_conv (hJ : ∀ x, J (J x) = -x) (a y : V) :
    ∫ u, gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ))) = gau a * gau y := by
  set m : V := (1 / 2 : ℝ) • (y - a) with hm
  have hym : y - a = m + m := by
    rw [hm, ← add_smul]; norm_num
  have hself : ∀ x : V, ⟪x, J x⟫ = 0 := by
    intro x
    have := omJ_skew hJ x x
    unfold omJ at this
    linarith
  have hsk : ∀ x z : V, ⟪z, J x⟫ = -⟪x, J z⟫ := fun x z => by
    have := omJ_skew hJ x z
    unfold omJ at this
    exact this
  have hpt : ∀ v : V, gau (v + m) * (gau (y - (v + m + a)) *
      cexp (π * I * ((omJ J (v + m) a + omJ J (v + m + a) y : ℝ) : ℂ))) =
      cexp (-(π : ℂ) * ‖v‖ ^ 2 + (π * I) * ⟪J (a + y), v⟫) * cexp (-(π : ℂ) * ‖m‖ ^ 2) := by
    intro v
    have e1 : y - (v + m + a) = m - v := by
      have hy : y = m + m + a := by rw [← hym]; abel
      rw [hy]; abel
    have h1 : ‖v + m‖ ^ 2 + ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 := by
      rw [e1, norm_add_sq_real, norm_sub_sq_real, real_inner_comm m v]; ring
    have h2 : omJ J (v + m) a + omJ J (v + m + a) y = ⟪J (a + y), v⟫ := by
      unfold omJ
      rw [real_inner_comm v (J (a + y)), hm]
      simp only [map_add (f := _), inner_add_left, inner_add_right, real_inner_smul_left, inner_sub_left]
      have h3 := hsk a y
      have h4 := hself a
      have h5 := hself y
      linarith
    have h1c : ((‖y - (v + m + a)‖ : ℝ) : ℂ) ^ 2 =
        2 * (‖v‖ : ℂ) ^ 2 + 2 * (‖m‖ : ℂ) ^ 2 - (‖v + m‖ : ℂ) ^ 2 := by
      have h6 : ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 - ‖v + m‖ ^ 2 := by linarith
      exact_mod_cast h6
    simp only [gau, ← Complex.exp_add]
    congr 1
    rw [h1c, h2]
    ring
  have hshift := integral_add_right_eq_self (μ := (volume : Measure V))
    (fun u => gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ)))) m
  rw [← hshift]
  simp only [hpt]
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb, div_self hπ, Complex.one_cpow, one_mul,
    LinearIsometryEquiv.norm_map, gau, gau, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h3 : ‖m‖ ^ 2 = ‖a‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2 - ‖a + y‖ ^ 2 / 4 := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_pow,
      norm_sub_sq_real, norm_add_sq_real, real_inner_comm y a]
    ring
  have h3c : (‖m‖ : ℂ) ^ 2 = (‖a‖ : ℂ) ^ 2 / 2 + (‖y‖ : ℂ) ^ 2 / 2 - (‖a + y‖ : ℂ) ^ 2 / 4 := by
    exact_mod_cast h3
  rw [h3c, mul_pow, I_sq]
  field_simp
  ring

theorem proj_heis_proj {ρ : V → B →L[ℂ] B} (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (a : V) (f : B) :
    proj h (ρ a (proj h f)) = gau a • proj h f := by
  have hself : ∀ x : V, omJ J x x = 0 := fun x => by
    have := omJ_skew hJ x x
    linarith
  set F : V → V → B := fun u z =>
    (gau u * (gau (z - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) z : ℝ) : ℂ)))) • ρ z f with hF
  have hin : ∀ u, gau u • ρ u (ρ a (proj h f)) = ∫ z, F u z := by
    intro u
    rw [h.2.1 u a, proj_apply h f, ← (ρ (u + a)).integral_comp_comm (h.integrable f), ← integral_smul,
      ← integral_smul, ← integral_add_right_eq_self (F u) (u + a)]
    congr 1
    ext w
    have hw : omJ J (u + a) (w + (u + a)) = omJ J (u + a) w := by
      have h0 := hself (u + a)
      unfold omJ at h0 ⊢
      rw [map_add (f := _), inner_add_right, h0, add_zero]
    show _ = (gau u * (gau (w + (u + a) - (u + a)) *
      cexp (π * I * ((omJ J u a + omJ J (u + a) (w + (u + a)) : ℝ) : ℂ)))) • ρ (w + (u + a)) f
    rw [add_sub_cancel_right, hw, add_comm w (u + a), map_smul, h.2.1 (u + a) w, smul_smul, smul_smul,
      smul_smul]
    congr 1
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  have he : ∀ r : ℝ, ‖cexp (π * I * (r : ℂ))‖ = 1 := fun r => by
    rw [Complex.norm_exp]
    simp
  have hnorm : ∀ u z, ‖F u z‖ = ‖gau u‖ * (‖gau (z - (u + a))‖ * ‖f‖) := by
    intro u z
    simp only [hF, norm_smul, norm_mul, h.2.2.1]
    rw [he, mul_one, mul_assoc]
  have hom : Continuous fun p : V × V => omJ J p.1 p.2 := by
    unfold omJ
    exact continuous_fst.inner (J.continuous.comp continuous_snd)
  have hcont : Continuous (Function.uncurry F) := by
    show Continuous fun p : V × V => (gau p.1 * (gau (p.2 - (p.1 + a)) *
      cexp (π * I * ((omJ J p.1 a + omJ J (p.1 + a) p.2 : ℝ) : ℂ)))) • ρ p.2 f
    refine Continuous.smul ?_ ((h.2.2.2 f).comp continuous_snd)
    refine (continuous_gau.comp continuous_fst).mul
      ((continuous_gau.comp (continuous_snd.sub (continuous_fst.add continuous_const))).mul ?_)
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact (hom.comp (continuous_fst.prodMk continuous_const)).add
      (hom.comp ((continuous_fst.add continuous_const).prodMk continuous_snd))
  have hint : Integrable (Function.uncurry F) ((volume : Measure V).prod volume) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    constructor
    · refine Filter.Eventually.of_forall fun u => ?_
      have hm : AEStronglyMeasurable (fun z => Function.uncurry F (u, z)) volume :=
        (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      rw [← integrable_norm_iff hm]
      simp only [Function.uncurry_apply_pair, hnorm]
      exact (((integrable_gau (V := V)).norm.comp_sub_right (u + a)).mul_const ‖f‖).const_mul ‖gau u‖
    · simp only [Function.uncurry_apply_pair, hnorm]
      simp only [integral_const_mul, integral_mul_const, integral_sub_right_eq_self (‖gau ·‖)]
      exact (integrable_gau (V := V)).norm.mul_const _
  rw [proj_apply h (ρ a (proj h f))]
  simp_rw [hin]
  rw [integral_integral_swap hint]
  have hinner : ∀ z, ∫ u, F u z = (gau a * gau z) • ρ z f := by
    intro z
    simp only [hF]
    rw [integral_smul_const, integral_gau_twisted_conv hJ a z]
  simp_rw [hinner]
  rw [proj_apply h f, ← integral_smul]
  congr 1
  ext z
  rw [smul_smul]

end GlobalTheory.RealWeil
end

section

noncomputable section

open NumberField

namespace GlobalTheory.HeckePoisson

variable {K : Type} [Field K] [NumberField K] {I : Type}

def embA (φ : I → K →+* ℂ) : 𝓞 K →+ EuclideanSpace ℂ I where
  toFun α := WithLp.toLp 2 (GlobalTheory.HeckeTheta.emb φ (α : K))
  map_zero' := by ext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by ext i; simp [GlobalTheory.HeckeTheta.emb]

def lat (φ : I → K →+* ℂ) (M : Ideal (𝓞 K)) : Submodule ℤ (EuclideanSpace ℂ I) :=
  AddSubgroup.toIntSubmodule (M.toAddSubgroup.map (embA φ))

theorem embA_apply (φ : I → K →+* ℂ) (α : 𝓞 K) (i : I) : embA φ α i = φ i (α : K) := rfl

theorem mem_lat {φ : I → K →+* ℂ} {M : Ideal (𝓞 K)} {x : EuclideanSpace ℂ I} :
    x ∈ lat φ M ↔ ∃ μ ∈ M, embA φ μ = x := by
  show x ∈ M.toAddSubgroup.map (embA φ) ↔ _
  rw [AddSubgroup.mem_map]
  rfl

def kappa [Fintype I] (n : I → ℤ) : ℂ := ((2 : ℂ) ^ Fintype.card I)⁻¹ * (-Complex.I) ^ (∑ i, (n i).natAbs)

end GlobalTheory.HeckePoisson
end
end
