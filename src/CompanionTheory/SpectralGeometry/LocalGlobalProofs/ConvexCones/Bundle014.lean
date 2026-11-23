module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle739
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle683
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle734
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarDepthGapOnCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle694
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle695
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.exists_psd_forms_cover_contact_set : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), HasRedCover bar X → Covers2 a → ∃ (k : ℕ) (m : Fin k → ℕ) (u : ∀ j, Fin (m j) → LinearMap.BilinForm ℤ X), (∀ j i y z, u j i y z = u j i z y) ∧ (∀ j i y, 0 ≤ u j i y y) ∧ ∀ B ∈ contact bar a, IsPosDef B → ∃ j, B ∈ rcone (u j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_rcone_cover_contact | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_rcone_cover_contact | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_rcone_cover_contact <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.uniform_cell_bound_polyhedral_fan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → ∃ N₀ C₀ : ℕ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith bar ψ N ℓ γ ∧ ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → ∃ h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, IsFaceCut γ s h' ∧ (∀ β, InRCone γ β → 0 < h β → 0 < h' β) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h' β) ≤ C₀ * ℓ β := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.UniformStrictBound.exists_strict_data | exact GlobalTheory.CompanionTheory.Ar.Fan.UniformStrictBound.exists_strict_data | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.UniformStrictBound.exists_strict_data <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.psd_balanced_form_mem_cell_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → Dominates bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms bar X, (∀ y, 0 ≤ x y y) → ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.RationalConeOfSum.inRCone_of_add | exact GlobalTheory.CompanionTheory.Ar.Fan.RationalConeOfSum.inRCone_of_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.RationalConeOfSum.inRCone_of_add <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.psd_balanced_form_vanishes_low_rank : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → Dominates bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ τ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone.vanish_of_inRCone_of_genRank_le | exact GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone.vanish_of_inRCone_of_genRank_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone.vanish_of_inRCone_of_genRank_le <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.PullbackCoordinates

theorem mem_balForms_of_descend {O : Type} [CommRing O] {bar : O → O} (hb : CMOrd O bar) {X Y : Type} [AddCommGroup X]
    [Module O X] [AddCommGroup Y] [Module O Y] (τ : O ≃+* O) {f : X →+ Y} (hf : Function.Surjective f)
    (hsm : ∀ (a : O) (x : X), f (a • x) = τ a • f x) {δ : LinearMap.BilinForm ℤ X} (hδ : δ ∈ balForms bar X)
    {ε : LinearMap.BilinForm ℤ Y} (hε : ∀ x y, ε (f x) (f y) = δ x y) : ε ∈ balForms bar Y := by
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · obtain ⟨y, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hf z
    rw [hε, hε, hδ.1]
  · obtain ⟨y, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hf z
    obtain ⟨a, rfl⟩ := τ.surjective a
    rw [← hb.comm τ a, ← hsm, ← hsm, hε, hε, hδ.2]

theorem exists_coord_pullAdd_of_pos : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell bar φ δ₀ → LinearIndependent ℤ δ₀ →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] (π : X₀ →ₗ[O] Y), Function.Surjective π → ∀ (τ : O ≃+* O) (f : X →+ Y), τ w0 = w0 →
    Function.Surjective f → (∀ (a : O) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y, (∀ i, 0 < t i → pull π (u i) = δ₀ i) →
  ∀ β : LinearMap.BilinForm ℤ X, (∀ (x y : X) (x₀ y₀ : X₀), π x₀ = f x → π y₀ = f y → β x y = v x₀ y₀) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧
    toReal (δ j) = ∑ i, a i • toReal (pullAdd f (u i)) := by
  intro O _ _ _ _ bar w0 hb φ htw X₀ _ _ _ m₀ δ₀ h₀ hind v t ht hvt X Y _ _ _ _ _ _ π hπ τ f hτ hf hsm u hu β hβ m δ hδ c hc hβc j hj
  classical
  have hval : ∀ x y, (β x y : ℝ) = ∑ l, c l * (δ l x y : ℝ) := fun x y => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hβc x y
  have hvan : ∀ l, 0 < c l → ∀ x, f x = 0 → ∀ y, δ l x y = 0 := by
    intro l hl x hx y
    have hb : β x x = 0 := by simpa using hβ x x 0 0 (by simp [hx]) (by simp [hx])
    have hk := hval x x
    rw [hb, Int.cast_zero] at hk
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hc i) (Int.cast_nonneg (hδ.nonneg i x))).1 hk.symm l (Finset.mem_univ _)
    have h0 : δ l x x = 0 := Int.cast_eq_zero.1 ((mul_eq_zero.1 hall).resolve_left hl.ne')
    exact ConeSub.eq_zero_of_self_eq_zero (δ l) (hδ.mem l).1 (hδ.nonneg l) h0 y
  set S : Finset (Fin m) := Finset.univ.filter fun l => 0 < c l with hS
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Set.range s = ↑S := Finset.range_orderEmbOfFin S rfl
  have hspos : ∀ i, 0 < c (s i) := fun i => by
    have : s i ∈ (S : Set (Fin m)) := hs ▸ Set.mem_range_self i
    simpa [hS] using this
  have hdesc : ∀ i : Fin S.card, ∃ ε : LinearMap.BilinForm ℤ Y, ∀ x y, ε (f x) (f y) = δ (s i) x y := fun i =>
    GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf _ (hvan _ (hspos i)) fun x hx y => by rw [(hδ.mem _).1]; exact hvan _ (hspos i) x hx y
  choose ε hε using hdesc
  have hεm : ∀ i, ε i ∈ balForms bar Y := fun i => mem_balForms_of_descend hb τ hf hsm (hδ.mem _) (hε i)
  have hεn : ∀ i y, 0 ≤ ε i y y := fun i y => by
    obtain ⟨y, rfl⟩ := hf y
    rw [hε]; exact hδ.nonneg _ _
  have hsemi := GlobalTheory.T.eval_pullback_semilinear_surjective O bar w0 hb φ htw τ hτ f hf hsm
  have hεl : φ.LinearOn ε := by
    intro d hd
    have h1 := linearOn_comp hδ.linear s d hd
    have h2 : ∀ i, φ.evalZ (δ (s i)) = φ.evalZ (ε i) := fun i => by
      have := hsemi fun a b => (ε i a b : ℝ)
      simp only [hε] at this
      exact this
    have h3 := hsemi fun a b => ∑ i, d i * (ε i a b : ℝ)
    simp only [hε] at h3
    simp only [h2] at h1
    exact h3.symm.trans h1
  have hvb : toReal v = ∑ i, c (s i) • toReal (pull π (ε i)) := LinearMap.ext₂ fun x₀ y₀ => by
    obtain ⟨x, hx⟩ := hf (π x₀)
    obtain ⟨y, hy⟩ := hf (π y₀)
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pull_apply]
    rw [← hβ x y x₀ y₀ hx.symm hy.symm, hval, ← hx, ← hy]
    simp only [hε]
    refine (Fintype.sum_of_injective s s.injective _ _ (fun l hl => ?_) fun i => rfl).symm
    have : ¬ 0 < c l := by rw [hs] at hl; simpa [hS] using hl
    rw [le_antisymm (not_lt.1 this) (hc l), zero_mul]
  obtain ⟨j, rfl⟩ : j ∈ Set.range s := by rw [hs]; simpa [hS] using hj
  obtain ⟨a, ha, ha0, he⟩ := exists_face_coord_of_linearOn h₀ hind (fun i => pull_mem π (hεm i)) (fun i y => hεn i _)
    ((linearOn_pull_iff hπ).2 hεl) ht hspos hvt hvb j
  refine ⟨a, ha, ha0, LinearMap.ext₂ fun x y => ?_⟩
  obtain ⟨x₀, hx⟩ := hπ (f x)
  obtain ⟨y₀, hy⟩ := hπ (f y)
  have h1 := LinearMap.congr_fun₂ he x₀ y₀
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pull_apply, pullAdd_apply] at h1 ⊢
  rw [hx, hy, hε] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (ht i).eq_or_lt with h | h
  · rw [ha0 i h.symm, zero_mul, zero_mul]
  · rw [← hu i h, pull_apply, hx, hy]

end GlobalTheory.CompanionTheory.Ar.Fan.PullbackCoordinates
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.exists_descending_rays_pullback : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀]
  [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (hm : ∀ i, δ₀ i ∈ balForms bar X₀),
  (∀ i y, 0 ≤ δ₀ i y y) → LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, hm i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) (τ : O ≃+* O)
    (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 → Function.Surjective f →
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) →
    (∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀) →
  ∃ u : Fin m₀ → LinearMap.BilinForm ℤ (X₀ ⧸ (CarDim.orad v : Submodule O X₀)),
    toReal β = ∑ i, t i • toReal (pullAdd f (u i)) ∧
    LinearIndependent ℤ (fun i : {i // 0 < t i} => pullAdd f (u i)) ∧
    ∀ i, 0 < t i → pull (CarDim.orad v : Submodule O X₀).mkQ (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms bar X ∧
      (∀ y, 0 ≤ pullAdd f (u i) y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = pullAdd f (u i) → k = 1) ∧
      ∀ lab : InvFun O, IsTwG w0 lab → lab.evalZ (pullAdd f (u i)) = lab.evalZ (δ₀ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.DescendingRaysPullback.exists_desc_rays_pullAdd | exact GlobalTheory.CompanionTheory.Ar.Fan.DescendingRaysPullback.exists_desc_rays_pullAdd | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.DescendingRaysPullback.exists_desc_rays_pullAdd <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.PullbackInCellCone

theorem inRCone_pullAdd_of_isCell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell bar φ δ₀ → ∀ t : Fin m₀ → ℝ, (∀ i, 0 ≤ t i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] (π : X₀ →ₗ[O] Y), Function.Surjective π → ∀ (τ : O ≃+* O) (f : X →+ Y), τ w0 = w0 →
    Function.Surjective f → (∀ (a : O) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y,
    (∀ i, 0 < t i → pull π (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms bar X ∧ ∀ y, 0 ≤ pullAdd f (u i) y y) →
  ∀ β : LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (pullAdd f (u i)) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ i, 0 < t i → InRCone δ (pullAdd f (u i)) := by
  intro O _ _ _ _ bar w0 hb φ htw X₀ _ _ _ m₀ δ₀ h₀ t ht X Y _ _ _ _ _ _ π hπ τ f hτ hf hsm u hu β hβ m δ hδ c hc hβc i hi
  classical
  let S : Finset (Fin m₀) := Finset.univ.filter fun j => 0 < t j
  let s : Fin S.card ↪ Fin m₀ := (S.orderEmbOfFin rfl).toEmbedding
  have hrange : Set.range s = (S : Set (Fin m₀)) := Finset.range_orderEmbOfFin S rfl
  have hs : ∀ j, 0 < t (s j) := fun j => by
    have : s j ∈ (S : Set (Fin m₀)) := hrange ▸ Set.mem_range_self j
    simpa [S] using this
  have hmem : ∀ j, 0 < t j → j ∈ Set.range s := fun j hj => by
    rw [hrange]; simpa [S] using hj
  have h1 : φ.LinearOn (fun j => δ₀ (s j)) := linearOn_comp h₀.linear s
  have e1 : (fun j => δ₀ (s j)) = fun j => pull π (u (s j)) := funext fun j => ((hu _ (hs j)).1).symm
  rw [e1] at h1
  have h2 : φ.LinearOn (fun j => u (s j)) := (linearOn_pull_iff hπ).1 h1
  have h3 : φ.LinearOn (fun j => pullAdd f (u (s j))) := by
    intro a ha
    have hz : ∀ j, φ.evalZ (pullAdd f (u (s j))) = φ.evalZ (u (s j)) := fun j =>
      GlobalTheory.T.eval_pullback_semilinear_surjective O bar w0 hb φ htw τ hτ f hf hsm fun x y => ((u (s j) x y : ℤ) : ℝ)
    have := h2 a ha
    simp only [hz]
    rw [← this]
    exact GlobalTheory.T.eval_pullback_semilinear_surjective O bar w0 hb φ htw τ hτ f hf hsm fun x y => ∑ j, a j * ((u (s j) x y : ℤ) : ℝ)
  have hsum : toReal β = ∑ j, t (s j) • toReal (pullAdd f (u (s j))) := by
    rw [hβ]
    refine (Fintype.sum_of_injective s s.injective _ _ (fun j hj => ?_) (fun j => rfl)).symm
    have : t j = 0 := le_antisymm (not_lt.1 fun h => hj (hmem j h)) (ht j)
    rw [this, zero_smul]
  obtain ⟨j, rfl⟩ := hmem i hi
  exact GlobalTheory.T.inRealCone_cell_of_linearPiece_through_cellPoint bar φ δ (fun j => pullAdd f (u (s j))) hδ (fun j => (hu _ (hs j)).2.1) (fun j => (hu _ (hs j)).2.2) h3
    β c (fun j => t (s j)) hc hs hβc hsum j

end GlobalTheory.CompanionTheory.Ar.Fan.PullbackInCellCone
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.star_depth_gap_on_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith bar ψ N ℓ γ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (starDepth bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarDepthGap.starDepth_le_gap | exact GlobalTheory.CompanionTheory.Ar.Fan.StarDepthGap.starDepth_le_gap | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarDepthGap.starDepth_le_gap <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_isPosDef_of_basis {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X) :
    ∃ B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∀ y z, B₀ y z = B₀ z y) ∧ IsPosDef B₀ := by
  classical
  let B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ k, toReal (GlobalTheory.RedTh.sqForm b (Pi.single k 1))
  have hv : ∀ i j, B₀ (b i) (b j) = if i = j then 1 else 0 := fun i j => by
    simp only [B₀, LinearMap.sum_apply, toReal_apply, GlobalTheory.RedTh.sqForm_basis]
    by_cases h : i = j
    · subst h
      simp [Pi.single_apply]
    · simp [Pi.single_apply, h]
  refine ⟨B₀, fun y z => ?_, (isPosDef_iff_basis b B₀).2 fun c hc => ?_⟩
  · simp only [B₀, LinearMap.sum_apply, toReal_apply, GlobalTheory.RedTh.sqForm_apply, mul_comm]
  · simp only [hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩

theorem hasRedCover_int : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X], HasRedCover (id : ℤ → ℤ) X := by
  intro X _ _ _
  classical
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℤ X = n := ⟨_, rfl⟩
  let b₀ : Module.Basis (Fin n) ℤ X := Module.finBasisOfFinrankEq ℤ X hn
  obtain ⟨B₀, hs₀, hp₀⟩ := exists_isPosDef_of_basis b₀
  obtain ⟨S, hS⟩ := GlobalTheory.SiegelCone.gram_mem_cone n
  refine GlobalTheory.RedTh.hasRedCover_of_fintype (ι := ↥S) _ (fun l => GlobalTheory.RedTh.sqForm b₀ l.1)
    (fun l y z => by simp only [GlobalTheory.RedTh.sqForm_apply, mul_comm])
    (fun l y => by simp only [GlobalTheory.RedTh.sqForm_apply]; exact mul_self_nonneg _) fun B hB => ?_
  obtain ⟨X₁, _, m₁, hproj, r, B₁, hr, hB₁, hp₁, hBr⟩ := hB
  obtain rfl : m₁ = AddCommGroup.toIntModule X₁ := Subsingleton.elim _ _
  have : Module.Finite ℤ X₁ := Module.Finite.of_surjective r hr
  have : Module.Free ℤ X₁ := inferInstance
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hrσ : ∀ y, r (σ y) = y := fun y => LinearMap.congr_fun hσ y
  obtain ⟨b, d, d', u, t, hd, -, -, hg, -⟩ :=
    GlobalTheory.RedTh.exists_siegel_split r σ hrσ B₀ hs₀ hp₀ B₁ hB₁.1 hp₁ n hn
  obtain ⟨c, hc, hG⟩ := hS d u hd
  let e : X ≃ₗ[ℤ] X := b₀.equiv b (Equiv.refl _)
  have he : ∀ i, e (b₀ i) = b i := fun i => by simp [e]
  refine ⟨e, fun l => c l.1, fun l => hc _, ?_⟩
  refine b₀.ext fun i => b₀.ext fun j => ?_
  have hl : B (b i) (b j) = ∑ l ∈ S, c l * ((l i : ℝ) * (l j : ℝ)) := by
    rw [hBr, hg, hG]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  simp only [pullR_apply, LinearEquiv.coe_coe, he, hl, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
    GlobalTheory.RedTh.sqForm_basis]
  rw [← Finset.sum_coe_sort S]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
