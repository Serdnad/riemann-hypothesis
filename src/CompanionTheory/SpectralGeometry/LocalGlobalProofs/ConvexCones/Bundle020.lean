module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle729
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle752
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle715
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle728
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle727
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section Pull

variable {O : Type} [CommRing O] {bar : O → O} {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]

theorem isMin2_pullR_iff {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (y : X) :
    IsMin2 (pullR r B) y ↔ IsMin2 B (r y) := by
  have e : ∀ x : X, r (y + (x + x)) = r y + (r x + r x) := fun x => by rw [map_add (f := _), map_add (f := _)]
  constructor
  · intro h x
    obtain ⟨x, rfl⟩ := hr x
    have := h x
    simp only [pullR_apply, e] at this
    exact this
  · intro h x
    simp only [pullR_apply, e]
    exact h (r x)

theorem pullR_mem_contact {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {ι : Type} {a : ι → X}
    (h : B ∈ contact bar fun i => r (a i)) : pullR r B ∈ contact bar a :=
  ⟨pullR_mem_psdCone hr h.1, fun i => (isMin2_pullR_iff hr B (a i)).2 (h.2 i)⟩

theorem mem_contact_of_pullR {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {ι : Type} {a : ι → X}
    (hB : B ∈ psdCone (bar := bar) (X := X₁)) (h : pullR r B ∈ contact bar a) : B ∈ contact bar fun i => r (a i) :=
  ⟨hB, fun i => (isMin2_pullR_iff hr B (a i)).1 (h.2 i)⟩

end Pull

theorem isSpanned_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X),
      Covers2 a → IsSpanned bar (contact bar a) := by
  intro O _ _ _ _ bar red X _ _ _ _ ι _ a ha
  have hadd : ∀ B ∈ contact bar a, ∀ B' ∈ contact bar a, B + B' ∈ contact bar a := fun B hB B' hB' =>
    ⟨GlobalTheory.T.psd_cone_add_mem O bar X B B' hB.1 hB'.1, fun i x => by
      have h1 := hB.2 i x
      have h2 := hB'.2 i x
      simp only [LinearMap.add_apply]
      exact add_le_add h1 h2⟩
  obtain ⟨B₁, hB₁, hrad⟩ := GlobalTheory.T.psd_cone_exists_maximal_support O bar X (contact bar a) ⟨0, zero_mem_contact bar a⟩ (fun B hB => hB.1) hadd
  obtain ⟨X₁, _, _, _, r, B₁', hr, hbal, hdef, hfac⟩ := id hB₁.1
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  have hfac' : B₁ = pullR r B₁' := LinearMap.ext₂ hfac
  have hB₁' : B₁' ∈ contact bar fun i => r (a i) :=
    mem_contact_of_pullR hr (hdef.mem_psdCone hbal) (hfac' ▸ hB₁)
  have hcov : Covers2 fun i => r (a i) := fun y => by
    obtain ⟨y, rfl⟩ := hr y
    obtain ⟨i, x, rfl⟩ := ha y
    exact ⟨i, r x, by rw [map_add (f := _), map_add (f := _)]⟩
  obtain ⟨m, γ, hγ, hnn, hK, hsub⟩ :=
    GlobalTheory.T.contact_set_spans_of_pos_def O bar X₁ ι (fun i => r (a i)) (red X₁) hcov ⟨B₁', hB₁', hdef⟩
  refine ⟨m, fun i => pull r (γ i), fun i => pull_mem r (hγ i), fun i y => hnn i (r y), fun i => ?_, fun B hB => ?_⟩
  · have e : toReal (pull r (γ i)) = pullR r (toReal (γ i)) := LinearMap.ext₂ fun _ _ => by simp
    rw [e]
    exact pullR_mem_contact hr (hK i)
  · have hker : ∀ y, r y = 0 → B y y = 0 := fun y hy => hrad B hB y (by rw [hfac, hy]; simp)
    obtain ⟨B', hB', rfl⟩ := GlobalTheory.T.psd_cone_descends_along_surjection O bar X X₁ r B hr hB.1 hker
    obtain ⟨t, ht, e⟩ := hsub (mem_contact_of_pullR hr hB' hB)
    refine ⟨t, ht, LinearMap.ext₂ fun y z => ?_⟩
    simp [e, LinearMap.sum_apply]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction

theorem exists_markFun_props_gen : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], _root_.GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → ∃ w : InvFun O, IsTwG w0 w ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  intro O _ _ _ _ bar w0 hb q ψ lab i hD hψ htψ htlab hlab
  classical
  obtain ⟨w, hw⟩ := GlobalTheory.PolFan.Mark.exists_markFun bar ψ lab i
  have ev := fun {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (β : LinearMap.BilinForm ℤ X) => GlobalTheory.PolFan.Mark.evalZ_markFun hw (X := X) β
  have mk : ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
      (β : LinearMap.BilinForm ℤ X), w.evalZ β = 1 → GlobalTheory.PolFan.Mark.IsMarked bar ψ lab i X β := fun β h => by
    rw [ev] at h
    split_ifs at h with h'
    · exact h'
    · norm_num at h
  refine ⟨w, fun σ hσ n B => by rw [hw, hw]; exact GlobalTheory.T.marking_value_galois_invariant O bar w0 hb ψ lab i htψ htlab σ hσ n B, ?_⟩
  intro X _ _ _ _ hX
  refine ⟨fun β _ _ => ?_, fun β _ _ h1 => (mk β h1).2.2.1, fun β _ _ h1 => (mk β h1).2.2.2.1,
    fun m v hv hle β _ _ β' _ _ h1 h1' hc hc' =>
      GlobalTheory.T.isMarked_unique_of_inRCone O bar hb q ψ lab i hD hψ hlab X hX m v hv hle β β' (mk β h1) (mk β' h1') hc hc',
    fun m v hv β hβ hp hc hl => ?_⟩
  · rw [ev]
    split_ifs <;> simp
  · obtain ⟨β₀, h0, hc0⟩ := GlobalTheory.T.exists_isMarked_inRCone_of_isCell_of_evalZ_eq O bar hb q ψ lab i hD hψ hlab X hX m v hv β hβ hp hc hl
    exact ⟨β₀, h0.1, h0.2.1, by rw [ev, if_pos h0], hc0⟩

end GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.new_cell_mult_lt_after_star : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    SimpLab bar q φ lab → IsCentreSet bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar φ γ → β₀ ∈ balForms bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) < M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity.cellMult_lt_of_star_new | exact GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity.cellMult_lt_of_star_new | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity.cellMult_lt_of_star_new <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.RadicalConeComparison

section General

variable {O : Type} [CommRing O] {bar : O → O} {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  [AddCommGroup Y] [Module O Y] [Module.Finite O Y]

theorem transport {φ χ : InvFun O} {b : ℕ} (e : X ≃ₗ[O] Y) {β : LinearMap.BilinForm ℤ Y}
    (h : ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      φ.LinearOn u ∧ χ.LinearOn u ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, χ.evalZ (u i) ≤ 1) ∧
      InRCone u (pull e.toLinearMap β)) :
    ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ Y), (∀ i, u i ∈ balForms bar Y) ∧ (∀ i y, 0 ≤ u i y y) ∧
      φ.LinearOn u ∧ χ.LinearOn u ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, χ.evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨n, u, h1, h2, h3, h4, h5, h6, c, hc, h7⟩ := h
  refine ⟨n, fun i => pull e.symm.toLinearMap (u i), fun i => pull_mem _ (h1 i), fun i y => h2 i _,
    (linearOn_pull_iff e.symm.surjective).2 h3, (linearOn_pull_iff e.symm.surjective).2 h4,
    fun i => by rw [evalZ_pull φ e.symm.surjective]; exact h5 i,
    fun i => by rw [evalZ_pull χ e.symm.surjective]; exact h6 i, c, hc, LinearMap.ext₂ fun x y => ?_⟩
  have := LinearMap.congr_fun₂ h7 (e.symm x) (e.symm y)
  simpa [LinearMap.sum_apply] using this

theorem linearOn_starDepth {ψ w : InvFun O} {n : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X}
    (h : (starFun bar ψ w 0 1).LinearOn u) : (starDepth bar ψ w).LinearOn u := by
  rw [linearOn_iff] at h ⊢
  intro c hc
  simpa [starFun_evalR, starFun_evalZ] using h c hc


omit [Module O X] [Module.Finite O X] in
theorem mul_le_of_sub_mem_rcone {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hγ : ∀ i, 0 ≤ h (γ i)) {β v : LinearMap.BilinForm ℤ X} {t : ℝ} (hm : toReal β - t • toReal v ∈ rcone γ) :
    t * (h v : ℝ) ≤ h β := by
  obtain ⟨g, hg, hBg⟩ := hm
  have key := apply_eq_of_toReal_eq (β := β) (γ := Fin.cons v γ) (c := Fin.cons t g) (by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [← hBg]; abel) h
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at key
  have hpos : 0 ≤ ∑ i, g i * (h (γ i) : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (by exact_mod_cast hγ i)
  linarith

theorem exists_nat_bound {α : Type} {S : Set α} (hS : S.Finite) (f : α → ℝ) : ∃ b : ℕ, ∀ x ∈ S, f x ≤ b := by
  obtain ⟨r, hr⟩ := (hS.image f).bddAbove
  exact ⟨⌈r⌉₊, fun x hx => (hr ⟨x, hx, rfl⟩).trans (Nat.le_ceil r)⟩

end General

section CM

variable {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
  {q : ℕ} {ψ w : InvFun O}

theorem centres_finite (hw : IsCentreSet bar q ψ w) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q)
    {S : Set (LinearMap.BilinForm ℤ X)} (hS : S.Finite) :
    {v | v ∈ balForms bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsCell bar ψ γ ∧ (∀ i, γ i ∈ S) ∧ InRCone γ v}.Finite := by
  refine (hS.finite_subsets.biUnion (t := fun T => {v | v ∈ balForms bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ Set.range γ = T ∧ InRCone γ v})
    fun T _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro v ⟨a1, a2, a3, m, γ, a4, a5, a6⟩ v' ⟨b1, b2, b3, m', γ', -, b5, b6⟩
    refine (hw X hX).2.2 m γ a4 v a1 a2 v' b1 b2 a3 b3 a6 (inRCone_trans (fun j => ?_) b6)
    obtain ⟨i, hi⟩ : γ' j ∈ Set.range γ := by rw [a5, ← b5]; exact ⟨j, rfl⟩
    rw [← hi]; exact inRCone_self γ i
  · rintro v ⟨a1, a2, a3, m, γ, a4, a5, a6⟩
    exact Set.mem_biUnion (x := Set.range γ) (by rintro _ ⟨i, rfl⟩; exact a5 i) ⟨a1, a2, a3, m, γ, a4, rfl, a6⟩

theorem of_cell (hcm : CMOrd O bar) (hw : IsCentreSet bar q ψ w) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) {b m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar ψ γ) (hb : ∀ i, ψ.evalZ (γ i) ≤ b)
    (hb' : ∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → ψ.evalZ v ≤ b)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      ψ.LinearOn u ∧ (starDepth bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧
      (∀ i, (starDepth bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨hC1, hC2, hC3⟩ := hw X hX
  obtain ⟨lin1, lin2⟩ := GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn O bar hcm q ψ w 0 1 hw
  by_cases hc : ∃ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v
  · obtain ⟨v, hv, hvp, hvw, hvin⟩ := hc
    have hne : v ≠ 0 := by
      rintro rfl
      have := hC2 0 hv hvp hvw 2 0 (by simp)
      norm_num at this
    obtain ⟨m', s, h, hcut, hh, hin⟩ := GlobalTheory.StarCover.star_cover X m γ v (toReal β) (fun i => (hγ.mem i).1)
      hγ.nonneg hne hvin hβ
    have hh' : (0 : ℝ) < h v := by exact_mod_cast hh
    have hmem : ∀ j, InRCone γ ((Fin.cons v fun j => γ (s j) : Fin (m' + 1) → _) j) := fun j =>
      Fin.cases (by simpa using hvin) (fun k => by simpa using inRCone_self γ (s k)) j
    have hle : ∀ j, (h ((Fin.cons v fun j => γ (s j) : Fin (m' + 1) → _) j) : ℝ) ≤ h v := fun j =>
      Fin.cases (by simp) (fun k => by
        simp only [Fin.cons_succ]; rw [(hcut.2 (s k)).2 ⟨k, rfl⟩]; simpa using hh.le) j
    refine ⟨m' + 1, Fin.cons v fun j => γ (s j), fun j => Fin.cases hv (fun k => hγ.mem (s k)) j,
      fun j => Fin.cases hvp (fun k => hγ.nonneg (s k)) j, linearOn_of_forall_inRCone ψ hγ.linear hmem,
      linearOn_starDepth (lin2 X hX m γ hγ v hv hvp hvw hvin m' s h hcut hh),
      fun j => Fin.cases (hb' v hv hvp hvw hvin) (fun k => hb (s k)) j, fun j => ?_, hin⟩
    rw [← evalR_toReal]
    refine evalR_starDepth_le _ bar ψ w X m γ _ 1 hγ (hmem j) zero_le_one fun v' a1 a2 a3 a4 t _ ht => ?_
    rw [hC3 m γ hγ v' a1 a2 v hv hvp a3 hvw a4 hvin] at ht
    have := (mul_le_of_sub_mem_rcone hcut.1 ht).trans (hle j)
    nlinarith
  · have hno : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0 := fun v a1 a2 a3 =>
      (hC1 v a1 a2).resolve_right fun a4 => hc ⟨v, a1, a2, a4, a3⟩
    refine ⟨m, γ, hγ.mem, hγ.nonneg, hγ.linear, linearOn_starDepth (lin1 X hX m γ hγ hno), hb, fun j => ?_, hβ⟩
    rw [← evalR_toReal]
    exact evalR_starDepth_le _ bar ψ w X m γ _ 1 hγ (inRCone_self γ j) zero_le_one fun v' a1 a2 a3 a4 _ _ _ =>
      (hc ⟨v', a1, a2, a3, a4⟩).elim

theorem per_module (hcm : CMOrd O bar) (hψ : IsPolyFan bar q ψ) (hw : IsCentreSet bar q ψ w) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) :
    ∃ b : ℕ, ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      ψ.LinearOn u ∧ (starDepth bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧
      (∀ i, (starDepth bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨S, hS, hcov⟩ := (hψ X hX).finite
  obtain ⟨b, hb⟩ := exists_nat_bound (hS.union (centres_finite hw X hX hS)) fun v => ψ.evalZ v
  refine ⟨b, fun β hβ hp => ?_⟩
  obtain ⟨e, m, γ, c, hγ, hγS, hc, hsum⟩ := hcov _ (GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership.toReal_mem_psdCone_of_nonneg O bar hcm X β hβ hp)
  refine transport e (of_cell hcm hw X hX hγ (fun i => hb _ (Or.inl (hγS i)))
    (fun v a1 a2 a3 a4 => hb _ (Or.inr ⟨a1, a2, a3, m, γ, hγ, hγS, a4⟩)) ⟨c, hc, ?_⟩)
  rw [← hsum]
  exact LinearMap.ext₂ fun x y => by simp

end CM

theorem exists_bounded_gens : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∃ b : ℕ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  intro O _ _ _ _ bar hcm q ψ w hψ hw
  obtain ⟨n, R, hR, hiso⟩ := hcm.classes q
  have key := fun k => @per_module O _ _ _ _ bar q ψ w hcm hψ hw (R k) _ _ (hR k).1 (hR k).2.1 (hR k).2.2
  choose b hb using key
  refine ⟨Finset.univ.sup b, fun X _ _ _ _ hX β hβ hp => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hiso X hX
  haveI := (hR k).1
  obtain ⟨m, u, h1, h2, h3, h4, h5, h6, h7⟩ := hb k (pull f.symm.toLinearMap β) (pull_mem _ hβ) fun y => hp _
  have hk : (b k : ℝ) ≤ (Finset.univ.sup b : ℕ) := by exact_mod_cast Finset.le_sup (f := b) (Finset.mem_univ k)
  exact transport f.symm ⟨m, u, h1, h2, h3, h4, fun i => (h5 i).trans hk, h6, h7⟩

end GlobalTheory.CompanionTheory.Ar.Fan.RadicalConeComparison
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.mul_starDepth_le_faceCut_on_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β) ∧ (starDepth bar ψ w).evalZ β₀ = 1 ∧ (∀ j, (starDepth bar ψ w).evalZ (γ (s j)) = 0) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β = h β → ∃ (k : ℕ) (c : Fin (m' + 1) → ℕ), 0 < k ∧ k • β = ∑ i, c i • (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarDepthOnCell.starDepth_on_cell | exact GlobalTheory.CompanionTheory.Ar.Fan.StarDepthOnCell.starDepth_on_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarDepthOnCell.starDepth_on_cell <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.star_depth_bounded_denominator : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (D₀ : ℝ) * (starDepth bar ψ w).evalZ β = n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarDepthDenominator.starDepth_den | exact GlobalTheory.CompanionTheory.Ar.Fan.StarDepthDenominator.starDepth_den | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarDepthDenominator.starDepth_den <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.star_function_linear_on_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O) (K D : ℕ), IsCentreSet bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn | exact GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_matching_pieces_of_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, h₀.mem i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ p : Fin m₀ → LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) ∧
    (∀ i, 0 < t i → p i ∈ balForms bar X ∧ (∀ y, 0 ≤ p i y y) ∧
      (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = p i → k = 1) ∧
      ∀ lab : InvFun O, IsTwG w0 lab → lab.evalZ (p i) = lab.evalZ (δ₀ i)) ∧
    ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ → LinearIndependent ℤ δ →
      ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
        (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
        (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MatchingPieces.exists_pieces_match | exact GlobalTheory.CompanionTheory.Ar.Fan.MatchingPieces.exists_pieces_match | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MatchingPieces.exists_pieces_match <;> assumption)
end
