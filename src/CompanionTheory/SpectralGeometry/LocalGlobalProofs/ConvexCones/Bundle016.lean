module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle686
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle726
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle713
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle712
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle696
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExistsMarkedFormInCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle735
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle725
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle746
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle727
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle734
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

section SlopeTestRemainingChoices

variable {X : Type} [AddCommGroup X]

theorem IsMin2.add {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (h : IsMin2 B y) (h' : IsMin2 B' y) : IsMin2 (B + B') y :=
  fun x => by
    simpa only [LinearMap.add_apply] using add_le_add (h x) (h' x)

theorem IsMin2.smul {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (h : IsMin2 B y) {t : ℝ} (ht : 0 ≤ t) : IsMin2 (t • B) y :=
  fun x => by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left (h x) ht

theorem isPosDef_smul_of_pos {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : IsPosDef B) {t : ℝ} (ht : 0 < t) : IsPosDef (t • B) :=
  fun n x hx c hc => by
    have key : ∑ i, ∑ j, c i * c j * (t • B) (x i) (x j) = t * ∑ i, ∑ j, c i * c j * B (x i) (x j) := by
      simp only [LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [key]
    exact mul_pos ht (h n x hx c hc)

theorem rcone_subset_sigma {k : ℕ} {s : Fin k → ℕ} (γ : ∀ j, Fin (s j) → LinearMap.BilinForm ℤ X) {N : ℕ}
    (e : (Σ j, Fin (s j)) ≃ Fin N) (j : Fin k) :
    rcone (γ j) ⊆ rcone (fun i => γ (e.symm i).1 (e.symm i).2) := by
  rintro B ⟨t, ht, rfl⟩
  have hinj : Function.Injective (fun b : Fin (s j) => (⟨j, b⟩ : Σ j, Fin (s j))) := fun b c h => by simpa using h
  let T : (Σ j, Fin (s j)) → ℝ := Function.extend (fun b : Fin (s j) => (⟨j, b⟩ : Σ j, Fin (s j))) t 0
  have hT : ∀ b, T ⟨j, b⟩ = t b := fun b => hinj.extend_apply t 0 b
  have hT0 : ∀ a, a ≠ j → ∀ b, T ⟨a, b⟩ = 0 := fun a ha b => by
    refine (Function.extend_apply' _ _ _ ?_).trans rfl
    rintro ⟨c, hc⟩
    exact ha (congrArg Sigma.fst hc).symm
  have hTn : ∀ p, 0 ≤ T p := fun ⟨a, b⟩ => by
    by_cases ha : a = j
    · subst ha
      rw [hT]
      exact ht b
    · rw [hT0 a ha]
  refine ⟨fun i => T (e.symm i), fun i => hTn _, ?_⟩
  rw [e.symm.sum_comp (fun p => T p • toReal (γ p.1 p.2)), Fintype.sum_sigma,
    Finset.sum_eq_single j (fun a _ ha => Finset.sum_eq_zero fun b _ => by rw [hT0 a ha, zero_smul])
      (fun h => (h (Finset.mem_univ j)).elim)]
  exact Finset.sum_congr rfl fun b _ => by rw [hT]

end SlopeTestRemainingChoices

theorem isSpanned_contact_of_posDef : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), HasRedCover bar X → Covers2 a → (∃ B₀ ∈ contact bar a, IsPosDef B₀) → IsSpanned bar (contact bar a) := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a hR hC ⟨B₀, hB₀, hd⟩
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨k, m, u, hsym, hnn, hcov⟩ := GlobalTheory.T.exists_psd_forms_cover_contact_set O bar X ι a hR hC
  choose s γ hbal hγnn hγK hsub using fun j => GlobalTheory.T.exists_balanced_forms_dominating O bar X ι a (m j) (u j) (hsym j) (hnn j)
  let e := Fintype.equivFin (Σ j, Fin (s j))
  refine ⟨_, fun i => γ (e.symm i).1 (e.symm i).2, fun i => hbal _ _, fun i y => hγnn _ _ _, fun i => hγK _ _,
    fun B hB => ?_⟩
  refine GlobalTheory.T.mem_rational_cone_of_perturbation X _ _ B B₀ fun ε hε => ?_
  have hεd : IsPosDef (ε • B₀) := isPosDef_smul_of_pos hd hε
  have hεr : ε • B₀ ∈ realForms bar X := (realForms bar X).smul_mem ε (mem_realForms_of_mem_psdCone hB₀.1)
  obtain ⟨hpd, hps⟩ := isPosDef_add_and_mem_psdCone O bar X B (ε • B₀) hB.1 hεr hεd
  have hmem : B + ε • B₀ ∈ contact bar a := ⟨hps, fun i => (hB.2 i).add ((hB₀.2 i).smul hε.le)⟩
  obtain ⟨j, hj⟩ := hcov _ hmem hpd
  exact rcone_subset_sigma γ e j (hsub j _ hmem hj)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan

theorem isPolyFan_star : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → IsStarOf bar q ψ w ψ' → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, ψ'.evalZ β = n) → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ψ'.evalZ β) → IsPolyFan bar q ψ' := by
  intro O _ _ _ _ bar hO q ψ w ψ' hψ hc hs hint hpos
  unfold GlobalTheory.PolFan.IsPolyFan
  intro X _ _ _ _ hX
  obtain ⟨S, hSf, hS⟩ := GlobalTheory.CompanionTheory.Ar.Fan.StarFiniteCover.isStarOf_finite_cover O bar hO q ψ w ψ' hψ hc hs X hX
  refine ⟨GlobalTheory.PolFan.StarFan.homog_of_cover O bar ψ' X ?_, GlobalTheory.T.superadditive_of_cells_cover_cone O bar ψ' X ?_, hint X hX, hpos X hX,
    ⟨S, hSf, hS⟩⟩
  all_goals
    intro B hB
    obtain ⟨e, m, γ, c, h1, -, h3, h4⟩ := hS B hB
    exact ⟨e, m, γ, c, h1, h3, h4⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.exists_pullback_coordinate_of_pos : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
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
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.PullbackCoordinates.exists_coord_pullAdd_of_pos | exact GlobalTheory.CompanionTheory.Ar.Fan.PullbackCoordinates.exists_coord_pullAdd_of_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.PullbackCoordinates.exists_coord_pullAdd_of_pos <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.pullback_mem_cell_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
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
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.PullbackInCellCone.inRCone_pullAdd_of_isCell | exact GlobalTheory.CompanionTheory.Ar.Fan.PullbackInCellCone.inRCone_pullAdd_of_isCell | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.PullbackInCellCone.inRCone_pullAdd_of_isCell <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
open _root_.GlobalTheory.PolFan.Mark.Exist

namespace GlobalTheory.CompanionTheory.Ar.Fan.MarkedRayInCone

section Face

variable {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O} {q : ℕ}
  {ψ lab : InvFun O} {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]

theorem inFace_iff (hb : CMOrd O bar) (hψ : IsPolyFan bar q ψ) (hl : IsCarrierDim bar q ψ lab)
    (hX : Module.finrank O X ≤ q) (hD : _root_.GlobalTheory.PolFan.Dominates bar X) {m : ℕ} {τ : Fin m → LinearMap.BilinForm ℤ X}
    (hτ : IsCell bar ψ τ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone τ β) (hr : (genRank τ : ℝ) ≤ lab.evalZ β)
    (x : LinearMap.BilinForm ℤ X) :
    InFace bar ψ lab β x ↔ InRCone τ x := by
  have b1 := cone_bal hτ.mem hβ
  have b2 := cone_nonneg hτ.nonneg hβ
  constructor
  · rintro ⟨h1, h2, -, h4, h5⟩
    exact GlobalTheory.T.psd_balanced_form_mem_cell_cone O bar hb q ψ lab hψ hl X hX hD m τ hτ β b1 b2 hβ x h1 h2 h4 h5
  · intro hx
    have hs := cone_add hβ hx
    refine ⟨cone_bal hτ.mem hx, cone_nonneg hτ.nonneg hx, fun y hy => cone_vanish hx fun j =>
      GlobalTheory.T.psd_balanced_form_vanishes_low_rank O bar hb q ψ lab hψ hl X hX hD m τ hτ β b1 b2 hβ hr j y hy,
      evalZ_add_of_linearOn_inRCone _ ψ X m τ hτ.linear _ _ hβ hx, le_antisymm ((lab_le hl hX hτ hs).trans hr) ?_⟩
    obtain ⟨c, hc, e⟩ := hx
    refine carrierDim_le_of_add_cell _ bar q ψ lab hl X hX m τ hτ β b1 b2 _ (cone_bal hτ.mem hs)
      (cone_nonneg hτ.nonneg hs) hβ 1 c one_pos hc ?_
    rw [← e]
    exact LinearMap.ext₂ fun a b => by simp

theorem isIndec_iff (hb : CMOrd O bar) (hψ : IsPolyFan bar q ψ) (hl : IsCarrierDim bar q ψ lab)
    (hX : Module.finrank O X ≤ q) (hD : _root_.GlobalTheory.PolFan.Dominates bar X) {m : ℕ} {τ : Fin m → LinearMap.BilinForm ℤ X}
    (hτ : IsCell bar ψ τ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone τ β) (hr : (genRank τ : ℝ) ≤ lab.evalZ β)
    (x : LinearMap.BilinForm ℤ X) :
    IsIndec bar ψ lab β x ↔
      InRCone τ x ∧ x ≠ 0 ∧ ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x := by
  simp only [IsIndec, inFace_iff hb hψ hl hX hD hτ hβ hr]

end Face

theorem exists_isMarked_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], _root_.GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ : LinearMap.BilinForm ℤ X, IsMarked bar ψ lab i X β₀ ∧ InRCone v β₀ := by
  intro O _ _ _ _ bar hbar q ψ lab i hDom hψ hl X _ _ _ _ hX m v hv β hb hp hvβ hlab
  classical
  have hD := hDom X
  have hfan := hψ X hX
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, τ, hτ, hβ, hr⟩ := exists_min hl hX hv hvβ
  have hF := inFace_iff hbar hψ hl hX hD hτ hβ hr.le
  have hI := isIndec_iff hbar hψ hl hX hD hτ hβ hr.le
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have h0 : ∀ j, τ j = 0 := fun j => eq_zero_of_diag (hτ.mem j).1 fun y =>
      GlobalTheory.T.psd_balanced_form_vanishes_low_rank O bar hbar q ψ lab hψ hl X hX hD n τ hτ 0 hb hp hβ hr.le j y rfl
    have h1 : Submodule.span ℤ (Set.range τ) = ⊥ := Submodule.span_eq_bot.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
    have h2 : genRank τ = 0 := by rw [genRank, h1, finrank_bot]
    rw [h2, hlab] at hr
    have : (0 : ℕ) = i + 1 := by exact_mod_cast hr
    omega
  have hfin := finite_indec_inRCone X n τ
  set S := hfin.toFinset with hSdef
  have hS : ∀ x, x ∈ S ↔ InRCone τ x ∧ x ≠ 0 ∧ ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x :=
    fun x => by simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hSτ : ∀ x ∈ S, InRCone τ x := fun x hx => ((hS x).1 hx).1
  have hcl : β ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y} :=
    GlobalTheory.T.mem_closure_sum_indecomposable_face_of_additive _ bar ψ lab X β
      (fun x y hx hy => ⟨(hF _).2 (cone_add ((hF _).1 hx) ((hF _).1 hy)),
        evalZ_add_of_linearOn_inRCone _ ψ X n τ hτ.linear _ _ ((hF _).1 hx) ((hF _).1 hy)⟩)
      (fun x hx => hfan.integral x hx.1 hx.2.1) (fun x hx h0 => hfan.pos x hx.1 hx.2.1 h0) β ((hF _).2 hβ)
  have hadd := evalZ_sum hτ.linear S hSτ
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : {y | IsIndec bar ψ lab β y} = ∅ := Set.eq_empty_of_forall_notMem fun y hy => by
      have := (hS y).2 ((hI y).1 hy)
      rw [h] at this
      exact Finset.notMem_empty _ this
    rw [this, AddSubmonoid.closure_empty, AddSubmonoid.mem_bot] at hcl
    exact hβ0 hcl
  have hσ : ∑ x ∈ S, x ≠ 0 := fun h => by
    rw [h, evalZ_zero'] at hadd
    refine (Finset.sum_pos (fun x hx => ?_) hne).ne hadd
    exact hfan.pos x (cone_bal hτ.mem (hSτ x hx)) (cone_nonneg hτ.nonneg (hSτ x hx)) ((hS x).1 hx).2.1
  obtain ⟨g, β₀, hg, hgβ, hprim⟩ := GlobalTheory.bilinForm_exists_primitive_of_ne_zero X _ hσ
  have hτ0 : InRCone τ β₀ := (cone_smul_iff hg).1 (hgβ ▸ cone_sum hSτ)
  have hge : lab.evalZ β ≤ lab.evalZ β₀ := by
    obtain ⟨k, γ, hγ, hγ0, hrγ⟩ := exists_min hl hX hτ hτ0
    have hσγ : InRCone γ (∑ x ∈ S, x) := hgβ ▸ (cone_smul_iff hg).2 hγ0
    let u : Fin S.card → LinearMap.BilinForm ℤ X := fun j => (S.equivFin.symm j : LinearMap.BilinForm ℤ X)
    have hu : ∀ {M : Type} [AddCommMonoid M] (f : LinearMap.BilinForm ℤ X → M), ∑ j, f (u j) = ∑ x ∈ S, f x :=
      fun f => by
        rw [← Finset.sum_coe_sort S f]
        exact S.equivFin.symm.sum_comp fun x => f x
    have hu1 : ∑ j, u j = ∑ x ∈ S, x := hu fun x => x
    have huτ : ∀ j, InRCone τ (u j) := fun j => hSτ _ (S.equivFin.symm j).2
    have hall := inRCone_of_evalZ_sum_le _ bar ψ X k γ hγ _ u (fun j => cone_bal hτ.mem (huτ j))
      (fun j => cone_nonneg hτ.nonneg (huτ j)) (by rw [hu1]; exact hσγ) (by rw [hu1, hu ψ.evalZ, hadd])
    have hSγ : ∀ x ∈ S, InRCone γ x := fun x hx => by
      simpa [u] using hall (S.equivFin ⟨x, hx⟩)
    have hβγ : InRCone γ β := AddSubmonoid.closure_induction (motive := fun x _ => InRCone γ x)
      (fun x hx => hSγ x ((hS x).2 ((hI x).1 hx))) cone_zero (fun _ _ _ _ => cone_add) hcl
    exact (lab_le hl hX hγ hβγ).trans hrγ.le
  have hle : lab.evalZ β₀ ≤ lab.evalZ β := (lab_le hl hX hτ hτ0).trans hr.le
  refine ⟨β₀, ⟨cone_bal hτ.mem hτ0, cone_nonneg hτ.nonneg hτ0, hprim, (le_antisymm hle hge).trans hlab, S,
    fun x => (hS x).trans (isIndec_iff hbar hψ hl hX hD hτ hτ0 (hr.le.trans hge) x).symm, g, hg, hgβ⟩, ?_⟩
  refine (cone_smul_iff hg).1 (hgβ ▸ cone_sum fun x hx => ?_)
  obtain ⟨h1, h2, -, h4, h5⟩ := (hF x).2 (hSτ x hx)
  exact GlobalTheory.T.psd_balanced_form_mem_cell_cone O bar hbar q ψ lab hψ hl X hX hD m v hv β hb hp hvβ x h1 h2 h4 h5

end GlobalTheory.CompanionTheory.Ar.Fan.MarkedRayInCone
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces

theorem genRank_le_of_label_le {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (q : ℕ)
    (ψ lab : InvFun O) (i : ℕ) (hlab : IsCarrierDim bar q ψ lab)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) {m : ℕ} (v : Fin m → LinearMap.BilinForm ℤ X) (hv : IsCell bar ψ v)
    (hb : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) :
    genRank v ≤ i + 1 := by
  set σ := ∑ j, v j with hσ
  have hσ1 : σ ∈ balForms bar X := Submodule.sum_mem _ fun j _ => hv.mem j
  have hσ2 : ∀ y, 0 ≤ σ y y := fun y => by
    simp only [hσ, LinearMap.sum_apply]; exact Finset.sum_nonneg fun j _ => hv.nonneg j y
  have hσv : InRCone v σ := ⟨fun _ => 1, fun _ => zero_le_one, toReal_sum' v⟩
  have hl := hb σ hσ1 hσ2 hσv
  rw [hlab X hX σ hσ1 hσ2] at hl
  have hS : ({k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ σ ∧
      genRank γ = k}).Nonempty := ⟨_, m, v, hv, hσv, rfl⟩
  obtain ⟨m', γ, hγ, hσγ, hrk⟩ := Nat.sInf_mem hS
  have hψσ : ψ.evalZ σ = ∑ j, ψ.evalZ (v j) := by
    have := (linearOn_iff ψ v).1 hv.linear (fun _ => 1) fun _ => zero_le_one
    rw [← toReal_sum', evalR_toReal] at this
    simpa using this
  have hin := GlobalTheory.T.inRealCone_summands_of_evalZ_additive_cell O bar ψ X m' γ hγ m v hv.mem hv.nonneg hσγ hψσ.le
  have hr := GlobalTheory.T.spanRank_le_of_inRealCone_polyhedralCell O bar ψ X m' m γ v hγ hv.mem hv.nonneg hin
  have h2 : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ σ ∧
      genRank γ = k} ≤ i + 1 := by exact_mod_cast hl
  rw [hrk] at hr
  exact hr.trans h2

theorem inFace_iff_of_isMarked {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (hO : CMOrd O bar) (q : ℕ)
    (ψ lab : InvFun O) (i : ℕ) (hψ : IsPolyFan bar q ψ) (hlab : IsCarrierDim bar q ψ lab)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) (hDom : _root_.GlobalTheory.PolFan.Dominates bar X) {m : ℕ} (v : Fin m → LinearMap.BilinForm ℤ X)
    (hv : IsCell bar ψ v)
    (hb : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ))
    {β : LinearMap.BilinForm ℤ X} (hβ : IsMarked bar ψ lab i X β) (hβv : InRCone v β) (x : LinearMap.BilinForm ℤ X) :
    InFace bar ψ lab β x ↔ x ∈ balForms bar X ∧ (∀ y, 0 ≤ x y y) ∧ InRCone v x := by
  obtain ⟨hβ1, hβ2, -, hβl, -⟩ := hβ
  constructor
  · rintro ⟨hx1, hx2, -, hx4, hx5⟩
    exact ⟨hx1, hx2, GlobalTheory.T.psd_balanced_form_mem_cell_cone O bar hO q ψ lab hψ hlab X hX hDom m v hv β hβ1 hβ2 hβv x hx1 hx2 hx4 hx5⟩
  · rintro ⟨hx1, hx2, hxv⟩
    have hrk := genRank_le_of_label_le bar q ψ lab i hlab X hX v hv hb
    have hvan := GlobalTheory.T.psd_balanced_form_vanishes_low_rank O bar hO q ψ lab hψ hlab X hX hDom m v hv β hβ1 hβ2 hβv (by rw [hβl]; exact_mod_cast hrk)
    have hsum := inRCone_add' hβv hxv
    have hs1 : β + x ∈ balForms bar X := add_mem hβ1 hx1
    have hs2 : ∀ y, 0 ≤ (β + x) y y := fun y => by
      simp only [LinearMap.add_apply]; exact add_nonneg (hβ2 y) (hx2 y)
    refine ⟨hx1, hx2, fun y hy => inRCone_apply_self_eq_zero hxv y fun j => hvan j y hy,
      GlobalTheory.T.invFun_evalZ_add_of_linearOn_realCone O ψ X m v hv.linear β x hβv hxv, le_antisymm ?_ ?_⟩
    · rw [hβl]; exact hb _ hs1 hs2 hsum
    · obtain ⟨c, hc, e⟩ := hxv
      exact carrierDim_le_of_add_cell O bar q ψ lab hlab X hX m v hv β hβ1 hβ2 (β + x) hs1 hs2 hβv 1 c one_pos hc
        (by rw [toReal_add', e, one_smul])

theorem eq_of_isMarked_of_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], _root_.GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β β' : LinearMap.BilinForm ℤ X, IsMarked bar ψ lab i X β → IsMarked bar ψ lab i X β' → InRCone v β → InRCone v β' → β = β' := by
  intro O _ _ _ _ bar hO q ψ lab i hDom hψ hlab X _ _ _ _ hX m v hv hb β β' hβ hβ' hβv hβ'v
  have hiff : ∀ x, InFace bar ψ lab β x ↔ InFace bar ψ lab β' x := fun x => by
    rw [inFace_iff_of_isMarked bar hO q ψ lab i hψ hlab X hX (hDom X) v hv hb hβ hβv x,
      inFace_iff_of_isMarked bar hO q ψ lab i hψ hlab X hX (hDom X) v hv hb hβ' hβ'v x]
  have hind : ∀ x, IsIndec bar ψ lab β x ↔ IsIndec bar ψ lab β' x := fun x => by
    simp only [IsIndec, hiff]
  obtain ⟨-, -, hp, -, S, hS, k, hk, hkS⟩ := hβ
  obtain ⟨-, -, hp', -, S', hS', k', -, hkS'⟩ := hβ'
  have hSS : S = S' := Finset.ext fun x => by rw [hS, hS', hind]
  exact eq_of_primitive_of_smul_eq hp hp' hk (by rw [hkS, hkS', hSS])

end GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces
end
end
