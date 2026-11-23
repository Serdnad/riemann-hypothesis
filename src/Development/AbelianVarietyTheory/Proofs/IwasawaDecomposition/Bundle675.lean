module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle651
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle657
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthUpperHalfLog
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle650
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle400
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle429
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle386
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle660
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle634
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.HolFrames

section Hol

open GlobalTheory.Points

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {T : Scheme.{0}}

theorem holTan_of_affine {U : T.Opens} (hU : IsAffineOpen U) (hB : IsOpen B) {z : V → (Sp (DualNumber ℂ) ⟶ T)}
    (hz : ∀ b ∈ B, ⊤ ≤ z b ⁻¹ᵁ U)
    (h₁ : ∀ a : Γ(T, U), DifferentiableOn ℂ (fun b => (valR (A := DualNumber ℂ) (z b) U a).fst) B)
    (h₂ : ∀ a : Γ(T, U), DifferentiableOn ℂ (fun b => (valR (A := DualNumber ℂ) (z b) U a).snd) B) : HolTan B z := by
  intro W f v hv
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (le_preimage_iff _ _).1 hv.2⟩
    ((le_preimage_iff _ _).1 (hz v hv.1))
  have key : ∀ b ∈ B, ⊤ ≤ z b ⁻¹ᵁ T.basicOpen h ↔ (valR (A := DualNumber ℂ) (z b) U h).fst ≠ 0 := fun b hb =>
    (le_preimage_basicOpen_iff _ (hz b hb) h).trans (TrivSqZeroExt.isUnit_iff_isUnit_fst.trans isUnit_iff_ne_zero)
  have hv0 := (key v hv.1).1 ((le_preimage_iff _ _).2 hh)
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((T.presheaf.map (homOfLE hhW).op).hom f)
  have d₁ := fun a => (h₁ a).differentiableAt (hB.mem_nhds hv.1)
  have d₂ := fun a => (h₂ a).differentiableAt (hB.mem_nhds hv.1)
  have nz : ∀ b ∈ B, (valR (A := DualNumber ℂ) (z b) U h).fst ≠ 0 →
      (valR (A := DualNumber ℂ) (z b) U (h ^ n)).fst ≠ 0 := fun b hb h0 => by
    rw [valR_pow _ _ (hz b hb), TrivSqZeroExt.fst_pow]
    exact pow_ne_zero n h0
  have di := (d₁ (h ^ n)).inv (nz v hv.1 hv0)
  have hq := ((d₂ a).sub (((d₁ a).mul di).mul (d₂ (h ^ n)))).mul di
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hB.mem_nhds hv.1, (d₁ h).continuousAt.eventually_ne hv0] with w hw hw0
  have hw1 := (key w hw).2 hw0
  have ha' : (T.presheaf.map (homOfLE hhW).op).hom f * (T.presheaf.map (homOfLE (T.basicOpen_le h)).op).hom h ^ n =
    (T.presheaf.map (homOfLE (T.basicOpen_le h)).op).hom a := ha
  have e := congrArg (valR (z w) (T.basicOpen h)) ha'
  rw [← map_pow, valR_mul _ _ hw1, valR_res _ _ hw1, valR_res _ _ hw1, valR_res _ _ hw1] at e
  have e₁ := congrArg TrivSqZeroExt.fst e
  have e₂ := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul] at e₁
  rw [DualNumber.snd_mul] at e₂
  have := nz w hw hw0
  simp only [Pi.inv_apply, Pi.sub_apply, Pi.mul_apply]
  rw [← e₁, ← e₂]
  field_simp
  ring

theorem holTan_dualMap {A : Type} [CommRing A] (hB : IsOpen B) (v : Sp (DualNumber A) ⟶ T) (ψ : ∀ b ∈ B, A →+* ℂ)
    (hψ : ∀ a, ∃ g : V → ℂ, DifferentiableOn ℂ g B ∧ ∀ b hb, ψ b hb a = g b) {w : V → (Sp (DualNumber ℂ) ⟶ T)}
    (hw : ∀ b hb, w b = spMap (dualMap (ψ b hb)) ≫ v) : HolTan B w := by
  classical
  by_cases hne : B.Nonempty
  swap
  · intro U f b hb
    exact (hne ⟨b, hb.1⟩).elim
  obtain ⟨b₀, hb₀⟩ := hne
  let ψ' : V → (A →+* ℂ) := fun b => if hb : b ∈ B then ψ b hb else ψ b₀ hb₀
  have e : ∀ b hb, ψ' b = ψ b hb := fun b hb => dite_eq_left hb
  have hd : ∀ a, DifferentiableOn ℂ (fun b => ψ' b a) B := fun a =>
    have ⟨g, hg, hg'⟩ := hψ a
    hg.congr fun b hb => by rw [e b hb, hg']
  have hv : ∀ b (a : DualNumber A), valR (spMap (dualMap (ψ' b))) ⊤
      ((Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom a) = dualMap (ψ' b) a := fun b a =>
    valR_specMap (CommRingCat.ofHom (dualMap (ψ' b))) a
  have hs : ∀ s : Γ(Sp (DualNumber A), ⊤), ∃ a, (Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom a = s := fun s =>
    ⟨(Scheme.ΓSpecIso (.of (DualNumber A))).hom.hom s, by simp⟩
  have h0 : HolTan B fun b => spMap (dualMap (ψ' b)) :=
    holTan_of_affine (isAffineOpen_top _) hB (fun b _ => le_preimage_top _)
      (fun s => by obtain ⟨a, rfl⟩ := hs s; simp only [hv]; simpa [dualMap] using hd a.fst)
      (fun s => by obtain ⟨a, rfl⟩ := hs s; simp only [hv]; simpa [dualMap] using hd a.snd)
  intro U f
  refine ((h0 (v ⁻¹ᵁ U) ((v.app U).hom f)).mono (s := {b ∈ B | ⊤ ≤ w b ⁻¹ᵁ U}) fun b hb => ⟨hb.1, ?_⟩).congr fun b hb => ?_
  · have := hb.2
    rw [hw b hb.1, ← e b hb.1] at this
    exact this
  · rw [hw b hb.1, ← e b hb.1, valR_comp]

theorem valR_eq_germ {C : Type} [CommRing C] [IsLocalRing C] (p : Sp C ⟶ T) (U : T.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    valMap p U h = T.presheaf.germ U _ ((le_preimage_iff p U).1 h) ≫ Scheme.stalkClosedPointTo (R := .of C) p := by
  rw [Scheme.germ_stalkClosedPointTo]
  rfl

end Hol

section Expo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)


end Expo

section Frames

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.CoordUniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_bc {A B : Type} [CommRing A] [CommRing B] {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x)
    (ψ : A →+* B) {φ' : c.F →+* B} {x' : Sp B ⟶ Z.X} (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) :
    ∃ g : EigFrame Z φ' x', ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ fr.v τ i := by
  subst hφ hx
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.Spread.exists_bc fr ψ rfl rfl
  exact ⟨g, fun τ i => congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) (hg τ i)⟩

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

end Frames


end GlobalTheory.ShFam.HolFrames
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.etaleChart_holomorphic_coordinate_change : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ)), DifferentiableOn ℂ ψ ψ.source → DifferentiableOn ℂ ψ.symm ψ.target → (∀ j, HolAlong (c.e.trans ψ).source fun x => (c.e.trans ψ) x j) ∧ IsHolTo (c.e.trans ψ).target (fun z => ((c.e.trans ψ).symm z).1) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.chart_change | exact GlobalTheory.ShFam.Hor.LogCh.chart_change | (intros; apply GlobalTheory.ShFam.Hor.LogCh.chart_change <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.punctPolydiscUniversalCover_open_convex_exp_analytic : ∀ (n a : ℕ), IsOpen (GlobalTheory.ShFam.Hor.logDom n a) ∧ Convex ℝ (GlobalTheory.ShFam.Hor.logDom n a) ∧ (∀ s, AnalyticAt ℂ (GlobalTheory.ShFam.Hor.logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧ Set.MapsTo (GlobalTheory.ShFam.Hor.logExp a) (GlobalTheory.ShFam.Hor.logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) := by
  first | exact @GlobalTheory.logDom_chart_props | exact GlobalTheory.logDom_chart_props | (intros; apply GlobalTheory.logDom_chart_props <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.two_markings_differ_by_level_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), (∀ i j Q Q', Per Fu a i Q → Per Fu a j Q' → i = j) ∧ ∀ i Q Q', Per Fu a i Q → Per Fu a i Q' → ∃ gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La, IsIsom (Fu.Di i) gm ∧ IsLev l (Fu.Di i) gm ∧ ∀ v, Q' (gm v) = Q v := by
  first | exact @GlobalTheory.ShFam.Hor.TwoMarkings.per_unique | exact GlobalTheory.ShFam.Hor.TwoMarkings.per_unique | (intros; apply GlobalTheory.ShFam.Hor.TwoMarkings.per_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw Di : Datum H) (τ : E →+* ℂ), Di.p = Dw.p ∧ Di.q = Dw.q → ∃ (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), IsPerBasis Di x hm := by
  first | exact @GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis | exact GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis | (intros; apply GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.exists_periods_in_frame_off_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), Inner a.1 → ∃ i Q, Per Fu a i Q := by
  first | exact @GlobalTheory.ShFam.Hor.exists_per | exact GlobalTheory.ShFam.Hor.exists_per | (intros; apply GlobalTheory.ShFam.Hor.exists_per <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem period_growth_mono_bound (x C : ℝ) (k K : ℕ) (hx : 0 ≤ x) (hk : k ≤ K) :
    C * (1 + x) ^ k ≤ max C 0 * (1 + x) ^ K := by
  have h1 : (1:ℝ) ≤ 1 + x := by linarith
  calc C * (1 + x) ^ k ≤ max C 0 * (1 + x) ^ k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + x) ^ K :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hk) (le_max_right _ _)

theorem period_matrix_polynomial_growth : ∀ (n a d : ℕ) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (c : Fin d → Fin d → ℂ), DifferentiableOn ℂ τ (logDom n a) → (∀ s ∈ logDom n a, ∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) → (∀ s ∈ logDom n a, ∀ i j, τ s i j - τ s j i = c i j) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a d τ c hτ hpos hc

  have key : ∀ v : Fin d → ℝ, v ≠ 0 → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 →
      (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) →
      ‖∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)‖ ≤ C * (1 + ‖s‖) ^ k := by
    intro v hv
    apply GlobalTheory.upper_half_growth n a
    · have hij : ∀ i j, DifferentiableOn ℂ (fun s => τ s i j) (logDom n a) :=
        fun i j => differentiableOn_pi.1 (differentiableOn_pi.1 hτ i) j
      fun_prop
    · intro s hs; exact hpos s hs v hv
  have e1 : ∀ (M : Fin d → Fin d → ℂ) (i : Fin d),
      ∑ i', ∑ j', (((Pi.single i (1:ℝ) : Fin d → ℝ) i' : ℝ) : ℂ) * M i' j' * (((Pi.single i (1:ℝ) : Fin d → ℝ) j' : ℝ) : ℂ) = M i i := by
    intro M i
    simp [Pi.single_apply, apply_ite Complex.ofReal, ite_mul, mul_ite, Finset.sum_ite_eq']
  have e2 : ∀ (M : Fin d → Fin d → ℂ) (i j : Fin d),
      ∑ i', ∑ j', ((((Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ)) i' : ℝ) : ℂ) * M i' j' * ((((Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ)) j' : ℝ) : ℂ) = M i i + M j j + M i j + M j i := by
    intro M i j
    simp [Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib, apply_ite Complex.ofReal, ite_mul, mul_ite, Finset.sum_ite_eq']
    ring
  have ne1 : ∀ i : Fin d, (Pi.single i (1:ℝ) : Fin d → ℝ) ≠ 0 := by
    intro i h
    have := congrFun h i
    simp at this
  have ne2 : ∀ i j : Fin d, (Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ) ≠ 0 := by
    intro i j h
    have := congrFun h i
    simp [Pi.single_apply] at this
    split_ifs at this <;> linarith

  have entry : ∀ i j : Fin d, ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 →
      (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s i j‖ ≤ C * (1 + ‖s‖) ^ k := by
    intro i j
    obtain ⟨C1, k1, h1⟩ := key _ (ne2 i j)
    obtain ⟨C2, k2, h2⟩ := key _ (ne1 i)
    obtain ⟨C3, k3, h3⟩ := key _ (ne1 j)
    refine ⟨(max C1 0 + max C2 0 + max C3 0 + ‖c i j‖) / 2, max k1 (max k2 k3), by positivity, ?_⟩
    intro s hs hl him
    set K := max k1 (max k2 k3)
    have hx : 0 ≤ ‖s‖ := norm_nonneg _
    have b1 := (h1 s hs hl him).trans (period_growth_mono_bound ‖s‖ C1 k1 K hx (by omega))
    have b2 := (h2 s hs hl him).trans (period_growth_mono_bound ‖s‖ C2 k2 K hx (by omega))
    have b3 := (h3 s hs hl him).trans (period_growth_mono_bound ‖s‖ C3 k3 K hx (by omega))
    rw [e2] at b1
    rw [e1] at b2 b3
    have hP : 1 ≤ (1 + ‖s‖) ^ K := one_le_pow₀ (by linarith)
    have hcc : ‖c i j‖ ≤ ‖c i j‖ * (1 + ‖s‖) ^ K := le_mul_of_one_le_right (norm_nonneg _) hP
    have hid : (2:ℂ) * τ s i j = (τ s i i + τ s j j + τ s i j + τ s j i) - τ s i i - τ s j j + c i j := by
      rw [← hc s hs i j]; ring
    have h2n : ‖(2:ℂ) * τ s i j‖ ≤ ‖τ s i i + τ s j j + τ s i j + τ s j i‖ + ‖τ s i i‖ + ‖τ s j j‖ + ‖c i j‖ := by
      rw [hid]
      refine (norm_add_le _ _).trans ?_
      gcongr
      refine (norm_sub_le _ _).trans ?_
      gcongr
      exact norm_sub_le _ _
    rw [norm_mul] at h2n
    norm_num at h2n
    nlinarith
  choose Ce ke hCe hke using entry
  refine ⟨∑ i, ∑ j, Ce i j, Finset.univ.sup (fun p : Fin d × Fin d => ke p.1 p.2), ?_⟩
  intro s hs hl him
  set K := Finset.univ.sup (fun p : Fin d × Fin d => ke p.1 p.2)
  have hx : 0 ≤ ‖s‖ := norm_nonneg _
  have hP : 0 ≤ (1 + ‖s‖) ^ K := by positivity
  have hS : 0 ≤ ∑ i, ∑ j, Ce i j := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hCe i j
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hk : ke i j ≤ K := Finset.le_sup (f := fun p : Fin d × Fin d => ke p.1 p.2) (Finset.mem_univ (i, j))
  have b := (hke i j s hs hl him).trans (period_growth_mono_bound ‖s‖ (Ce i j) (ke i j) K hx hk)
  rw [max_eq_left (hCe i j)] at b
  have hle : Ce i j ≤ ∑ i, ∑ j, Ce i j :=
    (Finset.single_le_sum (f := fun j => Ce i j) (fun j _ => hCe i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, Ce i j) (fun i _ => Finset.sum_nonneg fun j _ => hCe i j) (Finset.mem_univ i))
  exact b.trans (mul_le_mul_of_nonneg_right hle hP)

end GlobalTheory
end

section

open NumberField

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.TrueCx Topology Filter

noncomputable section

namespace GlobalTheory.LocInj

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domI : IsOpen (DomI ι p q) := by
  have hc : Continuous (flat : (ι → Matrix (Fin p) (Fin q) ℂ) → ι × Fin p × Fin q → ℂ) :=
    continuous_pi fun x => (continuous_apply x.1).matrix_elem x.2.1 x.2.2
  exact GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage hc

theorem continuousAt_moeb (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ)
    (hu : IsUnit (M.toBlocks₂₁ * z + M.toBlocks₂₂).det) :
    ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => moeb M w) z := by
  unfold moeb
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  have h1 : Continuous (fun w : Matrix (Fin p) (Fin q) ℂ => A * w + B) :=
    (continuous_const.matrix_mul continuous_id).add continuous_const
  have h2 : Continuous (fun w : Matrix (Fin p) (Fin q) ℂ => C * w + D) :=
    (continuous_const.matrix_mul continuous_id).add continuous_const
  have hi : ContinuousAt (Inv.inv : Matrix (Fin q) (Fin q) ℂ → Matrix (Fin q) (Fin q) ℂ) (C * z + D) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hu.ne_zero
  have h3 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (C * w + D)⁻¹) z :=
    ContinuousAt.comp (g := Inv.inv) hi h2.continuousAt
  have hm : Continuous (fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ => x.1 * x.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact ContinuousAt.comp (g := fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ => x.1 * x.2)
    (f := fun w => (A * w + B, (C * w + D)⁻¹)) hm.continuousAt (h1.continuousAt.prodMk h3)

theorem continuousAt_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : ι → Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ DomI ι p q) : ContinuousAt (moebI g) z := by
  refine continuousAt_pi.2 fun t => ?_
  have hu := GlobalTheory.HodgeDomain.kapQ_isUnit (hg t trivial) (hz t)
  exact ContinuousAt.comp (g := fun w => moeb ((g t : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) w)
    (continuousAt_moeb _ _ hu) (continuous_apply t).continuousAt

theorem moebI_one (z : ι → Matrix (Fin p) (Fin q) ℂ) : moebI (1 : ι → GL (Fin p ⊕ Fin q) ℂ) z = z := by
  funext t
  simp [moebI, GlobalTheory.TrueCx.PointWell.moeb_one]

end GlobalTheory.LocInj

namespace GlobalTheory.LocInj

open GlobalTheory.ShFam.SecFrame

theorem continuous_frameAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) {Tau : Type} (κ : Tau ≃ X.Ψ) : Continuous (frameAt X hj κ) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun z : Tau → Matrix (Fin j) (Fin (r - j)) ℂ =>
    mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1)
  refine continuous_const.matrix_mul ?_
  simp only [reindex_symm, reindex_apply, Equiv.symm_symm]
  exact (continuous_const.matrix_fromBlocks (continuous_apply _) continuous_const continuous_const).matrix_submatrix _ _

theorem locInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := by
  intro E _ _ _ r j X hj Tau _ κ hp z₀ hz₀
  haveI : LocallyCompactSpace (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Tau → Fin j → Fin (r - j) → ℂ))

  obtain ⟨C, hCn, hCD, hCc⟩ := local_compact_nhds (isOpen_domI.mem_nhds hz₀)
  set K := frameAt X hj κ '' C with hK
  have hKc : IsCompact K := hCc.image (continuous_frameAt X hj κ)
  have hKd : K ⊆ X.dom := by
    rintro _ ⟨z, hz, rfl⟩
    exact frameAt_mem X hj κ hp (hCD hz)
  have hS := GlobalTheory.T.finite_setOf_lact_eq_rmul_blockTriangular E r X K hKc hKd
  set S := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
    (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧
    (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
    ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b} with hSdef

  have hev : ∀ γ ∈ S, ∀ᶠ w in 𝓝 z₀ ×ˢ 𝓝 z₀, γ ≠ 1 → moebI (toUpq X hj κ γ) w.1 ≠ w.2 := by
    intro γ hγS
    by_cases h1 : γ = 1
    · exact Filter.Eventually.of_forall fun _ h => absurd h1 h
    have hne : moebI (toUpq X hj κ γ) z₀ ≠ z₀ := by
      intro h
      have hx := frameAt_mem X hj κ hp hz₀
      refine h1 (GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq E r j X hj Tau κ hp γ hγS.1 _ hx ?_)
      rw [domPt_lact X hj κ hp γ hx, domPt_frameAt, h]
    have hc : ContinuousAt (fun w : (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) × (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) =>
        moebI (toUpq X hj κ γ) w.1) (z₀, z₀) :=
      ContinuousAt.comp (g := moebI (toUpq X hj κ γ))
        (continuousAt_moebI (gammaU_le X hj κ hp ⟨γ, hγS.1, rfl⟩) hz₀) continuous_fst.continuousAt
    have hO : IsOpen {w : (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) × (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) |
        w.1 ≠ w.2} := isOpen_ne_fun continuous_fst continuous_snd
    have := (hc.prodMk continuous_snd.continuousAt).preimage_mem_nhds (hO.mem_nhds hne)
    rw [nhds_prod_eq] at this
    exact Filter.mem_of_superset this fun w hw _ => hw
  have hCC : C ×ˢ C ∈ 𝓝 z₀ ×ˢ 𝓝 z₀ := Filter.prod_mem_prod hCn hCn
  have hall : ∀ᶠ w in 𝓝 z₀ ×ˢ 𝓝 z₀, (fun a b => a ∈ C ∧ b ∈ C ∧ ∀ γ ∈ S, γ ≠ 1 → moebI (toUpq X hj κ γ) a ≠ b) w.1 w.2 :=
    (Filter.Eventually.and hCC ((Filter.eventually_all_finite hS).2 hev)).mono fun w h => ⟨h.1.1, h.1.2, h.2⟩
  obtain ⟨t, ht, htP⟩ := (Filter.eventually_prod_self_iff (la := 𝓝 z₀)
    (r := fun a b => a ∈ C ∧ b ∈ C ∧ ∀ γ ∈ S, γ ≠ 1 → moebI (toUpq X hj κ γ) a ≠ b)).1 hall
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht, ?_⟩
  rintro z ⟨hzt, hzD⟩ z' ⟨hzt', hzD'⟩ γ hγ e
  obtain ⟨hzC, hzC', hmove⟩ := htP z (interior_subset hzt) z' (interior_subset hzt')
  have hx := frameAt_mem X hj κ hp hzD
  have hy := frameAt_mem X hj κ hp hzD'
  have hgx := KU.lact_dom X hγ hx
  set x := frameAt X hj κ z
  set y := frameAt X hj κ z'
  have hpt : domPt X hj κ (lact γ x) = domPt X hj κ y := by
    rw [domPt_lact X hj κ hp γ hx, domPt_frameAt, domPt_frameAt, e]
  have hblk : ∀ τ (a c : Fin r), X.p0 ≤ a → (c : ℕ) < X.p0 → ((mat y τ)⁻¹ * mat (lact γ x) τ) a c = 0 := by
    intro τ
    refine GlobalTheory.TrueCx.PointWell.block_of_moeb_eq X hj hp hy hgx τ ?_
    obtain ⟨s, rfl⟩ := κ.surjective τ
    exact (congrFun hpt s).symm
  have hγS : γ ∈ S := by
    refine ⟨hγ, x, ⟨z, hzC, rfl⟩, y, ⟨z', hzC', rfl⟩, fun τ => (mat y τ)⁻¹ * mat (lact γ x) τ, fun τ => ?_,
      fun τ a c hc ha => hblk τ a c (not_lt.1 ha) hc, ?_⟩
    · show ((mat y τ)⁻¹ * mat (lact γ x) τ).det ≠ 0
      rw [det_mul, det_nonsing_inv]
      exact mul_ne_zero (by rw [Ring.inverse_eq_inv']; exact inv_ne_zero (hy τ).1) (hgx τ).1
    · funext τ
      show mat (lact γ x) τ = mat y τ * ((mat y τ)⁻¹ * mat (lact γ x) τ)
      rw [mul_nonsing_inv_cancel_left _ _ (hy τ).1.isUnit]
  by_contra hne
  by_cases h1 : γ = 1
  · subst h1
    apply hne
    rw [e, map_one, moebI_one]
  · exact hmove γ hγS h1 e.symm

end GlobalTheory.LocInj
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_ideal_map_of_germs_affineScheme : ∀ {T Y' : Scheme.{0}} [IsAffine T] (χ : T ⟶ Y') (I : Y'.IdealSheafData) (W : Y'.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ (W : Y'.Opens)) (s : Γ(T, ⊤)), (∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ FinalTheorems.stalkId (I.comap χ) t) → s ∈ (I.ideal W).map (χ.appLE W ⊤ hle).hom := by
  first | exact @GlobalTheory.GermAff.mem_map_of_germ | exact GlobalTheory.GermAff.mem_map_of_germ | (intros; apply GlobalTheory.GermAff.mem_map_of_germ <;> assumption)
end
