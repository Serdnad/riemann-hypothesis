module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle077
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle012
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle075
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsCurveThroughSpecialPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle038
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.eq_of_eq_generic_projective : ∀ (R : Type) [CommRing R] (Z W : Scheme.{0}) [IsIntegral Z] (s : W ⟶ Sp R) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (f g : Z ⟶ W), IsProjOver s → (∀ q : Z, genPt ξ ⤳ q) → ξ ≫ f = ξ ≫ g → f = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic | exact GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem top_le_iff_centre (y : Sp ℂ ⟶ X) (U : X.Opens) : ⊤ ≤ y ⁻¹ᵁ U ↔ centre y ∈ U :=
  ⟨fun h => h trivial, fun h => (Scheme.preimage_eq_top_of_closedPoint_mem y h).ge⟩

theorem val_germ (y : Sp ℂ ⟶ X) (N : X.Opens) (h : centre y ∈ N) (v : Γ(X, N)) :
    (Scheme.stalkClosedPointTo y).hom (X.presheaf.germ N (centre y) h v) = valAt' y N v := by
  have e := congrArg (fun q => q.hom v) (germ_stalkClosedPointTo_eq y N h)
  rw [valAt'_of _ _ ((top_le_iff_centre y N).2 h)]
  simp only [valAt]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

def genV (ξ : Sp Ω ⟶ X) (N : X.Opens) (h : genPt ξ ∈ N) : Γ(X, N) →+* Ω :=
  ((X.presheaf.germ N (genPt ξ) h) ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (N : X.Opens) {q : X} (hq : genPt ξ ⤳ q) (hN : q ∈ N) (h : genPt ξ ∈ N) (v : Γ(X, N)) :
    genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q hN v) = genV ξ N h v := by
  have e := X.presheaf.germ_stalkSpecializes hN hq
  simp only [genMap, genV]
  rw [← e]
  rfl

theorem genPt_mem {N : X.Opens} {q : X} (hq : genPt ξ ⤳ q) (hN : q ∈ N) : genPt ξ ∈ N :=
  hq.mem_open N.isOpen hN

theorem ValAt.of_section {y : Sp ℂ ⟶ X} {N : X.Opens} (hy : centre y ∈ N) (h : genPt ξ ⤳ centre y) {v : Γ(X, N)}
    {a : Ω} (ha : genMap ξ ⟨centre y, h⟩ (X.presheaf.germ N (centre y) hy v) = a) :
    ValAt ξ y a (valAt' y N v) :=
  ⟨h, _, ha, val_germ y N hy v⟩

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem ValAt.unique (hξ : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h₁, s, hs, rfl⟩ := h
  obtain ⟨h₂, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h₁⟩ (hs.trans hs'.symm)]

theorem ValAt.mul {z : Spec (CommRingCat.of R) ⟶ X} {a b : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z b r') : ValAt ξ z (a * b) (r * r') := by
  obtain ⟨h₁, s, hs, rfl⟩ := h
  obtain ⟨h₂, s', hs', rfl⟩ := h'
  exact ⟨h₁, s * s', by rw [map_mul, hs]; congr 1, map_mul _ _ _⟩

theorem ValAt.one {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) :=
  ⟨h, 1, map_one _, map_one _⟩

theorem ValAt.exists_of_mem {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

theorem ValAt.exists_ne_zero (hξ : IsCptGen ξ) {z : Sp ℂ ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : unitAt ξ ⟨centre z, h⟩ a) : ∃ r : ℂ, r ≠ 0 ∧ ValAt ξ z a r := by
  obtain ⟨r, hr⟩ := ValAt.exists_of_mem h ha.2.1
  obtain ⟨r', hr'⟩ := ValAt.exists_of_mem h ha.2.2
  have e := ValAt.unique hξ (ValAt.mul hr hr') (by rw [mul_inv_cancel₀ ha.1]; exact ValAt.one h)
  exact ⟨r, left_ne_zero_of_mul_eq_one e, hr⟩

theorem exists_section {q : X} (h : genPt ξ ⤳ q) {a : Ω} (ha : a ∈ regAt ξ ⟨q, h⟩) (M : X.Opens) (hM : q ∈ M) :
    ∃ (N : X.Opens) (hq : q ∈ N) (v : Γ(X, N)), N ≤ M ∧ genMap ξ ⟨q, h⟩ (X.presheaf.germ N q hq v) = a := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨N, hq, v, hv⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf s
  refine ⟨N ⊓ M, ⟨hq, hM⟩, X.presheaf.map (homOfLE inf_le_left).op v, inf_le_right, ?_⟩
  have e : X.presheaf.germ (N ⊓ M) q ⟨hq, hM⟩ (X.presheaf.map (homOfLE inf_le_left).op v) =
      X.presheaf.germ N q hq v := TopCat.Presheaf.germ_res_apply _ _ _ _ _
  exact congrArg (genMap ξ ⟨q, h⟩) (e.trans hv)

theorem exists_unit_section (hξ : IsCptGen ξ) {q : X} (h : genPt ξ ⤳ q) {a : Ω} (ha : unitAt ξ ⟨q, h⟩ a)
    (M : X.Opens) (hM : q ∈ M) :
    ∃ (N : X.Opens) (hq : q ∈ N) (v : Γ(X, N)), N ≤ M ∧ IsUnit v ∧
      genMap ξ ⟨q, h⟩ (X.presheaf.germ N q hq v) = a := by
  obtain ⟨N₁, h₁, v, l₁, e₁⟩ := exists_section h ha.2.1 M hM
  obtain ⟨N₂, h₂, w, l₂, e₂⟩ := exists_section h ha.2.2 M hM
  let i₁ : N₁ ⊓ N₂ ⟶ N₁ := homOfLE inf_le_left
  let i₂ : N₁ ⊓ N₂ ⟶ N₂ := homOfLE inf_le_right
  have hq : q ∈ N₁ ⊓ N₂ := ⟨h₁, h₂⟩
  have g₁ : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₁.op v) = X.presheaf.germ N₁ q h₁ v :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have g₂ : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₂.op w) = X.presheaf.germ N₂ q h₂ w :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have one : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₁.op v * X.presheaf.map i₂.op w) =
      X.presheaf.germ (N₁ ⊓ N₂) q hq 1 := by
    apply hξ.inj ⟨q, h⟩
    rw [map_mul, g₁, g₂, map_mul, e₁, e₂, mul_inv_cancel₀ ha.1, map_one, map_one]
  obtain ⟨N₃, h₃, j₁, j₂, e₃⟩ := TopCat.Presheaf.germ_eq X.presheaf q hq hq _ _ one
  have hj : j₁ = j₂ := Subsingleton.elim _ _
  subst hj
  refine ⟨N₃, h₃, X.presheaf.map (j₁ ≫ i₁).op v, (leOfHom (j₁ ≫ i₁)).trans l₁, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one (X.presheaf.map (j₁ ≫ i₂).op w) ?_
    rw [map_mul, map_one] at e₃
    simpa [op_comp, Functor.map_comp] using e₃
  · rw [TopCat.Presheaf.germ_res_apply, e₁]

theorem unitAt_div_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {a b : Ω} (ha : Λ.IsGenAt p a) (hb : Λ.IsGenAt p b) :
    unitAt ξ p (b / a) := by
  have h₁ : b ∈ Submodule.span (regAt ξ p) {a} := by
    rw [← ha.2, hb.2]; exact Submodule.mem_span_singleton_self b
  have h₂ : a ∈ Submodule.span (regAt ξ p) {b} := by
    rw [← hb.2, ha.2]; exact Submodule.mem_span_singleton_self a
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h₁
  obtain ⟨e, he⟩ := Submodule.mem_span_singleton.1 h₂
  have hc' : (c : Ω) * a = b := hc
  have he' : (e : Ω) * b = a := he
  refine ⟨div_ne_zero hb.1 ha.1, ?_, ?_⟩
  · rw [← hc', mul_div_cancel_right₀ _ ha.1]; exact c.2
  · rw [inv_div, ← he', mul_div_cancel_right₀ _ hb.1]; exact e.2

theorem isGenAt_mul_of_unitAt {Λ : Lat ξ Ω} {p : Cpt ξ} {a u : Ω} (ha : Λ.IsGenAt p a) (hu : unitAt ξ p u) :
    Λ.IsGenAt p (u * a) := by
  refine ⟨mul_ne_zero hu.1 ha.1, ?_⟩
  rw [ha.2]
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨⟨u⁻¹, hu.2.2⟩, ?_⟩
    show u⁻¹ * (u * a) = a
    rw [← _root_.mul_assoc, inv_mul_cancel₀ hu.1, _root_.one_mul]
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨u, hu.2.1⟩, rfl⟩

structure IsChart (s : X ⟶ Sp ℂ) {d : ℕ} (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) : Prop where
  isOpen : IsOpen B
  hol : IsHolTo B Y
  isOver : ∀ b ∈ B, Y b ≫ s = 𝟙 _
  factor : ∀ (m : ℕ) (B' : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B' → IsHolTo B' y →
    (∀ b ∈ B', y b ≫ s = 𝟙 _) → ∀ b₀ ∈ B', ∀ b₁ ∈ B, y b₀ = Y b₁ →
    ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B' ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧
      κ b₀ = b₁ ∧ ∀ b ∈ ball b₀ ε, κ b ∈ B ∧ y b = Y (κ b)

theorem IsChart.mono {s : X ⟶ Sp ℂ} {d : ℕ} {B B₂ : Set (Fin d → ℂ)} {Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)}
    (h : IsChart s B Y) (o : IsOpen B₂) (l : B₂ ⊆ B) : IsChart s B₂ Y := by
  refine { isOpen := o, hol := ?_, isOver := fun b hb => h.isOver b (l hb), factor := ?_ }
  · intro U f
    have e : {b ∈ B₂ | ⊤ ≤ Y b ⁻¹ᵁ U} = B₂ ∩ {b ∈ B | ⊤ ≤ Y b ⁻¹ᵁ U} := by
      ext b; exact ⟨fun hb => ⟨hb.1, l hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
    rw [e]
    exact ⟨o.inter (h.hol U f).1, (h.hol U f).2.mono Set.inter_subset_right⟩
  · intro m B' y oB hy ov b₀ h₀ b₁ h₁ e
    obtain ⟨ε, κ, ε0, sub, dκ, k₀, hκ⟩ := h.factor m B' y oB hy ov b₀ h₀ b₁ (l h₁) e
    have c : ContinuousAt κ b₀ := (dκ.differentiableAt (ball_mem_nhds _ ε0)).continuousAt
    have m₂ : κ ⁻¹' B₂ ∈ 𝓝 b₀ := c.preimage_mem_nhds (o.mem_nhds (k₀ ▸ h₁))
    obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem m₂ (ball_mem_nhds b₀ ε0))
    have sb : ball b₀ δ ⊆ ball b₀ ε := fun b hb => (hδ hb).2
    exact ⟨δ, κ, δ0, sb.trans sub, dκ.mono sb, k₀, fun b hb => ⟨(hδ hb).1, (hκ b (sb hb)).2⟩⟩

structure HChart (s : X ⟶ Sp ℂ) (ξ : Sp Ω ⟶ X) (W U : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T : Ω) {d : ℕ}
    (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) : Prop where
  chart : IsChart s B Y
  inU : ∀ b ∈ B, centre (Y b) ∈ U
  cpt : ∀ b ∈ B, genPt ξ ⤳ centre (Y b)
  dense : ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W
  hol : DifferentiableOn ℂ H B
  ne : ∀ b ∈ B, H b ≠ 0
  rel : ∀ b ∈ B, centre (Y b) ∈ W → ∀ r : ℂ, ValAt ξ (Y b) T r → F (Y b) = H b * r

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtTorPull

theorem spMap_comp_fields {A B C : Type} [Field A] [Field B] [Field C] (i : A →+* B) (τ : B →+* C) :
    spMap (τ.comp i) = spMap τ ≫ spMap i := by
  simp only [spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem cancel_spMap {K K' : Type} [Field K] [Field K'] (τ : K →+* K') {Z : Scheme.{0}}
    (a b : Spec (CommRingCat.of K) ⟶ Z) (h : spMap τ ≫ a = spMap τ ≫ b) : a = b := by
  have hd : IsSchemeTheoreticallyDominant (spMap τ) :=
    LieEx.std_of_inj (CommRingCat.ofHom τ) τ.injective
  have hs : Function.Surjective (spMap τ) := by
    intro p
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K')) := inferInstance
    exact ⟨x, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  exact LieEx.epi_of_surj (spMap τ) hs a b h

theorem secVal_eq_of_eq {B : Type} [CommRing B] {Z : Scheme.{0}} {x x' : Spec (CommRingCat.of B) ⟶ Z} (e : x = x')
    (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ x' ⁻¹ᵁ W) (s : Γ(Z, W)) : secVal x W h s = secVal x' W h' s := by
  subst e
  rfl

theorem torsion_clause : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (n : ℕ) (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ), GenWeil G L ξ n e → FullTorsion G ξ n → ∀ (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → FullTorsion G' ξ' n → ∀ (L' : LB G'.left) (e' : (Over.mk ξ' ⟶ G') → (Over.mk ξ' ⟶ G') → Ω'ˣ), GenWeil G' L' ξ' n e' → ∀ (y : Over.mk ξ ⟶ G) (y' : Over.mk ξ' ⟶ G'), y ^ n = 1 → y' ^ n = 1 → (∀ (g : Over.mk ξ ⟶ G) (g' : Over.mk ξ' ⟶ G'), g ^ n = 1 → g' ^ n = 1 → g'.left ≫ φ = spMap i ≫ g.left → (e' y' g' : Ω') = i (e y g)) → (∀ (g : Over.mk ξ ⟶ G), g ^ n = 1 → ∃ g' : Over.mk ξ' ⟶ G', g' ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → (∀ (g' : Over.mk ξ' ⟶ G'), g' ^ n = 1 → ∃ g : Over.mk ξ ⟶ G, g ^ n = 1 ∧ g'.left ≫ φ = spMap i ≫ g.left) → ∀ (W : G.left.Opens) (s : Γ(G.left, W)),
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω →+* k) (xk g : Over.mk (spMap τ ≫ ξ) ⟶ G) (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap τ ≫ y.left → g ^ n = 1 → Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h s = c) →
  (∀ (k : Type) [Field k] [IsAlgClosed k] (τ : Ω' →+* k) (xk g : Over.mk (spMap τ ≫ ξ') ⟶ G') (c : kˣ) (h : ⊤ ≤ g.left ⁻¹ᵁ (φ ⁻¹ᵁ W)), xk.left = spMap τ ≫ y'.left → g ^ n = 1 → Out.WeilIs G' L' n xk g (unitOn c) → secVal (B := k) g.left (φ ⁻¹ᵁ W) h (φ.app W s) = c) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hD G _ _ L n e hGW hFT G' _ _ φ hP hFT' L' e' hGW' y y' hy hy' hcomp hlift hdown W s hW
    k _ _ τ xk g c h hxk hgn hWeil
  obtain ⟨x', hx⟩ := hFT' k τ g hgn
  let U : Over.mk (spMap τ ≫ ξ') ⟶ Over.mk ξ' := Over.homMk (spMap τ) rfl
  have hgU : g = U ≫ x' := Over.OverMorphism.ext hx
  have hx'n : x' ^ n = 1 := by
    have e1 : preHom (G := G') U (x' ^ n) = preHom (G := G') U 1 := by
      rw [map_pow, map_one]
      show (U ≫ x') ^ n = 1
      rw [← hgU]
      exact hgn
    apply Over.OverMorphism.ext
    apply cancel_spMap τ
    exact congrArg (fun z => z.left) e1
  obtain ⟨g₀, hg₀, hxg⟩ := hdown x' hx'n
  have hc' : (c : k) = τ (e' y' x') := (hGW'.weil y' x' hy' hx'n k τ xk g c hxk hx).1 hWeil
  have hc : (c : k) = (τ.comp i) (e y g₀) := by
    rw [hc', hcomp g₀ x' hg₀ hx'n hxg]
    rfl
  let U₀ : Over.mk (spMap (τ.comp i) ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap (τ.comp i)) rfl
  have hW1 : Out.WeilIs G L n (U₀ ≫ y) (U₀ ≫ g₀) (unitOn c) :=
    (hGW.weil y g₀ hy hg₀ k (τ.comp i) (U₀ ≫ y) (U₀ ≫ g₀) c rfl rfl).2 hc
  have hg₁ : (U₀ ≫ g₀) ^ n = 1 := by
    have e1 : preHom (G := G) U₀ (g₀ ^ n) = (U₀ ≫ g₀) ^ n := map_pow _ _ _
    rw [← e1, hg₀, map_one]
  have hl : g.left ≫ φ = (U₀ ≫ g₀).left := by
    show g.left ≫ φ = spMap (τ.comp i) ≫ g₀.left
    rw [hx, Category.assoc, hxg, spMap_comp_fields, Category.assoc]
  have h' : ⊤ ≤ (g.left ≫ φ) ⁻¹ᵁ W := h
  have h₁ : ⊤ ≤ (U₀ ≫ g₀).left ⁻¹ᵁ W := hl ▸ h'
  rw [HtPull.seccomp k _ _ g.left φ W h h' s, secVal_eq_of_eq hl W h' h₁ s]
  exact hW k (τ.comp i) (U₀ ≫ y) (U₀ ≫ g₀) c h₁ rfl hg₁ hW1

end GlobalTheory.CompanionTheory.Ar.HtTorPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.regular_everywhere_isIntegral : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ a : Ω, ((∀ p : Cpt ξ, a ∈ regAt ξ p) → IsIntegral O a) ∧ ((∀ p ∈ genFibre O ξ, a ∈ regAt ξ p) → IsAlgebraic O a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isIntegral_and_isAlgebraic_of_regular | exact GlobalTheory.CompanionTheory.Ar.Flat.isIntegral_and_isAlgebraic_of_regular | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isIntegral_and_isAlgebraic_of_regular <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtPull

theorem secVal_congr {B : Type} [CommRing B] {Z : Scheme.{0}} {x x' : Spec (CommRingCat.of B) ⟶ Z} (e : x = x')
    (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ x' ⁻¹ᵁ W) (s : Γ(Z, W)) : secVal x W h s = secVal x' W h' s := by
  subst e
  rfl

theorem epsMul_snd {C : Type} [CommRing C] (c : C) (a : DualNumber C) :
    (GlobalTheory.CompanionTheory.Ar.epsMul c a).snd = c * a.snd := by
  simp [GlobalTheory.CompanionTheory.Ar.epsMul]

theorem one_left_eps {S : Scheme.{0}} (G : Over S) [GrpObj G] {C : Type} [CommRing C] (y : Sp C ⟶ S) :
    (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left = spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def]
  simp

theorem pt_zero {S : Scheme.{0}} {G : Over S} [GrpObj G] {C : Type} [CommRing C] {y : Sp C ⟶ S} {L : Type}
    [AddCommGroup L] [Module C L] (M : LieModel G y L) : M.pt 0 = 1 := by
  have := M.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem one_snd {S : Scheme.{0}} (G : Over S) [GrpObj G] {C : Type} [CommRing C] (y : Sp C ⟶ S) (W : G.left.Opens)
    (h0 : ⊤ ≤ (1 : Over.mk y ⟶ G).left ⁻¹ᵁ W) (h1 : ⊤ ≤ (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left ⁻¹ᵁ W) (s : Γ(G.left, W)) :
    (secVal (B := DualNumber C) (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left W h1 s).snd = 0 := by
  have e := one_left_eps G y
  have h2 : ⊤ ≤ (spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left) ⁻¹ᵁ W := e ▸ h1
  rw [secVal_congr e W h1 h2 s, secring C (DualNumber C) _ G.left _ W h0 h2 s]
  exact TrivSqZeroExt.snd_inl _ _

theorem exists_linear_snd : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S) (L : Type) [AddCommGroup L] [Module C L] (M : LieModel G y L) (W : G.left.Opens) (h : ∀ l, ⊤ ≤ (M.pt l).left ⁻¹ᵁ W) (s : Γ(G.left, W)), ∃ D : L →ₗ[C] C, ∀ l, D l = (secVal (B := DualNumber C) (M.pt l).left W (h l) s).snd := by
  intro S G _ C _ y L _ _ M W h s
  have p0 := pt_zero M
  have h1 : ⊤ ≤ (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left ⁻¹ᵁ W := p0 ▸ h 0
  have h0 : ⊤ ≤ (1 : Over.mk y ⟶ G).left ⁻¹ᵁ W := by
    intro z _
    have t : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ (M.pt 0).left = (1 : Over.mk y ⟶ G).left := M.tan 0
    show (1 : Over.mk y ⟶ G).left z ∈ W
    rw [← t]
    exact h 0 (show spMap (TrivSqZeroExt.fstHom C C C).toRingHom z ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨{ toFun := fun l => (secVal (B := DualNumber C) (M.pt l).left W (h l) s).snd, map_add' := ?_, map_smul' := ?_ },
    fun l => rfl⟩
  · intro l l'
    have e : (M.pt (l + l')).left = (M.pt l * M.pt l').left := by rw [M.add]
    have hvw : ⊤ ≤ (M.pt l * M.pt l').left ⁻¹ᵁ W := e ▸ h (l + l')
    have key := GlobalTheory.T.tangent_section_additive S G C y (M.pt l) (M.pt l') (M.tan l) (M.tan l') W (h l) (h l') hvw h1 s
    have key' := congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom.hom t) key
    simp only [map_add (f := _)] at key'
    have key'' : secVal (B := DualNumber C) (M.pt l * M.pt l').left W hvw s +
        secVal (B := DualNumber C) (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left W h1 s =
        secVal (B := DualNumber C) (M.pt l).left W (h l) s + secVal (B := DualNumber C) (M.pt l').left W (h l') s := key'
    have key3 := congrArg TrivSqZeroExt.snd key''
    rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, one_snd G y W h0 h1 s, add_zero] at key3
    show (secVal (B := DualNumber C) (M.pt (l + l')).left W (h (l + l')) s).snd = _
    rw [secVal_congr e W (h (l + l')) hvw s]
    exact key3
  · intro c l
    have e := M.smul c l
    have h2 : ⊤ ≤ (spMap (GlobalTheory.CompanionTheory.Ar.epsMul c) ≫ (M.pt l).left) ⁻¹ᵁ W := e ▸ h (c • l)
    show (secVal (B := DualNumber C) (M.pt (c • l)).left W (h (c • l)) s).snd = c • _
    rw [secVal_congr e W (h (c • l)) h2 s, secring _ _ _ G.left _ W (h l) h2 s, epsMul_snd]
    rfl

end GlobalTheory.CompanionTheory.Ar.HtPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.full_torsion_pullback_points : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ n : ℕ, FullTorsion G ξ n →
  FullTorsion G' ξ' n ∧
  (∀ y : Over.mk ξ ⟶ G, y ^ n = 1 → ∃ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 → ∃ y : Over.mk ξ ⟶ G, y ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c'.left → (a * a').left ≫ φ = spMap i ≫ (c * c').left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c.left → a = a') ∧
  (∀ (a : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a.left ≫ φ = spMap i ≫ c'.left → c = c') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorsPull.torsion_of_pullback | exact GlobalTheory.CompanionTheory.Ar.TorsPull.torsion_of_pullback | (intros; apply GlobalTheory.CompanionTheory.Ar.TorsPull.torsion_of_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem tw_iso_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) :=
  PositivityTheory.UnitarySelfGeneration.tw_iso

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwistOk

theorem twOK_obj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a :=
  @PositivityTheory.UnitarySelfGeneration.tw_ok

end GlobalTheory.CompanionTheory.Ar.TwistOk
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.fibre_curve_degree_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree | exact GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.fibreCurve_curveIn_degree <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_fibreCurve_through_closed_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ∀ (y x : Cpt ξ) (g : Ω), ¬ unitAt ξ y (algebraMap O Ω ϖ) → y.1 ⤳ x.1 → IsClosed ({x.1} : Set X) → g ∈ regAt ξ x → unitAt ξ y g → ¬ unitAt ξ x g → ∃ (Γ : FibreCurve ξ (algebraMap O Ω ϖ)) (i : Γ.C.I), y.1 ⤳ centre Γ.η ∧ unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ g ∧ centre (Γ.z i) = x.1 := by
  exact @PositivityTheory.Xgn.exists_curve_through_special_point

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem pairingRegular_mem_prodSpan : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, ζ n ^ p ^ n = 1) → X.PairingRegular B ζ → ∀ n, ∃ s ∈ prodSpan ((X.Γ n).btOrder ⊤), ∀ a b, s (lev p n a, lev p n b) = ((ζ n ^ B a b : Oˣ) : O) :=
  PositivityTheory.HtPt.Twpair.tw_pair

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.is_comb_tangent_iff_linear_sum : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (n : ℕ) (b : Fin n → Em) (cf : Fin n → R) (e : Em),
    IsComb cf (fun i => M.pt (b i)) (M.pt e) ↔ e = ∑ i, cf i • b i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isComb_lieModel_pt_iff | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isComb_lieModel_pt_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isComb_lieModel_pt_iff <;> assumption)
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.exists_prodSpan_torsion_pairing_eq_zeta_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, ζ n ^ p ^ n = 1) → X.PairingRegular B ζ → ∀ n, ∃ s ∈ prodSpan ((X.Γ n).btOrder ⊤), ∀ a b, s (lev p n a, lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.pairingRegular_mem_prodSpan | exact GlobalTheory.CompanionTheory.Ar.HT.pairingRegular_mem_prodSpan | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.pairingRegular_mem_prodSpan <;> assumption)

end
end
