module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle163
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle174
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle175
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle105
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle130
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle004
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt

variable {X : Scheme.{0}}

abbrev cst (s : X ⟶ Sp ℂ) (V : X.Opens) : ℂ →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)).hom

theorem top_le_spMap (hV' : X.Opens) (hV : IsAffineOpen hV') (ψ : Γ(X, hV') →+* ℂ) :
    ⊤ ≤ (spMap ψ ≫ hV.fromSpec) ⁻¹ᵁ hV' := by
  have h : ∀ p, hV.fromSpec p ∈ hV' := fun p => by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨p, rfl⟩
  have e := h (spMap ψ (show Sp ℂ from IsLocalRing.closedPoint ℂ))
  rw [← Scheme.Hom.comp_apply] at e
  exact (top_le_iff_centre _ hV').2 e

theorem val_spMap {V : X.Opens} (hV : IsAffineOpen V) (ψ : Γ(X, V) →+* ℂ) (a : Γ(X, V)) :
    valAt' (spMap ψ ≫ hV.fromSpec) V a = ψ a :=
  (valAt'_fromSpec hV _ a).trans (valAt'_spMap ψ a)

theorem eq_spMap {V : X.Opens} (hV : IsAffineOpen V) (y : Sp ℂ ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ V) :
    y = spMap (valHom y V h) ≫ hV.fromSpec := by
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact h (Set.mem_univ p)
  have hl : IsOpenImmersion.lift hV.fromSpec y hr ≫ hV.fromSpec = y := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, V) →+* ℂ, spMap φ = IsOpenImmersion.lift hV.fromSpec y hr :=
    ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr)).hom, Spec.map_preimage _⟩
  rw [← hφ] at hl
  have e : valHom y V h = φ := RingHom.ext fun a => by
    show valAt' y V a = φ a
    rw [← hl]
    exact val_spMap hV φ a
  rw [e, hl]

theorem fromSpec_comp_structure_map (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) : hV.fromSpec ≫ s = spMap (cst s V) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  exact (Spec.map_comp _ _).symm

theorem over_iff (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) (ψ : Γ(X, V) →+* ℂ) :
    (spMap ψ ≫ hV.fromSpec) ≫ s = 𝟙 _ ↔ ψ.comp (cst s V) = RingHom.id ℂ := by
  rw [Category.assoc, fromSpec_comp_structure_map]
  constructor
  · intro h
    have e : spMap (ψ.comp (cst s V)) = spMap (RingHom.id ℂ) := (Spec.map_comp _ _).trans (h.trans (Spec.map_id _).symm)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  · intro h
    refine (Spec.map_comp _ _).symm.trans ?_
    exact (congrArg spMap h).trans (Spec.map_id _)

theorem comp_cst (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) (y : Sp ℂ ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ V)
    (hy : y ≫ s = 𝟙 _) : (valHom y V h).comp (cst s V) = RingHom.id ℂ :=
  (over_iff s hV _).1 (by rw [← eq_spMap hV y h]; exact hy)

theorem isOpen_near {E : Type} [TopologicalSpace E] {T : Set E} (hT : IsOpen T) {n : ℕ} (v : Fin n → E → ℂ)
    (c : Fin n → ℂ) (ε : ℝ) (hv : ∀ j, ContinuousOn (v j) T) : IsOpen {b ∈ T | ∀ j, ‖v j b - c j‖ < ε} := by
  rw [isOpen_iff_mem_nhds]
  rintro b ⟨hb, hj⟩
  have h : ∀ j, ∀ᶠ y in 𝓝 b, ‖v j y - c j‖ < ε := fun j =>
    (((hv j).continuousAt (hT.mem_nhds hb)).sub continuousAt_const).norm.eventually_lt continuousAt_const (hj j)
  filter_upwards [hT.mem_nhds hb, Filter.eventually_all.2 h] with y h₁ h₂ using ⟨h₁, h₂⟩

theorem isChart_of_data (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) {D M : ℕ} (g : Fin M → Γ(X, V))
    (f : Fin D → Γ(X, V)) {B₀ : Set (Fin D → ℂ)} {ε : ℝ} (Ψ : (Fin D → ℂ) → (Γ(X, V) →+* ℂ)) (ψ₀ : Γ(X, V) →+* ℂ)
    (o : IsOpen B₀) (a₁ : ∀ b ∈ B₀, (Ψ b).comp (cst s V) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i)
    (a₂ : ∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B₀)
    (a₃ : ∀ ψ : Γ(X, V) →+* ℂ, ψ.comp (cst s V) = RingHom.id ℂ → (∀ j, ‖ψ (g j) - ψ₀ (g j)‖ < ε) →
      (fun i => ψ (f i)) ∈ B₀ ∧ Ψ (fun i => ψ (f i)) = ψ) :
    IsChart s {b ∈ B₀ | ∀ j, ‖Ψ b (g j) - ψ₀ (g j)‖ < ε} (fun b => spMap (Ψ b) ≫ hV.fromSpec) := by
  have oB : IsOpen {b ∈ B₀ | ∀ j, ‖Ψ b (g j) - ψ₀ (g j)‖ < ε} :=
    isOpen_near o (fun j b => Ψ b (g j)) _ ε fun j => (a₂ (g j)).continuousOn
  refine ⟨oB, ?_, fun b hb => (over_iff s hV _).2 (a₁ b hb.1).1, ?_⟩
  · exact isHolTo_comp (isHolTo_spMap oB fun a => (a₂ a).mono fun b hb => hb.1) hV.fromSpec
  intro m B' y oB' hy ov b₀ h₀ b₁ h₁ e
  have oT : IsOpen {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} := (hy V 0).1
  have dv : ∀ a : Γ(X, V), DifferentiableOn ℂ (fun b => valAt' (y b) V a) {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} := fun a => (hy V a).2
  have oT' := isOpen_near oT (fun j b => valAt' (y b) V (g j)) (fun j => ψ₀ (g j)) ε fun j => (dv (g j)).continuousOn
  have v₀ : ∀ a, valAt' (y b₀) V a = Ψ b₁ a := fun a => by rw [e]; exact val_spMap hV _ a
  have m₀ : b₀ ∈ {b ∈ {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} | ∀ j, ‖valAt' (y b) V (g j) - ψ₀ (g j)‖ < ε} :=
    ⟨⟨h₀, by rw [e]; exact top_le_spMap V hV _⟩, fun j => by rw [v₀]; exact h₁.2 j⟩
  obtain ⟨δ, δ0, hδ⟩ := Metric.isOpen_iff.1 oT' b₀ m₀
  refine ⟨δ, fun b i => valAt' (y b) V (f i), δ0, fun b hb => (hδ hb).1.1,
    differentiableOn_pi.2 fun i => (dv (f i)).mono fun b hb => (hδ hb).1, funext fun i => ?_, fun b hb => ?_⟩
  · show valAt' (y b₀) V (f i) = b₁ i
    rw [v₀]; exact (a₁ b₁ h₁.1).2 i
  · have t := (hδ hb).1.2
    have k := a₃ (valHom (y b) V t) (comp_cst s hV _ t (ov b (hδ hb).1.1)) (hδ hb).2
    have k₂ : Ψ (fun i => valAt' (y b) V (f i)) = valHom (y b) V t := k.2
    refine ⟨⟨k.1, fun j => ?_⟩, ?_⟩
    · rw [k₂]; exact (hδ hb).2 j
    · show y b = spMap (Ψ (fun i => valAt' (y b) V (f i))) ≫ hV.fromSpec
      rw [k₂]; exact eq_spMap hV _ t

theorem res_cst (s : X ⟶ Sp ℂ) {U V : X.Opens} (h : V ≤ U) (c : ℂ) :
    (X.presheaf.map (homOfLE h).op).hom (cst s U c) = cst s V c :=
  congr($(Scheme.Hom.appLE_map s (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))

theorem exists_std (s : X ⟶ Sp ℂ) [Smooth s] (q : X) (M : X.Opens) (hq : q ∈ M) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (D : ℕ), V ≤ M ∧ q ∈ V ∧ (cst s V).IsStandardSmoothOfRelativeDimension D := by
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ := Smooth.exists_isStandardSmooth s q
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h2 : y = s q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact hle hp
  subst hU₀
  obtain ⟨n, hn⟩ : ∃ n, RingHom.IsStandardSmoothOfRelativeDimension n (s.appLE ⊤ U hle).hom := by
    let _ := (s.appLE ⊤ U hle).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp ℂ, ⊤) Γ(X, U) := hsm
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  obtain ⟨a, haM, hqa⟩ := hU.exists_basicOpen_le (V := M) ⟨q, hq⟩ hp
  refine ⟨X.basicOpen a, hU.basicOpen a, n, haM, hqa, ?_⟩
  have := hU.isLocalization_basicOpen a
  have h1 : (algebraMap Γ(X, U) Γ(X, X.basicOpen a)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway a
  have h2 : (cst s U).IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have h3 := h1.comp h2
  rw [zero_add] at h3
  convert h3 using 1
  ext c
  exact (res_cst s (X.basicOpen_le a) c).symm

theorem isDomain_of_le {Z V : X.Opens} [AlgebraicGeometry.IsIntegral Z.toScheme] (h : V ≤ Z) {q : X} (hq : q ∈ V) :
    IsDomain Γ(X, V) := by
  haveI : Nonempty V.toScheme := ⟨⟨q, hq⟩⟩
  haveI : AlgebraicGeometry.IsIntegral V.toScheme := isIntegral_of_isOpenImmersion (X.homOfLE h)
  haveI : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨q, hq⟩, trivial⟩⟩
  exact MulEquiv.isDomain Γ(V.toScheme, ⊤) (Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv.toMulEquiv

theorem exists_chart : (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ))
    (f : Fin D → A) (a : A), IsOpen O → O.Nonempty →
    (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0) →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W N : X.Opens) (x : Sp ℂ ⟶ X), Smooth s →
    IsCptGen ξ → genPt ξ ∈ W → x ≫ s = 𝟙 _ → genPt ξ ⤳ centre x → centre x ∈ N →
    ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsChart s B Y ∧ b₁ ∈ B ∧
      Y b₁ = x ∧ (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) ∧
      ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W := by
  intro hring X s Ω _ ξ W N x hs hξ hW hxs hgx hxN
  haveI := hs
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨Z, hZ, -, hZi⟩ := cpt_open_integral X Ω ξ hξ
  obtain ⟨V, hV, D, hVM, hxV, hstd⟩ := exists_std s (centre x) (N ⊓ Z) ⟨hxN, (hZ _).2 hgx⟩
  letI alg : Algebra ℂ Γ(X, V) := (cst s V).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D ℂ Γ(X, V) := hstd
  haveI : IsDomain Γ(X, V) := isDomain_of_le (hVM.trans inf_le_right) hxV
  have hxt : ⊤ ≤ x ⁻¹ᵁ V := (top_le_iff_centre x V).2 hxV
  have h₀ : (valHom x V hxt).comp (algebraMap ℂ Γ(X, V)) = RingHom.id ℂ := comp_cst s hV x hxt hxs
  obtain ⟨M, g, f, B₀, ε, Ψ, ε0, o, a₁, a₂, a₃⟩ := anChart_alg D (RingHom.id ℂ) (valHom x V hxt) h₀
  have hc := isChart_of_data s hV g f Ψ (valHom x V hxt) o a₁ a₂ a₃
  have m₁ := a₃ _ h₀ fun _ => by simpa using ε0
  have hY : ∀ b, centre (spMap (Ψ b) ≫ hV.fromSpec) ∈ V := fun b => (top_le_iff_centre _ V).1 (top_le_spMap V hV _)
  refine ⟨D, _, _, fun i => valHom x V hxt (f i), hc, ⟨m₁.1, fun j => ?_⟩, ?_, fun b _ => ⟨(hVM (hY b)).1, (hZ _).1 (hVM (hY b)).2⟩, ?_⟩
  · rw [m₁.2]; simpa using ε0
  · show spMap (Ψ fun i => valHom x V hxt (f i)) ≫ hV.fromSpec = x
    rw [m₁.2]; exact (eq_spMap hV x hxt).symm
  intro O oO sO nO
  have hgV : genPt ξ ∈ V := genPt_mem hgx hxV
  obtain ⟨a, haW, haξ⟩ := hV.exists_basicOpen_le (V := W) ⟨genPt ξ, hW⟩ hgV
  have a0 : a ≠ 0 := by
    rintro rfl
    simp at haξ
  by_contra hc'
  push_neg at hc'
  refine a0 (hring Γ(X, V) D O Ψ f a oO nO (fun b hb => a₁ b (sO hb).1) fun b hb => ?_)
  by_contra hne
  refine hc' b hb (haW ?_)
  have hv : valAt' (spMap (Ψ b) ≫ hV.fromSpec) V a ≠ 0 := by rw [val_spMap]; exact hne
  exact (valAt'_ne_zero_iff _ V (top_le_spMap V hV _) a _).1 hv

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

section Linear

variable {ι O : Type} [Fintype ι] [CommRing O]
variable {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]

theorem mem_eig (ρ : O →+* Module.End R N) (σ : O →+* R) (u : N) : u ∈ eigSp ρ σ ↔ ∀ a, ρ a u = σ a • u := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

def Splits (ρ : O →+* Module.End R N) (τ : ι → O →+* R) : Prop :=
  ∀ m : N, ∃! f : ι → N, (∀ s a, ρ a (f s) = τ s a • f s) ∧ ∑ s, f s = m

def sumMap (ρ : O →+* Module.End R N) (τ : ι → O →+* R) : (∀ s, eigSp ρ (τ s)) →ₗ[R] N :=
  ∑ s, (eigSp ρ (τ s)).subtype ∘ₗ LinearMap.proj s

theorem sumMap_apply (ρ : O →+* Module.End R N) (τ : ι → O →+* R) (g : ∀ s, eigSp ρ (τ s)) :
    sumMap ρ τ g = ∑ s, (g s : N) := by
  simp [sumMap, LinearMap.sum_apply]

theorem sumMap_bij {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) :
    Function.Bijective (sumMap ρ τ) := by
  constructor
  · intro g g' e
    have := (h (sumMap ρ τ g)).unique (y₁ := fun s => (g s : N)) (y₂ := fun s => (g' s : N))
      ⟨fun s a => (mem_eig ρ (τ s) _).1 (g s).2 a, (sumMap_apply ρ τ g).symm⟩
      ⟨fun s a => (mem_eig ρ (τ s) _).1 (g' s).2 a, by rw [e, sumMap_apply]⟩
    exact funext fun s => Subtype.ext (congrFun this s)
  · intro m
    obtain ⟨f, ⟨hf, hs⟩, -⟩ := h m
    exact ⟨fun s => ⟨f s, (mem_eig ρ (τ s) _).2 (hf s)⟩, by rw [sumMap_apply]; exact hs⟩

theorem exists_bases [DecidableEq ι] [IsLocalRing R] [Module.Finite R N] [Module.Projective R N]
    {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) :
    ∃ r : ι → ℕ, Nonempty (∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) := by
  let e := LinearEquiv.ofBijective (sumMap ρ τ) (sumMap_bij h)
  haveI hP : Module.Projective R (∀ s, eigSp ρ (τ s)) := Module.Projective.of_equiv e.symm
  have key : ∀ s, Module.Free R (eigSp ρ (τ s)) ∧ Module.Finite R (eigSp ρ (τ s)) := fun s => by
    haveI : Module.Finite R (∀ s, eigSp ρ (τ s)) := Module.Finite.equiv e.symm
    haveI : Module.Finite R (eigSp ρ (τ s)) :=
      Module.Finite.of_surjective (LinearMap.proj s : (∀ s, eigSp ρ (τ s)) →ₗ[R] eigSp ρ (τ s))
        (fun y => ⟨Pi.single s y, by simp⟩)
    haveI : Module.Projective R (eigSp ρ (τ s)) :=
      Module.Projective.of_split (LinearMap.single R (fun s => eigSp ρ (τ s)) s) (LinearMap.proj s)
        (LinearMap.ext fun y => by simp)
    haveI : Module.FinitePresentation R (eigSp ρ (τ s)) := Module.finitePresentation_of_projective _ _
    exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
  refine ⟨fun s => Module.finrank R (eigSp ρ (τ s)), ⟨fun s => ?_⟩⟩
  haveI := (key s).1
  haveI := (key s).2
  exact Module.finBasis R _

def totBasis [DecidableEq ι] {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) : Module.Basis (Σ s, Fin (r s)) R N :=
  (Pi.basis b).map (LinearEquiv.ofBijective (sumMap ρ τ) (sumMap_bij h))

theorem totBasis_apply [DecidableEq ι] {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) (s : ι) (i : Fin (r s)) :
    totBasis h b ⟨s, i⟩ = b s i := by
  simp only [totBasis, Module.Basis.map_apply, LinearEquiv.ofBijective_apply, sumMap_apply, Pi.basis_apply]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

variable {T N' : Type} [CommRing T] [AddCommGroup N'] [Module T N']

theorem image_frame [DecidableEq ι] {θ : R →+* T} {ρ : O →+* Module.End R N} {τ : ι → O →+* R}
    {ρ' : O →+* Module.End T N'} (h' : Splits ρ' fun s => θ.comp (τ s)) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) (β : N →ₛₗ[θ] N')
    (B : Module.Basis (Σ s, Fin (r s)) T N') (hB : ∀ s i, B ⟨s, i⟩ = β (b s i))
    (hρ : ∀ a e, ρ' a (β e) = β (ρ a e)) (s : ι) :
    LinearIndependent T (fun i => β (b s i)) ∧
      Submodule.span T (Set.range fun i => β (b s i)) = eigSp ρ' (θ.comp (τ s)) := by
  have hv : ∀ s i, ∀ a, ρ' a (β (b s i)) = (θ.comp (τ s)) a • β (b s i) := fun s i a => by
    rw [hρ, (mem_eig ρ (τ s) _).1 (b s i).2 a, β.map_smulₛₗ]
    rfl
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_⟩
  · have := B.linearIndependent.comp (Sigma.mk s) sigma_mk_injective
    convert this using 1
    exact funext fun i => (hB s i).symm
  · rintro _ ⟨i, rfl⟩
    exact (mem_eig ρ' _ _).2 (hv s i)
  · let f : ι → N' := fun s' => ∑ i, B.repr w ⟨s', i⟩ • β (b s' i)
    have hf : ∀ s' a, ρ' a (f s') = (θ.comp (τ s')) a • f s' := fun s' a => by

      simp only [f, map_sum, Finset.smul_sum, map_smul, hv s']
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    have hsum : ∑ s', f s' = w := by
      have := B.sum_repr w
      rw [Fintype.sum_sigma] at this
      simpa only [f, hB] using this
    have hw' := (mem_eig ρ' _ _).1 hw
    have hu := (h' w).unique (y₁ := f) (y₂ := fun s' => if s' = s then w else 0) ⟨hf, hsum⟩
      ⟨fun s' a => by
        by_cases e : s' = s
        · subst e; simpa using hw' a
        · simp [e], by simp⟩
    have : w = f s := by simpa using (congrFun hu s).symm
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Linear

end GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

namespace GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

open GlobalTheory.CompanionTheory.Ar.LieVB

theorem splits_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {S : Type} [CommRing S] (κ : c.F →+* S) {N : Type} [AddCommGroup N] [Module S N]
    (ρ : 𝓞 E →+* Module.End S N) : Splits ρ (fun s : E →+* ℂ => κ.comp (tauIn c s)) := by
  letI : Algebra c.F S := κ.toAlgebra
  exact fun m => GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum E H l c S N ρ m

theorem exists_stableEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ), ∃ (r : ℕ) (e : Fin r → (epsAt x ⟶ t.G)), StableEig t x κ σ e := by
  classical
  intro E _ _ _ H l c X t A _ _ x κ σ
  haveI hsm : Smooth t.G.hom := t.semi.smooth
  obtain ⟨N, _, _, ⟨M⟩⟩ := lieModel_exists X t.G A x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X t.G A x N M (𝓞 E) t.act.act t.act.hom t.act.one t.act.mul
    t.act.add
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_model_finite_base_change X t.G A x N M
  have hsp := splits_of c κ ρ
  obtain ⟨r, ⟨b⟩⟩ := exists_bases hsp
  refine ⟨r σ, fun i => M.pt (b σ i), ?_⟩
  intro T _ θ x' hx' v hv
  subst hx'
  obtain ⟨N', _, _, ⟨M'⟩⟩ := lieModel_exists X t.G T (spMap θ ≫ x)
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act X t.G T (spMap θ ≫ x) N' M' (𝓞 E) t.act.act t.act.hom
    t.act.one t.act.mul t.act.add
  let q := Fintype.equivFin (Σ s, Fin (r s))
  obtain ⟨β, B, hB, hβ⟩ := basis_tr θ x (spMap θ ≫ x) rfl M M' ((totBasis hsp b).reindex q)
  have hB' : ∀ s i, (B.reindex q.symm) ⟨s, i⟩ = β (b s i) := fun s i => by
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
      totBasis_apply]
  have hact : ∀ a e, ρ' a (β e) = β (ρ a e) := fun a e => pt_left_inj M' (by
    rw [hβ, hρ a e, Over.comp_left, ← Category.assoc, ← hβ e, hρ' a (β e), Over.comp_left])
  have hsp' : Splits ρ' (fun s : E →+* ℂ => θ.comp (κ.comp (tauIn c s))) := splits_of c (θ.comp κ) ρ'
  obtain ⟨hli, hspan⟩ := image_frame hsp' b β (B.reindex q.symm) hB' hact σ
  have hvv : v = fun k => M'.pt (β (b σ k)) := funext fun k => Over.OverMorphism.ext (by
    rw [hv k, hβ])
  rw [hvv]
  exact (((GlobalTheory.T.lie_model_eigenvectors_action X T t.G (spMap θ ≫ x) N' M').2 (𝓞 E) t.act ρ' ((θ.comp κ).comp (tauIn c σ)) hρ').2 _ _).2
    ⟨hli, hspan⟩

end GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_germ_substitution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ (m : ℕ) (a : 𝓞 E), (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g.B.A.act a p.2)).comp (sub1 Qs m) = (sub1 Qs m).comp (jetSubstP m fun p : Fin 1 × Fin d' => psTrunc m (gB.B.A.act a p.2)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.substitution_action_commutes | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.substitution_action_commutes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.substitution_action_commutes <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_line_bundle_gauge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → ∃ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr.adjunction_ratio <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem prov_an : Prov.An :=
  ⟨GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds, GlobalTheory.T.convergence_statement_holds, GlobalTheory.T.signed_convergence_statement_holds, GlobalTheory.T.convergence_rate_statement_holds, GlobalTheory.T.uniform_integrability_statement_holds,
    GlobalTheory.T.pullback_statement_holds, GlobalTheory.T.global_regularization_statement_holds⟩

end GlobalTheory.CompanionTheory.Ar.Link
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec

namespace SharpLaws

theorem card_psi (D : D7) (Q : Par D) : Fintype.card (CMType Q.H) = D.R.f := by
  have h := GlobalTheory.PeriodCoord.card_cmType Q.H
  rw [Nat.card_eq_fintype_card, D.host.finrank_cmField] at h
  rw [h]
  show 4 * D.R.ord / 2 = 2 * D.R.ord
  omega

end SharpLaws

end GlobalTheory.CompanionTheory.Ar.Rec
end
end
