module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem spread_slice {n g N : ℕ} {W : Set ((Fin n → ℂ) × (Fin g → ℂ))} (hW : IsOpen W)
    {Φ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin N → ℂ)} (hΦ : ∀ j, DifferentiableOn ℂ (fun bz => Φ bz j) W)
    {b₀ : Fin n → ℂ} {x : Fin g → ℂ} (hmem : (b₀, x) ∈ W)
    {L : (Fin n → ℂ) × (Fin N → ℂ) → (Fin g → ℂ)} (hL : AnalyticAt ℂ L (b₀, Φ (b₀, x)))
    {Q : (Fin n → ℂ) × (Fin N → ℂ) → Prop} (hQ : ∀ᶠ p in 𝓝 (b₀, Φ (b₀, x)), Q p) :
    ∃ ε : ℝ, 0 < ε ∧ DifferentiableOn ℂ (fun b => L (b, Φ (b, x))) (ball b₀ ε) ∧
      ∀ b ∈ ball b₀ ε, (b, x) ∈ W ∧ Q (b, Φ (b, x)) := by
  have hcont : Continuous (fun b : Fin n → ℂ => (b, x)) := continuous_id.prodMk continuous_const
  have hUo : IsOpen ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) := hW.preimage hcont
  have hΦd : DifferentiableOn ℂ (fun b => Φ (b, x)) ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) := by
    rw [differentiableOn_pi]
    intro j
    exact (hΦ j).comp (differentiable_id.prodMk (differentiable_const x)).differentiableOn
      (fun b hb => hb)
  have hFd : DifferentiableOn ℂ (fun b => (b, Φ (b, x))) ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) :=
    differentiableOn_id.prodMk hΦd
  have hb₀ : b₀ ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W := hmem
  have hFc : ContinuousAt (fun b => (b, Φ (b, x))) b₀ :=
    (hFd.differentiableAt (hUo.mem_nhds hb₀)).continuousAt
  have hU' : ∀ᶠ b in 𝓝 b₀, b ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W := hUo.mem_nhds hb₀
  have hev : ∀ᶠ b in 𝓝 b₀, b ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W ∧
      AnalyticAt ℂ L (b, Φ (b, x)) ∧ Q (b, Φ (b, x)) :=
    hU'.and (Filter.Tendsto.eventually hFc (hL.eventually_analyticAt.and hQ))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ε, hε, fun b hb => ?_, fun b hb => ⟨(hball b hb).1, (hball b hb).2.2⟩⟩
  exact ((hball b hb).2.1.differentiableAt.comp b
    (hFd.differentiableAt (hUo.mem_nhds (hball b hb).1))).differentiableWithinAt

theorem per_spreads : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsOpen B → ∀ b₀ ∈ B, ∀ x ∈ e.per b₀, ∃ (ε : ℝ) (s : (Fin n → ℂ) → (Fin g → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ s (ball b₀ ε) ∧ s b₀ = x ∧ ∀ b ∈ ball b₀ ε, s b ∈ e.per b := by
  intro R _ G _ _ g n M B ψ e _ b₀ hb₀ x hx
  have hx1 : e.ex b₀ x = 1 := hx
  have h01 : e.ex b₀ 0 = 1 := by
    have h := e.add b₀ hb₀ 0 0
    rw [add_zero] at h
    exact mul_right_cancel (h.symm.trans (_root_.one_mul _).symm)
  have hx0 : e.ex b₀ x = e.ex b₀ 0 := hx1.trans h01.symm
  obtain ⟨V, N, f, L, hV, hLan, hinv, huniq⟩ := e.log b₀ hb₀
  let W : Set ((Fin n → ℂ) × (Fin g → ℂ)) := {bz | bz ∈ B ×ˢ Set.univ ∧
    ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex bz.1 bz.2)).base).obj V}
  have hWo : IsOpen W := (e.hol V 0).1
  let Φ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin N → ℂ) :=
    fun bz j => valAt' (Over.Hom.left (e.ex bz.1 bz.2)) V (f j)
  have hΦ : ∀ j, DifferentiableOn ℂ (fun bz => Φ bz j) W := fun j => (e.hol V (f j)).2
  have hmemW : (b₀, x) ∈ W := by
    refine ⟨⟨hb₀, Set.mem_univ _⟩, ?_⟩
    show ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex b₀ x)).base).obj V
    rw [hx0]
    exact hV
  have hΦx : Φ (b₀, x) = fun j => valAt' (Over.Hom.left (e.ex b₀ 0)) V (f j) := by
    show (fun j => valAt' (Over.Hom.left (e.ex b₀ x)) V (f j)) = _
    rw [hx0]
  have hL' : AnalyticAt ℂ L (b₀, Φ (b₀, x)) := by
    rw [hΦx]
    exact hLan
  let Q : (Fin n → ℂ) × (Fin N → ℂ) → Prop := fun p =>
    ∀ y : Over.mk (spMap (ψ p.1)) ⟶ G,
      ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left y).base).obj V →
        (∀ j, valAt' (Over.Hom.left y) V (f j) = p.2 j) → y = e.ex p.1 (L p)
  have hQ : ∀ᶠ p in 𝓝 (b₀, Φ (b₀, x)), Q p := by
    rw [hΦx]
    exact huniq
  obtain ⟨ε, hε, hdiff, hprop⟩ := spread_slice hWo hΦ hmemW hL' hQ
  have hWmem : ∀ b ∈ ball b₀ ε, b ∈ B ∧
      ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex b x)).base).obj V := by
    intro b hb
    obtain ⟨⟨hbB, -⟩, hcov⟩ := (hprop b hb).1
    exact ⟨hbB, hcov⟩
  refine ⟨ε, fun b => x - L (b, Φ (b, x)), hε, fun b hb => (hWmem b hb).1,
    (differentiableOn_const x).sub hdiff, ?_, ?_⟩
  · show x - L (b₀, Φ (b₀, x)) = x
    have h0 : L (b₀, fun j => valAt' (Over.Hom.left (e.ex b₀ 0)) V (f j)) = 0 :=
      hinv.self_of_nhds
    rw [hΦx, h0, sub_zero]
  · intro b hb
    obtain ⟨hbB, hcov⟩ := hWmem b hb
    have hyx : e.ex b x = e.ex b (L (b, Φ (b, x))) :=
      (hprop b hb).2 (e.ex b x) hcov (fun j => rfl)
    show e.ex b (x - L (b, Φ (b, x))) = 1
    have hadd := e.add b hbB (x - L (b, Φ (b, x))) (L (b, Φ (b, x)))
    rw [sub_add_cancel, hyx] at hadd
    exact mul_right_cancel (hadd.symm.trans (_root_.one_mul _).symm)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem FamExp.per_discrete : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), ∀ b ∈ B, ∃ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b ∧ DiscreteTopology Γ₀ ∧ Module.Finite ℤ Γ₀ ∧ Module.Free ℤ Γ₀ := by
  intro R _ G _ _ g n M B ψ e b hb
  have h0 : e.ex b 0 = 1 := by
    have h := e.add b hb 0 0
    rw [add_zero] at h
    exact (left_eq_mul.mp h)
  let A : AddSubgroup (Fin g → ℂ) :=
    { carrier := e.per b
      zero_mem' := h0
      add_mem' := by
        intro z w hz hw
        have hz' : e.ex b z = 1 := hz
        have hw' : e.ex b w = 1 := hw
        show e.ex b (z + w) = 1
        rw [e.add b hb, hz', hw', _root_.one_mul]
      neg_mem' := by
        intro z hz
        have hz' : e.ex b z = 1 := hz
        show e.ex b (-z) = 1
        have h := e.add b hb z (-z)
        rw [add_neg_cancel, h0, hz', _root_.one_mul] at h
        exact h.symm }
  let Γ₀ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule A
  obtain ⟨V, N, f, L, -, -, hL, -⟩ := e.log b hb
  have hslice : ∀ᶠ z : Fin g → ℂ in 𝓝 0,
      L (b, fun j => valAt' (e.ex b z).left V (f j)) = z := by
    have hc : Tendsto (fun z : Fin g → ℂ => (b, z)) (𝓝 0) (𝓝 (b, 0)) :=
      (Continuous.prodMk_right b).tendsto 0
    exact hc.eventually hL
  have hiso : ∀ᶠ z : Fin g → ℂ in 𝓝 0, z ∈ e.per b → z = 0 := by
    have h00 := hslice.self_of_nhds
    filter_upwards [hslice] with z hz hper
    have hz' : e.ex b z = e.ex b 0 := by
      have : e.ex b z = 1 := hper
      rw [this, h0]
    rw [hz'] at hz
    exact hz.symm.trans h00
  have hdisc : DiscreteTopology Γ₀ := by
    obtain ⟨U, hU, hUo, h0U⟩ := _root_.eventually_nhds_iff.mp hiso
    apply discreteTopology_of_isOpen_singleton_zero
    have : ({0} : Set Γ₀) = Subtype.val ⁻¹' U := by
      ext ⟨z, hz⟩
      constructor
      · intro h
        have : z = 0 := congrArg Subtype.val h
        simpa [this] using h0U
      · intro h
        have : z = 0 := hU z h hz
        exact Subtype.ext this
    rw [this]
    exact hUo.preimage continuous_subtype_val
  refine ⟨Γ₀, rfl, hdisc, ?_, ?_⟩
  · exact instModuleFinite_of_discrete_submodule Γ₀
  · exact instModuleFree_of_discrete_submodule Γ₀

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem exists_open_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → ∃ (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ₀ = y₁ ≫ Y.j ∧ 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) ∧ 𝔐.fn.comp cst₀ = 𝔐.cst := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 y₀ hy
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI := Y.jQ_open
  have hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over

  let b₀ : 𝓞 c.F →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀ := (Spec.map_preimage _).symm
  have hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      have hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀ := by
        rw [← Spec.map_comp]; rfl
      rw [hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]
    have := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    simpa using this
  have hinj : Function.Injective b₀ := by
    intro u v huv
    have h := congrArg 𝔐.fn huv
    have hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w) := fun w => RingHom.congr_fun hc w
    rw [hu, hu] at h
    exact IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)
  let cst₀ : c.F →+* 𝔐.Ω₀ := IsFractionRing.lift hinj
  have hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀ := by
    ext w
    exact IsFractionRing.lift_algebraMap hinj w
  have hfn : 𝔐.fn.comp cst₀ = 𝔐.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
    rw [RingHom.comp_assoc, hl, hc]
  have hs : 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by rw [hl, hb]
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := by
    intro A B C _ _ _ f g
    rw [← Spec.map_comp]; rfl

  let w : Sp 𝔐.Ω₀ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift 𝔐.ξ₀ (spMap cst₀) (by rw [hs, hcomp])

  let u : c.F →+* Ω := (Spec.preimage (y₀ ≫ pullback.snd _ _)).hom
  have hu : y₀ ≫ pullback.snd _ _ = spMap u := (Spec.map_preimage _).symm
  have huc : u = 𝔐.cst := by
    have hsp : spMap (u.comp (algebraMap (𝓞 c.F) c.F)) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [hcomp, ← hu, ← 𝔐.cst_over, ← Category.assoc 𝔐.ξ, hy, Model.j]
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    have h1 := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    have h2 : u.comp (algebraMap (𝓞 c.F) c.F) = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by simpa using h1
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2
  have hw : spMap 𝔐.fn ≫ w = y₀ ≫ Y.jQ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← hd, hy, Model.j, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, ← hcomp, hfn, Category.assoc, Y.jQ_over, hu, huc]
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', (spMap 𝔐.fn) a' = a :=
      ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩
    refine ⟨y₀ a', ?_⟩
    have := congrArg (fun φ => φ a') hw
    simpa using this.symm
  refine ⟨cst₀, IsOpenImmersion.lift Y.jQ w hr, ?_, hs, hfn⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.CompanionTheory.Ar.GenPoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def AbBound {X : Scheme.{0}} (t : SAB H X) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel t.G ξ Li} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (h : LieMetric M y) (C : ℝ)
    (z : Sp ℂ ⟶ X) : Prop :=
  ∀ P : AbPart t z, IsPrincipal P.tB ∧ ∀ (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt z ⟶ t.G) (c : ℂ),
    IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left →
    HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ C * (h.ip z v₀ v₀).re

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
  {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def GoodPt (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) : Prop :=
  ∃ τ : c.F →+* ℂ, z ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧
    (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsAbLift {R : Type} [CommRing R] {t : SAB H (Sp R)} {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)}
    {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (e : FamExp t.G M B ψ) (b : Fin n → ℂ)
    (P : AbPart t (spMap (ψ b))) {A : Over (Sp ℂ)} [GrpObj A] (φ : A.left ⟶ P.tB.G.left) {Lb : LB A.left} {g' : ℕ}
    (u : HolUnif A Lb g') (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) : Prop :=
  ∀ (y : Fin g → ℂ) (s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G), s.left ≫ P.m.φ = (e.ex b y).left →
    (u.ex (ℓ y)).left ≫ φ = (s ≫ P.τ.q ≫ P.e.hom).left

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

def IsOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type}
    [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ)
    (p : Sp ℂ ⟶ Xo.X) : Prop :=
  ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ Y.j = z ≫ 𝔐.f ∧ x ≫ pullback.fst _ _ = p ∧ x ≫ pullback.snd _ _ = spMap κ

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Type} [Field L] [NumberField L]

def subGens (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : Set V :=
  {x' | ∃ e ∈ U, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
    M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x').left)}

def subFib (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : Submodule (𝓞 L) V where
  carrier := {x | ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L) (subGens M U z MB)}
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mem_subFib {M : LieModel G ξ Li} {U : Submodule Ω Li} {z : Sp (𝓞 L) ⟶ X} {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] {MB : LieModel G z V} {x : V} :
    x ∈ subFib M U z MB ↔ ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L) (subGens M U z MB) := Iff.rfl

theorem isSubFibre_subFib (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : IsSubFibre M U z MB (subFib M U z MB) := fun _ => Iff.rfl

theorem subFib_mono (M : LieModel G ξ Li) {U U' : Submodule Ω Li} (h : U ≤ U') (z : Sp (𝓞 L) ⟶ X) {V : Type}
    [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V) : subFib M U z MB ≤ subFib M U' z MB := by
  rintro x ⟨a, ha, hx⟩
  refine ⟨a, ha, Submodule.span_mono ?_ hx⟩
  rintro y ⟨e, he, r⟩
  exact ⟨e, h he, r⟩

theorem subFib_saturated (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X)
    (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier) : B.Saturated (subFib M U z MB) := by
  rintro a x ha ⟨b, hb, hx⟩
  exact ⟨b * a, mul_ne_zero hb ha, by rwa [mul_smul]⟩

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}

def gen (y : (Σ k, J k) → Ω) (a : K → ℤ) (e₀ : Ω) (c : (k : K) → J k) : Ω :=
  (∏ k, y ⟨k, c k⟩ ^ a k) * e₀

def IsCls {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : Fin r) (e : E) (t : Ω) : Prop :=
  e - t • b₀ i ∈ flagStep Ω b₀ i

def Sandwich {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    (M : LieModel G ξ Li) (V : Lat ξ Li) {r : ℕ} (b₀ : Fin r → Li) (m : ℕ) : Prop :=
  ∀ p : Cpt ξ, ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li), (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) ∧
    V.IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ M.lat p) ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧
    ∀ i, ∀ e ∈ M.lat p, (m : Ω) * π i e ∈ regAt ξ p

def gramAt {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel G ξ Li} {y : (Σ k, J k) → Ω} (h : LieMetric M y) (z : Sp ℂ ⟶ X) {n : ℕ}
    (v : Fin n → (epsAt z ⟶ G)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => h.ip z (v a) (v b)

def locRatio {L : Type} [Field L] [NumberField L] (a : K → ℤ) (w : (Σ k, J k) → L)
    (c : (k : K) → J k) (v : FinitePlace L) : ℝ :=
  ∏ k, ((⨆ i, v (w ⟨k, i⟩)) / v (w ⟨k, c k⟩)) ^ a k

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def IsValues (𝔐 : HodgeCpt Y S y) {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
    (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (MV : LieModel P.tK.G (𝟙 (Sp L)) V)
    {m : ℕ} (s : Fin m → 𝔐.Li) (sL : Fin m → V) : Prop :=
  ∀ k, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ 𝔐.t.G,
    𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) (s k) v ∧ (MV.pt (sL k)).left ≫ P.m.φ = v.left

def primeOf {L : Type} [Field L] [NumberField L] (v : FinitePlace L) : PrimeSpectrum (𝓞 L) :=
  ⟨v.maximalIdeal.asIdeal, v.maximalIdeal.isPrime⟩

end Defs

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AbPartPull

theorem exists_sabMap_tK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (K : Type) [Field K] (z : Sp K ⟶ S') (P : AbPart t (z ≫ f)), ∃ m' : SABMap P.tK t' z, m'.φ ≫ m.φ = P.m.φ := by
  intro E _ _ _ H S S' t' t f m K _ z P
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ t t' P.tK f z m P.m
  exact ⟨n, hn.symm⟩

end GlobalTheory.CompanionTheory.Ar.AbPartPull
end
