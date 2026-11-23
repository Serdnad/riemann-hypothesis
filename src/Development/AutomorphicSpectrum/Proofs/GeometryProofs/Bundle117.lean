module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle104
public import GroundTheory.FunctionField.PlaceDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle102
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverDvrExtension
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle105
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle106
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogCardQuotientBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.Twist

section Holo

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem continuousAt_holo (A : FinHolAtlas e X) {W : Set X} {g : X → ℂ} (hg : A.HoloOn W g) {x : X}
    (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) :=
    (hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩).continuousAt
  have h3 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm) h1 ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

theorem holoOn_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h) {U : Set X}
    {g : X → ℂ} (hg : A.HoloOn U g) : B.HoloOn (h ⁻¹' U) (fun y => g (h y)) := by
  rintro j y ⟨hy, hyU⟩
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm y))
  have a1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y := hh.2 j k y ⟨hy, hk⟩
  have a2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart j).symm) y) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      simpa [Function.comp, (A.chart k).left_inv hk] using hyU⟩
  refine (a2.comp a1).congr ?_
  filter_upwards [((B.chart j).isOpen_inter_preimage_symm
    ((A.chart k).open_source.preimage hh.1)).mem_nhds ⟨hy, hk⟩] with y' hy'
  simp [Function.comp, (A.chart k).left_inv hy'.2]

theorem exists_log (A : FinHolAtlas e X) {W : Set X} (hW : IsOpen W) {c : X → ℂ} (hc : A.HoloOn W c) {x : X}
    (hx : x ∈ W) (h0 : c x ≠ 0) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ ∃ L : X → ℂ, A.HoloOn V L ∧
      ∀ y ∈ V, c y ≠ 0 ∧ (L y).re = Real.log ‖c y‖ := by
  have hcont : ContinuousOn (fun y => c y / c x) W := fun y hy =>
    ((continuousAt_holo A hc hy).div_const _).continuousWithinAt
  have hV : IsOpen (W ∩ (fun y => c y / c x) ⁻¹' Complex.slitPlane) :=
    hcont.isOpen_inter_preimage hW Complex.isOpen_slitPlane
  refine ⟨_, hV, ⟨hx, ?_⟩, Set.inter_subset_left, fun y => Complex.log (c y / c x) + (Real.log ‖c x‖ : ℂ), ?_, ?_⟩
  · simp [div_self h0]
  · rintro j z ⟨hz, hzW, hzs⟩
    have a1 : AnalyticAt ℂ (c ∘ (A.chart j).symm) z := hc j z ⟨hz, hzW⟩
    have a2 : AnalyticAt ℂ (fun z => (c ∘ (A.chart j).symm) z / c x) z := a1.div analyticAt_const h0
    exact (a2.clog hzs).add analyticAt_const
  · rintro y ⟨-, hy⟩
    have hy' : c y / c x ≠ 0 := Complex.slitPlane_ne_zero hy
    have hcy : c y ≠ 0 := fun e => hy' (by simp [e])
    refine ⟨hcy, ?_⟩
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hcy) (norm_ne_zero_iff.2 h0)]
    ring

end Holo

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type}
  [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k}
  {P₀ Jd₀ : Ideal (MRing J₀)} {P Jd : Ideal (MRing J)} {D : ℕ}

theorem orbit_key (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (hv : IsBlockMap κ v) (h : R.X → R₀.X)
    (ho : ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) {x y : R.X} (hy : y ∈ R.U x)
    (hy₀ : h y ∈ R₀.U (h x)) :
    ∃ c : K₀ → ℂ, (∀ k, c k ≠ 0) ∧ ∀ p, R.lift x y (v p) = c p.1 * R₀.lift (h x) (h y) p := by
  obtain ⟨c₁, h₁, e₁⟩ := R.compat x y y ⟨hy, R.mem_U y⟩
  obtain ⟨c₂, h₂, e₂⟩ := ho y
  obtain ⟨c₃, h₃, e₃⟩ := R₀.compat (h x) (h y) (h y) ⟨hy₀, R₀.mem_U _⟩
  refine ⟨fun k => c₁ (κ k) / (c₃ k * c₂ k), fun k => div_ne_zero (h₁ _) (mul_ne_zero (h₃ k) (h₂ k)), fun p => ?_⟩
  have a₁ := congrFun e₁ (v p)
  have a₂ := congrFun e₂ p
  have a₃ := congrFun e₃ p
  simp only at a₁ a₂ a₃
  have n₂ := h₂ p.1
  have n₃ := h₃ p.1
  rw [a₃, a₂, a₁, hv.2.2.1 p]
  field_simp

theorem exists_coeff_log (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (hv : IsBlockMap κ v) (h : R.X → R₀.X)
    (hh : HoloMap R.A R₀.A h)
    (ho : ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) (x : R.X) (k : K₀) :
    ∃ V : Set R.X, IsOpen V ∧ x ∈ V ∧ V ⊆ R.U x ∩ h ⁻¹' R₀.U (h x) ∧ ∃ L : R.X → ℂ, R.A.HoloOn V L ∧
      ∀ y ∈ V, ∀ c : K₀ → ℂ, (∀ k, c k ≠ 0) →
        (∀ p, R.lift x y (v p) = c p.1 * R₀.lift (h x) (h y) p) → (L y).re = Real.log ‖c k‖ := by
  have oW : IsOpen (R.U x ∩ h ⁻¹' R₀.U (h x)) := (R.isOpen_U x).inter ((R₀.isOpen_U _).preimage hh.1)
  have mW : x ∈ R.U x ∩ h ⁻¹' R₀.U (h x) := ⟨R.mem_U x, R₀.mem_U _⟩
  obtain ⟨i, hi⟩ := (R₀.mem (h x) (h x) (R₀.mem_U _)).1 k
  obtain ⟨cx, hcx, ecx⟩ := orbit_key R₀ R hv h ho (R.mem_U x) (R₀.mem_U (h x))
  have hn : R.A.HoloOn (R.U x ∩ h ⁻¹' R₀.U (h x)) (fun y => R.lift x y (v ⟨k, i⟩)) := fun j z hz =>
    R.holo x (v ⟨k, i⟩) j z ⟨hz.1, hz.2.1⟩
  have hd : R.A.HoloOn (R.U x ∩ h ⁻¹' R₀.U (h x)) (fun y => R₀.lift (h x) (h y) ⟨k, i⟩) := fun j z hz =>
    holoOn_comp hh (R₀.holo (h x) ⟨k, i⟩) j z ⟨hz.1, hz.2.2⟩
  have hnx : R.lift x x (v ⟨k, i⟩) ≠ 0 := by
    rw [ecx ⟨k, i⟩]
    exact mul_ne_zero (hcx k) hi
  obtain ⟨Vn, oVn, mVn, sVn, Ln, hLn, eLn⟩ := exists_log R.A oW hn mW hnx
  obtain ⟨Vd, oVd, mVd, -, Ld, hLd, eLd⟩ := exists_log R.A oW hd mW hi
  refine ⟨Vn ∩ Vd, oVn.inter oVd, ⟨mVn, mVd⟩, Set.inter_subset_left.trans sVn, fun y => Ln y - Ld y, ?_, ?_⟩
  · rintro j z ⟨hz, hzn, hzd⟩
    exact (hLn j z ⟨hz, hzn⟩).sub (hLd j z ⟨hz, hzd⟩)
  · rintro y ⟨hyn, hyd⟩ c hc ec
    obtain ⟨-, e1⟩ := eLn y hyn
    obtain ⟨d0, e2⟩ := eLd y hyd
    simp only [Complex.sub_re, e1, e2]
    rw [ec ⟨k, i⟩, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 d0)]
    ring

theorem samePot_twist : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (κ : K₀ → K) (v : (Σ k, J₀ k) → Σ k, J k) (P₀ Jd₀ : Ideal (MRing J₀)) (P Jd : Ideal (MRing J)) (D : ℕ) (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (X : Type) [TopologicalSpace X] (B : FinHolAtlas D X) (Θ : LocPot X) (A₀ : HermLine J₀) (T : HermLine J) (π : R₀.X → X) (hπ : HoloMap R₀.A B π) (h : R.X → R₀.X) (hv : IsBlockMap κ v) (hc : Continuous (π ∘ h)), HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) → SamePot R₀.A Set.univ (potOf R₀ A₀) (Θ.pullback π hπ.1) → IsFlatOn R T → SamePot R.A Set.univ (potOf R ((pullHerm hv A₀).tensor T)) (Θ.pullback (π ∘ h) hc) := by
  intro K₀ K _ _ J₀ J _ _ κ v P₀ Jd₀ P Jd D R₀ R X _ B Θ A₀ T π hπ h hv hc hh ho h0 hF x _
  obtain ⟨V₀, oV₀, mV₀, G₀, hG₀, e₀⟩ := h0 (h x) trivial
  obtain ⟨V₁, oV₁, mV₁, G₁, hG₁, e₁⟩ := hF x trivial
  choose Vk oVk mVk sVk L hL eL using exists_coeff_log R₀ R hv h hh ho x
  refine ⟨(⋂ k, Vk k) ∩ ((h ⁻¹' V₀ ∩ V₁) ∩ (R.U x ∩ h ⁻¹' R₀.U (h x))),
    (isOpen_iInter_of_finite oVk).inter (((oV₀.preimage hh.1).inter oV₁).inter
      ((R.isOpen_U x).inter ((R₀.isOpen_U _).preimage hh.1))),
    ⟨Set.mem_iInter.2 mVk, ⟨mV₀, mV₁⟩, R.mem_U x, R₀.mem_U _⟩,
    fun y => G₀ (h y) + G₁ y + ∑ k, ((A₀.a k : ℝ) : ℂ) * L k y, ?_, ?_⟩
  · rintro j z ⟨hz, hzk, ⟨hz₀, hz₁⟩, -⟩
    have t0 : AnalyticAt ℂ (fun z => G₀ (h ((R.A.chart j).symm z))) z := holoOn_comp hh hG₀ j z ⟨hz, hz₀⟩
    have t1 : AnalyticAt ℂ (fun z => G₁ ((R.A.chart j).symm z)) z := hG₁ j z ⟨hz, hz₁⟩
    have t2 : ∀ k ∈ (Finset.univ : Finset K₀),
        AnalyticAt ℂ (fun z => ((A₀.a k : ℝ) : ℂ) * L k ((R.A.chart j).symm z)) z := fun k _ =>
      analyticAt_const.mul (hL k j z ⟨hz, Set.mem_iInter.1 hzk k⟩)
    exact (t0.add t1).add (Finset.analyticAt_fun_sum _ t2)
  · rintro y ⟨hyk, ⟨hy₀, hy₁⟩, hyU, hyU₀⟩
    obtain ⟨c, hc0, ec⟩ := orbit_key R₀ R hv h ho hyU hyU₀
    have E0 : Real.log (A₀.h (R₀.lift (h x) (h y))) - Θ.φ (π (h x)) (π (h y)) = (G₀ (h y)).re := e₀ (h y) hy₀
    have E1 : Real.log (T.h (R.lift x y)) - 0 = (G₁ y).re := e₁ y hy₁
    have E2 : (fun p => R.lift x y (v p)) = fun p => c p.1 * R₀.lift (h x) (h y) p := funext ec
    show Real.log (((pullHerm hv A₀).tensor T).h (R.lift x y)) - Θ.φ (π (h x)) (π (h y)) = _
    rw [log_tensor_pull hv A₀ T (R.mem x y hyU).1, E2, log_h_smul A₀ hc0 (R₀.mem _ _ hyU₀).1]
    simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, ← E0, ← E1,
      fun k => eL k y (Set.mem_iInter.1 hyk k) c hc0 ec]
    ring

end GlobalTheory.CompanionTheory.Ar.Chg.Twist
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem normPull_of_stalks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), CharZero Ω → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ) → NormPull Fl₀ Fl i h := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl j hc hreg hsl hli hfl hst hgr
    z s a t₀ ν hN
  obtain ⟨hh, b, Γ, hfs, hfr, hb, hG, hP, rfl⟩ := hN
  have hq : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hbase : Fl.b s = fun k => j (Fl₀.b s k) := funext fun k => (hfl s k).symm
  have hnf : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r ⟨centre z, hq⟩ := fun r hr => not_inFibre 𝔐.ξ z hq hr
  have hV := hst ⟨centre z, hq⟩ hnf s
  have hpush : (⟨centre (z ≫ h), hh⟩ : Cpt 𝔐₀.ξ) = pushCpt hd ⟨centre z, hq⟩ :=
    Subtype.ext (Scheme.Hom.comp_apply z h _)
  have hfr' : (𝔐₀.V s).IsFrameAt b (pushCpt hd ⟨centre z, hq⟩) := hpush ▸ hfr
  refine ⟨hq, fun k => j (b k), Γ, fun s' => ?_, ⟨hli _ b hfr.1, ?_⟩, ?_, hgr z _ b Γ hG, hP, rfl⟩
  · rw [hbase]
    exact FlagPull.flagStep_map_eq hsl hfs s'
  · rw [hV]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨e, he, rfl⟩
      have he' : e ∈ 𝔐₀.V s (pushCpt hd ⟨centre z, hq⟩) := he
      rw [hfr'.2] at he'
      clear he
      show j e ∈ Submodule.span (regAt 𝔐.ξ ⟨centre z, hq⟩) (Set.range fun k => j (b k))
      induction he' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul u x _ hx =>
        have e1 : j (u • x) = (⟨i u, hreg _ _ u.2⟩ : regAt 𝔐.ξ ⟨centre z, hq⟩) • j x := hsl (u : Ω₀) x
        rw [e1]
        exact Submodule.smul_mem _ _ hx
    · rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨b k, ?_, rfl⟩
      show b k ∈ 𝔐₀.V s (pushCpt hd ⟨centre z, hq⟩)
      rw [hfr'.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  · have hm := FlagPull.map_mem_flagStep hsl (Fl₀.b s) a hb
    rw [map_sub, hsl, hfl, ← hbase] at hm
    exact hm

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.dominating_regular_push : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i), IsCptGen ξ → (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → i a ∈ regAt ξ p) ∧ (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → unitAt ξ p (i a) → unitAt ξ₀ (pushCpt hd p) a) ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), genPt ξ ⤳ centre z → ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.Stalk.regular_along_dominant | exact GlobalTheory.CompanionTheory.Ar.Chg.Stalk.regular_along_dominant | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.Stalk.regular_along_dominant <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.dominating_coords_reindexed : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)), GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i → CoordTie ℤ ξ₀ (fun c' : (k : K₀) → J₀ k => ∏ k, y₀ ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ₀ y₀ (z ≫ h) (fun p => w (blkV bk bx p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.coordsAt_blkV | exact GlobalTheory.CompanionTheory.Ar.Chg.coordsAt_blkV | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.coordsAt_blkV <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.function_field_model_exists : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (W : Ideal (MRing J)) (p : ℕ) [Fact p.Prime], IsMultiProjPrime W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : GroundTheory.FunctionField.IsFunctionField (ZMod p) K) (w : (Σ k, J k) → K), mCoordIdeal w = W ∧ Birational w ∧ ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.Field.curve_field | exact GlobalTheory.CompanionTheory.Ar.Crv.Field.curve_field | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.Field.curve_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem _root_.GlobalTheory.T.model_over_dvr_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → pointIdeal O' (fun v => algebraMap Ω Ω' (y v)) = (pointIdeal O y).map (MvPolynomial.map (algebraMap O O')) ∧ IsModelOver (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.model_baseChange_algebraic | exact GlobalTheory.CompanionTheory.Ar.Num.model_baseChange_algebraic | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.model_baseChange_algebraic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.gram_det_ne_zero_of_indep : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (f : Fin n → B.carrier), LinearIndependent (𝓞 L) f → B.gramDet σ f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.gramDet_ne_zero_of_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.RootHt.gramDet_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.gramDet_ne_zero_of_linearIndependent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.uniform_bound_on_closed_cone : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (T : Set ((Σ k, J k) → ℂ))
    (Bd : ((Σ k, J k) → ℂ) → ℝ → Prop),
    (∀ w ∈ T, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ w ∈ closure T, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → w ∈ T) →
    (∀ w x, Bd w x → w ∈ T) →
    (∀ w x (c : K → ℂ), (∀ k, c k ≠ 0) → Bd w x → Bd (fun p => c p.1 * w p) x) →
    (∀ w₀ ∈ T, ∃ N ∈ 𝓝 w₀, ∃ C : ℝ, ∀ w ∈ N, ∀ x, Bd w x → |x| ≤ C) →
    ∃ C : ℝ, ∀ w x, Bd w x → |x| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.bound_of_local_bounds_of_blockScale | exact GlobalTheory.CompanionTheory.Ar.RootHt.bound_of_local_bounds_of_blockScale | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.bound_of_local_bounds_of_blockScale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem _root_.GlobalTheory.T.smooth_algebra_eq_zero_of_vanish_open : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ)) (f : Fin D → A) (a : A), IsOpen O → O.Nonempty → (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.eq_zero_of_forall_points_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.eq_zero_of_forall_points_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.eq_zero_of_forall_points_eq_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.gram_det_change_of_basis : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) (n : ℕ)
    (β : Fin (n + 1) → V) (x : Fin n → V) (xe : V) (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ),
    (∀ j, x j = ∑ l, C j l • β l.castSucc) → xe = ∑ l, d l • β l.castSucc + s • β (Fin.last n) → s ≠ 0 →
    (Matrix.of fun a b => core.inner (x a) (x b)).det ≠ 0 → (Matrix.of fun a b => core.inner (β a) (β b)).det ≠ 0 →
    (1 / 2) * (Real.log ‖(Matrix.of fun a b => core.inner ((Fin.snoc x xe : Fin (n + 1) → V) a)
        ((Fin.snoc x xe : Fin (n + 1) → V) b)).det‖ - Real.log ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖) =
      Real.log ‖s‖ + (1 / 2) * (Real.log ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ -
        Real.log ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_quot | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_quot <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.iota_multi_linear_combination_det : ∀ (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] (p : ℕ) (P : Matrix (Fin p) (Fin p) Ω) (v : Fin p → Vs),
    exteriorPower.ιMulti Ω p (fun i => ∑ k, P i k • v k) = P.det • exteriorPower.ιMulti Ω p v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.log_card_quotient_bound : ∀ (L : Type) [Field L] [NumberField L] (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc]
    (F₀ F₁ : Submodule (𝓞 L) Bc) (φ : F₁ →ₗ[𝓞 L] L) (s : F₁) (m : ℕ) (ρ : FinitePlace L → ℝ),
    F₁.FG → (∀ x, φ x = 0 ↔ (x : Bc) ∈ F₀) → φ s ≠ 0 → 0 < m → (∀ v, 0 < ρ v) → (Function.mulSupport ρ).Finite →
    (∀ v : FinitePlace L, (∀ x, v (φ x) ≤ (v (m : L))⁻¹ * ρ v) ∧ ∃ x, v (m : L) * ρ v ≤ v (φ x)) →
    |Real.log (Nat.card (F₁ ⧸ (F₀ ⊔ Submodule.span (𝓞 L) {(s : Bc)}).comap F₁.subtype)) -
      ∑ᶠ v : FinitePlace L, (Real.log (ρ v) - Real.log (v (φ s)))| ≤ Module.finrank ℚ L * Real.log m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.log_index_le | exact GlobalTheory.CompanionTheory.Ar.RootHt.log_index_le | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.log_index_le <;> assumption)
end
