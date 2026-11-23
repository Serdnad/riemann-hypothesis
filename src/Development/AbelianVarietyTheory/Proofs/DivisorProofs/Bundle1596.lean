module

public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CompactSpacePointsPolAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsLocalHomeomorphAddMonoidHomOfEventuallyEq
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftOfNoetherianCase
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace GlobalTheory.RealMultChart

theorem comp_mulN {S : Scheme.{0}} (B : Over S) [GrpObj B] {T : Over S} (x : T ⟶ B) (n : ℕ) :
    x ≫ mulN B n = x ^ n := by
  induction n with
  | zero =>
    show x ≫ (toUnit B ≫ η[B]) = x ^ 0
    rw [pow_zero, Hom.one_def, ← Category.assoc, toUnit_unique (x ≫ toUnit B) (toUnit T)]
  | succ n ih =>
    show x ≫ (lift (mulN B n) (𝟙 B) ≫ μ[B]) = x ^ (n + 1)
    rw [pow_succ, Hom.mul_def, ← ih, ← Category.assoc, comp_lift, Category.comp_id]

theorem mulN_eq_mulA {S : Scheme.{0}} (B : Over S) [GrpObj B] (n : ℕ) : mulN B n = Out.mulA B n := by
  have h1 := comp_mulN B (𝟙 B) n
  rw [Category.id_comp] at h1
  rw [h1]

theorem exists_pow_eq (B : Over (Sp ℂ)) [GrpObj B] (hB : IsAbelianScheme B) (a₀ : 𝟙_ (Over (Sp ℂ)) ⟶ B)
    (n : ℕ) (hn : n ≠ 0) : ∃ b : 𝟙_ (Over (Sp ℂ)) ⟶ B, b ^ n = a₀ := by
  have hn' : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsurj : Surjective (mulN B n).left := surjective_mulN_of_isAbelianScheme ℂ B hB n hn'
  have hfin : IsFinite (mulN B n).left := by
    rw [mulN_eq_mulA]
    exact MulFiniteAny.isFinite_mulA ℂ B hB n (Nat.one_le_iff_ne_zero.2 hn)
  obtain ⟨t, ht⟩ := H1.SectionDivision.exists_section (pullback.snd (mulN B n).left a₀.left)
  have hb' : (t ≫ pullback.fst (mulN B n).left a₀.left) ≫ (mulN B n).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulN B n).left a₀.left) ≫ B.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [← Over.w (mulN B n), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  rw [← comp_mulN]
  exact Over.OverMorphism.ext hb'

theorem compactSpace_points (A : Over (Sp ℂ)) (L : LB A.left) (hL : Out.RelAmple A L) :
    @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) (PointsCompact.pointTopology A) := by
  have h1 : PointsCompact.ValueRules := valAt'_rules
  have h2 : PointsCompact.AffinePoints := existsUnique_point_of_ringHom
  obtain ⟨N, -, M, s, hcov, H⟩ := hL ⊤ (isAffineOpen_top _)
  let Y : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  let φ : Y ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι A.hom ⊤).symm
  let c₀ : ℂ →+* Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤) :=
    ((⊤ : (Sp ℂ).Opens).ι.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hc₀ : Function.Surjective c₀ := by
    have : IsIso (⊤ : (Sp ℂ).Opens).ι := inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
  have hY : @CompactSpace _ (PointsCompact.pointTopology Y) := by
    refine PointsCompact.compact_of_sections h1 h2 Y (Out.powOver A L ⊤ N) s hcov fun i => ⟨(H i).1, ?_⟩
    obtain ⟨r, hr, hs⟩ := (H i).2
    refine ⟨r, hr, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom.comp c₀,
      fun a => ?_, fun f => ?_⟩
    · have := Scheme.Hom.comp_appLE (A.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤
        (Out.nonzeroLocus (s i)) le_top
      exact (congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) this).symm
    · obtain ⟨p, rfl⟩ := hs f
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective c₀ hc₀ p
      exact ⟨q, (MvPolynomial.eval₂_map c₀ r _ q).symm⟩
  letI := PointsCompact.pointTopology Y
  letI := PointsCompact.pointTopology A
  have hsurj : Function.Surjective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ Y => x ≫ φ := by
    intro x
    have hrange : Set.range x.left ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
      rw [Scheme.Opens.range_ι]
      intro _ _
      trivial
    have hl := IsOpenImmersion.lift_fac (A.hom ⁻¹ᵁ ⊤).ι x.left hrange
    refine ⟨Over.homMk (IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hrange) ?_, ?_⟩
    · have := Over.w x
      rw [← hl, Category.assoc, ← morphismRestrict_ι] at this
      exact this
    · ext1
      exact hl
  exact hsurj.compactSpace (PointsCompact.continuous_comp h1 φ)

def trivLB (A : Over (Sp ℂ)) : LB A.left := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩


open AbelianExp in
theorem exists_holUnif_of_compact (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ)
    (hs : SmoothOfRelativeDimension g A.hom)
    (hcpt : @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) (PointsCompact.pointTopology A))
    (hdiv : ∀ (a : 𝟙_ (Over (Sp ℂ)) ⟶ A) (n : ℕ), n ≠ 0 → ∃ b, b ^ n = a) :
    Nonempty (HolUnif A (trivLB A) g) := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  have hprod := @holFamily_lift hval
  have hchart := HolChart.exists_holomorphic_chart hval hvalaff exists_holomorphic_section_of_etale
  letI := pointTopology A
  have := isTopologicalGroup_complexPoints hval A
  have : CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := hcpt
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A g hs 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin g → ℂ) :=
    chart t hW hσ ht ho
  have hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U := hσ0 ▸ (ht 0 h0).1
  have hφ : IsAnalyticGroupChart φ := by
    refine ⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩
    · have := (ht 0 h0).2 i
      rwa [hσ0] at this
    · have hH := hmulHol _ (W ×ˢ W) _ _
        (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1)
        (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)
      refine hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_
      simpa only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one] using hU1
  have hsurj : Function.Surjective hφ.exp := hφ.exp_surjective fun n hn x => hdiv x.toMul n hn
  obtain ⟨W', L, hW', h0', hL, hLm, hLe⟩ : ∃ (W' : Set (Fin g → ℂ))
      (L : (Fin g → ℂ) → (Fin g → ℂ)), IsOpen W' ∧ 0 ∈ W' ∧ DifferentiableOn ℂ L W' ∧
      Set.MapsTo L W' W ∧ ∀ᶠ v in 𝓝 0, (hφ.exp v).toMul = σ (L v) := by
    have ha := hφ.isLocalCommGroupLaw.analyticAt_logChart_symm
    have h1 : ∀ᶠ v in 𝓝 0, hφ.isLocalCommGroupLaw.logChart.symm v ∈ W :=
      ha.continuousAt.eventually (hW.mem_nhds (by simpa using h0))
    obtain ⟨W', h2, h3, h4⟩ := eventually_nhds_iff.mp (ha.eventually_analyticAt.and h1)
    exact ⟨W', _, h3, h4, fun v hv => (h2 v hv).1.differentiableAt.differentiableWithinAt,
      fun v hv => (h2 v hv).2, hφ.exp_eventuallyEq⟩
  refine ⟨⟨fun v => (hφ.exp v).toMul, fun z w => congrArg Additive.toMul (hφ.exp.map_add z w), hsurj,
    hφ.periodLattice, fun z => Iff.rfl, inferInstance, hφ.isZLattice_periodLattice.span_top,
    HolOn.of_local fun z => ?_, fun _ _ => 1, fun _ => differentiableOn_const _,
    fun _ _ _ => one_ne_zero, fun i j z hz => ?_⟩⟩
  · have hs : Continuous fun v : Fin g → ℂ => v - z := continuous_sub_right z
    have hWz : IsOpen ((fun v => v - z) ⁻¹' W') := hW'.preimage hs
    refine ⟨(fun v => v - z) ⁻¹' W', fun v => (hφ.exp z).toMul * σ (L (v - z)), by simpa using h0',
      hmulHol _ _ _ _ (HolOn.const hWz _) (HolOn.comp (HolOn.comp hσ hW' hL hLm) hWz
        (differentiableOn_id.sub_const z) fun v hv => hv), ?_⟩
    filter_upwards [(hs.tendsto' z 0 (sub_self z)).eventually hLe] with v hv
    rw [← hv, ← toMul_add, ← map_add (f := _), add_sub_cancel]
  · obtain ⟨e, he⟩ := (hval _ _).2.1 _ hz
    rw [he]
    show (1 : ℂ) = e (((1 : Γ(A.left, ⊤ ⊓ ⊤)ˣ)) : Γ(A.left, ⊤ ⊓ ⊤)) * 1
    rw [Units.val_one]
    exact ((_root_.mul_one _).trans e.map_one).symm

end GlobalTheory.RealMultChart

namespace GlobalTheory.RealMult


end GlobalTheory.RealMult
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) (m : ι → ℕ) (E' : Fr (ratOf Y) m m) (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ (y : Y.X), ∀ A ∈ E'.S y, Par m ⊤ (B * A⁻¹) ∧ ∀ x : Root m, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t := by
  first | exact @GlobalTheory.FlagPush.isEqn_diag_of_frame | exact GlobalTheory.FlagPush.isEqn_diag_of_frame | (intros; apply GlobalTheory.FlagPush.isEqn_diag_of_frame <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.linearForm_eq_of_weylAntisymmetrization_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  first | exact @GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq | exact GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq | (intros; apply GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.det_wirtingerAntiholomorphicDeriv_eq_sum : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, ContDiffAt ℝ 2 (f i) v) → (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) := by
  first | exact @GlobalTheory.GoodTop.det_dbar_eq_sum_dbar | exact GlobalTheory.GoodTop.det_dbar_eq_sum_dbar | (intros; apply GlobalTheory.GoodTop.det_dbar_eq_sum_dbar <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finiteDimensional_matrixCoefficientSpan : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W), FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first | exact @GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan | exact GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan | (intros; apply GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.grothendieckMessing_lift_of_noetherian_case : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ h) π := by
  first | exact @GlobalTheory.NoethLiftObj.liftObj_of_noetherian | exact GlobalTheory.NoethLiftObj.liftObj_of_noetherian | (intros; apply GlobalTheory.NoethLiftObj.liftObj_of_noetherian <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.isNef_pow_of_isNef : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ), M.IsNef D → (M.pow n).IsNef D := by
  first | exact @GlobalTheory.NefPow.isNef_pow | exact GlobalTheory.NefPow.isNef_pow | (intros; apply GlobalTheory.NefPow.isNef_pow <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {B N P : LB X}

theorem IsNef.topSelf_le_of_cls_eq_add (h : Published.NefProductNonneg)
    (hp : IsProjOver (strHom k (X := X))) {D : ℕ} (hD : topologicalKrullDim X = D)
    (hB : IsNef k B) (hN : IsNef k N) (hP : P.IsLB)
    (e : cls P hP = cls B hB.isLB + cls N hN.isLB) : topSelfIntersection k B D ≤ topSelfIntersection k P D := by
  classical
  have hf := algebraMap_eq_strHom k X
  have hS : QCoh.suppDim (structureModule X) ≤ D := by
    unfold QCoh.suppDim
    exact (topologicalKrullDim_subspace_le X _).trans hD.le
  have hV := diffVanish_chiPic_of_isProjOver hf (structureModule X) hp hS
  have hL : ∀ j : Fin 2, ((![B, N] : Fin 2 → LB X) j).IsLB := by
    intro j; fin_cases j
    · exact hB.isLB
    · exact hN.isLB
  have hQ : ∀ _ : Fin D, P.IsLB := fun _ => hP
  have hexp := hV.interNum_of_cls_eq_sum hL hQ (fun _ _ => (1 : ℤ)) (by
    intro _
    simp [Fin.sum_univ_two, e])
  have hnn : ∀ a : Fin D → Fin 2, 0 ≤ interNum k (structureModule X) ((![B, N] : Fin 2 → LB X) ∘ a) := by
    intro a
    refine h.interNum_nonneg hp hD ?_
    intro i
    show IsNef k (![B, N] (a i))
    generalize a i = j
    fin_cases j
    · exact hB
    · exact hN
  rw [topSelf_def, topSelf_def, hexp]
  simp only [Finset.prod_const_one, one_mul]
  have h0 := Finset.single_le_sum (fun a _ => hnn a) (Finset.mem_univ (fun _ : Fin D => (0 : Fin 2)))
  exact h0

theorem IsBig.of_cls_eq_add_nef (h : Published.NefNumerics) (hp : IsProjOver (strHom k (X := X)))
    (hb : IsBig k B) (hB : IsNef k B) (hN : IsNef k N) (hP : P.IsLB)
    (e : cls P hP = cls B hB.isLB + cls N hN.isLB) : IsBig k P := by
  obtain ⟨D, hD, -⟩ := hb.growth
  have hf := algebraMap_eq_strHom k X
  have hT : (CechPic.tens B N).IsLB := CechPic.isLB_tens hB.isLB hN.isLB
  have hTn : IsNef k (CechPic.tens B N) := IsNef.tens_of_isProjOver hB hN hp
  have hPn : IsNef k P := hTn.of_cls_eq hP (by rw [e, CechPic.cls_tens hB.isLB hN.isLB])
  have hle := IsNef.topSelf_le_of_cls_eq_add h.1 hp hD hB hN hP e
  have hpos : 0 < topSelfIntersection k B D := (h.2.2.isBig_iff hp hD hB).1 hb
  exact (h.2.2.isBig_iff hp hD hPn).2 (lt_of_lt_of_le hpos hle)

theorem IsBig.tens_nef (h : Published.NefNumerics) (hp : IsProjOver (strHom k (X := X)))
    (hb : IsBig k B) (hB : IsNef k B) (hN : IsNef k N) : IsBig k (CechPic.tens B N) := by
  have hT : (CechPic.tens B N).IsLB := CechPic.isLB_tens hB.isLB hN.isLB
  exact IsBig.of_cls_eq_add_nef h hp hb hB hN hT (CechPic.cls_tens hB.isLB hN.isLB hT)

theorem IsNef.isBig_tens_ample [IsIntegral X] (h : Published.NefNumerics)
    (hp : IsProjOver (strHom k (X := X))) (hN : IsNef k N) (hB : IsAmpleLB B) :
    IsBig k (CechPic.tens N B) := by
  have hT : (CechPic.tens N B).IsLB := CechPic.isLB_tens hN.isLB hB.isLB
  have hbig : IsBig k B := IsAmpleLB.isBig k X hp B hB
  exact IsBig.of_cls_eq_add_nef h hp hbig hB.isNef hN hT
    (by rw [CechPic.cls_tens hN.isLB hB.isLB hT, add_comm])

theorem IsNef.isPsEff : Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ N : LB X, IsNef k N → IsPsEff N := by
  intro h k _ X _ _ hp N hN
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  refine ⟨hN.isLB, A, hA, fun m hm => ?_⟩
  have hNm : IsNef k (lbPow N m) := hN.pow hA m
  have hbig : IsBig k (CechPic.tens (lbPow N m) A) := IsNef.isBig_tens_ample h hp hNm hA
  obtain ⟨r, hr, hs⟩ := (hbig.frequently_hasNonzeroSec.and_eventually (Filter.eventually_ge_atTop 1)).exists
  exact ⟨r, hs, hr⟩

end GlobalTheory
end
end

section

set_option autoImplicit false

namespace GlobalTheory.Published

theorem nefNumerics_of_product_of_riemannRoch
    (h₁ : NefProductNonneg) (h₂ : NefRiemannRoch) : NefNumerics :=
  ⟨h₁, h₂.nefBigIff, h₂⟩

end GlobalTheory.Published
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.NefGrowth

section SlopeTestRemainingChoices

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

theorem isLocallyNoetherian_of_isProjOver (hp : IsProjOver (strHom k (X := X))) :
    IsLocallyNoetherian X := by
  obtain ⟨N, ι, _, h⟩ := hp
  have : LocallyOfFiniteType (strHom k (X := X)) := h ▸ inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (strHom k X)

theorem lineBundleGlobalSectionsDim_eq_zero_of_isEmpty [IsEmpty X] (L : LB X) : lbH0 k L = 0 := by
  have : Subsingleton (coh (twist (structureModule X) L) 0) := by
    refine ⟨fun x y => ?_⟩
    have h : ∀ z : coh (twist (structureModule X) L) 0, z = 0 := fun z => by
      rw [← one_smul Γ(X, ⊤) z, Subsingleton.elim (1 : Γ(X, ⊤)) 0, zero_smul]
    rw [h x, h y]
  exact hdim_eq_zero_of_subsingleton k 0

theorem lineBundleGlobalSectionsDim_le_of_injective_section_mul [IsLocallyNoetherian X] {N A B : LB X} (hN : N.IsLB)
    (hA : A.IsLB) (hB : B.IsLB) (e : cls N hN = cls A hA + cls B hB) (s : B.Sec)
    (hs : Mono (cutHom (structureModule X) hB s))
    (hfin : Module.Finite k (coh (twist (structureModule X) N) 0)) : lbH0 k A ≤ lbH0 k N := by
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule X) hA hB hN e
  have := Twist.isQuasicoherent_twist (F := structureModule X) hA
  have : Mono (Twist.secHom (twist (structureModule X) A) s) := by
    rw [mono_secHom_iff _ hB, Twist.assPoints_twist hA, ← mono_cutHom_iff _ hB]
    exact hs
  exact LinearMap.finrank_le_finrank_of_injective
    (cohOn.map_zero_injective_of_mono k ⊤ (Twist.secHom (twist (structureModule X) A) s ≫ i.hom))

end SlopeTestRemainingChoices

open GlobalTheory.Published

theorem lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] (Z : Scheme.{0})
    [Algebra F Γ(Z, ⊤)] (d : ℕ), IsProjOver (strHom F (X := Z)) → topologicalKrullDim Z ≤ d →
    ∀ L A : LB Z, IsNef F L → IsAmpleLB A → ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ C * (m : ℝ) ^ d := by
  intro hNum F _ Z _ d hp hd L A hL hA
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact ⟨0, .of_forall fun m => by rw [lineBundleGlobalSectionsDim_eq_zero_of_isEmpty]; simp⟩
  have := isLocallyNoetherian_of_isProjOver hp
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim Z = e := by
    have h0 : topologicalKrullDim Z ≠ ⊥ := topologicalKrullDim_eq_bot_iff.not.2 (not_isEmpty_of_nonempty Z)
    revert h0 hd
    generalize topologicalKrullDim Z = D
    intro hd h0
    induction D using WithBot.recBotCoe with
    | bot => exact absurd rfl h0
    | coe D =>
      induction D using ENat.recTopCoe with
      | top =>
        have h' : (⊤ : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast hd
        exact absurd (top_le_iff.1 h') (ENat.coe_ne_top d)
      | coe n => exact ⟨n, rfl⟩
  have hed : e ≤ d := by
    rw [he] at hd
    exact_mod_cast hd
  have hLA : IsNef F (tens L A) := hL.tens hA.isNef hA
  have ht := hNum.2.2.tendsto hp he hLA
  set c : ℝ := (topSelfIntersection F (tens L A) e : ℝ) / e.factorial
  have hb := ht.eventually (gt_mem_nhds (lt_add_one c))
  have hcut : ∀ᶠ m : ℕ in atTop,
      ∃ t : (lbPow A (m - 1)).Sec, Mono (cutHom (structureModule Z) (isLB_lbPow hA.isLB (m - 1)) t) :=
    (tendsto_sub_atTop_nat 1).eventually (hA.eventually_exists_mono_cutHom_pow (structureModule Z))
  refine ⟨|c| + 1, ?_⟩
  filter_upwards [hcut, hb, eventually_ge_atTop 1] with m ⟨t, hts⟩ hm hm1
  have hcls : cls _ (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m) =
      cls _ (isLB_tens (isLB_lbPow hL.isLB m) hA.isLB) + cls _ (isLB_lbPow hA.isLB (m - 1)) := by
    rw [cls_lbPow (isLB_tens hL.isLB hA.isLB), cls_tens hL.isLB hA.isLB,
      cls_tens (isLB_lbPow hL.isLB m) hA.isLB, cls_lbPow hL.isLB, cls_lbPow hA.isLB]
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, add_smul, one_smul, smul_add]
    abel
  have h1 := lineBundleGlobalSectionsDim_le_of_injective_section_mul (k := F) (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m)
    (isLB_tens (isLB_lbPow hL.isLB m) hA.isLB) (isLB_lbPow hA.isLB (m - 1)) hcls t hts
    (finite_coh_zero_twist_of_isProjOver (algebraMap_eq_strHom F Z) hp
      (isLB_lbPow (isLB_tens hL.isLB hA.isLB) m))
  have hmpos : (0 : ℝ) < (m : ℝ) ^ e := by positivity
  have h2 : (lbH0 F (lbPow (tens L A) m) : ℝ) ≤ (c + 1) * (m : ℝ) ^ e :=
    ((div_lt_iff₀ hmpos).1 hm).le
  have h3 : (m : ℝ) ^ e ≤ (m : ℝ) ^ d := pow_le_pow_right₀ (by exact_mod_cast hm1) hed
  calc (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ lbH0 F (lbPow (tens L A) m) := by exact_mod_cast h1
    _ ≤ (c + 1) * (m : ℝ) ^ e := h2
    _ ≤ (|c| + 1) * (m : ℝ) ^ e := by gcongr; exact le_abs_self c
    _ ≤ (|c| + 1) * (m : ℝ) ^ d := by gcongr

end GlobalTheory.NefGrowth
end
end
