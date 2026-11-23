module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ExistsLeftInv
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenericFrameIntegralOffFinitelyManyFunctions
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.DualMapRComp
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.IsTanIff
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle159
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle141
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsCompatibleLaws
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle027
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.CombComb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle002
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio

@[expose] public section

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

open AlgebraicGeometry CategoryTheory ModelDimension.Near


theorem ModelDimension.integral_frame_over_cdvr : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntAll Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → T.FinRes → ∀ y : IntFr Xo c T io, letI := io.toAlgebra; ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (ψ : S →ₐ[c.F] T.Fr) (z₀ : FrPt Xo c T.Fr) (t₀ : Ix Dw → T.Frˣ), FrMap ψ w z₀ → FrBor t₀ z₀ y.1 → ∃ (F : Finset S) (n : ℕ), ∀ ψ' : S →ₐ[c.F] T.Fr, (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) → ∀ z' : FrPt Xo c T.Fr, FrMap ψ' w z' → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ letI := io'.toAlgebra; ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z'' : FrPt Xo c T'.Fr) (t' : Ix Dw → T'.Frˣ), FrMap φ z' z'' ∧ FrBor t' z'' y'.1 ∧ (∀ x : T.Fr, x ≠ 0 → vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), vV T'.V ((t' (some ⟨τ, i⟩) : T'.Frˣ) : T'.Fr) * (e₀ : ℤ) = (e' : ℤ) * vV T.V ((t₀ (some ⟨τ, i⟩) : T.Frˣ) : T.Fr) := by
  intro hG E _ _ _ H Dw l Xo c hI Y la T io e₀ ho hfin y
  letI := io.toAlgebra
  intro S _ _ w ψ z₀ t₀ hz₀ hb₀
  classical
  have hExt : GlobalTheory.Published.SemiAbelianHomExtension := hG.2.2.1
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  obtain ⟨b, hb⟩ := GlobalTheory.Reg.GenInt.exists_factor (algebraMap T.V T.Fr) hinj (io.comp (algebraMap (𝓞 c.F) c.F))
    (fun o => GlobalTheory.Reg.GenInt.int_mem_range io o)
  obtain ⟨yt, -, hyt⟩ := valCrit_proj Y.s Y.proj T.V T.Fr b (Small.ptY Y y.1) (by
    rw [Small.ptY_over, ← Tor.spMap_comp, hb])
  have := Y.t.semi.smooth
  have := projProper _ _ _ Y.proj
  obtain ⟨U, hU, hxU, -, n, v₀, hC⟩ :=
    GlobalTheory.exists_affine_lieBasis_baseChange Y.X Y.t.G (yt (IsLocalRing.closedPoint T.V)) ⊤ trivial
  replace hC : IsChart Y hU v₀ := hC
  obtain ⟨f₀, hf₀, -⟩ := GlobalTheory.ModelPoints.existsUnique_chartHom hU T.V yt hxU
  obtain ⟨α, hα, hαf⟩ := GlobalTheory.ModelPoints.exists_chart_finiteType Y.s hU
  obtain ⟨gens, hgens⟩ := fin_gen hαf
  have hy : Small.ptY Y y.1 = Tor.spMap ((algebraMap T.V T.Fr).comp f₀) ≫ hU.fromSpec := by
    rw [← hyt, ← hf₀, Tor.spMap_comp f₀, Category.assoc]
  have hz₀Y : Small.ptY Y z₀ = Tor.spMap ((algebraMap T.V T.Fr).comp f₀) ≫ hU.fromSpec :=
    (ptY_bor Y hb₀).symm.trans hy
  obtain ⟨h, hh, fh, hfh⟩ := exists_spread hU (Small.ptY Y w) ψ.toRingHom _
    ((Small.ptY_map Y hz₀).symm.trans hz₀Y)
  have hg : ∀ τ i, ∃ cv, Crd Y hU v₀ fh cv
      (Tor.spMap (Chart.dualMapR (algebraMap S (Localization.Away h))) ≫ Small.tanY Y w τ i) := fun τ i =>
    (hC.isBas fh).exists (hfh ▸ gt_bc _ (tanY_gt Y w τ i))
  choose cv hcv using hg
  let g : ∀ τ : E →+* ℂ, Matrix (Fin n) (Fin (Dw.mult τ)) (Localization.Away h) :=
    fun τ => Matrix.of fun j i => cv τ i j
  have key : ∀ (ψ' : S →ₐ[c.F] T.Fr) (z' : FrPt Xo c T.Fr), FrMap ψ' w z' → ∀ χ : Localization.Away h →+* T.Fr,
      χ.comp (algebraMap S _) = ψ'.toRingHom → Small.ptY Y z' = Tor.spMap (χ.comp fh) ≫ hU.fromSpec ∧
        ∀ τ i, Crd Y hU v₀ (χ.comp fh) (fun j => ((g τ).map χ) j i) (Small.tanY Y z' τ i) := by
    intro ψ' z' hz' χ hχ
    refine ⟨?_, fun τ i => ?_⟩
    · rw [Small.ptY_map Y hz', ← hχ, Tor.spMap_comp _ χ, Tor.spMap_comp fh χ, Category.assoc, Category.assoc, hfh]
    · have h1 := (hcv τ i).bc χ
      rw [← Category.assoc, ← Tor.spMap_comp, ← dualMapR_comp, hχ] at h1
      rw [Small.tanY_map Y hz']
      exact h1
  let χ₀ : Localization.Away h →+* T.Fr := IsLocalization.Away.lift h (Ne.isUnit hh)
  have hχ₀ : χ₀.comp (algebraMap S _) = ψ.toRingHom := IsLocalization.Away.lift_comp h _
  obtain ⟨k1, k2⟩ := key ψ z₀ hz₀ χ₀ hχ₀
  have hf : χ₀.comp fh = (algebraMap T.V T.Fr).comp f₀ := chart_inj hU (k1.symm.trans hz₀Y)
  choose C hC1 hC2 hC3 using fun τ => hC.crd_bor hb₀ τ
  choose u hu1 hu2 using fun τ => hC.integral hExt y f₀ hy τ
  have e0 : ∀ τ, (g τ).map χ₀ * C τ = (u τ).map (algebraMap T.V T.Fr) := fun τ =>
    hC3 τ _ k1 _ _ (k2 τ) (by rw [hf]; exact hu2 τ)
  have ev1 : ∀ᶠ ψ' in closeF T.V ψ.toRingHom, ∀ s ∈ gens, ModelDimension.Near.ext h χ₀ ψ' (fh s) ∈ (algebraMap T.V T.Fr).range := by
    rw [Filter.eventually_all_finset]
    intro s _
    have h1 := tend_ext (V := T.V) hh hχ₀ (fh s)
    rw [show χ₀ (fh s) = algebraMap T.V T.Fr (f₀ s) from RingHom.congr_fun hf s] at h1
    filter_upwards [h1.cong] with ψ' ⟨b', h2, _⟩
    exact ⟨b', h2⟩
  have ev2 : ∀ᶠ ψ' in closeF T.V ψ.toRingHom, ∀ τ j i, ∃ b' : T.V,
      algebraMap T.V T.Fr b' = ((g τ).map (ModelDimension.Near.ext h χ₀ ψ') * C τ) j i ∧
        b' - u τ j i ∈ IsLocalRing.maximalIdeal T.V := by
    simp only [Filter.eventually_all]
    intro τ j i
    have h1 := Tend.sum Finset.univ fun k => (tend_ext (V := T.V) hh hχ₀ (g τ j k)).mul_const (C τ k i)
    rw [show ∑ k, χ₀ (g τ j k) * C τ k i = algebraMap T.V T.Fr (u τ j i) from congrFun (congrFun (e0 τ) j) i] at h1
    exact h1.cong
  obtain ⟨F, N, hFN⟩ : ∃ (F : Finset S) (N : ℕ), ∀ ψ' : S →+* T.Fr,
      (∀ s ∈ F, ψ' s = ψ.toRingHom s ∨ (N : ℤ) ≤ vV T.V (ψ' s - ψ.toRingHom s)) → _ :=
    (eventually_ne (V := T.V) hh).and (ev1.and ev2)
  refine ⟨F, N, fun ψ' hψ' z' hz' => ?_⟩
  obtain ⟨q1, q2, q3⟩ := hFN ψ'.toRingHom hψ'
  generalize hχ : ModelDimension.Near.ext h χ₀ ψ'.toRingHom = χ at q2 q3
  have hχ' : χ.comp (algebraMap S _) = ψ'.toRingHom := hχ ▸ ext_comp χ₀ q1
  obtain ⟨k3, k4⟩ := key ψ' z' hz' χ hχ'
  have hα' : (χ.comp fh).comp α = (algebraMap T.V T.Fr).comp b := by
    apply spMap_inj
    rw [Tor.spMap_comp, ← hα, ← Category.assoc, ← k3, Small.ptY_over, hb]
  obtain ⟨f', hf'⟩ := GlobalTheory.Reg.GenInt.exists_factor (algebraMap T.V T.Fr) hinj (χ.comp fh)
    (hgens ((algebraMap T.V T.Fr).range.comap (χ.comp fh)) (fun o => ⟨b o, (RingHom.congr_fun hα' o).symm⟩) q2)
  choose W hW1 hW2 using q3
  obtain ⟨T', io', e', y', ho', halg, hrest⟩ := hI la T io e₀ ho hfin z'
  refine ⟨T', io', e', y', ho', halg, ?_⟩
  letI := io'.toAlgebra
  obtain ⟨φ, z'', t', hφ, hz'', hb''⟩ := hrest
  obtain ⟨r, -, her, hr, -⟩ := GlobalTheory.IntegralFrameCheck.nval_map_of_overLa ho ho' φ.toRingHom (fun a => φ.commutes a) hφ
  have hval : ∀ x : T.Fr, vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x := fun x => by
    rw [show vV T'.V (φ x) = _ from hr x, her]
    push_cast
    ring
  refine ⟨φ, z'', t', hz'', hb'', fun x _ => hval x, fun τ i => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.Reg.GenInt.exists_factor (algebraMap T'.V T'.Fr) (IsFractionRing.injective _ _)
    (φ.toRingHom.comp (algebraMap T.V T.Fr)) hφ
  have hF : φ.toRingHom.comp (χ.comp fh) = (algebraMap T'.V T'.Fr).comp (φ₀.comp f') := by
    rw [← hf', ← RingHom.comp_assoc, ← hφ₀, RingHom.comp_assoc]
  have k5 : Small.ptY Y z'' = Tor.spMap (φ.toRingHom.comp (χ.comp fh)) ≫ hU.fromSpec := by
    rw [Small.ptY_map Y hz'', k3, Tor.spMap_comp (χ.comp fh), Category.assoc]
  obtain ⟨C', hC1', hC2', hC3'⟩ := hC.crd_bor hb'' τ
  obtain ⟨u', hu1', hu2'⟩ := hC.integral hExt y' (φ₀.comp f') (by rw [ptY_bor Y hb'', k5, hF]) τ
  have e1 : ((g τ).map χ).map φ.toRingHom * C' = u'.map (algebraMap T'.V T'.Fr) :=
    hC3' _ k5 _ _ (fun i => by rw [Small.tanY_map Y hz'']; exact (k4 τ i).bc φ.toRingHom) (by rw [hF]; exact hu2')
  obtain ⟨B, hB⟩ := exists_left_inv (u' := Matrix.of (W τ)) (hu1 τ) (hW2 τ)
  have e2 : ((g τ).map χ).map φ.toRingHom * (C τ).map φ.toRingHom =
      ((Matrix.of (W τ)).map φ₀).map (algebraMap T'.V T'.Fr) := by
    rw [← Matrix.map_mul]
    ext j k
    rw [Matrix.map_apply, ← hW1]
    exact (RingHom.congr_fun hφ₀ _).symm
  have hB' : B.map φ₀ * (Matrix.of (W τ)).map φ₀ = 1 := by
    rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero _) (map_one _)]
  have e3 := vV_diag_eq (C := (C τ).map φ.toRingHom)
    (fun j k hjk => by rw [Matrix.map_apply, hC1 τ hjk, map_zero]) hC1'
    (fun j => by rw [Matrix.map_apply, hC2]; exact (map_ne_zero _).2 (Units.ne_zero _))
    (fun j => by rw [hC2']; exact Units.ne_zero _) hB' hu1' e2 e1 i
  rw [hC2', Matrix.map_apply, hC2] at e3
  rw [e3]
  exact hval _
end

section

open AlgebraicGeometry CategoryTheory
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace ModelDimension

theorem mem_regAt_of_over {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {R : Type} [CommRing R] (g : X ⟶ Spec (CommRingCat.of R)) (φ : R →+* Ω)
    (h : ξ ≫ g = Spec.map (CommRingCat.ofHom φ)) (q : Cpt ξ) (r : R) : φ r ∈ regAt ξ q := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.fromSpecStalk q.1 ≫ g)
  have h1 : Spec.map (ψ ≫ CommRingCat.ofHom (genMap ξ q)) = Spec.map (CommRingCat.ofHom φ) :=
    (Spec.map_comp _ _).trans ((congrArg (Spec.map (CommRingCat.ofHom (genMap ξ q)) ≫ ·) hψ).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) (LieCarrier.genMap_fromSpecStalk q)).trans h)))
  have h2 := Spec.map_injective h1
  exact ⟨ψ.hom r, congrArg (fun t => t.hom r) h2⟩

theorem inv_natCast_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (q : Cpt ξ) (hq : ∀ p : ℕ, p.Prime → ¬ InFibre ξ p q) (n : ℕ) : ((n : Ω))⁻¹ ∈ regAt ξ q := by
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => exact (not_not.1 (hq p hp)).2.2
  | mul a b ha hb => rw [Nat.cast_mul, mul_inv]; exact mul_mem ha hb

theorem constant_regular_away_fibres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (q : Cpt 𝔐.ξ), (∀ p : ℕ, p.Prime → ¬ InFibre 𝔐.ξ p q) → ∀ a : c.F, 𝔐.cst a ∈ regAt 𝔐.ξ q := by
  intro E _ _ _ H Dw l Xo c Y S Ω _ K _ J y 𝔐 q hq a
  have hfin := c.fin
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a)
  obtain ⟨n, o, hn, ho⟩ := halg.exists_nsmul_eq (𝓞 c.F)
  have h1 : 𝔐.cst (algebraMap (𝓞 c.F) c.F o) ∈ regAt 𝔐.ξ q :=
    mem_regAt_of_over (𝔐.f ≫ Y.s) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) 𝔐.cst_over q o
  have h0 : (n : Ω) ≠ 0 := by
    rw [← map_natCast 𝔐.cst]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)
  have h2 : 𝔐.cst a = (n : Ω)⁻¹ * 𝔐.cst (algebraMap (𝓞 c.F) c.F o) := by
    rw [← ho, nsmul_eq_mul, map_mul, map_natCast, inv_mul_cancel_left₀ h0]
  rw [h2]
  exact mul_mem (inv_natCast_mem_regAt q hq n) h1

end ModelDimension
end
end

section

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.Ar.Rec.ReadEx
attribute [-instance] GlobalTheory.CompHt.fintypePsi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {SS : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

theorem ModelDimension.geo_core (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (Z : Comp Xo c)
    (hZ : GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z)) :
    letI := Small.cstAlg Or
    ∃ (φ : Om Z →ₐ[c.F] RM.Ω) (P : FrPt Xo c RM.Ω) (t : Ix Dw → (RM.Ω)ˣ), FrMap φ (genFr h Z) P ∧ FrBor t P Fr.y₀ ∧
      (letI := φ.toRingHom.toAlgebra; Module.finrank (Om Z) RM.Ω = Or.Fl.deg) := by
  letI algΩ := Small.cstAlg Or
  obtain ⟨ψ, hψ, hc⟩ := GlobalTheory.T.root_origin_component_generic_point E H Dw l Xo c Y SS RM Sys Fx Or Z hZ
  obtain ⟨hgx, y₀, hy₀, hy₀c⟩ := isGenFr_genFr h Z
  obtain ⟨N, ec, hx, hb, hj, hli₀, hli, hmem⟩ := flags_setup Or Fr Z ψ hψ hc y₀ hy₀
  letI algfn : Algebra Or.𝔐.Ω₀ RM.Ω := Or.𝔐.fn.toAlgebra
  have hg' := generic_cast Or.Fl.j (labelRk Dw) (fun s => Dw.mult (Small.labelC s)) (Small.mult_labelC Dw) Or.Fl.V₀
    Or.Fl.b Or.Fl.deg Or.Fl.generic
  obtain ⟨v, Tm, hv1, hv0, hvi, hvd, hbT, hT0, hTd⟩ := lin_core Or.Fl.j Or.Fl.V₀ _ Or.Fl.deg hg'
    (fun s => ec (Small.labelC s)) (fun s => hli₀ _) hmem (fun s => hli _)
  obtain ⟨T, hTi, hTr, hTv⟩ := exists_strictHenselian_absolutely_closed_local_ring v hvi
  obtain ⟨φ, hφC, hφX, hφd⟩ := exists_lift ψ T hTi
  have hφk : ∀ x, φ (algebraMap (kap Z) (Om Z) x) = Or.𝔐.fn (ψ x) := fun x => by
    rw [IsScalarTower.algebraMap_apply (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) x]
    exact hφC x
  have hφc : ∀ a : c.F, φ (algebraMap c.F (Om Z) a) = Or.𝔐.cst a := fun a => by
    rw [gfp_tower Z a, hφk, hc]
  let φA : Om Z →ₐ[c.F] RM.Ω := { φ with commutes' := hφc }
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  obtain ⟨y₃, h₃⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ φA (genFr h Z)
  have hk : φ.comp (algebraMap (kap Z) (Om Z)) = Or.𝔐.fn.comp ψ.toRingHom := RingHom.ext hφk
  have hbase : spMap φ ≫ (genFr h Z).x = Fr.y₀.x := by
    rw [hgx, ← Category.assoc, spc, hk, ← hy₀]
    exact hx
  have hx₃ : y₃.x = Fr.y₀.x := h₃.1.trans hbase
  have hcoef : ∀ s (i j : Fin (Dw.mult (Small.labelC s))), φ (genCoef Z (Small.labelC s) i j) = v s j i := by
    intro s i j
    unfold genCoef
    split_ifs with h1 h2
    · rw [hφX]
      exact hTv s i j h1
    · subst h2
      rw [map_one, hv1]
    · rw [map_zero, hv0 s j i (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))]
  have hy3 : ∀ s, y₃.u (Small.labelC s) = fun m =>
      (N.pt (∑ l, v s l m • Or.Fl.j (ec (Small.labelC s) l))).left := by
    intro s
    funext i
    have h1 := GlobalTheory.T.is_comb_base_change E H Dw l Xo _ _ φ (genFr h Z).x _ _ _ _ (hy₀c (Small.labelC s) i)
    have hv : (fun j => spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (Formalism.L2.Pj.dualMap (algebraMap (kap Z) (Om Z))) ≫
        y₀.u (Small.labelC s) j) = fun j => (N.pt (Or.Fl.j (ec (Small.labelC s) j))).left := by
      funext j
      rw [hj, ← Category.assoc, spc, ← dualMap_comp₂, hk]
    rw [hbase, hv, comb_iff N] at h1
    rw [h₃.2.1]
    refine h1.trans ?_
    simp only [hcoef]
  obtain ⟨t, ht⟩ : ∃ t, FrBor t y₃ Fr.y₀ := frBor_of_comb y₃ Fr.y₀ hx₃.symm (fun τ i => by
    obtain ⟨s, rfl⟩ := (Small.labelC_bijective H).2 τ
    refine ⟨Tm s i, isUnit_iff_ne_zero.2 (hTd s i), fun j hij => hT0 s i j hij, ?_⟩
    rw [hx₃, hy3 s, comb_iff N]
    exact (hb s i).symm.trans (congrArg (fun e => (N.pt e).left) (hbT s i)))
  refine ⟨φA, y₃, t, h₃, ht, hφd.trans ?_⟩
  rw [hTr, ← adjoin_all_eq_strict v hv1 hv0]
  exact hvd

end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace ModelDimension

theorem component_laws_unif_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → letI := Small.cstAlg Or; ∃ (φ : Om Z →ₐ[c.F] RM.Ω) (P : FrPt Xo c RM.Ω) (t : Ix Dw → (RM.Ω)ˣ), FrMap φ (genFr h Z) P ∧ FrBor t P Fr.y₀ ∧ (letI := φ.toRingHom.toAlgebra; Module.finrank (Om Z) RM.Ω = Or.Fl.deg) := by
  intro E _ _ _ H Dw l Xo c r U h e _ Y S RM Sys Fx Or Fr Z hZ
  exact geo_core Or Fr h Z hZ

end ModelDimension
end

section

open AlgebraicGeometry CategoryTheory
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace ModelDimension

theorem subring_spec_morphism_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Ω : Type) [Field Ω] (A : Subring Ω) (g₁ g₂ : Spec (CommRingCat.of A) ⟶ Y.X), Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ g₁ = Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ g₂ → g₁ = g₂ := by
  intro E _ _ _ H Dw l Xo c O _ β Y Ω _ A g₁ g₂ h
  have hpr : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hsep : Y.X.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from Y.s]
    infer_instance
  have hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A Ω))) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap A Ω)).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (Subtype.val_injective)]
      exact bot_le)
  exact ext_of_isDominant _ h

end ModelDimension
end
end
