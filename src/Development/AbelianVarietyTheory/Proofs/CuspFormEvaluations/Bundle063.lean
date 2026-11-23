module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle062
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingProductsIndependentModuloDeepProducts
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle060
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumNormSqOrbit
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle008
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLastEntryPosNotLastPos
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.finrank_lower_bound_cuspForm_vanishing_low_coeff : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → MggOnto h j CR Tn c (addL wF wL Tn) → δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))) := by
  first | exact @GlobalTheory.LowerBound.lower_bound | exact GlobalTheory.LowerBound.lower_bound | (intros; apply GlobalTheory.LowerBound.lower_bound <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GenericFlat

theorem ae_exists_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] [Countable K] (σ : K →+* ℂ), RelIn σ X Xa → ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, ∃ Fl : FlatM X Xa, (∀ x, Fl.w0 x = ∑ j, t (0, j) * Xa.w j x) ∧ ∀ k x, Fl.s k x = ∑ j, t (k.succ, j) * Xa.w j x := by
  intro E _ _ _ r X Xa K _ _ σ hR
  filter_upwards [GlobalTheory.T.ae_transcendental_point_nonvanishing K σ (Fin (nd X + 1) × Fin Xa.N), GlobalTheory.T.ae_coefficients_common_zeros_simple E r X Xa] with t hgen hsimple

  have hdom : ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖∑ j, t (i, j) * Xa.w j x‖ ^ 2 :=
    GlobalTheory.T.theta_forms_bounded_by_generic_combinations E r X Xa K σ t hgen hR
  have hlow : ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom,
      ∑ i : Fin (nd X), ‖∑ j, t (i.succ, j) * Xa.w j x‖ ^ 2 < ε * ‖∑ j, t (0, j) * Xa.w j x‖ ^ 2 →
        c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
    GlobalTheory.T.theta_forms_not_small_where_combinations_vanish E r X Xa K σ t hgen hR
  have hsim : ∀ x ∈ X.dom, ∑ j, t (0, j) * Xa.w j x ≠ 0 →
      (∀ k : Fin (nd X), ∑ j, t (k.succ, j) * Xa.w j x = 0) →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        (∑ j, t (k.succ, j) * Xa.w j (cpt X x z)) / ∑ j, t (0, j) * Xa.w j (cpt X x z) : V (nd X))) 0).det ≠ 0 :=
    hsimple
  obtain ⟨C, hC⟩ := hdom

  have hzero : ∀ x ∈ X.dom, (∀ k : Fin (nd X), ∑ j, t (k.succ, j) * Xa.w j x = 0) →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        (∑ j, t (k.succ, j) * Xa.w j (cpt X x z)) / ∑ j, t (0, j) * Xa.w j (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
    intro x hx hs
    have hs0 : ∑ j, t (0, j) * Xa.w j x ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Xa.w_nz x hx
      have hsum : ∑ i, ‖∑ j, t (i, j) * Xa.w j x‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
        · simp [h0]
        · simp [hs m]
      have hle := hC x hx
      rw [hsum, mul_zero] at hle
      have hk' : ‖Xa.w k x‖ ^ 2 ≤ ∑ k, ‖Xa.w k x‖ ^ 2 :=
        Finset.single_le_sum (f := fun k => ‖Xa.w k x‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
      have h2 : ‖Xa.w k x‖ ^ 2 = 0 := le_antisymm (hk'.trans hle) (by positivity)
      exact hk (by simpa using h2)
    exact hsim x hx hs0 hs
  obtain ⟨Fl, h0, hs⟩ := GlobalTheory.FlatPoints.exists_flat GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames
    GlobalTheory.FlagMahler.mahler_compactness r X Xa (fun i j => t (i, j)) ⟨C, hC⟩ hlow hzero
  exact ⟨Fl, fun x => congrFun h0 x, fun k x => congrFun (congrFun hs k) x⟩

end GlobalTheory.GenericFlat
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.leadingProducts_independent_modulo_deepProducts : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → LinearIndependent ℂ (vals xs θ) → LinearIndependent ℂ (R.lead w t Tn (a0 D j Tn) θ) ∧ Disjoint (Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ))) (R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn)) := by
  first | exact @GlobalTheory.Shares.LeadDeep.main | exact GlobalTheory.Shares.LeadDeep.main | (intros; apply GlobalTheory.Shares.LeadDeep.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem nonempty_heightOneSpectrum_ringOfIntegers (K : Type) [Field K] [NumberField K] :
    Nonempty (HeightOneSpectrum (𝓞 K)) := by

  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩⟩

theorem shareRhoP_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ) (CR c : ℝ) (δ : ℕ) (xs : Fin δ → R.Y), AnFacts R w t ka wF T (WeightFamilies.MggK B CR T c j ka) xs → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ T → LatAt B j ka → ShareRhoP (D := D) (j := j) T (WeightFamilies.rhoP B CR T c j ka) (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF N w R t T CR c δ xs hA hD hT hL
  obtain ⟨la⟩ := nonempty_heightOneSpectrum_ringOfIntegers B.KO

  have hdim : ∀ M : Submodule B.KO (B.Cusp j ka),
      Module.finrank ℂ (R.sp ka M) = Module.finrank B.KO M := fun M =>
    ((GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t).2.2.2.2.2.2.2 ka M).2
  have hspan : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ :=
    Submodule.IsFullLattice.span_eq_top (self := hL)

  have hd : X.rk ka (B.Mlat j ka) = Module.finrank B.KO (B.Cusp j ka) := by
    unfold PJ.rk
    rw [hspan, finrank_top]
  have hup : Module.finrank ℂ (R.sp ka Set.univ) = Module.finrank B.KO (B.Cusp j ka) := by
    have h := hdim ⊤
    rwa [Submodule.top_coe, finrank_top] at h

  have hsum := Submodule.finrank_quotient_add_finrank (WeightFamilies.MggK B CR T c j ka)
  have hq := rhoP_eq_finrank B CR T c j ka hspan
  have hlo := hA.lower
  rw [hdim] at hlo
  have key := (GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair (WeightFamilies.dimY D j) T).2 δ (X.rk ka (B.Mlat j ka)) (WeightFamilies.rhoP B CR T c j ka) hD hT
    (by rw [hd, ← hup]; exact hA.upper)
  exact key.2 (by rw [hq, hd, ← hsum]; omega)

end GlobalTheory.Shares
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsCore : ∀ (D : D7) (T : Core D), LawsCore T → GamAt T := by
  intro D T h j hj σ hσ k γ h1 h2
  exact GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence D T h j hj σ hσ k γ h1 h2

end GlobalTheory.RunIn
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory

theorem isHomogeneous_of_rowDeg {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) :
    P.IsHomogeneous (∑ τ, ∑ i : Fin (r τ), a τ i) := by
  intro m hm
  have h := hP m (MvPolynomial.mem_support_iff.2 hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using h τ i

theorem exists_harmA_ne_zero_and_isHomogeneous :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (Dom a n → Dw.p + Dw.q ≤ n → ∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) ∧ ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P.IsHomogeneous (Formalism.L2.Pj.DF Dw a) :=
  fun _ _ _ _ _ _ _ c _ _ =>
    ⟨fun ha hn => ThetaClaimsCompare.exists_harmA_ne_zero c (ThetaClaimsCompare.rowsDominant_of_dom ha) hn,
      fun _ hP => isHomogeneous_of_rowDeg hP.2.2⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.isotropicSum_independent_of_choices_local : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (P : MvPolynomial (LtN Dw n) c.F) (T : Type) [CommRing T] [IsLocalRing T] [Algebra c.F T] (y : FrPt Xo c T) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ q, ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F1 q i b) (colOf m b) = ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b) := by
  first | exact @GlobalTheory.shortSum_indep_local | exact GlobalTheory.shortSum_indep_local | (intros; apply GlobalTheory.shortSum_indep_local <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.runScalars_ne_zero_and_log_bounded : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ), 0 < p → 1 ≤ nW → wL.n = nW → IsF' ka wL wF Tn nP → ka.n = nP + Tn * nW → (scalOfP B hinj EX p ka wL wF Tn).sF ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).s0 ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).sK ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, (Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sW : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wL.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sF : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).s0 : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul (WeightFamilies.dimY D j) wL)).size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sK : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * ka.size) := by
  first | exact @GlobalTheory.RunIn.scalOfP_size | exact GlobalTheory.RunIn.scalOfP_size | (intros; apply GlobalTheory.RunIn.scalOfP_size <;> assumption)
end
