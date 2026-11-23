module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle056
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsNotSmallWhereCombinationsVanish
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle057
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle055
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle028
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle027
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle032
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

theorem _root_.GlobalTheory.T.genericSections_polynomial_dictionary : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ), (∀ i, toRp X la N (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = sec X la w i ∧ R.toFn t (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = R.s w t i ∧ OfWt X wL (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k)) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ F, toRp X la N (MvPolynomial.C F) = emb X la N F ∧ R.toFn t (MvPolynomial.C F) = R.ev F) ∧ (∀ u (F : B.Cusp j u), OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q)) ∧ (∀ u (p : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → toRp X la N p ∈ Vw X la N u ∧ R.toFn t p ∈ R.sp u Set.univ) ∧ (∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ) ∧ (∀ u (s : Set (B.Cusp j u)), R.sp u (Submodule.span B.KO s) = R.sp u s) ∧ (∀ u (M : Submodule B.KO (B.Cusp j u)), FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M) := by
  first | exact @GlobalTheory.Shares.polyDictionary | exact GlobalTheory.Shares.polyDictionary | (intros; apply GlobalTheory.Shares.polyDictionary <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.mem_span_cuspReadings_iff_components : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ u : WeightFamilies.Wt D j, (∀ g ∈ R.sp u Set.univ, ∃ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0) ∧ ∀ y, g y = f (e y).1 (e y).2.1) ∧ (∀ (A : ∀ k : (T.U j T.σ₀).Comp, Set (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)) (s : Set ((recB h.toLawsCore).Cusp j u)), OntoBy h j u A s → ∀ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ A k) → (fun y => f (e y).1 (e y).2.1) ∈ R.sp u s) ∧ ∀ (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp), rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0 := by
  first | exact @GlobalTheory.Shares.span_readings_components | exact GlobalTheory.Shares.span_readings_components | (intros; apply GlobalTheory.Shares.span_readings_components <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.theta_forms_bounded_by_generic_combinations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖sf i x‖ ^ 2 := by
  first | exact @GlobalTheory.Shares.forms_le_generic_comb | exact GlobalTheory.Shares.forms_le_generic_comb | (intros; apply GlobalTheory.Shares.forms_le_generic_comb <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.LowerBound

theorem le_finrank_of_pieces {K Z : Type} [Fintype K] [DecidableEq K] {Y : K → Type} (dom : ∀ k, Set (Y k))
    (e : Z ≃ Σ k, dom k) (d : K → ℕ) (C δ : ℕ) (en : Fin δ ≃ Σ k, Fin (d k))
    (f : ∀ k, Fin (d k * C) → Y k → ℂ)
    (hf : ∀ k (u : Fin (d k * C) → ℂ), (∀ x ∈ dom k, ∑ q, u q * f k q x = 0) → u = 0)
    (S : Submodule ℂ (Z → ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ k q, (fun z => (Pi.single k (f k q) : ∀ k, Y k → ℂ) (e z).1 (e z).2.1) ∈ S) :
    δ * C ≤ Module.finrank ℂ S := by
  let v : (Σ k, Fin (d k * C)) → S := fun p => ⟨_, hS p.1 p.2⟩
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have key := hf p.1 (fun q => g ⟨p.1, q⟩) fun x hx => by
      have h1 := congrFun (congrArg Subtype.val hg) (e.symm ⟨p.1, x, hx⟩)
      rw [Submodule.coe_sum, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single p.1] at h1
      · refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h1
        show _ = g _ * (Pi.single p.1 (f p.1 q) : ∀ k, Y k → ℂ) (e (e.symm ⟨p.1, x, hx⟩)).1
          (e (e.symm ⟨p.1, x, hx⟩)).2.1
        rw [e.apply_symm_apply]
        simp
      · intro k _ hk
        refine Finset.sum_eq_zero fun q _ => ?_
        show g _ * (Pi.single k (f k q) : ∀ k, Y k → ℂ) (e (e.symm ⟨p.1, x, hx⟩)).1
          (e (e.symm ⟨p.1, x, hx⟩)).2.1 = 0
        rw [e.apply_symm_apply]
        simp [Pi.single_eq_of_ne hk.symm]
      · simp
    exact congrFun key p.2
  have h1 := hv.fintype_card_le_finrank
  have h2 := Fintype.card_congr en
  simp only [Fintype.card_sigma, Fintype.card_fin] at h1 h2
  rwa [← Finset.sum_mul, ← h2] at h1

variable {D : D7}

theorem laR_wadd (T : Top D) (j : ℕ) (u v : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp) :
    laR T j (wadd u v) k = laR T j u k + laR T j v k := by
  unfold laR
  rw [wtA_wadd]
  exact laU_add (T.U j T.σ₀) (wtA u) (wtA v) u.n v.n u.n_even v.n_even k

theorem laR_wsmul (T : Top D) (j : ℕ) (m : ℕ) (u : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp) :
    laR T j (wsmul m u) k = m • laR T j u k := by
  induction m with
  | zero =>
    funext τ a
    simp [laR, laU, wtA, wsmul, Formalism.L2.Pj.ext0]
  | succ m ih =>
    have e : wsmul (m + 1) u = wadd (wsmul m u) u := by
      simp only [wsmul, wadd, add_mul, one_mul]
    rw [e, laR_wadd, ih, succ_nsmul]

theorem lower_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → MggOnto h j CR Tn c (addL wF wL Tn) → δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))) := by
  classical
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en _ CR c hc hM
  have hex : ∀ k : (T.U j T.σ₀).Comp,
      ∃ f : Fin ((Fl.Fl k).δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j)) → Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ,
        (∀ q, f q ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) ∧
        ∀ u : Fin ((Fl.Fl k).δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j)) → ℂ,
          (∀ x ∈ ((T.U j T.σ₀).X k).dom, ∑ q, u q * f q x = 0) → u = 0 := by
    intro k
    obtain ⟨⟨bb, m, h1, h2, h3⟩, -, h4, h5, h6⟩ := A.mar k
    have hint := interpCStatement_holds _ _ (A.Xa k) (Fl.Fl k) (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
      ⟨bb, m, h1, h2, h3 _ (by simp)⟩ h4 h5 (by simpa using h6 0) (GlobalTheory.ClosedModes.modeHalf_closed _ _)
    have hmany := GlobalTheory.ManyForms.exists_indep_forms _ _ (A.Xa k) (Fl.Fl k) (A.Xa k).Fp Tn (A.Xa k).c1
      (A.Xa k).frame_theta_const_pos.le hint
    rw [A.hF k, A.hL k, A.hc k] at hmany
    rw [← A.dim k, addL, laR_wadd, laR_wsmul]
    exact hmany
  choose f hfm hfi using hex
  haveI := (GlobalTheory.Shares.PolyDict.sp_finrank R (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))).1
  refine le_finrank_of_pieces (fun k => ((T.U j T.σ₀).X k).dom) e (fun k => (Fl.Fl k).δ) _ δ en f hfi _ fun k q => ?_
  obtain ⟨m, a, F, hF, hsum⟩ := hM (Pi.single k (f k q)) fun k' => by
    rw [← hc]
    by_cases hk : k' = k
    · subst hk
      rw [Pi.single_eq_same]
      exact hfm _ q
    · rw [Pi.single_eq_of_ne hk]
      exact (siegelSpaceAlgebra_holds _ _ _ (laR T j (addL wF wL Tn) k') c1).2.2.1.1
  have hE : (fun z => (Pi.single k (f k q) : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) (e z).1 (e z).2.1) =
      ∑ i, a i • R.ev ((recPlusN h j hj n).inc _ (F i)) := by
    funext z
    rw [hsum _ _ (e z).2.2, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hR.2]
  rw [hE]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, hF i, rfl⟩)

end GlobalTheory.LowerBound
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

theorem _root_.GlobalTheory.T.exists_valueBasis_in_spanning_forms : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), AnFacts R w t ka wF T Mg xs → ∀ Sh : Set (B.Cusp j wF), Submodule.span B.KO Sh = ⊤ → ∃ θ : Fin δ → B.Cusp j wF, (∀ i, θ i ∈ Sh) ∧ LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (θ i))) := by
  first | exact @GlobalTheory.Shares.exists_valueBasis_in_spanning | exact GlobalTheory.Shares.exists_valueBasis_in_spanning | (intros; apply GlobalTheory.Shares.exists_valueBasis_in_spanning <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.points_interpolation_genericSections : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → (∀ q, R.s w t 0 (xs q) ≠ 0 ∧ ∀ i : Fin (WeightFamilies.dimY D j), R.s w t i.succ (xs q) = 0) ∧ ∀ v : Fin δ → ℂ, ∃ f ∈ R.sp wF Set.univ, ∀ q, f (xs q) = v q := by
  first | exact @GlobalTheory.Shares.points_and_interp | exact GlobalTheory.Shares.points_and_interp | (intros; apply GlobalTheory.Shares.points_and_interp <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.theta_forms_not_small_where_combinations_vanish : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom, ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 < ε * ‖sf 0 x‖ ^ 2 → c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  first | exact @GlobalTheory.Shares.Low.forms_not_small | exact GlobalTheory.Shares.Low.forms_not_small | (intros; apply GlobalTheory.Shares.Low.forms_not_small <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.componentModelWeight_dimension_dictionary : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (k : (T.U j T.σ₀).Comp), (∀ u u' : WeightFamilies.Wt D j, laR T j (wadd u u') k = laR T j u k + laR T j u' k) ∧ (∀ (m : ℕ) (u : WeightFamilies.Wt D j), laR T j (wsmul m u) k = m • laR T j u k) ∧ (∀ (u v : WeightFamilies.Wt D j) (m : ℕ), laR T j (addL u v m) k = laR T j u k + m • laR T j v k) ∧ (∀ i : ℕ, laR T j (etWt D j i) k = (i * (g0 D / 2)) • de2W ((T.U j T.σ₀).X k)) ∧ nd ((T.U j T.σ₀).X k) = WeightFamilies.dimY D j ∧ ((T.U j T.σ₀).X k).p0 = (D.R.sigW j).2 ∧ ((T.U j T.σ₀).X k).Ψ.card = D.R.f ∧ ∃ tt : ((T.U j T.σ₀).X k).Ψ ≃ D.what₂.Tau, ∀ (u : WeightFamilies.Wt D j) (τ : ((T.U j T.σ₀).X k).Ψ) (a : Fin D.R.r), laR T j u k τ a = if ((T.U j T.σ₀).X k).p0 ≤ (a : ℕ) then (ext0 (u.aP (tt τ)) ((a : ℕ) - ((T.U j T.σ₀).X k).p0) : ℤ) + ((u.n / 2 : ℕ) : ℤ) else -(ext0 (u.aM (tt τ)) (((T.U j T.σ₀).X k).p0 - 1 - (a : ℕ)) : ℤ) - ((u.n / 2 : ℕ) : ℤ) := by
  first | exact @GlobalTheory.Shares.WtDic.weights_dictionary | exact GlobalTheory.Shares.WtDic.weights_dictionary | (intros; apply GlobalTheory.Shares.WtDic.weights_dictionary <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.RunIn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem firstMin_at_halfMax : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, ∀ (k : (T.U j σ).Comp), ∀ z0 ∈ ((T.U j σ).X k).dom, (∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x ≤ 2 * ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0) → 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0 → 0 < ((T.U j σ).X k).firstMinimumSq z0 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤ 80 * large₂.sc.L := by
  intro D T hL hG large₂ j hj w hP hL2 hr σ hσ f hf k z0 hz0 hmax hpos

  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega

  have hSS : ∀ Q ∈ Formalism.L2.Pj.holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n), ∀ c,
      Q c ∈ ((T.U j σ).X c).SS (laU (T.U j σ) (wtA w) w.n c) := by
    intro Q hQ
    unfold Formalism.L2.Pj.holSub at hQ
    induction hQ using Submodule.span_induction with
    | mem x hx => intro c; exact hx c
    | zero =>
      intro c
      exact ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero _ _,
        fun ξ _ x _ => ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_zero _ _ _ _ _⟩
    | add x y _ _ hx hy =>
      intro c
      obtain ⟨hx1, hx2⟩ := hx c
      obtain ⟨hy1, hy2⟩ := hy c
      refine ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add _ hx1 hy1, fun ξ hξ x' hx' => ?_⟩
      rw [Pi.add_apply, ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_add _ hx1 hy1 hξ hx', hx2 ξ hξ x' hx',
        hy2 ξ hξ x' hx', add_zero]
    | smul a x _ hx =>
      intro c
      obtain ⟨hx1, hx2⟩ := hx c
      refine ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul _ a hx1, fun ξ hξ x' hx' => ?_⟩
      rw [Pi.smul_apply, ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_smul, hx2 ξ hξ x' hx', mul_zero]
  have hcusp : (rdU (T.U j σ)) f ∈ Formalism.L2.Pj.holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
    unfold Formalism.L2.Pj.Core.C at hf
    exact ((Formalism.L2.Pj.mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n f).1 hf).2 σ hσ
  have hPk := hSS _ hcusp k
  obtain ⟨e, M, wg, hM1, hMlog, hwg, _hwglog, hfwlog, hk⟩ :=
    GlobalTheory.T.exists_rankOne_cuspData_log_bounds D T hL hG large₂ j hj w hP hL2 hr σ hσ
  obtain ⟨hspread, hflow, _hla, hNA, _hNC, _hg, hk0⟩ := hk k

  have hmb := ReciprocityTheory.ChartRestriction.G.FD.maxBound_holds D.R.r (e k).toX (laU (T.U j σ) (wtA w) w.n k)
    ((rdU (T.U j σ)) f k) M wg hPk (by linarith) hspread hwg hflow z0 hz0 hmax hpos
  have hk0pos : 0 < (e k).k0 := (e k).minWeight_pos
  have hk0le : (e k).k0 ≤ 2 := (e k).k0_le
  have hNApos : (0 : ℝ) < (e k).NA := by exact_mod_cast (e k).NA_pos
  have hMpos : 0 < M := by linarith
  have hfw : (0 : ℝ) < (fdeg D.host.E : ℝ) * wg + 2 := by positivity
  have hε : 0 < ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.epStar
    apply lt_min one_pos
    apply div_pos Real.pi_pos
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity

  have hc : ∀ τ : ((T.U j σ).X k).Ψ, ((T.U j σ).X k).c τ = (e k).k0 := by
    intro τ
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.c
    rw [(e k).ξ0_abs τ]
    ring

  have hbpos : 0 < (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 :=
    div_pos (mul_pos hk0pos hε) (pow_pos hNApos 2)
  have hlow : (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 ≤
      ((T.U j σ).X k).firstMinimumSq z0 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    apply le_csInf
    · by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have h0 : ∀ v ∈ ((T.U j σ).X k).Λ, v = 0 := by
        intro v hv
        by_contra hv0
        have hin : (∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) ∈
            {t | ∃ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 ∧
              t = ∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)} :=
          ⟨v, hv, hv0, rfl⟩
        rw [hemp] at hin
        exact hin
      have hbot : Submodule.span D.host.E (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = ⊥ :=
        Submodule.span_eq_bot.mpr h0
      rw [((T.U j σ).X k).Λ_span] at hbot
      have hmem : (Pi.single (⟨0, hr1⟩ : Fin D.R.r) (1 : D.host.E)) ∈
          (⊤ : Submodule D.host.E (Fin D.R.r → D.host.E)) := Submodule.mem_top
      rw [hbot, Submodule.mem_bot] at hmem
      have h01 := congrFun hmem ⟨0, hr1⟩
      simp at h01
    · rintro t ⟨v, hv, hv0, rfl⟩
      have hNAv : ((e k).NA : D.host.E) • v ∈ (e k).L' := (e k).NA_sub v hv
      have hNAv0 : ((e k).NA : D.host.E) • v ≠ 0 := by
        refine smul_ne_zero ?_ hv0
        exact_mod_cast (e k).NA_pos.ne'
      obtain ⟨τ0, hτ0⟩ := hmb _ hNAv hNAv0
      have hτ0' : ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 ≤
          ((T.U j σ).X k).maj z0 τ0 (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 (((e k).NA : D.host.E) • v)) := hτ0
      have hemb : ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 (((e k).NA : D.host.E) • v) =
          (Complex.ofReal ((e k).NA : ℝ)) • ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v := by
        funext a
        simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
      rw [hemb, ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_smul _ hz0 τ0 ((e k).NA : ℝ) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v)] at hτ0'
      have hsum := Finset.single_le_sum
        (f := fun τ => ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v))
        (fun τ _ => mul_nonneg (by rw [hc τ]; exact hk0pos.le)
          (ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.maj_nonneg _ hz0 τ _)) (Finset.mem_univ τ0)
      simp only [hc τ0] at hsum
      have hstep : (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 ≤
          (e k).k0 * ((T.U j σ).X k).maj z0 τ0 (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v) := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ hk0pos.le
        rw [div_le_iff₀ (pow_pos hNApos 2)]
        linarith
      exact le_trans hstep hsum
  have hla1 : 0 < ((T.U j σ).X k).firstMinimumSq z0 := lt_of_lt_of_le hbpos hlow
  refine ⟨hla1, ?_⟩

  have h1 : Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤
      Real.log (1 / ((e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2)) :=
    Real.log_le_log (one_div_pos.mpr hla1) (one_div_le_one_div_of_le hbpos hlow)
  have hlog2 : Real.log 2 ≤ large₂.sc.L := by
    have := Real.log_two_lt_d9
    linarith
  have hε' := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row.neg_log_epStar M (fdeg D.host.E) wg (e k).k0 hMpos hfw hk0pos hk0le
  have hε2 : -Real.log (ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0) ≤ 36 * large₂.sc.L := by
    refine hε'.trans (max_le (by linarith) ?_)
    linarith
  have h1b : Real.log (1 / ((e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2)) =
      2 * Real.log ((e k).NA : ℝ) + Real.log (1 / (e k).k0) -
        Real.log (ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0) := by
    rw [one_div_div, Real.log_div (pow_pos hNApos 2).ne' (mul_pos hk0pos hε).ne', Real.log_pow,
      Real.log_mul hk0pos.ne' hε.ne', one_div, Real.log_inv]
    push_cast
    ring
  rw [h1b] at h1
  linarith

end GlobalTheory.RunIn
end
end
