module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle092
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle083
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle050
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle030
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortFiniteGeneratorsThetaLattice
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle093
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle049
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle010

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem fg_of_trivAt_even {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {bad : ℕ}
    (h2 : 2 ∣ bad) (h : Λ.TrivAt bad) : Λ.La.FG := by
  obtain ⟨k, hk, hle, -⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hk
    omega
  have hstd : (stdLat E n).FG := by
    unfold stdLat
    exact Submodule.fg_pi fun _ => Submodule.fg_unit 1
  have hkO : (k : 𝓞 E) ≠ 0 := by exact_mod_cast hk0
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E)) :=
    LinearMap.lsmul_injective hkO
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  have hN := isNoetherian_of_fg_of_noetherian _ hstd
  refine isNoetherian_submodule.1 hN _ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hle (Submodule.smul_mem_smul (Ideal.subset_span rfl) hv)

theorem sh_mem_span_small : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F {g' : T.R j | g' ∈ T.sh j w ∧ ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
  intro hCI D T h hG large₂ j hj w hP hL hrn hlp hS hA g hg
  obtain ⟨hgs, Λ, N, x0, P, hU, hT1, hT2, hLev, hAdm, hPh, hR⟩ := hg
  obtain ⟨-, -, -, -, -, hfd, -, hrd, hfr, hf1, -⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L hL hP.2.1 hP.2.2.1 hP.2.2.2.1
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := ((GlobalTheory.T.numerical_consequences_of_pins D T.Q h.pins).2.2.2.2.2.2 j hj).1
  have hfg : Λ.La.FG := fg_of_trivAt_even Λ (by
    unfold badN
    have h2 : 2 ∣ D.host.QS := (D.host.mem_small_iff.1 D.host.two_mem_small).2
    exact ((h2.mul_right _).mul_right _).mul_right _) hT1
  have hdf : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (Formalism.MainNotions.WeightAlgebra.DF w : ℝ) := by
    exact_mod_cast ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
  have e : ((Formalism.MainNotions.WeightAlgebra.DF w : ℕ) : ℝ) = absA w := by
    unfold absA Formalism.MainNotions.WeightAlgebra.DF degP
    push_cast
    rfl
  obtain ⟨S, hS1, hS2, -⟩ := GlobalTheory.T.exists_short_harmonic_family_unimodular D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n Λ hU hfg (hr ▸ hrn) (wtA w)
    large₂.sc.L hL hrd (by rw [hfd]; exact hP.2.2.2.2.1)
    ((Real.log_le_log (by positivity) (by linarith)).trans hP.2.2.2.2.2.2.2.1) hP.2.2.2.2.2.2.2.2
  obtain ⟨m, cf, Q, hsum⟩ := Submodule.mem_span_set'.1 (hS2 P hPh.1)
  have hQ : ∀ i, (Q i).1 ∈ harmL T.Q.c Λ (wtA w) := fun i => (hS1 _ (Q i).2).1
  choose gs hgs1 hgs2 using fun i =>
    (hS.shTot j hj (wtA w) w.n (dom_wtA w) Λ N x0 (Q i).1 hU hT1 hT2 hLev hAdm (hQ i)).2
  have hlin := GlobalTheory.T.shortThetaRule_linear_in_harmonic_polynomial hCI D T h hS j hj w Λ N x0 hU hT2 hLev m cf (fun i => (Q i).1) g gs hQ hgs hgs1
    (by rw [hsum]; exact hR) hgs2
  rw [hlin]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨⟨hgs1 i, Λ, N, x0, (Q i).1, hU, hT1, hT2, hLev, hAdm, hQ i, hgs2 i⟩, fun σ => ?_⟩)
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hA0 : 0 ≤ absA w := by rw [← e]; positivity
  have hb : Real.log (l1At σ (Q i).1) ≤ 140 * D.R.r * large₂.sc.L * absA w := by
    refine ((hS1 _ (Q i).2).2 σ).trans ?_
    rw [hr, ← e]
    exact mul_le_mul_of_nonneg_left hdf (by positivity)
  have hl1 : l1At σ (Q i).1 ≤ Real.exp (140 * D.R.r * large₂.sc.L * absA w) :=
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 hb)
  have hsup := GlobalTheory.T.log_supNorm_shortThetaGenerator_le hCI D T h hG large₂ j hj w hP hL hrn (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlp) hS hA
    Λ N x0 (Q i).1 (gs i) hU hT1 hT2 hLev hAdm (hQ i) (hgs2 i) (hgs1 i) σ _ (by positivity) hl1
  exact hsup.trans (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w 0 hL (by omega)).1

end GlobalTheory.RunIn
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_short_finite_generators_thetaLattice : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → (fun (B : WeightFamilies.Prov D) (X : PJ D B T.G.P j) => ∃ (N : ℕ) (w0 : Fin N → B.Cusp j w), Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll w ∧ N ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n)) ∧ ∀ k σ, Real.log (B.supN j w σ (w0 k)) ≤ 400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) (recB h.toLawsCore) (recPJ h j hj) := by
  first | exact @GlobalTheory.ThetaFamily.theta_family | exact GlobalTheory.ThetaFamily.theta_family | (intros; apply GlobalTheory.ThetaFamily.theta_family <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem exists_theta_ne_zero_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → 3 * WeightAlgebra.DF w + 2 ≤ T.Q.l.M → ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ f ∈ T.th j w, rdU (T.U j σ) f k x ≠ 0 := by
  intro hC D T h j hj w hn hM σ hσ k x hx
  obtain ⟨_, _, _, _, hr1, hxi, hDF, _, hc, _⟩ := GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T h j hj w
  obtain ⟨st, hnab⟩ := h.nabPin j hj
  obtain ⟨f, hf, hne⟩ := GlobalTheory.T.exists_thetaGenerator_reading_ne_zero_at_frame hC _ _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.goodEmb_iff σ).2 hσ) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.toLawsCore.unf j hj σ hσ)) hr1
    (2 * xiR D) (mul_pos two_pos hxi) (hc σ hσ) (wtA w) w.n (dom_wtA w) hn (by omega) st (T.nab j) hnab k x hx
  refine ⟨f, hf, ?_⟩
  rwa [Formalism.L2.PjFree.rdU_ofPj] at hne

end GlobalTheory.RunIn
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem noCommonZero_of_chartIndep : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → NoCommonZeroSt := by
  intro hC D T h j hj w hn _hlast hM _hα σ hσ k x hx

  obtain ⟨-, -, -, -, hr1, hxi, hDF, -, hc, -⟩ := GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T h j hj w

  obtain ⟨st, hnab⟩ := h.nabPin j hj

  obtain ⟨f, hf, hne⟩ := GlobalTheory.T.exists_thetaGenerator_reading_ne_zero_at_frame hC _ _ _ _ _ _ σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.goodEmb_iff σ).mpr hσ) ((Formalism.L2.PjFree.isUnf_ofPj _).mpr (h.unf j hj σ hσ)) hr1
    (2 * xiR D) (by linarith) (fun k τ => hc σ hσ k τ) (wtA w) w.n (dom_wtA w) hn (by omega) st (T.nab j)
    hnab k x hx
  exact ⟨f, hf, by rwa [Formalism.L2.PjFree.rdU_ofPj] at hne⟩

end GlobalTheory
end
