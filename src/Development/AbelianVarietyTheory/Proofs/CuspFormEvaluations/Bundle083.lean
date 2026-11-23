module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle081
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle107
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.analyticFacts_of_thetaData_on_models : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (N : ℕ) (ka wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (CR c : ℝ), addL wF wL Tn = ka → Nonempty (ArchAt h j w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → TieMaxCuspSt h j CR Tn c ka → ∃ (R : Rdg (recPlusN h j hj n)) (t : Idx D j N → ℂ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t ∧ AnFacts R w t ka wF Tn (WeightFamilies.MggK n.base CR Tn c j ka) xs := by
  first | exact @GlobalTheory.Shares.exists_anFacts_record | exact GlobalTheory.Shares.exists_anFacts_record | (intros; apply GlobalTheory.Shares.exists_anFacts_record <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

theorem _root_.GlobalTheory.T.levelCover_larger_coeffField_lying_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (d : DeltaDat Xo c n), (∀ (k : Type) [CommRing k] [Algebra c.F k] [Algebra c'.F k] [Algebra d.c₂.F k] [A₂ : Algebra (covCoeff hle d).F k] (h : AlgOver c c' hle k) (h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k) (y₂ : FrPt d.Xo₂ (covCoeff hle d) k) (y : FrPt Xo c' k), @FrOver E _ _ _ H Dw l Xo c' n (ddBC hle d) k _ _ A₂ y₂ y ↔ FrOver d (y₂.res (le_covCoeff hle d) h₂) (y.res hle h)) ∧ (d.IsLev → (ddBC hle d).IsLev) := by
  first | exact @GlobalTheory.FieldBC.frOver_isLev_ddBC | exact GlobalTheory.FieldBC.frOver_isLev_ddBC | (intros; apply GlobalTheory.FieldBC.frOver_isLev_ddBC <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaValue_analyticFrame_eq_polyDeriv_fock : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ mk : Dw.La →+ (Fin g → ℂ), (∀ a, mk a ∈ Φ.lat) → (∀ (α : 𝓞 E) a, mk (α • a) = tyAct ty α (mk a)) → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • mk a)) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ θ, Φ.toAnFr.Rd 1 y.s θ → ∀ (n : ℕ) (x x2 : Fin n → Dw.La), (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ b, x2 b - x b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v : ℂ, ThValAt Xo c nab y x P v → v = ((l.M : ℂ)⁻¹) ^ P.totalDegree * I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, fock Φ.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • mk (x2 b)) (fun w => θ ((l.M : ℂ) • w)) (z b)) 0 := by
  first | exact @GlobalTheory.AnVal.thValAt_eq_polyDeriv_fock | exact GlobalTheory.AnVal.thValAt_eq_polyDeriv_fock | (intros; apply GlobalTheory.AnVal.thValAt_eq_polyDeriv_fock <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.log_card_components_le_at_good_embedding : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * Zb D large₂ ^ 2 := by
  first | exact @GlobalTheory.RunIn.log_card_comp_le | exact GlobalTheory.RunIn.log_card_comp_le | (intros; apply GlobalTheory.RunIn.log_card_comp_le <;> assumption)
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

theorem thetaRule_exists_and_eval : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (xx : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → (∃ f : Rul Xo c, IsThRule Xo c nab xx P f ∧ f ∈ sec Xo c a n) ∧ ∀ f : Rul Xo c, IsThRule Xo c nab xx P f → ∀ (k : Type) [Field k] [Algebra c.F k] (y : FrPt Xo c k), ThValAt Xo c nab y xx P (evR Xo c f y) := by
  intro hC E _ _ _ H Dw l Xo c _ nab hn a n xx P hP
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hT := GlobalTheory.thValTot_of_chartIndep hL hC E H Dw l Xo c nab hn
  refine ⟨?_, fun f hf k _ _ y => ?_⟩
  · obtain ⟨f, hf, -⟩ := existsUnique_thRule Xo c nab hT xx hP
    exact ⟨f, hf, GlobalTheory.thetaRule_mem_sec hL hC E H Dw l Xo c nab hn a n f ⟨xx, P, hP, hf⟩⟩
  · have h := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c k y
    obtain ⟨w, hw, -⟩ := hT k y a n xx P hP
    have e : evR Xo c f y = w := by
      unfold evR Formalism.L2.Pj.evalAt
      rw [dite_eq_left h]
      exact GlobalTheory.thetaValue_natural hL hC E H Dw l Xo c nab hn _ _ _ _ y
        h.choose_spec.choose_spec.choose_spec a n xx P hP _ _ (hf _ _) hw
    rw [e]
    exact hw

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.ShortRuleLinear

section General

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem map_mem_HHa {F F₂ : IntermediateField ℚ ℂ} (h : F = F₂) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) F}
    (hP : P ∈ HHa Dw.mult n F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    MvPolynomial.map (IntermediateField.equivOfEq h : F →+* F₂) P ∈
      HHa Dw.mult n F₂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  subst h
  have e : (IntermediateField.equivOfEq (rfl : F = F) : F →+* F) = RingHom.id F := RingHom.ext fun _ => rfl
  rw [e, MvPolynomial.map_id]
  exact hP

theorem eq_sum_of_isShortRule (hC : ChartIndepSt2) (Xo : Moduli Dw l) (c : Coeff l) {n : ℕ} (d : DeltaDat Xo c n)
    (hd : d.IsLev) [StarRing (𝓞 E)] (hn : IsNab d.Xo₂ d.c₂ d.nab₂) (a : (E →+* ℂ) × ℕ → ℕ) (Λ : GenLat E n) (N : ℕ)
    (x0 : Fin n → Dw.La) (hU : Λ.Unimod) (hT : Λ.TrivAt d.l₂.M) (hL : Λ.LevOK N d.l₂.M) (m : ℕ) (cf : Fin m → c.F)
    (Q : Fin m → MvPolynomial (LtN Dw n) c.F) (g : Rul Xo c) (gs : Fin m → Rul Xo c)
    (hQ : ∀ i, Q i ∈ harmL c Λ a) (hg : g ∈ sec Xo c a n) (hgs : ∀ i, gs i ∈ sec Xo c a n)
    (hr : IsShortRule Xo c d Λ N x0 (∑ i, cf i • Q i) g) (hrs : ∀ i, IsShortRule Xo c d Λ N x0 (Q i) (gs i)) :
    g = ∑ i, cf i • gs i := by
  rw [← sub_eq_zero]
  refine GlobalTheory.Frames.ptsDetect_framed E H Dw l Xo c a n _
    (Submodule.sub_mem _ hg (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hgs i))) ?_
  intro k _ _ _ y
  let _ : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have hk : ∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x := fun x => by
    show algebraMap c.F k (d.eF.symm (d.eF x)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := hr k hk y y₂ hy
  choose u hu eu using fun i => hrs i k hk y y₂ hy
  have hm : MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (∑ i, cf i • Q i) =
      ∑ i, d.eF (cf i) • MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (Q i) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    rfl
  rw [hm] at hv
  have hlin := GlobalTheory.T.short_theta_value_linear_in_polynomial hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hn n Λ N hU hT hL a (d.w x0) _ m (fun i => d.eF (cf i))
    (fun i => MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (Q i)) (fun i => map_mem_HHa d.hF.symm (hQ i).1) k y₂ v u hv hu
  let L := evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
  have hL : ∀ f, L f = evR Xo c f y := fun _ => rfl
  change L (g - ∑ i, cf i • gs i) = 0

  rw [map_sub, map_sum, hL, e, hlin, Finset.mul_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hL, eu, hk, Algebra.smul_def]
  ring

end General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem shortRule_linear : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), LawsSh T → ∀ (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La), Λ.Unimod → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → ∀ (m : ℕ) (cf : Fin m → T.Q.c.F) (Q : Fin m → MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j) (gs : Fin m → T.R j), (∀ i, Q i ∈ harmL T.Q.c Λ (wtA w)) → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → (∀ i, gs i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (∑ i, cf i • Q i) g → (∀ i, IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (Q i) (gs i)) → g = ∑ i, cf i • gs i := by
  intro hC D T _ hS j hj w Λ N x0 hU hT hL m cf Q g gs hQ hg hgs hr hrs
  obtain ⟨_, hn⟩ := hS.dNab j hj w.n
  exact eq_sum_of_isShortRule hC (T.Q.Xo j) T.Q.c (T.dδ j w.n) (hS.dLev j hj w.n) hn (wtA w) Λ N x0 hU hT hL m cf Q g gs
    hQ hg hgs hr hrs

end GlobalTheory.ShortRuleLinear
end
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.shortThetaRule_linear_in_harmonic_polynomial : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), LawsSh T → ∀ (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La), Λ.Unimod → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → ∀ (m : ℕ) (cf : Fin m → T.Q.c.F) (Q : Fin m → MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j) (gs : Fin m → T.R j), (∀ i, Q i ∈ harmL T.Q.c Λ (wtA w)) → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → (∀ i, gs i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (∑ i, cf i • Q i) g → (∀ i, IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (Q i) (gs i)) → g = ∑ i, cf i • gs i := by
  first | exact @GlobalTheory.ShortRuleLinear.shortRule_linear | exact GlobalTheory.ShortRuleLinear.shortRule_linear | (intros; apply GlobalTheory.ShortRuleLinear.shortRule_linear <;> assumption)

end
end
