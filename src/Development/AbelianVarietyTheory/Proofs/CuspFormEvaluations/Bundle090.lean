module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle038
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormShortGeneratorEvalLeOrthonormalFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle089
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle049
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_level_translate_jet_ne_zero_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), P ≠ 0 → 3 * P.totalDegree + 2 ≤ M → ∃ y : Matrix (Fin n) (Fin r) E, (∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ y' : Matrix (Fin n) (Fin r) E, (∀ b, y' b - y b ∈ L) → κ * thP X hr bas idx (heisG X bas y' v) P x ≠ 0 := by
  first | exact @GlobalTheory.Dict.exists_level_translate_jet_ne_zero | exact GlobalTheory.Dict.exists_level_translate_jet_ne_zero | (intros; apply GlobalTheory.Dict.exists_level_translate_jet_ne_zero <;> assumption)
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

theorem _root_.GlobalTheory.T.norm_short_generator_eval_le_orthonormal_frame : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → ∀ d : DeltaDat Xo c n, d.IsLev → 0 < d.pd → l.A = 1 → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∃ ph ψ x₀, d.PhiPin ph ψ x₀) → UnitC d → ∀ (Λ : GenLat E n) (N : ℕ) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → (∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) → P ∈ harmL c Λ a → IsShortRule Xo c d Λ N x0 P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (d.pd : ℝ) ^ (fdeg E * r * n) * ((∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n)) := by
  first | exact @GlobalTheory.Dict.ShortPoint.norm_evR_le | exact GlobalTheory.Dict.ShortPoint.norm_evR_le | (intros; apply GlobalTheory.Dict.ShortPoint.norm_evR_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integralityBound_of_family_containing_scaled_thetaRules : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → (∀ σ, GoodEmb c σ → IsUnf (U σ) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)) ∧ ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), Dom a n → P₁ ∈ harmA c a n → _root_.GlobalTheory.BlockTh.IsBlockProd P₁ → ∀ s : c.F, (∀ σ : c.F →+* ℂ, (l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ s‖ ^ 2) → ∀ (N : ℕ) (wR : Fin (N + 1) → Rul Xo c), (∀ i, wR i ∈ sec Xo c a n) → ContainsTh Xo c nab s P₁ wR → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ tableLineDegreeFive cc : ℝ, p14 E r n m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (m : ℝ) ^ 4 * (I2.dstar (E := E) m : ℝ) ^ 4 * I2.RR (E := E) / l.M ≤ cc → I2AtFramePoints U xR wR (a, n) (I2.th (E := E) l.M R0) tableLineDegreeFive P₁.totalDegree cc := by
  first | exact @GlobalTheory.AnVal.i2iAt_of_containsTh | exact GlobalTheory.AnVal.i2iAt_of_containsTh | (intros; apply GlobalTheory.AnVal.i2iAt_of_containsTh <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem log_sup_theta_generator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ f) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  intro hCI D T hT hG large₂ j hj w hPR hL hr hLP x P hP f hf σ ℓ hℓ hp1
  obtain ⟨inst, hnab⟩ := hT.nabPin j hj
  have hunf : IsUnf (T.U j (goodOf T.Q.c σ)) := hT.toLawsCore.unf j hj _ (goodEmb_goodOf T.Q.c σ)
  obtain ⟨hfd, hrdl, hrd1, hf1, hr1, hxi, hDF, habs, hcU, hlie, -, -, -, hl1⟩ :=
    GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T hT j hj w
  obtain ⟨-, hLrd, -, -, hLf, -, -, hLa, hLn⟩ := id hPR
  have hL0 : (0 : ℝ) < large₂.sc.L := by linarith
  have ha0 : (0 : ℝ) ≤ absA w := by rw [habs]; exact Nat.cast_nonneg _
  have hσg : GoodEmb T.Q.c (goodOf T.Q.c σ) := goodEmb_goodOf T.Q.c σ
  have hNs : T.Ns j w σ f = lieFac (T.Q.Dw j) (xiR D) (wtA w) *
      supN (T.U j (goodOf T.Q.c σ)).X (laU (T.U j (goodOf T.Q.c σ)) (wtA w) w.n)
        (rdU (T.U j (goodOf T.Q.c σ)) f) := rfl
  have hS0 : 0 ≤ supN (T.U j (goodOf T.Q.c σ)).X (laU (T.U j (goodOf T.Q.c σ)) (wtA w) w.n)
      (rdU (T.U j (goodOf T.Q.c σ)) f) := ENNReal.toReal_nonneg
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [hNs, ← h0, mul_zero, Real.log_zero]
    positivity

  have hC : f ∈ T.C j w := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1.cuspTie D T hT j hj w hLP x P hP f hf
  obtain ⟨k, xf, -, hort, hSle, hla, hlog⟩ :=
    GlobalTheory.T.cuspForm_halfSup_at_orthonormalFrame_firstMin D T hT hG large₂ j hj w hPR hL hr hLP (goodOf T.Q.c σ) hσg f hC hpos
  have hlam0 : 0 < Real.sqrt (((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1) := Real.sqrt_pos.mpr hla
  have hlam2 : Real.sqrt (((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1) ^ 2 =
      ((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1 := Real.sq_sqrt hla.le

  have hU := GlobalTheory.T.thetaGenerator_pointwise_bound_orthonormal_frame hCI _ _ _ _ (T.Q.Xo j) T.Q.c (goodOf T.Q.c σ) D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j (goodOf T.Q.c σ))) ((Formalism.L2.PjFree.goodEmb_iff _).mpr hσg)
    ((Formalism.L2.PjFree.isUnf_ofPj _).mpr hunf) hr1 (2 * xiR D) (by linarith)
    (fun k τ => hcU _ hσg k τ) (wtA w) w.n (dom_wtA w) inst (T.nab j) hnab x P hP f hf k xf hort
    _ hlam0 hlam2.le
  rw [hfd] at hU
  have key := GlobalTheory.log_exp_mul_le_of_generator_sup_bound D.R.f D.R.r w.n
    (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w)) large₂.sc.L ℓ (absA w) (rdE D.host.E)
    (Real.sqrt (((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1)) (2 * xiR D) 1 _ _ (l1At σ P)
    hL hf1 hr1 hr (by rw [habs]; exact_mod_cast hDF) (by rw [habs]; exact hLa) hLn hLf hrd1
    (by rw [hrdl]; exact hLrd) hlam0 (by rw [hlam2]; exact hlog) (by linarith) hℓ
    (by unfold l1At; exact Finset.sum_nonneg fun _ _ => norm_nonneg _) hp1 zero_le_one
    (Real.one_le_exp (by positivity)) hS0 hSle (by rw [one_mul, ← hl1 _ σ P]; exact hU)
  rw [hNs, hlie]
  exact key

end GlobalTheory.RunIn
end
