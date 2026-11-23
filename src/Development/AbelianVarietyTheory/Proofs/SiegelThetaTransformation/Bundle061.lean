module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle060
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle059
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle081
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle077
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle047
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle049
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle045
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle011
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

theorem _root_.GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (h : Matrix (Fin n) (Fin n) E), IsUnitaryM h → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), pushLet c h P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ∧ ∀ Λ : GenLat E n, (Λ.Unimod → (actLat h Λ).Unimod) ∧ Moves h Λ.La (actLat h Λ).La ∧ ccT h * h = 1 ∧ ∀ P ∈ harmL (Dw := Dw) c Λ a, pushLet c h P ∈ harmL (Dw := Dw) c (actLat h Λ) a := by
  first | exact @GlobalTheory.PushKeeps.push_keeps | exact GlobalTheory.PushKeeps.push_keeps | (intros; apply GlobalTheory.PushKeeps.push_keeps <;> assumption)
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

theorem _root_.GlobalTheory.T.component_eq_of_matched_lattices_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r), _root_.Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → ∀ (W : UW U) (k k' : U.Comp), SameSp (U.X k) (U.X k') → ∀ ga : GL (Fin r) E, IsUn (U.X k) ga → mapL ga (U.X k).Λ = (U.X k').Λ → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ (U.X k').Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ W.mark k a = W.mark k' a + l.M • u) → k = k' := by
  first | exact @GlobalTheory.Dict.comp_eq_of_matched | exact GlobalTheory.Dict.comp_eq_of_matched | (intros; apply GlobalTheory.Dict.comp_eq_of_matched <;> assumption)
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

namespace GlobalTheory.Dict.ThRead

theorem cmHost_idempotent_trace_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hs]; simp
    have hre : (τ (H.rt : E)).re = 0 := by
      have a1 := congrArg Complex.re h1
      have a2 := congrArg Complex.im h1
      simp [pow_two] at a1 a2
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      by_contra hne
      have : (τ (H.rt : E)).im = 0 := by
        have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at a1
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    rw [cc, IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hre]
  have h3 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    simpa [cc, map_ofNat] using this
  have : 2 * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h2 + h3 + hc
  exact mul_left_cancel₀ two_ne_zero this

theorem theta_smul₂ {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (C : ℂ) (φ : TF n g)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r)
    (h : AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ) :
    thP X hr bas idx (C • φ) P x = C * thP X hr bas idx φ P x := by
  have e : thA X bas idx (C • φ) x = C • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, tsum_mul_left]
    ring
  rw [thP, thP, e, I2.polyDeriv, I2.polyDeriv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_const_smul_apply ((h 0 trivial).contDiffAt)]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem isSB_smul {n g : ℕ} (C : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (C • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem thValAt_evR (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab : NabV Xo c) (hn : IsNab Xo c nab) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (xs : Fin n → Dw.La)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) {f : Rul Xo c} (hf : IsThRule Xo c nab xs P f)
    (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    ThValAt Xo c nab y xs P (evR Xo c f y) := by
  have hL : Laws := GlobalTheory.allSixLaws.1
  have ht := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S y
  obtain ⟨w, hw, -⟩ := GlobalTheory.thValTot_of_chartIndep hL hC E H Dw l Xo c nab hn S y a n xs P hP
  have e : evR Xo c f y = w := by
    unfold evR evalAt
    rw [dite_eq_left ht]
    exact GlobalTheory.thetaValue_natural hL hC E H Dw l Xo c nab hn _ S _ _ y ht.choose_spec.choose_spec.choose_spec
      a n xs P hP _ w (hf _ _) hw
  rw [e]
  exact hw

theorem reading_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ n : ℕ, ∀ (W : UW U) (k : U.Comp) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ Dc : Dic Dw c σ (U.X k) W.g Dw.p n a, Dc.e = W.e → ∀ (xs : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab xs P f → f ∈ sec Xo c a n ∧ ∃ φ : TF n W.g, IsSB φ ∧ ∀ x ∈ (U.X k).dom, rdU U f k x = thP (U.X k) Dc.hr Dc.bas Dc.idx φ (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) x := by
  intro hC E _ _ _ H Dw l Xo c σ r U hσ hU hr1 _ nab hn n W k a hD Dc he xs P hP f hf
  have hL : Laws := GlobalTheory.allSixLaws.1
  have hsec : f ∈ sec Xo c a n := GlobalTheory.thetaRule_mem_sec hL hC E H Dw l Xo c nab hn a n f ⟨xs, P, hP, hf⟩
  refine ⟨hsec, ?_⟩
  have hev : Even n := hD.2
  obtain ⟨-, hsd, hmk, -⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw1 := cmHost_idempotent_trace_eq_one H
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd 1 _
    (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hsd hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  obtain ⟨ρ, hρ, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd v hv
  set Y₀ := Y (fun b => Submodule.Quotient.mk (xs b)) with hY₀
  have hsb : IsSB (heisG (U.X k) Dc.bas Y₀ v) :=
    ((GlobalTheory.SW.heisG_laws E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev).2.2.2 Y₀ v hv.1).1
  have hhol := GlobalTheory.SW.theta_holomorphic_weight E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev Dc.k Dc.k'
    _ hsb _ (Dc.mem P hP.1)
  have hS := hU.2.2.2.2.1 a n hD f hsec k
  have hwt : wtOf (U.X k) Dc.hr Dc.k Dc.k' n = laU U a n k := Dc.wt_eq
  rw [hwt] at hhol
  obtain ⟨C, -, hCeq⟩ := GlobalTheory.Dict.const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Unit
    (fun _ => rdU U f k)
    (fun _ => thP (U.X k) Dc.hr Dc.bas Dc.idx (heisG (U.X k) Dc.bas Y₀ v)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P))) ρ hρ
    (fun _ => ⟨hS.1, hhol.1, fun x hx b hb => ⟨hS.2.1 x hx b hb, hhol.2.1 x hx b hb⟩⟩) (by
      intro x hx hux
      letI : Algebra c.F ℂ := σ.toAlgebra
      obtain ⟨A, hA, θ, hθ, hmean⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx Dc.sympl
        (he ▸ Dc.per_eq) (he ▸ Dc.ty_eq) ⟨x, hx⟩ hux
      have h1 := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd θ hθ
      obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd v hv x hx θ h1
      refine ⟨κ, hnorm x hx hux θ κ h1 hmean hκ, fun _ => ?_⟩
      have hval := thValAt_evR hC Xo c nab hn xs hP hf ℂ (unC U k ⟨x, hx⟩)
      have := GlobalTheory.Dict.thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd Dw.p n Dc.hr
        Dc.eL hU.1 hev (he ▸ Dc.dir_eq) nab hn θ v κ hθ hv hκ (W.mark k) hmk hA xs Y₀ (fun b => by
          obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY (fun b => Submodule.Quotient.mk (xs b)) b
          exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hy⟩, hj⟩) a P hP _ hval
      refine Eq.trans ?_ this
      show (if h : x ∈ (U.X k).dom then Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) = _
      rw [dite_eq_left hx]
      rfl)
  refine ⟨C • heisG (U.X k) Dc.bas Y₀ v, isSB_smul C hsb, fun x hx => ?_⟩
  rw [theta_smul₂ _ _ _ _ _ _ _ _ (hhol.2.2.2 x hx)]
  exact hCeq () x hx

end GlobalTheory.Dict.ThRead
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

namespace GlobalTheory.Dict.ShortPt

theorem iteratedFDeriv_smul_all {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (a : ℂ) (F : W → ℂ) (k : ℕ) :
    iteratedFDeriv ℂ k (a • F) = a • iteratedFDeriv ℂ k F := by
  induction k with
  | zero => ext x m; simp
  | succ k ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih, fderiv_const_smul_field]
    funext x
    simp only [Function.comp_apply, Pi.smul_apply, map_smul]

theorem theta_smul₂ {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r) :
    thP X hr bas idx (a • φ) P x = a * thP X hr bas idx φ P x := by
  have h : thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc a, tsum_mul_left]
    ring
  unfold thP I2.polyDeriv
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_smul_all]
  simp only [Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem finite_levQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem vset_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n M : ℕ} {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨h1, h2, s, hs, -, h3⟩ := h
  exact ⟨h1, h2, s, hs, Nat.coprime_one_right s, h3⟩

theorem shortRule_value : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∀ y₂ : FrPt d.Xo₂ d.c₂ ℂ, ‖evR d.Xo₂ d.c₂ d.cδ y₂‖ = 1) → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r g q0 : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c (algebraMap c.F ℂ) X g q0 n a) (D : SW.Level X) (hn : r ≤ n), Even n → r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X Dc.bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ u : Lt E n → ℕ → ℂ, (∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → u Λ N ≠ 0) ∧ ∀ L ∈ D.lats, ∀ mk δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ X.dom, IsUnitFr X x → ∀ (y : FrPt Xo c ℂ) (A : AnFib X Dc.bas Dc.idx Dc.e x L y) (θ : (Fin g → ℂ) → ℂ), A.Marked mk → A.Reads 1 y.s θ → MeanOne X Dc.bas Dc.idx x L θ → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ f : Rul Xo c, IsShortRule Xo c d (⟨Λ⟩ : GenLat E n) N x0 P f → evR Xo c f y = κ * u Λ N * thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ L Λ) (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
  intro hCI E _ _ _ H Dw l Xo c n d _ _ hcomp hlev hnab hcδ ph ψ x₀ hpin r g q0 X a Dc D hn hev hr htie v₀ hv₀ x0
  obtain ⟨_, hnab⟩ := hnab
  obtain ⟨ρ₁, s, hρ₁, hg⟩ := GlobalTheory.Dict.GPhi.gphi_eq_smul_phiF E H Dw l Xo c n d hcomp hlev ph ψ x₀ hpin r g X Dc.bas Dc.idx D hn
    Dc.sympl hev hr htie v₀ hv₀ x0
  have hwi : IsIntegral ℤ (H.w0 : E) := htie.w ▸ D.w_int
  have hwt : (H.w0 : E) + cc (H.w0 : E) = 1 := htie.w ▸ D.w_tr
  have hΛ0 : SelfD X X.Λ := (GlobalTheory.SW.level_laws E r X g Dc.bas Dc.idx n Dc.sympl hev D hn).1.1
  refine ⟨fun Λ N => algebraMap d.c₂.F ℂ ((d.eF (betaH (Dw := Dw) c (⟨Λ⟩ : GenLat E n)))⁻¹ *
      (((⟨Λ⟩ : GenLat E n).mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ *
      ((⟨Λ⟩ : GenLat E n).zCard N r : d.c₂.F)) * (((if 0 < s Λ then s Λ else 1 : ℝ)) : ℂ), ?_, ?_⟩
  · intro Λ hΛ N hN
    obtain ⟨-, -, -, hz, hm, -⟩ := GlobalTheory.Dict.ZLat.exists_reps_sum E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt
      X.Λ hΛ0 Λ (vset_one hΛ) N hN.1 (hN.2.2.trans inf_le_left)
    haveI := finite_levQ Dw d.l₂
    have hb : betaH (Dw := Dw) c (⟨Λ⟩ : GenLat E n) ≠ 0 := by
      unfold betaH
      split_ifs with h
      · exact h.choose_spec.1
      · exact one_ne_zero
    have hc : 0 < Nat.card (Fin n → LevQ Dw d.l₂) := Nat.card_pos
    refine mul_ne_zero ((_root_.map_ne_zero _).2 ?_) ?_
    · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)) (inv_ne_zero ?_)) ?_
      · exact (_root_.map_ne_zero _).2 hb
      · exact Nat.cast_ne_zero.2 hm.ne'
      · exact Nat.cast_ne_zero.2 hc.ne'
      · exact Nat.cast_ne_zero.2 hz.ne'
    · rw [Complex.ofReal_ne_zero]
      split_ifs with h
      · exact h.ne'
      · exact one_ne_zero
  intro L hL mk δ hmk hδ hx0
  have hLs : SelfD X L := hL.1
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs 1 _
    (Base.stdL_mem_Vset (E := E) n 1)).1
  obtain ⟨ρ₀, hρ₀, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs v hv
  refine ⟨ρ₀ * ρ₁, mul_pos hρ₀ hρ₁, ?_⟩
  intro x hx hux y A θ hA hθ hmean
  obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ hcomp y
  obtain ⟨A₂, hA₂, mk₂, hmk₂, hA₂m, hover⟩ := GlobalTheory.Dict.Lift.anFib_lift E H Dw l Xo c n d hcomp hlev r g X Dc.bas Dc.idx Dc.e x L y A
    Dc.sympl hx hLs y₂ hy₂ mk hA
  have hth := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r g X Dc.bas Dc.idx Dc.e x L y A Dc.sympl hx hLs θ hθ
  obtain ⟨κ₀, hκ₀⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs v hv x hx θ hth
  obtain ⟨t, ht, hgt⟩ := hg L hL mk mk₂ δ v hmk hmk₂ hover hδ hx0 hv
  refine ⟨evR d.Xo₂ d.c₂ d.cδ y₂ * κ₀ * t, ?_, ?_⟩
  · rw [norm_mul, norm_mul, hcδ y₂, hnorm x hx hux θ κ₀ hth hmean hκ₀, ht, _root_.one_mul]
  intro Λ hΛ N hN P hP f hf
  obtain ⟨hs, hgt⟩ := hgt Λ hΛ
  have hM : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking E H Dw d.l₂ r X L mk₂ _ hLs hmk₂ (Complex.isPrimitiveRoot_exp _ hM)).2.2.2.2 n N
    hN.1.pos
  obtain ⟨v0, hv0, hfv⟩ := hf ℂ hcomp y y₂ hy₂
  have hval := GlobalTheory.Dict.shortValAt_eq_thP hCI E H Dw d.l₂ d.Xo₂ d.c₂ r g X Dc.bas Dc.idx Dc.e x L y₂ A₂ Dc.sympl hx hLs q0 n Dc.hr
    Dc.eL hr hev Dc.dir_eq d.nab₂ hnab θ v κ₀ (hA₂ θ hθ) hv hκ₀ mk₂ hmk₂ hA₂m Λ hΛ N hN Y hY a _
    ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP) _ _ v0 hv0
  have hmap : MvPolynomial.map (algebraMap d.c₂.F ℂ) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
      MvPolynomial.map (algebraMap c.F ℂ) P := by
    rw [MvPolynomial.map_map]
    congr 2
    exact RingHom.ext hcomp
  rw [hgt N hN Y hY, theta_smul₂, hmap] at hval
  beta_reduce
  rw [hfv, hval, if_pos hs]
  ring

end GlobalTheory.Dict.ShortPt
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

theorem _root_.GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → ∀ Λ ∈ Vset E n l.M, ∀ N : ℕ, NOK Λ N l.M → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (wq : (Fin n → LevQ Dw l) → c.F) (β : c.F) (v0 : ℂ), ShortValAt Xo c nab wq (⟨Λ⟩ : GenLat E n) β N P y v0 → v0 = algebraMap c.F ℂ (β⁻¹ * (((⟨Λ⟩ : GenLat E n).mIdx N r : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((⟨Λ⟩ : GenLat E n).zCard N r : c.F)) * κ * thP X hr bas idx (gphi X bas (H.w0 : E) Λ L v (fun q => algebraMap c.F ℂ (wq q)) Y) (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
  first | exact @GlobalTheory.Dict.shortValAt_eq_thP | exact GlobalTheory.Dict.shortValAt_eq_thP | (intros; apply GlobalTheory.Dict.shortValAt_eq_thP <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_vacua_inner_eq_const_mul_testInner : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ φ' : TF S.rank C.g, SW.IsSB φ → SW.IsSB φ' → ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ') = a * ip φ φ' := by
  first | exact @GlobalTheory.KerVacIp.ip_vacua | exact GlobalTheory.KerVacIp.ip_vacua | (intros; apply GlobalTheory.KerVacIp.ip_vacua <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finitePoints_carry_latticeVacuum_to_moved_vacuum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ Λ' ∈ Vset D.host.E S.rank M, ∀ L L' : Lt D.host.E T.rank, SelfD C.X L → SelfD C.X L' → ∀ h ∈ GfC S, ∀ g ∈ GfC T, IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → ∀ v v', IsVac C.X C.bas w (tens Λ L) v → IsVac C.X C.bas w (tens Λ' L') v' → ∀ B, C.IsB B → ∃ c : ℂ, ‖c‖ = 1 ∧ om (h, g) (C.Th (C.xB B) v) = c • (C.Th (C.xB B) v') := by
  first | exact @GlobalTheory.Ker.om_Th_vac | exact GlobalTheory.Ker.om_Th_vac | (intros; apply GlobalTheory.Ker.om_Th_vac <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

theorem readings_independent :
    ∀ (D : D7) (T : Top D), LawsM T.toCore → ∀ j, InR D j → ∀ a n, JInjRd T j a n := by
  intro D T hM j hj a n

  have hA := GlobalTheory.FramedBaseChange.bcEx_all _ _ _ _ (T.Q.Xo j) T.Q.c T.σ₀
  have hF := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.1
  exact jInjRd_of_wt T hM hj a n hA hF

end GlobalTheory.Dict
end
