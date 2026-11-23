module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle046
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpec
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle018
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MapConjInv
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle032
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle012
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle038
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsIsometryModPrimePow
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinates
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle047
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SumMovedVacuumTranslatesEqFreeRowTestFunction
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle048
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

@[expose] public section

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.exists_theta_eq_of_translation_invariant_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ (N : ℕ), 0 < N → ∀ θ : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ θ → (∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ v : WR X n, cexp (-(π * I * (EFR X v (N • embR X y) : ℝ))) * (gaussR X bas idx x (zR X idx x (v + N • embR X y)) * θ (zR X idx x (v + N • embR X y))) = gaussR X bas idx x (zR X idx x v) * θ (zR X idx x v)) → ∃ φ : TF n g, IsSB φ ∧ ∀ z, thA X bas idx φ x z = θ z := by
  first | exact @GlobalTheory.Ker.Onto.exists_thA_eq | exact GlobalTheory.Ker.Onto.exists_thA_eq | (intros; apply GlobalTheory.Ker.Onto.exists_thA_eq <;> assumption)
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

theorem _root_.GlobalTheory.T.anFib_lift_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ y₂ : FrPt d.Xo₂ d.c₂ ℂ, FrOver d y₂ y → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → ∃ A₂ : AnFib X bas idx e x L y₂, (∀ θ, A.Reads 1 y.s θ → A₂.Reads 1 y₂.s θ) ∧ ∃ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ L mk₂ ∧ A₂.Marked mk₂ ∧ MarkOver l d.l₂ L mk mk₂ := by
  first | exact @GlobalTheory.Dict.Lift.anFib_lift | exact GlobalTheory.Dict.Lift.anFib_lift | (intros; apply GlobalTheory.Dict.Lift.anFib_lift <;> assumption)
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

theorem _root_.GlobalTheory.T.framedPoint_generator_isThetaLevelOne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ θ, A.Reads 1 y.s θ → IsTheta1 X bas idx (H.w0 : E) x L θ := by
  first | exact @GlobalTheory.Dict.isTheta1_of_reads_generator | exact GlobalTheory.Dict.isTheta1_of_reads_generator | (intros; apply GlobalTheory.Dict.isTheta1_of_reads_generator <;> assumption)
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

theorem _root_.GlobalTheory.T.sections_read_as_translates_at_scaled_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (N : ℕ), Odd N → ∀ θ, A.Reads 1 y.s θ → (∀ a₁ a₂ : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a₁ = (2 : ℕ) • u) → (∃ u ∈ L, (N ^ 2 : ℕ) • a₂ = (2 : ℕ) • u) → ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (A.ex (pv X idx x a₁)) (A.ex (pv X idx x a₂)) F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a₂)) (fock X bas idx x 1 (pv X idx x ((N : E) • a₁)) θ) ((N : ℂ) • z))) ∧ ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) → ∀ (t : (ptO Xo y.x) ⟶ Xo.univ.t.G) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t' => t' = A.ex (pv X idx x a)) y.s t F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a)) θ ((N : ℂ) • z)) := by
  first | exact @GlobalTheory.Dict.reads_isUUOver_isVtOver | exact GlobalTheory.Dict.reads_isUUOver_isVtOver | (intros; apply GlobalTheory.Dict.reads_isUUOver_isVtOver <;> assumption)
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

theorem _root_.GlobalTheory.T.theta_heisenberg_unitary_column_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ φ' : TF n g, IsSB φ → IsSB φ' → ∀ t : ℂ, ∀ x ∈ X.dom, (∀ z, thA X bas idx φ' x (hAct X idx h z) = t * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) z, thA X bas idx (heisG X bas (h * y) φ') x (hAct X idx h z) = t * thA X bas idx (heisG X bas y φ) x z := by
  first | exact @GlobalTheory.Dict.thA_heisG_hAct | exact GlobalTheory.Dict.thA_heisG_hAct | (intros; apply GlobalTheory.Dict.thA_heisG_hAct <;> assumption)
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

theorem _root_.GlobalTheory.T.sum_moved_vacuum_translates_eq_freeRow_testFunction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, ∀ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' → (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' → (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' → ∃ t : ℂ, t ≠ 0 ∧ ∀ L ∈ D.lats, ∃ s : Finset (Matrix (Fin n) (Fin r) E), D.phi bas hn v₀ L Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ ∑ y ∈ s, D.dat hn y • heisG X bas (h * y) (unitv (projA X bas D.w (tens Λ'' (D.sh L)) (v₀ L))) = t • phiF bas D 𝔐 hn v₀ L Λ' := by
  first | exact @GlobalTheory.Dict.SumFree.sum_free | exact GlobalTheory.Dict.SumFree.sum_free | (intros; apply GlobalTheory.Dict.SumFree.sum_free <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

private theorem kZero_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom)
    (h₂ : x₂ ∈ X.dom) (z₁ w : Fin n → Fin g → ℂ) : kZero X idx x₁ x₂ z₁ w ≠ 0 := by
  unfold kZero
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => mul_ne_zero ?_ (Complex.exp_ne_zero _)
  exact inv_ne_zero (pow_ne_zero _ (mul_ne_zero (DblPoint.det_aLin_ne_zero h₁ h₂ τ)
    (DblPoint.det_aAnti_ne_zero h₁ h₂ τ)))

private theorem isUn_one' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) : IsUn X (1 : GL (Fin r) E) := by
  unfold IsUn
  intro x y
  simp

theorem eisTerm_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ z₁ w : Fin n → Fin g → ℂ, kZero X idx x₁ x₂ z₁ w * eisTerm X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w) = dbl X bas idx φ₁ (wG X bas idx γ φ₂) 0 * kZero X idx x₁ (lact γ x₂) z₁ w := by
  intro E _ _ _ r X g bas idx n hs hn γ hγ φ₁ φ₂ h₁ h₂ x₁ hx₁ x₂ hx₂ z₁ w

  obtain ⟨hsb₂, hth₂, -⟩ := wG_laws E r X g bas idx n hs hn γ hγ φ₂ h₂
  have hγx₂ : lact γ x₂ ∈ X.dom := IsUn.lact_mem hγ hx₂
  obtain ⟨hT, hZ', -⟩ := dblZ_mem_Hn E r X x₁ hx₁ (lact γ x₂) hγx₂
  have hZ : dblZ X x₁ x₂ ∈ Hn X.Ψ r := (dblZ_mem_Hn E r X x₁ hx₁ x₂ hx₂).2.1

  obtain ⟨hU, a, ha, hact⟩ := iota_act_dbl E r X g bas idx n hs hn 1 γ (isUn_one' X) hγ
  obtain ⟨hA, hzz⟩ := hact x₁ hx₁ x₂ hx₂
  have e1 : lact (1 : GL (Fin r) E) x₁ = x₁ := UnAct.lact_one' x₁
  simp only [e1] at hA hzz

  obtain ⟨hΦ, hΦd, -⟩ := DblEx.dbl_spec E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂
  obtain ⟨hΦ', hΦ'd, -⟩ :=
    DblEx.dbl_spec E r X g bas idx n hs hn φ₁ (wG X bas idx γ φ₂) h₁ hsb₂
  obtain ⟨hW, hWT, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E X.Ψ hT n r hn (iota X 1 γ) hU (dbl X bas idx φ₁ φ₂) hΦ

  have key : ∀ u v : Fin n → Fin g → ℂ,
      thH X.Ψ (weil X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂)) (dblZ X x₁ (lact γ x₂))
          (dblz X idx x₁ (lact γ x₂) u v) (dblz' X idx x₁ (lact γ x₂) u v) =
        a * thH X.Ψ (dbl X bas idx φ₁ (wG X bas idx γ φ₂)) (dblZ X x₁ (lact γ x₂))
          (dblz X idx x₁ (lact γ x₂) u v) (dblz' X idx x₁ (lact γ x₂) u v) := by
    intro u v
    obtain ⟨hz, hz', hk⟩ := hzz u v
    have d1 := hΦd x₁ hx₁ x₂ hx₂ u v
    have d2 := hΦ'd x₁ hx₁ (lact γ x₂) hγx₂ u v
    have t2 : thA X bas idx (wG X bas idx γ φ₂) (lact γ x₂) = thA X bas idx φ₂ x₂ :=
      hth₂ x₂ hx₂
    rw [t2, d1] at d2
    have tw := hWT (dblZ X x₁ x₂) hZ (dblz X idx x₁ x₂ u v) (dblz' X idx x₁ x₂ u v)
    rw [hA, ← hz, ← hz'] at tw
    have hK' := kZero_ne_zero X idx hx₁ hγx₂ u v
    apply mul_left_cancel₀ hK'
    rw [tw, ← mul_assoc, hk, mul_assoc, d2]
    ring

  have hW' : weil X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) =
      a • dbl X bas idx φ₁ (wG X bas idx γ φ₂) := by
    refine (thH_summable_and_inj E X.Ψ hT n r _ hW _ hZ').2 _ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ hΦ' hΦ').2.1 a) ?_
    intro z z'
    obtain ⟨u, v, rfl, rfl⟩ := DblEx.dblz_surj E r X g idx n x₁ hx₁ (lact γ x₂) hγx₂ z z'
    rw [key u v]
    unfold thH
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [tsum_mul_left]

  obtain ⟨-, -, hk⟩ := hzz z₁ w
  have hK := kZero_ne_zero X idx hx₁ hx₂ z₁ w
  have hH : hFac X.Ψ (iota X 1 γ) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w)
      (dblz' X idx x₁ x₂ z₁ w) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    exact mul_ne_zero ha hK hk.symm
  unfold eisTerm
  rw [hW', Pi.smul_apply, smul_eq_mul, ← mul_inv_cancel_right₀ hH
    (kZero X idx x₁ (lact γ x₂) z₁ w), hk]
  field_simp

end GlobalTheory.SW
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.OntoLat

theorem exists_tower {R L M : Type} [CommRing R] [AddCommGroup L] [AddCommGroup M] [Module R L] [Module R M]
    [Module.Finite ℤ L] [Module.Finite ℤ M] (hc : ∀ r : ℕ, 0 < r → ∀ a c : L, r • a = r • c → a = c)
    (Q : ℕ → (L →ₗ[R] M) → Prop) (hQ : ∀ n m f, Q (n * m) f → Q n f)
    (hex : ∀ n : ℕ, 0 < n → ∃ f : L →ₗ[R] M,
      ((∀ a, (∃ e, f a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f a + n • e) ∧ Q n f) :
    ∃ f : ℕ → L →ₗ[R] M, (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      ∀ n : ℕ, 0 < n → Q n (f n) := by
  choose g hg using fun j : ℕ => hex _ j.factorial_pos
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : ∀ n, 0 < n → ∀ᶠ j : ℕ in U, n ∣ j.factorial := fun n hn =>
    Ultrafilter.of_le _ ((Filter.eventually_ge_atTop n).mono fun j hj => Nat.dvd_factorial hn hj)
  have hs : ∀ n : ℕ, ∃ i : ℕ, 0 < n →
      (n ∣ i.factorial ∧ ∀ᶠ j in U, ∀ a, ∃ e, g j a = g i a + n • e) := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨i, hi⟩ := IsoTower.exists_eventually_congr U (fun j => (g j).toAddMonoidHom) hn _ (hU n hn)
      exact ⟨i, fun _ => hi⟩
  choose s hs using hs
  refine ⟨fun n => g (s n), fun n m hn hm a => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨j, h1, h2⟩ := ((hs _ (Nat.mul_pos hn hm)).2.and (hs n hn).2).exists
    obtain ⟨e1, h1⟩ := h1 a
    obtain ⟨e2, h2⟩ := h2 a
    refine ⟨e2 - m • e1, ?_⟩
    show g (s (n * m)) a = g (s n) a + _
    rw [smul_sub, ← mul_smul, ← add_sub_assoc, ← h2, h1, add_sub_cancel_right]
  · obtain ⟨r, hr⟩ := (hs n hn).1
    have hr0 : 0 < r := Nat.pos_of_mul_pos_left (hr ▸ (s n).factorial_pos)
    obtain ⟨⟨h1, h2⟩, -⟩ := hg (s n)
    rw [hr] at h1 h2
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨e, he⟩
      have he' : g (s n) a = n • e := he
      obtain ⟨b, hb⟩ := (h1 (r • a)).1 ⟨e, by rw [map_nsmul, he', mul_comm, mul_smul]⟩
      exact ⟨b, hc r hr0 _ _ (by rw [hb, mul_comm, mul_smul])⟩
    · rintro ⟨e, rfl⟩
      exact ⟨_, map_nsmul _ _ _⟩
    · obtain ⟨a, e, h⟩ := h2 a'
      exact ⟨a, r • e, by rw [h, mul_smul]⟩
  · obtain ⟨r, hr⟩ := (hs n hn).1
    exact hQ n r _ (hr ▸ (hg (s n)).2)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_valueIdeal (X : Data E r) : ∃ J : FractionalIdeal (𝓞 E)⁰ E, J ≠ 0 ∧ (∀ z ∈ J, cc z ∈ J) ∧
    ∀ L : Lt E r, SelfD X L → ∀ x, x ∈ L ↔ ∀ y ∈ L, herm X.Gm x y ∈ J := by
  set ξ : E := X.κ0 / 2 with hξ
  have hξ' : ξ = X.ξ0 ∨ ξ = -X.ξ0 := X.κ0_xi.imp (fun h => by rw [hξ, h]; ring) fun h => by rw [hξ, h]; ring
  have hξ0 : ξ ≠ 0 := by
    rcases hξ' with h | h <;> rw [h]
    exacts [X.ξ0_ne, neg_ne_zero.2 X.ξ0_ne]
  have hξc : cc ξ = -ξ := by
    have := X.ξ0_im
    rcases hξ' with h | h <;> rw [h]
    · exact this
    · simp only [cc, map_neg] at this ⊢
      rw [this]
  have hI0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ0
  have hJ : ∀ z : E, z ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ) ↔
      ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (-ξ * ((a : E) * z)) = k := by
    intro z
    rw [FractionalIdeal.mem_dual hI0]
    constructor
    · intro h a
      obtain ⟨k, hk⟩ := h ((-a) • ξ) ((FractionalIdeal.mem_spanSingleton _).2 ⟨-a, rfl⟩)
      refine ⟨k, ?_⟩
      rw [eq_intCast, Algebra.traceForm_apply, Algebra.smul_def, map_neg] at hk
      rw [hk]
      congr 1
      change _ = z * (-(a : E) * ξ)
      ring
    · intro h w hw
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hw
      obtain ⟨k, hk⟩ := h (-c)
      refine ⟨k, ?_⟩
      rw [eq_intCast, ← hk, Algebra.traceForm_apply, Algebra.smul_def]
      congr 1
      change -ξ * (((-c : 𝓞 E) : E) * z) = z * ((c : E) * ξ)
      push_cast
      ring
  have htr : ∀ z : E, Algebra.trace ℚ E (cc z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  refine ⟨_, FractionalIdeal.dual_ne_zero ℤ ℚ hI0, fun z hz => ?_, fun L hL x => ?_⟩
  · rw [hJ] at hz ⊢
    intro a
    obtain ⟨k, hk⟩ := hz (-RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a)
    refine ⟨k, ?_⟩
    rw [← hk, ← htr]
    congr 1
    have e : ((-RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a : 𝓞 E) : E) = -cc (a : E) := rfl
    rw [e]
    simp only [cc, map_mul, map_neg, IsCMField.complexConj_apply_apply] at hξc ⊢
    rw [hξc]
    ring
  · have hE : ∀ (a : 𝓞 E) (u v : Fin r → E),
        EF X (a • u) v = Algebra.trace ℚ E (-ξ * ((a : E) * herm X.Gm u v)) := fun a u v => by
      rw [EF_def, ← algebraMap_smul E, HermitianTraceFormVanishing.herm_smul_left]
    constructor
    · intro hx y hy
      rw [hJ]
      intro a
      rw [← hE]
      exact (hL.2 _).1 (L.smul_mem a hx) y hy
    · intro h
      refine (hL.2 x).2 fun y hy => ?_
      have := (hJ _).1 (h y hy) 1
      rwa [← hE, one_smul] at this

theorem exists_adelic_matrix [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (F : Type) [Field F]
    [NumberField F] [Algebra F E] (c : E ≃ₐ[F] E) (hcc : ∀ x, c x = cc x) (X : Data E r) {L L' : Lt E r}
    (hL : SelfD X L) (hL' : SelfD X L') :
    ∃ g : GL (Fin r) (AdLat.RA F E),
      (g : Matrix (Fin r) (Fin r) (AdLat.RA F E)).mulVec '' (AdLat.hat F (L : Set (Fin r → E))) =
        AdLat.hat F (L' : Set (Fin r → E)) ∧
      ∀ x y, AdLat.hermA c X.Gm ((g : Matrix (Fin r) (Fin r) (AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin r) (Fin r) (AdLat.RA F E)) *ᵥ y) = AdLat.hermA c X.Gm x y := by
  obtain ⟨J, hJ0, hJc, hJ⟩ := exists_valueIdeal X
  have h1 : ReciprocityTheory.MultiplicativeHeights.IsLattice L := ⟨hL.1, SW.TensLat.span_of_selfD X hL⟩
  have h2 : ReciprocityTheory.MultiplicativeHeights.IsLattice L' := ⟨hL'.1, SW.TensLat.span_of_selfD X hL'⟩
  have hγ := SelfDualGenus.exists_isLocalIsometry_of_modular hJ0 hJc X.Gm_herm X.Gm_herm X.Gm_det X.Gm_det h2 h1
    (hJ L' hL') (hJ L hL)
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.1
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  haveI : Module.Finite (𝓞 E) L' := Module.Finite.iff_fg.2 hL'.1
  haveI : Module.Finite ℤ L' := Module.Finite.trans (𝓞 E) L'
  obtain ⟨f, f1, f2, f3⟩ := exists_tower (R := 𝓞 E) (L := L) (M := L')
    (fun n hn a b h => by
      have hn' : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have h' : (n : E) • (a : Fin r → E) = (n : E) • (b : Fin r → E) := by
        simpa only [Nat.cast_smul_eq_nsmul, Submodule.coe_smul_of_tower] using congrArg Subtype.val h
      exact Subtype.ext (smul_right_injective _ hn' h'))
    (fun n f => ∀ a a' : L, ∃ z ∈ J, herm X.Gm (f a) (f a') - herm X.Gm a a' = n • z)
    (fun n m f h a a' => by
      obtain ⟨z, hz, e⟩ := h a a'
      exact ⟨m • z, nsmul_mem (show z ∈ (J : Submodule (𝓞 E) E) from hz) m, by rw [e, mul_smul]⟩)
    (fun n hn => by
      obtain ⟨f, hf, hf'⟩ := IsomModN.exists_isometry_mod h1 h2 (IsomModN.isLattice_ideal hJ0)
        (fun x hx y hy i _ => (hJ L' hL' x).1 hx y hy) hγ hn
      refine ⟨f, hf, fun a a' => ?_⟩
      obtain ⟨m, hm, e⟩ := hf' a a'
      exact ⟨m 0, hm 0 trivial, e⟩)
  have hh : ∀ x y : Fin r → E, (∑ a, ∑ b, x a * X.Gm a b * c (y b)) = herm X.Gm x y := fun x y => by
    simp only [herm, hcc]
  obtain ⟨g, g1, -, g3⟩ := AdLat.exists_adelic_matrix_of_tower F E r L L' f h1.1 h1.2 h2.1 h2.2 f1 f2
  refine ⟨g, g1, g3 c X.Gm J (fun x hx y hy => ?_) fun n hn x y => ?_⟩
  · rw [hh]
    exact (hJ L' hL' x).1 hx y hy
  · obtain ⟨z, hz, e⟩ := f3 n hn x y
    exact ⟨z, hz, by rw [hh, hh, ← e, add_sub_cancel]⟩

theorem exists_mov_of_selfD {D : D7} {S T : HSp D} (C : Ctx S T) {L : Lt D.host.E T.rank} (hL : SelfD C.X L) :
    ∃ g ∈ GfC T, IsMov (fmt T g) C.X.Λ L := by
  haveI := (hostOfRecord D).unram
  obtain ⟨g, g1, g2⟩ := exists_adelic_matrix D.host.F (Member.cF D)
    (Member.latHat_eq_hat_and_gram D T).2.2.2.2.2.1 C.X (SW.Lev.selfD_of_sympl C.sympl) hL
  rw [C.m.gT] at g2
  obtain ⟨k, hk, rfl⟩ := (UnitarySplit.real_finite_split D T).2.2.2.1 g g2
  refine ⟨k, hk, fun u => ?_⟩
  have e : u ∈ hatV L ↔ u ∈ (AdLat.hat D.host.F (L : Set (Fin T.rank → D.host.E)) : Set _) := Iff.rfl
  rw [e, ← g1]
  exact ⟨fun ⟨u₀, h₀, h⟩ => ⟨u₀, h₀, h.symm⟩, fun ⟨u₀, h₀, h⟩ => ⟨u₀, h₀, h.symm⟩⟩

theorem exists_trivAt_mov : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ Lv : SW.Level C.X, ∀ L ∈ Lv.lats,
    ∃ g ∈ GfC T, TrivAt T (C.under Lv) g ∧ IsMov (fmt T g) C.X.Λ L := by
  intro D S T C Lv L hL
  obtain ⟨g, -, hg⟩ := exists_mov_of_selfD C hL.1
  exact ((GlobalTheory.T.self_dual_lattices_at_level D S T C).2 Lv g L hL.1.1 hg).2.2.2 hL

end GlobalTheory.Ker.OntoLat
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.annihilation_creation_periodCoordinates : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℝ Φ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w)) → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ), u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) → ∀ w, IsRealPt w → annih (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u + I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)) ∧ crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (2 * ((-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k))) * Φ (C.zOf (C.xB B) w) + (1 / 2 : ℂ) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u - I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)))) := by
  first | exact @GlobalTheory.Ker.annih_crea_coord | exact GlobalTheory.Ker.annih_crea_coord | (intros; apply GlobalTheory.Ker.annih_crea_coord <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_trivialAtLevel_unitary_transport_selfDual : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ M : ℕ, 0 < M → ∀ Λ ∈ Vset D.host.E S.rank M, ∃ h ∈ GfC S, TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h ∧ IsMov (fmtC S h) (stdL D.host.E S.rank) Λ := by
  first | exact @GlobalTheory.KerOntoStd.exists_trivAt_isMov | exact GlobalTheory.KerOntoStd.exists_trivAt_isMov | (intros; apply GlobalTheory.KerOntoStd.exists_trivAt_isMov <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isLatticeVacuum_iff_signedRational_fixed : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ L : Lt D.host.E T.rank, SelfD C.X L → ∀ f, C.IsTh f → (IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f ↔ ∀ y ∈ tens Λ L, epsW C.X w y • C.rho (finW S T y) f = f) := by
  first | exact @GlobalTheory.Ker.SignVac.isLatVac_iff | exact GlobalTheory.Ker.SignVac.isLatVac_iff | (intros; apply GlobalTheory.Ker.SignVac.isLatVac_iff <;> assumption)
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

namespace GlobalTheory.Dict

theorem nab_harm_val_eq_polyDeriv : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (th : Fin n → (Fin g → ℂ) → ℂ), (∀ b, A.Reads ((N : ℤ) ^ 2) (F b) (th b)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (fun ℓ => (Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1) : Fin n → Fin g → ℂ)) (fun z => ∏ b, th b (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A h1 h2 h3 _ nab hn n N a P hP
  obtain ⟨Φ, -, -, -, -, -, hRd, -⟩ := GlobalTheory.T.exists_analyticFrame_of_analyticFibre E H Dw l Xo c r g X bas idx e x L y A h1 h2 h3
  have hk : ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  rw [hk]
  intro F th hF
  have key := GlobalTheory.T.harmonicValue_canonicalConnection_eq_polyDeriv hC E H Dw l Xo c y g _ e Φ nab hn (N ^ 2) n F th
    (fun b => (hRd _ _ _).2 (hF b)) a P hP
  rw [key]
  congr 1

end GlobalTheory.Dict
end
