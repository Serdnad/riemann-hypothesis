module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle154
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle058
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeSignEta

theorem idF_ratF (D : D7) (a : D.host.Fˣ) :
    idF D (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) =
      Units.map (incA D).toMonoidHom (Units.map (algebraMap D.host.F D.host.E).toMonoidHom a) := by
  refine Units.ext ?_
  show algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (a : D.host.F)) =
    incA D (algebraMap D.host.F D.host.E (a : D.host.F))
  show _ = Algebra.TensorProduct.includeRight (algebraMap D.host.F D.host.E (a : D.host.F))
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]

theorem resEta_of_sign : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (N : ℕ), IsHeckeChar D χ →
    (∀ x y : (AE D)ˣ, (y : AE D) = x * cA D x → χ y = 1) →
    ∀ θ : InfFam D, IsInfFam θ →
    (∀ (τ : D.what₂.Tau) (x : (AE D)ˣ), finPart D (x : AE D) = 1 → θ τ (infPart D (x : AE D)) = -1 →
      (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) → ((χ x : Circle) : ℂ) = (-1) ^ N) →
    ResEta D χ N := by
  intro D χ N hχ hnorm θ hθ hsign
  refine ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun ε hε => ?_⟩

  set ψ : (AF D.host.F)ˣ →* Circle := χ.comp (idF D) * (ε ^ N)⁻¹ with hψ
  have hψa : ∀ a, ψ a = χ (idF D a) * (ε a ^ N)⁻¹ := fun a => rfl
  have hker : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs.normGroup D ≤ ψ.ker := by
    rw [GlobalTheory.VolHeckeCompare.normGroup_eq]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      show ψ (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) = 1
      rw [hψa, idF_ratF, hχ.2, hε.2.1 a, one_pow, inv_one, mul_one]
    · rintro _ ⟨x, rfl⟩
      obtain ⟨-, -, hN, -⟩ := GlobalTheory.VolHeckeCompare.exists_form D
      have e : (idF D (GlobalTheory.VolHeckeCompare.normU D x) : AE D) = (x : AE D) * cA D (x : AE D) := by
        have e0 : idF D (GlobalTheory.VolHeckeCompare.normU D x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs.normId D x := hN x
        rw [e0]; rfl
      show ψ (GlobalTheory.VolHeckeCompare.normU D x) = 1
      rw [hψa, hnorm x _ e, hε.2.2.1 x, one_pow, inv_one, mul_one]

  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨η, -, -, hη1, hη2⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨N1, hN1, -, hηx⟩ := hη2 τ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  set w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1) with hw
  have wτ : w τ = -1 := by simp [w]
  have wo : ∀ τ', τ' ≠ τ → w τ' = 1 := fun τ' ht => by simp [w, Pi.mulSingle_eq_of_ne ht]
  have ww : w * w = 1 := by
    funext τ'
    by_cases ht : τ' = τ
    · subst ht; simp [wτ]
    · simp [wo τ' ht]
  let x : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have x1 : finPart D (x : AE D) = 1 := e1 w
  have x2 : ∀ τ', θ τ' (infPart D (x : AE D)) = w τ' := e2 w
  have xτ : θ τ (infPart D (x : AE D)) = -1 := by rw [x2, wτ]
  have xo : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' ht => by rw [x2, wo τ' ht]
  have hcx : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ N := hsign τ x x1 xτ xo
  have hN1' : N1 = 1 := by
    have : (N1 : ℚ) = 1 := by rw [hN1]; norm_num
    exact_mod_cast this
  have hηc : ((η x : Circle) : ℂ) = -1 := by rw [hηx θ hθ x x1 xo, xτ, hN1']; simp
  have hfix : cA D (x : AE D) = x := by
    refine GlobalTheory.SplitCharExp.ext_of_chart h ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
      rw [e3, x1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, x2]
      by_cases ht : τ' = τ
      · rw [ht, wτ]; simp
      · rw [wo τ' ht]; simp
  obtain ⟨y, hy⟩ := GlobalTheory.SplitParity.exists_idF_of_fixed D x hfix

  have hneg : ∀ ε', IsEta D ε' → ((ε' y : Circle) : ℂ) = -1 := fun ε' hε' => by
    have c2 := hη1.2 ε' hε' y
    rw [hy, pow_one] at c2
    rw [← c2, hηc]
  have hψy : ψ y = 1 := by
    refine Circle.ext ?_
    rw [hψa, hy, Circle.coe_mul, Circle.coe_inv, Circle.coe_pow, hcx, hneg ε hε, Circle.coe_one]
    exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
  have hψ1 : ψ = 1 := by
    by_contra hne
    have hψE : IsEta D ψ := (GlobalTheory.VolHeckeCompare.isEta_iff_normGroup D ψ).2 ⟨hker, hne⟩
    have := hneg ψ hψE
    rw [hψy, Circle.coe_one] at this
    norm_num at this
  intro a
  have ha : ψ a = 1 := by rw [hψ1]; rfl
  rw [hψa, mul_inv_eq_one] at ha
  exact ha

end GlobalTheory.HeckeSignEta
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PhaseMove

theorem trace_sum_int : ∀ (D : D7) (w : D.host.E), IsIntegral ℤ w → ∃ m : ℤ, 2 * (∑ τ, Formalism.MainNotions.TaylorLogMetric.embT D τ w).re = m := by
  intro D w hw
  have htr := Formalism.MainNotions.Ext.trace_sum_over_letters_holds D w
  have ht : IsIntegral ℤ (Algebra.trace D.host.K D.host.E w) := Algebra.isIntegral_trace hw
  obtain ⟨u, v, huv⟩ := ((GlobalTheory.MomDict.main D).2.2.1 _).2 ⟨⟨_, ht⟩, rfl⟩
  refine ⟨2 * u + v, ?_⟩
  rw [htr]
  erw [huv]
  simp [GlobalTheory.MomOne.wK]
  ring

def cTA (D : D7) {m p : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin p) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D) :=
  (B.map (Formalism.MainNotions.StandardLatticesGL3.sgA D)).transpose

theorem sq_unitary : ∀ {D : D7} {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (A : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∑ i, ∑ j, (((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * A * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j * Formalism.MainNotions.StandardLatticesGL3.sgA D ((((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * A * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j)) = ∑ i, ∑ j, A i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A i j) := by
  intro D a d x y A
  have hinv : ∀ e : D.host.E, D.host.conj (D.host.conj e) = e := fun e => by
    apply D.host.φ₀.injective
    have h1 := D.host.conjE_apply D.host.φ₀
    change D.host.φ₀ (D.host.conj (D.host.conj e)) = _
    rw [h1, h1, Complex.conj_conj]
  have hsg : ∀ u : Formalism.MainNotions.StandardLatticesGL3.AE D, Formalism.MainNotions.StandardLatticesGL3.sgA D (Formalism.MainNotions.StandardLatticesGL3.sgA D u) = u := fun u => by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul e r =>
      change (Algebra.TensorProduct.map _ _) ((Algebra.TensorProduct.map _ _) (e ⊗ₜ r)) = e ⊗ₜ r
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      exact hinv e
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
  have hΦ : ∀ B : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D), (∑ i, ∑ j, B i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (B i j)) = (B * cTA D B).trace := fun B => by
    simp [cTA, Matrix.trace, Matrix.mul_apply]
  have hmul : ∀ {m p q : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (C : Matrix (Fin p) (Fin q) (Formalism.MainNotions.StandardLatticesGL3.AE D)), cTA D (B * C) = cTA D C * cTA D B := fun B C => by
    simp only [cTA, Matrix.map_mul, Matrix.transpose_mul]
  have hcc : ∀ {m p : ℕ} (B : Matrix (Fin m) (Fin p) (Formalism.MainNotions.StandardLatticesGL3.AE D)), cTA D (cTA D B) = B := fun B => by
    ext i j; simp [cTA, hsg]
  have hU : ∀ {m : ℕ} (g : Formalism.MainNotions.StandardLatticesGL3.GA D m), cTA D ((g : GL (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * ((g : GL (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) = 1 := fun g => by
    have h := g.2
    change Formalism.UG.cT _ _ * ((1 : Matrix _ _ D.host.E).map _) * _ = (1 : Matrix _ _ D.host.E).map _ at h
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
    exact h
  set X : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hX
  set V : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hV
  set Y : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hY
  have hVX : V * X = 1 := by rw [hV, hX, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXc : X * cTA D X = 1 := mul_eq_one_comm.1 (hU x)
  have hVe : V = cTA D X := by
    calc V = V * (X * cTA D X) := by rw [hXc, Matrix.mul_one]
      _ = cTA D X := by rw [← Matrix.mul_assoc, hVX, Matrix.one_mul]
  have hVV : V * cTA D V = 1 := by rw [hVe, hcc, hU x]
  rw [hΦ, hΦ, hmul, hmul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV, Matrix.one_mul,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hY1 : cTA D Y * Y = 1 := hU y
  rw [Matrix.mul_assoc (cTA D A), hY1, Matrix.mul_one, Matrix.trace_mul_comm]

theorem sq_move_int : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) {a d : ℕ} (A : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (M : ℕ), 0 < M → ∃ n : ℕ, 0 < n ∧ ∀ A' : Matrix (Fin d) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D), (∀ i j, ∃ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc, A' i j - A i j = (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * t) → ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, (∑ i, ∑ j, A' i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A' i j)) - (∑ i, ∑ j, A i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (A i j)) = (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
  intro D cc a d A M hM
  obtain ⟨B, hB, hBA⟩ := GlobalTheory.NormSum.Expand.denom_fin (fun k : Fin d × Fin a => A k.1 k.2)
  obtain ⟨m, hm, hmI⟩ := GlobalTheory.CompletedLattice.exists_mul_IhE_mem D cc
  refine ⟨M * B * m, by positivity, fun A' hA' => ?_⟩
  choose t ht et using hA'
  have hsg : ∀ u ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, Formalism.MainNotions.StandardLatticesGL3.sgA D u ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun u hu =>
    GlobalTheory.NormSum.UnramHecke.sgA_mem D hu
  have hA1 : ∀ i j, (B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun i j => hBA (i, j)
  have ht1 : ∀ i j, (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := fun i j => hmI _ (ht i j)
  refine ⟨∑ i, ∑ j, (((B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) +
      ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((B : Formalism.MainNotions.StandardLatticesGL3.AE D) * A i j) +
      ((M * B * B : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * (((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j) * Formalism.MainNotions.StandardLatticesGL3.sgA D ((m : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j))),
    sum_mem fun i _ => sum_mem fun j _ => add_mem (add_mem (mul_mem (hA1 i j) (hsg _ (ht1 i j)))
      (mul_mem (ht1 i j) (hsg _ (hA1 i j)))) (mul_mem (natCast_mem _ _) (mul_mem (ht1 i j) (hsg _ (ht1 i j)))), ?_⟩
  have hA' : ∀ i j, A' i j = A i j + ((M * B * m : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * t i j := fun i j => by
    rw [← et i j]; ring
  simp only [hA', Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add (f := _), map_mul, map_natCast]
  push_cast
  ring

theorem sq_diff_int : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (z : Matrix (Fin d) (Fin a) D.host.E) (M : ℕ), 0 < M → ∃ n : ℕ, 0 < n ∧ ∀ z' : Matrix (Fin d) (Fin a) D.host.E, Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' → IsIntegral ℤ (((∑ i, ∑ j, z' i j * D.host.conj (z' i j)) - ∑ i, ∑ j, z i j * D.host.conj (z i j)) / (M : D.host.E)) := by
  intro D cc a d x y z M hM
  obtain ⟨n, hn, h⟩ := sq_move_int cc ((((y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) * ((((x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)))) M hM
  refine ⟨n, hn, fun z' hz' => ?_⟩
  obtain ⟨s, hs, e⟩ := h (z'.map (Formalism.MainNotions.StandardLatticesGL3.inc D)) fun i j => by
    obtain ⟨t, ht, et⟩ := hz' i j
    exact ⟨t, ht, by rw [← et, Matrix.sub_apply]⟩
  rw [sq_unitary] at e
  have hinc : ∀ w : Matrix (Fin d) (Fin a) D.host.E, (∑ i, ∑ j, w.map (Formalism.MainNotions.StandardLatticesGL3.inc D) i j * Formalism.MainNotions.StandardLatticesGL3.sgA D (w.map (Formalism.MainNotions.StandardLatticesGL3.inc D) i j)) = Formalism.MainNotions.StandardLatticesGL3.inc D (∑ i, ∑ j, w i j * D.host.conj (w i j)) := fun w => by

    simp only [Matrix.map_apply, map_sum, map_mul]
    rfl
  rw [hinc, hinc, ← map_sub] at e
  have hM0 : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← GlobalTheory.HeckeVal.inc_mem_iff]
  have e2 : Formalism.MainNotions.StandardLatticesGL3.inc D (((∑ i, ∑ j, z' i j * D.host.conj (z' i j)) - ∑ i, ∑ j, z i j * D.host.conj (z i j)) / (M : D.host.E)) = Formalism.MainNotions.StandardLatticesGL3.inc D (M : D.host.E)⁻¹ * (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
    rw [div_eq_inv_mul, map_mul, e, mul_assoc]
  have e3 : Formalism.MainNotions.StandardLatticesGL3.inc D (M : D.host.E)⁻¹ * (M : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 := by
    rw [← map_natCast (Formalism.MainNotions.StandardLatticesGL3.inc D), ← map_mul, inv_mul_cancel₀ hM0, map_one]
  rw [e2, e3, one_mul]
  exact hs

theorem qH_pt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hC : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) {a d : ℕ}
    (z : Matrix (Fin d) (Fin a) D.host.E) :
    Formalism.MainNotions.TaylorLogMetric.qH D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) =
      (∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j))).re / (Ideal.absNorm cc : ℝ) := by
  have hδ : δ ≠ 0 := GlobalTheory.NormExact.delta_ne_zero hC
  have hN : (0 : ℝ) < Ideal.absNorm cc := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hC.1.1)
  have hd : (0 : ℝ) < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hc : ∀ τ x, embT D τ (D.host.conj x) = starRingEnd ℂ (embT D τ x) := fun τ x =>
    D.host.conjE_apply (embT D τ) x
  have hpt : ∀ τ i j, pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := fun τ i j => rfl
  have hS : ∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j)) =
      ∑ τ, ∑ i, ∑ j, embT D τ (z i j) * starRingEnd ℂ (embT D τ (z i j)) := by

    simp only [map_sum, map_mul, hc]
  have hH : Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ z) =
      ((Complex.normSq δ : ℝ) : ℂ) * (∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (z i j))) /
        ((area (lamOf D cc δ) : ℝ) : ℂ) := by
    rw [hS, Hf]
    simp only [hpt, map_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [Formalism.MainNotions.TaylorLogMetric.qH, hH, GlobalTheory.MomDict.area_lamOf D cc δ hC.1.1]
  have hδ2 : 0 < Complex.normSq δ := Complex.normSq_pos.2 hδ
  rw [show ((Complex.normSq δ * (Ideal.absNorm cc : ℝ) * √(D.host.d : ℝ) / 2 : ℝ) : ℂ) =
    ((Complex.normSq δ * (Ideal.absNorm cc : ℝ) * √(D.host.d : ℝ) / 2 : ℝ) : ℂ) from rfl,
    mul_div_assoc, Complex.re_ofReal_mul, Complex.div_ofReal_re]
  field_simp

theorem phase_eq : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ →
  ∀ {a d : ℕ} (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (z : Matrix (Fin d) (Fin a) D.host.E),
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') = Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  intro D cc δ hC a d x y z
  have hN : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hC.1.1)
  obtain ⟨n, hn, h⟩ := sq_diff_int cc x y z (8 * Ideal.absNorm cc) (by positivity)
  refine ⟨n, hn, fun z' hz' => ?_⟩
  obtain ⟨m, hm⟩ := trace_sum_int D _ (h z' hz')
  set S' := ∑ i, ∑ j, z' i j * D.host.conj (z' i j)
  set S := ∑ i, ∑ j, z i j * D.host.conj (z i j)
  have h8 : ((8 * Ideal.absNorm cc : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have hsplit : S' = S + ((8 * Ideal.absNorm cc : ℕ) : D.host.E) * ((S' - S) / ((8 * Ideal.absNorm cc : ℕ) : D.host.E)) := by
    field_simp; ring
  have key : (∑ τ, embT D τ S').re = (∑ τ, embT D τ S).re + 4 * (Ideal.absNorm cc : ℝ) * m := by
    rw [hsplit]
    simp only [map_add (f := _), map_mul, map_natCast, Finset.sum_add_distrib, ← Finset.mul_sum, Complex.add_re]
    have e : ((8 * Ideal.absNorm cc : ℕ) : ℂ) = (((8 * Ideal.absNorm cc : ℕ) : ℝ) : ℂ) := rfl
    rw [e, Complex.re_ofReal_mul]
    push_cast at hm ⊢
    rw [← hm]; ring
  have hN' : (0 : ℝ) < Ideal.absNorm cc := by exact_mod_cast hN
  have harg : (∑ τ, embT D τ S').re / (Ideal.absNorm cc : ℝ) / 2 =
      (∑ τ, embT D τ S).re / (Ideal.absNorm cc : ℝ) / 2 + 2 * m := by
    rw [key]; field_simp; ring
  rw [Formalism.MainNotions.StandardLatticesGL3.wdPh, Formalism.MainNotions.StandardLatticesGL3.wdPh, qH_pt hC z', qH_pt hC z, harg]
  unfold Formalism.MainNotions.StandardLatticesGL3.ee
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨2 * m, ?_⟩
  push_cast
  ring

end GlobalTheory.PhaseMove
end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.weilOperator_normalisingVector_ne_zero : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) {a d : ℕ} (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0),
  Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ → oddE0 D cc δ t0 a d e0 →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d), W.Om x y e0 ≠ 0 := by
  first | exact @GlobalTheory.NormExact.om_normalising_ne_zero | exact GlobalTheory.NormExact.om_normalising_ne_zero | (intros; apply GlobalTheory.NormExact.om_normalising_ne_zero <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_pos_nat_mul_inv_idealLattice_mem_integral : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (r : D.host.E), ∃ M : ℕ, 0 < M ∧
    ∀ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc, (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * t) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  first | exact @GlobalTheory.NormSum.IdealDenom.exists_nat_mul_inv_mul_mem | exact GlobalTheory.NormSum.IdealDenom.exists_nat_mul_inv_mul_mem | (intros; apply GlobalTheory.NormSum.IdealDenom.exists_nat_mul_inv_mul_mem <;> assumption)
end

section

open MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.ConvSeries

theorem exists_mem_prod_mul_gauss {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ))
    (hM : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M)
    (G : SchwartzMap E ℂ) (hG : G ∈ M) :
    ∀ (m : ℕ) (ℓ : Fin m → E →L[ℝ] ℝ), ∃ t ∈ M, ∀ y, t y = (∏ i, ((ℓ i y : ℝ) : ℂ)) * G y := by
  intro m
  induction m with
  | zero => intro ℓ; exact ⟨G, hG, fun y => by simp⟩
  | succ m ih =>
    intro ℓ
    obtain ⟨t, ht, hty⟩ := ih (fun i => ℓ i.succ)
    have hg : (fun x : E => ((ℓ 0 x : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp (ℓ 0)).hasTemperateGrowth
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ 0 x : ℝ) : ℂ)) t,
      hM (ℓ 0) t _ ht (fun x => by rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]), fun y => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hty, Fin.prod_univ_succ, mul_assoc]

theorem gauss_mul_diag_mem : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (c : ℝ), 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (k : ℕ) (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ),
      ∃ t ∈ M, ∀ y, t y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * B (fun _ => y) := by
  intro E _ _ _ M hM c hc hGM k B
  have hin : ∀ x : E, innerSL ℝ x x = ‖x‖ ^ 2 := fun x => by
    first
    | rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
    | simp [real_inner_self_eq_norm_sq]
    | exact real_inner_self_eq_norm_sq x
  obtain ⟨G, hG⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag (-c • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
    (fun x hx => by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; rw [hin]
      have : 0 < ‖x‖ ^ 2 := by positivity
      nlinarith)
  have hG' : ∀ y, G y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := fun y => by
    rw [hG, Complex.ofReal_exp]
    congr 1
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; rw [hin]
    push_cast; ring
  have hGmem := hGM G hG'
  let b := stdOrthonormalBasis ℝ E
  have key : ∀ r : Fin k → Fin (Module.finrank ℝ E), ∃ t ∈ M,
      ∀ y, t y = (∏ j, ((innerSL ℝ (b (r j)) y : ℝ) : ℂ)) * G y :=
    fun r => exists_mem_prod_mul_gauss M hM G hGmem k (fun j => innerSL ℝ (b (r j)))
  choose t ht hty using key
  refine ⟨∑ r, B (fun j => b (r j)) • t r, M.sum_mem fun r _ => M.smul_mem _ (ht r), fun y => ?_⟩
  have hy : (fun _ : Fin k => y) = fun _ : Fin k => ∑ i, (inner ℝ (b i) y) • b i := by
    funext _; exact (b.sum_repr' y).symm

  rw [hy, ContinuousMultilinearMap.map_sum, Finset.mul_sum, SchwartzMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [B.map_smul_univ (fun j => inner ℝ (b (r j)) y) (fun j => b (r j)), SchwartzMap.smul_apply, hty, hG',
    Complex.real_smul, smul_eq_mul]
  have hi : ∀ v : E, innerSL ℝ v y = inner ℝ v y := fun v => rfl
  simp only [hi]
  push_cast
  ring

end GlobalTheory.ConvSeries
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.integral_eq_volume_sum_characterTwistedCosets : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (U : AddSubgroup X), IsOpen (U : Set X) → μ (U : Set X) ≠ ⊤ →
    ∀ g : X → ℂ, HasCompactSupport g → (∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) →
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.TwistedCosetSum.integral_eq_sum_twisted | exact GlobalTheory.TwistedCosetSum.integral_eq_sum_twisted | (intros; apply GlobalTheory.TwistedCosetSum.integral_eq_sum_twisted <;> assumption)
end
