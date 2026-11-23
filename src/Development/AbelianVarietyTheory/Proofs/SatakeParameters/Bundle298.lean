module

public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle119
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle296
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle288
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle122
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle140
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle239
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThCLeftStab
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle003
public import Formalism.LocalRingCardinality.Bundle003
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle289
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle292
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

noncomputable section

namespace GlobalTheory.AtG.KernelSizes

variable {D : D7} {L : SizeData₂ D}

theorem key_ineq (A N Y : ℝ) (hA : 10 ≤ A) (hN : 2 ≤ N) (h1 : A ^ 8 ≤ Y) (h2 : N ^ 16 ≤ Y) :
    6 * A ^ 2 * N + 2 < Y := by
  have hA1 : 1 ≤ A := by linarith
  by_cases h : N ≤ A ^ 5
  · have hA7 : 1 ≤ A ^ 7 := one_le_pow₀ hA1
    have e1 : 6 * A ^ 2 * N ≤ 6 * A ^ 7 := by
      have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 6 * A ^ 2)
      calc 6 * A ^ 2 * N ≤ 6 * A ^ 2 * A ^ 5 := this
        _ = 6 * A ^ 7 := by ring
    have e2 : A ^ 8 = A * A ^ 7 := by ring
    have e3 : 10 * A ^ 7 ≤ A * A ^ 7 := mul_le_mul_of_nonneg_right hA (by positivity)
    linarith
  · push_neg at h
    have hA25 : A ^ 2 ≤ A ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
    have hAN : A ^ 2 < N := lt_of_le_of_lt hA25 h
    have e1 : 6 * A ^ 2 * N < 6 * N * N := by nlinarith
    have hN14 : 8 ≤ N ^ 14 := by
      have : (2 : ℝ) ^ 14 ≤ N ^ 14 := pow_le_pow_left₀ (by norm_num) hN 14
      linarith
    have e2 : N ^ 16 = N ^ 2 * N ^ 14 := by ring
    have e3 : N ^ 2 * 8 ≤ N ^ 2 * N ^ 14 := mul_le_mul_of_nonneg_left hN14 (by positivity)
    nlinarith

theorem exists_Y (P : ParameterChoice' D L) :
    ∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧ (D.R.N D.R.m : ℝ) ^ 16 ≤ Y ∧ ∀ i, Y ≤ (D.host.g i : ℝ) := by
  obtain ⟨Y, h1, h2, -, h4⟩ := P.g_Y
  have hx0 : (0 : ℝ) < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hq : (0 : ℝ) < D.host.q := lt_trans (Real.rpow_pos_of_pos hx0 _) P.qd_pow.1
  have hd : (0 : ℝ) < D.host.d := lt_trans (Real.rpow_pos_of_pos hx0 _) P.qd_pow.2
  have hq1 : (1 : ℝ) ≤ D.host.q := by
    have : 0 < D.host.q := by exact_mod_cast hq
    exact_mod_cast this
  have hd1 : (1 : ℝ) ≤ D.host.d := by
    have : 0 < D.host.d := by exact_mod_cast hd
    exact_mod_cast this
  have hQ1 : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hc : (1 : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by
    unfold LevelStarExponents.condE
    push_cast
    calc (1 : ℝ) ≤ 1 * 1 * 1 := by norm_num
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by gcongr
  have hcC : 1 ≤ (LevelStarExponents.condE D : ℝ) ^ P.CY := Real.one_le_rpow hc P.CY_pos.le
  have hY0 : 0 ≤ Y := le_trans (by positivity) h1
  have hN4 : (D.R.N D.R.m : ℝ) ^ 4 ≤ Y ^ ((1 : ℝ) / 4) := by
    have hN : 0 ≤ (D.R.N D.R.m : ℝ) ^ 4 := by positivity
    nlinarith
  refine ⟨Y, h1, ?_, fun i => (h4 i).1⟩
  have h5 : ((D.R.N D.R.m : ℝ) ^ 4) ^ 4 ≤ (Y ^ ((1 : ℝ) / 4)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hN4 4
  have h6 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y := by
    rw [← Real.rpow_natCast (Y ^ ((1 : ℝ) / 4)), ← Real.rpow_mul hY0]
    norm_num
  rw [h6] at h5
  calc (D.R.N D.R.m : ℝ) ^ 16 = ((D.R.N D.R.m : ℝ) ^ 4) ^ 4 := by ring
    _ ≤ Y := h5

theorem nuAbs_le (P : ParameterChoice' D L) (u : D.what₂.Word) (j : ℕ) (hj : j ∈ LiftErrorLocal.lifts D) (τ : D.what₂.Tau) :
    nuAbs D u j τ ≤ (D.R.N D.R.m : ℝ) * (3 * L.sc.a) := by
  unfold LiftErrorLocal.lifts at hj
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := by omega
  have hb : ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b' := fun t => by
    have := P.bT_le' t
    have := GlobalTheory.CoreHt.RowsRange.b'_pos L
    linarith
  have hT : GlobalTheory.CoreHt.ThickUp L := fun j h1 h2 τ hc => (L.win_thick j h1 h2 τ hc).2
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a
    have := GlobalTheory.CoreHt.RowsRange.one_le_b L
    have := L.sc.one_lt_alt
    positivity
  have hrow : ∀ r ∈ Finset.range (D.R.N (i + 1 - 1)), DV.nuRow D u (i + 1) τ r ≤ 3 * L.sc.a := by
    intro r hr
    rw [Finset.mem_range, Nat.add_sub_cancel] at hr
    exact (RowWeightLemmas.nuRow_anti' D u i hi τ r 0 (Nat.zero_le _) hr).trans
      (GlobalTheory.CoreHt.RowsRange.nuRow_zero_le_three_mul L P hb hT u i hi τ)
  unfold nuAbs
  have hs := Finset.sum_le_card_nsmul _ _ _ hrow
  rw [Finset.card_range, nsmul_eq_mul, Nat.add_sub_cancel] at hs
  have hNi : (D.R.N i : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.N i ≤ D.R.N D.R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right (D.R.t + 1) hi.le
      omega
    exact_mod_cast this
  rw [Nat.add_sub_cancel]
  calc _ ≤ (D.R.N i : ℝ) * (3 * L.sc.a) := hs
    _ ≤ _ := mul_le_mul_of_nonneg_right hNi (by positivity)

theorem Dpi_le (P : ParameterChoice' D L) (u : D.what₂.Word) (j : ℕ) (hj : j ∈ LiftErrorLocal.lifts D) :
    LiftErrorLocal.Dpi D u j ≤ (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * (3 * L.sc.a)) := by
  unfold LiftErrorLocal.Dpi
  have hs := Finset.sum_le_card_nsmul (Finset.univ : Finset D.what₂.Tau) (fun τ => nuAbs D u j τ) _
    (fun τ _ => nuAbs_le P u j hj τ)
  rw [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at hs
  exact hs

theorem sizeAt_of_params : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L →
    Formalism.MainNotions.SizesAt L → L.sc.eps = eps → x0 ≤ L.sc.x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i := by
  intro eps _ _
  refine ⟨0, fun D L P hS _ _ i => ?_⟩
  obtain ⟨Y, hY1, hY2, hY3⟩ := exists_Y P
  have hx1 := L.sc.one_lt_alt
  have hk5 : (5 : ℝ) ≤ D.R.k := P.five_le_k
  have hb2 : 2 ≤ L.sc.b := by
    have h1 := GlobalTheory.CoreHt.RowsRange.one_le_scL L
    have h2 := Real.add_one_le_exp L.sc.L
    unfold Scale.b
    linarith
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by
    have : D.R.f ≤ D.R.k := D.R.f_le_k
    exact_mod_cast this
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hNk : (D.R.k : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this

  have hxk : L.sc.x ≤ D.R.k := by
    have hK := hS.2.2.1.1
    have he : (1 : ℝ) ≤ 9 / 2 + 10 * L.sc.eps - szTh L := by
      unfold szTh
      linarith [L.sc.eps_pos, L.sc.eps_lt]
    have := Real.rpow_le_rpow_of_exponent_le hx1.le he
    rw [Real.rpow_one] at this
    linarith
  have hak : L.sc.a ≤ D.R.k * L.sc.b := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right hxk (by linarith)
  set A : ℝ := (D.R.k : ℝ) * L.sc.b with hA
  set N : ℝ := (D.R.N D.R.m : ℝ) with hN
  have hA10 : 10 ≤ A := by rw [hA]; nlinarith
  have hN2 : 2 ≤ N := by linarith
  have hkey := key_ineq A N Y hA10 hN2 hY1 hY2
  have hkA : (D.R.k : ℝ) ^ 2 * L.sc.b ≤ A ^ 2 := by
    rw [hA]
    have : (D.R.k : ℝ) ^ 2 * L.sc.b * 1 ≤ (D.R.k : ℝ) ^ 2 * L.sc.b * L.sc.b :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith

  have hD : ∀ u : D.what₂.Word, ∀ j ∈ LiftErrorLocal.lifts D, LiftErrorLocal.Dpi D u j ≤ 3 * A ^ 2 * N := by
    intro u j hj
    have h1 := Dpi_le P u j hj
    have hN0 : 0 ≤ N := by linarith
    have h2 : (D.R.f : ℝ) * (N * (3 * L.sc.a)) ≤ (D.R.k : ℝ) * (N * (3 * (D.R.k * L.sc.b))) := by
      apply mul_le_mul hfk _ (by have := GlobalTheory.CoreHt.RowsRange.one_le_b L; unfold Scale.a; positivity) (by linarith)
      exact mul_le_mul_of_nonneg_left (by linarith) hN0
    have h3 : (D.R.k : ℝ) * (N * (3 * (D.R.k * L.sc.b))) = 3 * ((D.R.k : ℝ) ^ 2 * L.sc.b) * N := by ring
    have h4 : 3 * ((D.R.k : ℝ) ^ 2 * L.sc.b) * N ≤ 3 * A ^ 2 * N := by
      have := mul_le_mul_of_nonneg_left hkA (by norm_num : (0 : ℝ) ≤ 3)
      exact mul_le_mul_of_nonneg_right this hN0
    linarith
  have hg := hY3 i
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  refine ⟨?_, fun u j hj => ?_⟩
  · have h1 : (2 * D.R.f * D.R.N D.R.m + 1 : ℝ) < D.host.g i := by
      have : (2 : ℝ) * D.R.f * N ≤ 2 * (3 * A ^ 2 * N) := by
        have : (D.R.f : ℝ) ≤ 3 * A ^ 2 := by nlinarith
        nlinarith
      linarith
    exact_mod_cast h1
  · have h := hD u j hj
    constructor
    · linarith
    · nlinarith

end GlobalTheory.AtG.KernelSizes
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.fontaineParameter_invariant_under_conjugation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (r r' : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A) →* GL (Fin a) (Qbar l)) (p : GL (Fin a) (Qbar l)), (∀ g, r' g = p * r g * p⁻¹) → IsPstAt P Bw r → IsPstAt P Bw r' ∧ wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  first | exact @GlobalTheory.PstConj.main | exact GlobalTheory.PstConj.main | (intros; apply GlobalTheory.PstConj.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ K, NG.rt L n κ f = ((θ ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f) → ∃ u : σ.V, u ≠ 0 ∧ ∀ g (h : g ∈ K), σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((θ ⟨g, h⟩ : ℂˣ) : ℂ) • u := by
  first | exact @GlobalTheory.LocVec.main | exact GlobalTheory.LocVec.main | (intros; apply GlobalTheory.LocVec.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_irreducible_fixed_vectors : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ), K ≤ KO (s.w.adicCompletion L) (Fin n) → (∀ h ∈ KOne (s.w.adicCompletion L) (Fin n), h ∈ K ∧ θ h = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∃ y : σ.V, y ≠ 0 ∧ ∀ h ∈ K, σ.ρ h y = θ h • y := by
  first | exact @GlobalTheory.EigLocal.exists_eigen_local | exact GlobalTheory.EigLocal.exists_eigen_local | (intros; apply GlobalTheory.EigLocal.exists_eigen_local <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KFiDat

theorem termLaw_of_xi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.X.Ok → IsSel t.X t.sel → (∀ i, t.Pr.g i ∈ t.S) → (∀ v, t.Pr.T v ∈ t.S) → (∀ l ∈ D.host.small, l ∈ t.S) → D.host.q ∈ t.S → (∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta) → ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K), gmap γ.1 ((t.rd u μ).N (i + 1) c') = (t.rd u μ).N (i + 1) c' → (∀ x, ∀ z ∈ mulLat (t.rd u μ).lev (homAt (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')), (t.rd u μ).Xi i c c' (x + z) = (t.rd u μ).Xi i c c' x) → (∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) * t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E)) = t.seam.σ₀ k * (t.rd u μ).Xi i c c' x) → TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
  intro D L hT Gi Gl K Y cX ex t hX hsel hgS hTS h2S hqS hTied u μ i hi c c' γ k hγ hΞ hXi
  obtain ⟨eta, hTied⟩ := hTied
  have hok := t.seam_ok
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  set z : t.X.E := ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) with hz
  have hz0 : z ≠ 0 := Units.ne_zero _
  have hSD' : IsSDLat D.host.E _ (t.seam.lat ((t.rd u μ).N (i + 1) c')) :=
    t.O_lat u μ (i + 1) c' ▸ ((t.O u μ).lat (i + 1) c').2
  obtain ⟨hzs, hzi, hprod1⟩ := GlobalTheory.T.det_unitaryStabiliser_selfDualLattice_normOne D t.X t.seam t.χ hok t.χ_ok _ _ hSD' γ hγ
  let eZ : Fin D.R.m → t.X.Tau → ℤ := fun j τ => (D.chTw u μ).sDiv j (t.seam.iT τ) + ((D.R.N j / 2 : ℕ) : ℤ)
  have heZ : ∀ j τ, ((eZ j τ : ℤ) : ℚ) = (D.hc (t.seam.iT τ)).e j := by
    intro j τ
    have h1 := (D.chTw u μ).sDiv_eq j j.2 (t.seam.iT τ)
    rw [D.hcW_e] at h1
    obtain ⟨m, hm⟩ := rank_even D.R j
    have h2 : ((D.R.N j / 2 : ℕ) : ℚ) = (D.R.N j : ℚ) / 2 := by
      rw [hm]; push_cast; rw [show m + m = 2 * m by ring, Nat.mul_div_cancel_left _ two_pos]; push_cast; ring
    simp only [eZ]
    rw [Int.cast_add, h1, Int.cast_natCast, h2, sExp, Nat.add_sub_cancel]
    ring
  have hTied' : t.Ch.Tied t.glob.σ₀ (fun j τ => ((eZ j τ : ℤ) : ℚ)) t.glob.mu0 eta := by
    have e : (fun j τ => ((eZ j τ : ℤ) : ℚ)) = (fun j τ => (D.hc (t.seam.iT τ)).e j) := funext fun j => funext fun τ => heZ j τ
    rw [e]; exact hTied
  have hP := GlobalTheory.NormOneUnit.prod_muAt t.Ch t.sel (t.tup μ) (t.cst μ) t.glob.σ₀ eZ t.glob.mu0 eta hX t.pr_ok hsel hgS
    (GlobalTheory.T.columnField_ramificationIdxIn_eq_one D t.X t.seam hX hok) hTied' ⟨i, hi⟩ z hzs hzi
  rw [t.glob_σ] at hP
  set M := t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P z) with hMdef
  have hw0 : ∀ τ, t.X.embC t.seam.σ₀ τ z ≠ 0 := fun τ => (map_ne_zero _).2 hz0
  have hP' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(eZ ⟨i, hi⟩ τ)) := hP
  have hM0 : M ≠ 0 := by
    rw [hP']
    exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hw0 τ)
  have hk : ∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) = (t.seam.σ₀ k / M) * (t.rd u μ).Xi i c c' x := by
    intro x
    have := hXi x
    field_simp
    linear_combination this
  have hA : TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) := by
    rw [← t.O_lat, ← t.O_lat]
    exact ⟨rank_even _ _, rank_even _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  have hSSc : ∀ P ∈ (t.rd u μ).SS, conjPrime₂ P ∉ (t.rd u μ).SS := by
    rw [hSS]
    exact GlobalTheory.T.memberBadPrimes_no_conjugatePair t.sel (t.tup μ) hX t.pr_ok hsel (t.word u) (hTS _) hgS
  have h2q : ∀ P ∈ (t.rd u μ).SS, ((D.host.QS : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal ∧ ((D.host.q : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
    intro P hP
    rw [hSS] at hP
    obtain ⟨p, hp, hpP, hk⟩ := sall_nat t.sel (t.tup μ) t.pr_ok hsel (t.word u) hP
    have hp2 : p ∉ D.host.small ∧ p ≠ D.host.q := by
      rcases hk with e | ⟨j, e⟩ | hn
      · rw [e, t.T_rec]; exact ⟨UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u), D.T_ne_q u⟩
      · rw [e, t.g_rec]; exact ⟨UpperTheory.Ram.g_notMem_small D j, GlobalTheory.ShortOwnCompare.level_ne_q D j⟩
      · exact ⟨fun e => hn (h2S _ e), fun e => hn (e ▸ hqS)⟩
    have key : ∀ l : ℕ, l.Prime → l ≠ p → ((l : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
      intro l hl hlp hlP
      have hc : IsCoprime ((p : ℕ) : 𝓞 t.X.E) ((l : ℕ) : 𝓞 t.X.E) := by
        have h1 := (Nat.coprime_primes hp hl).2 (Ne.symm hlp)
        have h2 := (Nat.isCoprime_iff_coprime.2 h1).map (Int.castRingHom (𝓞 t.X.E))
        simpa using h2
      obtain ⟨a, b, hab⟩ := hc
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (P.asIdeal.mul_mem_left a hpP) (P.asIdeal.mul_mem_left b hlP)))
    exact ⟨UpperTheory.Ram.natCast_notMem_of_coprime P.isPrime.ne_top hpP
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (UpperTheory.Small.not_dvd_QS D.host hp hp2.1)).symm, key _ D.host.hyp.1 hp2.2.symm⟩
  have hlev0 : 0 < (t.rd u μ).lev := by
    rw [hlev]
    exact modulus_pos t.sel (t.tup μ) (t.cst μ) (t.word u) (t.pr_ok.T_prime _).pos
  have key := GlobalTheory.KerLaw.thC_left_stab D t.X t.seam t.cc t.δ t.B t.χ t.cD hok t.cc_ok t.δ_ok t.χ_ok _ _ _ _ hA
    (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c') hlev0 hSSc h2q hΞ γ hγ _ hk
  have hdet : (matE t.seam γ.1).det = t.seam.iE z := by
    rw [matE]
    change ((t.seam.iE : t.X.E →+* D.host.E).mapMatrix (LinearMap.toMatrix' γ.1.toLinearMap)).det = _
    rw [← RingHom.map_det, LinearMap.det_toMatrix', hz, LinearEquiv.coe_det]
    rfl
  refine ⟨by rw [hdet]; exact (map_ne_zero _).2 hz0, t.seam.σ₀ k / M, fun w => ?_, ?_⟩
  · rw [t.O_Th]
    unfold KerRead.Th Seam.push
    refine (congrArg _ ?_).trans (key (fun τ => w (t.seam.iT τ)))
    funext τ
    refine congrArg (· * Matrix.of (w (t.seam.iT τ))) ?_
    ext a b
    simp only [matE, Matrix.map_apply]
    exact (hok.1 τ _).symm
  · show t.seam.σ₀ k = t.seam.σ₀ k / M * ∏ τ, TaylorLogMetric.embT D τ (matE t.seam γ.1).det ^ (-(D.chTw u μ).sDiv i τ)
    rw [hdet]
    have hw : ∀ τ, t.X.embC t.seam.σ₀ τ z = TaylorLogMetric.embT D (t.seam.iT τ) (t.seam.iE z) := fun τ => hok.1 τ z
    have hR : ∏ τ, TaylorLogMetric.embT D τ (t.seam.iE z) ^ (-(D.chTw u μ).sDiv i τ) =
        ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) :=
      (Fintype.prod_equiv t.seam.iT _ _ fun τ => by rw [hw]).symm
    have h1 : ∏ τ, t.X.embC t.seam.σ₀ τ z = 1 := by
      rw [← hprod1]
      exact Fintype.prod_equiv t.seam.iT _ _ fun τ => hw τ
    have hM' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) := by
      rw [hP']
      simp only [eZ]
      have e1 : ∀ τ, t.X.embC t.seam.σ₀ τ z ^ (-((D.chTw u μ).sDiv i (t.seam.iT τ) + ((D.R.N i / 2 : ℕ) : ℤ))) =
          t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) * t.X.embC t.seam.σ₀ τ z ^ (-((D.R.N i / 2 : ℕ) : ℤ)) :=
        fun τ => by rw [neg_add, zpow_add₀ (hw0 τ)]
      rw [Finset.prod_congr rfl fun τ _ => e1 τ, Finset.prod_mul_distrib, Finset.prod_zpow, h1, one_zpow, mul_one]
    rw [hR, ← hM']
    field_simp

end GlobalTheory.KFiDat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ D.sp.X'.rank → MatchE R t (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (splitC (Yc D 0).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf D.sp.X'.rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Yc D 0).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Yc D 0).rank (A.q P) a).comp (C ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) * ((A.fam.R t).blockProd P).map D.what₂.embLL := by
  first | exact @GlobalTheory.Hk3.SplitChain.exists_transfer | exact GlobalTheory.Hk3.SplitChain.exists_transfer | (intros; apply GlobalTheory.Hk3.SplitChain.exists_transfer <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transportedPolynomial_complexPoint_evaluation : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = ι ((∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  first | exact @GlobalTheory.TwV.DelA.evD_trDY_polDY | exact GlobalTheory.TwV.DelA.evD_trDY_polDY | (intros; apply GlobalTheory.TwV.DelA.evD_trDY_polDY <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.Pdv.stdKer_stdRd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.supercuspidal_support_characters : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ), HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (chars ξ hξ) ∧ (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) ∧ Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) ∧ B = Finset.univ.val.map fun j => ξ j ϖ := by
  first | (exact @GlobalTheory.SatSupp.hasSupport_of_hasSatGL) | (exact GlobalTheory.SatSupp.hasSupport_of_hasSatGL) | (intros; apply GlobalTheory.SatSupp.hasSupport_of_hasSatGL  <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weilDeligneParam_eq_unramifiedSatake_of_frobenius : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w), ∀ B : Multiset ℂˣ, UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat n (normV w) B) → wdOf h hl ι r = satWD h n B := by
  first | (exact @GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig) | (exact GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig) | (intros; apply GlobalTheory.RoadU.wdOf_eq_satWD_of_frobEig  <;> assumption)
end
