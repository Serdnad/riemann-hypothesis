module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle319
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle212
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle172
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle299
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle109
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle306
import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle287
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle322
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle323
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle324
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTubeGaugeMassAsymptotic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.HahnBanach
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017

@[expose] public section

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm

theorem pairsPar : ∀ (Ca Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D), HostC →
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → 1 ≤ C' → 1 ≤ Cl → CT ≤ Ca →
    Module.finrank ℚ D.host.E = 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m = 2 * D.R.rS + 2 ∧ Cl ≤ (D.R.m : ℝ) ∧
    D.R.m ^ 4 ≤ Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m ^ 5 * Formalism.HermitianLatticesTheory.fDeg D.host.E ≤ D.R.k ∧
    Cl * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k ∧ Real.log (Formalism.HermitianLatticesTheory.fDeg D.host.E : ℝ) ≤ Real.sqrt D.R.rS ∧
    2 ≤ large₂.sc.b ∧ 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E ∧ 2 * Formalism.HermitianLatticesTheory.vInv D.host.E ≤ large₂.sc.b ∧
    ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (_root_.Formalism.MainNotions.S.Lat.gS D : ℝ) ∧
    ∀ u : D.what₂.Word, 1 ≤ Tu D u ∧ (Tu D u : ℝ) ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
  intro Ca Cg cb Cw cT CT C0 C' Cl D large₂ hH hK hC' hCl hCa
  have hStd : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩
  obtain ⟨_, _, hvI, hv1, hf, _, hfin, _, _, _, _, hg2, hT⟩ := hH D large₂ hStd
  obtain ⟨⟨hS0, _, _⟩, _⟩ := hK
  obtain ⟨_, h2, h3, _, h5, _, h7, _, _, _, h11, h12, _, _, _, _, _, _, _, _, _, _, h23, h24, h25⟩ := hS0
  have hL : 1 < large₂.sc.L := one_lt_scale_L D large₂
  have hb2 : 2 ≤ large₂.sc.b := two_le_scale_b D large₂
  have hlb : Real.log large₂.sc.b = large₂.sc.L := log_scale_eq_L D large₂
  refine ⟨by rw [hfin, hf], (two_rank_add_two_eq_m D).symm, h24, by rw [hf]; exact h3, ?_, by rw [hlb]; exact h7,
    by rw [hf]; exact h5, hb2, by rw [hvI]; exact hv1, ?_, ?_, ?_⟩
  · rw [hf]
    have hm : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := by positivity
    have : ((D.R.m ^ 5 * D.R.f : ℕ) : ℝ) ≤ D.R.k := by
      push_cast
      calc (D.R.m : ℝ) ^ 5 * D.R.f = 1 * ((D.R.m : ℝ) ^ 5 * D.R.f) * 1 := by ring
        _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f) * large₂.sc.L := by gcongr <;> linarith
        _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
        _ ≤ D.R.k := h2
    exact_mod_cast this
  · rw [hvI]
    have hrd : 0 < D.host.rdE := pf_rd_pos D
    have hL0 : 0 < large₂.sc.L := by linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := by
      refine h11.trans ?_
      rw [div_le_iff₀ h25]; nlinarith
    have h2v : 2 * D.host.v = D.host.rdE := by
      show 2 * (D.host.rdE / 2) = D.host.rdE; ring
    rw [h2v]
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log hrd).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.2 h1
      _ = large₂.sc.b := by rw [← hlb, Real.exp_log (by linarith)]
  · have hg1 : 1 ≤ D.host.g 1 := by
      rcases Nat.eq_zero_or_pos (D.host.g 1) with h | h
      · have : _root_.Formalism.MainNotions.S.Lat.gS D = 0 := by simp [_root_.Formalism.MainNotions.S.Lat.gS, h]
        omega
      · exact h
    calc ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 0 : ℝ) := h12
      _ = (D.host.g 0 : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by gcongr; exact_mod_cast hg1
      _ = (_root_.Formalism.MainNotions.S.Lat.gS D : ℝ) := by simp [_root_.Formalism.MainNotions.S.Lat.gS]
  · intro u
    refine ⟨(hT u).1.one_lt.le, ?_⟩
    have h := (h23 u).2
    calc (Tu D u : ℝ) = Tr D u := rfl
      _ ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := h
      _ ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        have : (0 : ℝ) ≤ D.R.m := by positivity
        nlinarith

end GlobalTheory.TypeAsm
end

section

noncomputable section
namespace GlobalTheory.TypeAsm
open Formalism.BasicNotions

theorem gap_hypothesis_of_kernel_bound_large_constant {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cw cT CT C0 : ℝ} (hCl : 1801 ≤ Cl)
    (h : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0) : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  obtain ⟨⟨hS, -, -⟩, -⟩ := h
  obtain ⟨-, -, hmf, hfk, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap, -, -, hClm, -⟩ := hS
  have hL : 1 < large₂.sc.L := Formalism.MainNotions.S.one_lt_scL large₂
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hf16 : 16 ≤ D.R.f := le_trans (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4) hmf
  have hf : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hmn : D.R.m ≤ D.R.r := by
    have h1 : 1 ≤ D.R.k := by omega
    show D.R.m ≤ D.R.k + D.R.m - 1
    omega
  have hmR : (1801 : ℝ) ≤ D.R.m := le_trans hCl hClm
  have hm1801 : 1801 ≤ D.R.m := by exact_mod_cast hmR
  refine ⟨le_trans hm1801 hmn, fun τ j hj => ?_⟩
  have g := hgap τ (j.1 + 1) (by omega) (by omega)
  rw [Formalism.MainNotions.S.bOne_succ τ (j.1 + 1) hj, Formalism.MainNotions.S.bOne_succ τ j.1 j.2] at g
  have hn0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by linarith)
  have h16 : 16 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have a1 : 16 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := by nlinarith
    have a2 : Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) :=
      le_mul_of_one_le_right (by positivity) (by nlinarith)
    linarith [show Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) =
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L by ring]
  have hR : ((16 * (D.R.r : ℚ) ^ 19 : ℚ) : ℝ) ≤ (((D.hc τ).b ⟨j.1 + 1, hj⟩ - (D.hc τ).b j : ℚ) : ℝ) := by
    push_cast
    have e : ((D.hc τ).b ⟨j.1, j.2⟩ : ℝ) = ((D.hc τ).b j : ℝ) := rfl
    linarith
  exact_mod_cast hR

theorem gapC : GapC :=
  ⟨1801, fun _ _ _ _ _ _ _ _ _ _ hCl h => gap_hypothesis_of_kernel_bound_large_constant hCl h⟩

end GlobalTheory.TypeAsm
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.Dec.ProjCuspGap

theorem rank_le_dim {n : ℕ} (ε : Fin n → Bool) : rkR ε ≤ n := by
  refine (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans ?_)
  simp

theorem gap_numeric {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (0 + 4 * n * rkR ε) < h := by
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | h0
  · exact Or.inl h0
  right
  have hq : (0 : ℝ) < rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by exact_mod_cast h0.trans_le (rank_le_dim ε)
  have e : ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt (rkR ε) * rkR ε := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hq.ne']
    norm_num
  rw [e] at hh
  have hp : 0 < (n : ℝ) * (Real.sqrt (rkR ε) * rkR ε) := by positivity
  nlinarith

theorem rank_pos_of_ne {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : ε a ≠ ε b) : 0 < rkR ε := by
  unfold rkR
  refine lt_min (Finset.card_pos.2 ?_) (Finset.card_pos.2 ?_)
  · by_cases ha : ε a = true
    · exact ⟨a, by simp [ha]⟩
    · exact ⟨b, by revert hab ha; cases ε a <;> cases hb : ε b <;> simp [hb]⟩
  · by_cases ha : ε a = true
    · exact ⟨b, by revert hab ha; cases ε a <;> cases hb : ε b <;> simp [hb]⟩
    · exact ⟨a, by simp [ha]⟩

theorem two_mul_lt {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (h0 : 0 < rkR ε) : 2 * (n : ℝ) < h := by
  have hq : (1 : ℝ) ≤ rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by exact_mod_cast h0.trans_le (rank_le_dim ε)
  have h1 : (1 : ℝ) ≤ ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := Real.one_le_rpow hq (by norm_num)
  nlinarith

theorem isStarProjection_of_isOrthProjOnto {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} {S : Submodule ℂ H} (hT : IsOrthProjOnto T S) : IsStarProjection T :=
  ⟨hT.1, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y => hT.2.1 x y⟩

theorem projector_rank_cuspidal : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → GapGe B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → Integrable (ph B d) (muInf B.I) ∧ (HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → IsStarProjection T ∧ FiniteDimensional ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧ Module.finrank ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) = B.D ∧ ∀ Fv ∈ LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund), B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext Fv)) := by
  intro B d h hds hgap hh
  have hD : DecGap := GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hloc : LocDec B h := GlobalTheory.Dec.locDec_of_decGap_gapGe hD B d h hds hgap hh
  have hK : ∀ v, IsKTypeOf (B.I.ε v) (B.σ v) (lowK (B.I.ε v) (B.lam v))
      (lowKSub (B.I.ε v) (B.lam v) (B.σ v)) := fun v =>
    GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub _ _ _ _ _ (hds v).1 (hds v).2.1 fun a b hab =>
      (two_mul_lt _ h (hh v) (rank_pos_of_ne _ hab)).trans_le (hgap v a b hab)
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hds hloc
  have hI := hint 0 le_rfl fun v => gap_numeric _ h (hh v)
  have hph : Integrable (ph B d) (muInf B.I) := by
    refine hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    simpa using hle g
  refine ⟨hph, fun hb hfin T hT => ?_⟩
  obtain ⟨h1, -, -, h4, h5⟩ := (GlobalTheory.GlobProj.globalProj_holds B d hds hph).2.2.2 T hT
  refine ⟨isStarProjection_of_isOrthProjOnto h1, h4 hfin, h5, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact (GlobalTheory.T.convolution_range_cuspidal_of_lowestKType B d h hds hK hh hloc hb hfin T hT y).2

end GlobalTheory.Dec.ProjCuspGap
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff ENNReal

namespace GlobalTheory.SobAtOne

theorem ofReal_list_sum {α : Type*} (S : List α) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ENNReal.ofReal (S.map g).sum = (S.map fun a => ENNReal.ofReal (g a)).sum := by
  induction S with
  | nil => simp
  | cons a S ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.ofReal_add (hg a) (List.sum_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact hg b), ih]

theorem sobolev_at_one_G : ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GG k r) μG → ∃ (C : ℝ)
    (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsCompact K₀ ∧ (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧
    ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B),
      SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C * (Ws.map fun ws =>
        ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum := by
  intro k r μG hμ
  obtain ⟨-, -, -, ε, -, P, hPd, hPJ⟩ := hpkFacts k r
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hPd
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  obtain ⟨S, C, Q, hQ, hS, hC, hsob⟩ := GlobalTheory.T.sobolev_valueAtOne_fixedCompact_diagSignUnitary (2 * r + k + 1) ε
  obtain ⟨c, hc, hB⟩ := GlobalTheory.T.besselUnitary_haar_transport_diagonal k r μG ε P hμ hPd hPJ
  let cj : Mat k r → Mat k r := fun Y => P⁻¹ * Y * P
  have hcjc : Continuous cj := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let ψ : Formalism.REAL.UJ ε → Mt k r := fun y => Matrix.of.symm (cj (umat y))
  have hψc : Continuous ψ := hcjc.comp (Units.continuous_val.comp continuous_subtype_val)
  have hmemG : ∀ g : Mat k r, Formalism.REAL.inUJ ε g → cj g ∈ GG k r := by
    intro g hg
    show cj g ∈ UH (Hpk k r)
    rw [uHConj _ ε (Hpk k r) P hPd hPJ]
    have e : P * cj g * P⁻¹ = g := by
      simp only [cj, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
      rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
    rw [e]; exact hg
  have hlie : ∀ X, Formalism.REAL.inG ε X → InLieHpk k r (cj X) := by
    intro X hX
    have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
    have e1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPP, conjTranspose_one]
    show (P⁻¹ * X * P)ᴴ * Hpk k r + Hpk k r * (P⁻¹ * X * P) = 0
    rw [← hPJ]
    calc (P⁻¹ * X * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) + Pᴴ * Formalism.REAL.Jm ε * P * (P⁻¹ * X * P)
        = Pᴴ * (Xᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (P * P⁻¹) * X) * P := by
          simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [e1, hPP, Matrix.mul_one, Matrix.mul_one, hX', Matrix.mul_zero, Matrix.zero_mul]
  have hwm : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ Y ∈ l.map cj, InLieHpk k r Y := by
    intro l hl Y hY
    obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
    exact hlie Z (hl Z hZ)
  have hK₀ : IsCompact (ψ '' Q) := hQ.image hψc
  have hK₀G : ∀ x ∈ ψ '' Q, Matrix.of x ∈ GG k r := by
    rintro _ ⟨y, -, rfl⟩
    change Matrix.of (Matrix.of.symm (cj (umat y))) ∈ GG k r
    rw [Equiv.apply_symm_apply]
    exact hmemG _ y.2
  have hfin : IsFiniteMeasureOnCompacts μG := by
    obtain ⟨hG, -⟩ := closedSub_groups k r (bvec (wI k r (Fin.last k))) (fun i hi => by
      simp only [bvec, wI]
      rw [Pi.single_apply, if_neg]
      intro h; rw [h] at hi; simp at hi) (by
      have h : herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) =
          Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
        simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [Tz, h]
      simp [Hpk, wI])
    exact ⟨fun K hK => (haarOn_locFinite_openPos k r (GG k r) μG hG hμ).1 K hK⟩
  refine ⟨C * c.toReal, S.map (List.map cj), ψ '' Q, hK₀, ?_, ?_⟩
  · intro ws hws X hX
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hws
    exact hwm l (hS l hl) X hX
  intro B _ _ _ f hf
  have hword : ∀ l : List (Mat k r), (∀ Y ∈ l, InLieHpk k r Y) → SmoothOnH (Hpk k r) (rdWord l f) := by
    intro l
    induction l with
    | nil => intro _; exact hf
    | cons X l ih =>
      intro hl
      exact (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) X B (rdWord l f) (hl X List.mem_cons_self)
        (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY))).2.1
  have hcont : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) →
      ContinuousOn (rdWord (l.map cj) f) (GG k r) := fun l hl =>
    (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) 0 B _ (by simp) (hword _ (hwm l hl))).1
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hI : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) →
      ContinuousOn (fun x : Mt k r => ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2) (ψ '' Q) := fun l hl =>
    (((hcont l hl).comp hof.continuousOn fun x hx => hK₀G x hx).norm).pow 2
  have hnn : 0 ≤ C * c.toReal * ((S.map (List.map cj)).map fun ws =>
      ∫ x in ψ '' Q, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum :=
    mul_nonneg (mul_nonneg hC ENNReal.toReal_nonneg) (List.sum_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact integral_nonneg fun _ => by positivity)
  by_cases h0 : f 1 = 0
  · rw [h0, norm_zero]; simpa using hnn
  haveI : Nontrivial B := ⟨⟨f 1, 0, h0⟩⟩
  obtain ⟨ℓ, hℓ1, hℓ⟩ := exists_dual_vector' ℂ (f 1)
  let F : List (Mat k r) → Mat k r → ℂ := fun l g => ℓ (rdWord (l.map cj) f (cj g))
  have hFc : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε) := fun l hl =>
    ℓ.continuous.comp_continuousOn ((hcont l hl).comp hcjc.continuousOn fun g hg => hmemG g hg)
  have hFd : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X →
      ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0 := by
    intro l hl X hX g hg
    have hA := (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) (cj X) B (rdWord (l.map cj) f) (hlie X hX) (hword _ (hwm l hl))).2.2
      (cj g) (hmemG g hg)
    have h2 := (ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    have e : ∀ t : ℝ, cj (g * NormedSpace.exp ((t : ℂ) • X)) = cj g * NormedSpace.exp ((t : ℂ) • cj X) := by
      intro t
      have e2 : (t : ℂ) • cj X = P⁻¹ * ((t : ℂ) • X) * P := by
        simp only [cj, Matrix.mul_smul, Matrix.smul_mul]
      rw [e2, Matrix.exp_conj' P _ hPu]
      simp only [cj, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P P⁻¹, hPP, Matrix.one_mul]
    have e3 : (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) = (ℓ.restrictScalars ℝ) ∘
        (fun t : ℝ => rdWord (l.map cj) f (cj g * NormedSpace.exp ((t : ℂ) • cj X))) := by
      funext t; simp only [F, Function.comp_apply, e]; rfl
    rw [e3]; exact h2
  have key := hsob F hFc hFd
  have hF1 : ‖F [] 1‖ = ‖f 1‖ := by
    have : cj 1 = 1 := by simp [cj, hPP']
    simp only [F, List.map_nil, this]
    show ‖ℓ (f 1)‖ = ‖f 1‖
    rw [hℓ]; simp
  rw [hF1] at key
  have hstep : ∀ l ∈ S, ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε) ≤
      c * ENNReal.ofReal (∫ x in ψ '' Q, ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2 ∂μG) := by
    intro l hlS
    have hl := hS l hlS
    classical
    set φ : Mt k r → ℝ≥0∞ := (ψ '' Q).indicator
      (fun x => ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2)) with hφ
    have hφm : Measurable φ := by
      have := ContinuousOn.measurable_piecewise (f := fun x : Mt k r =>
        ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2)) (g := 0)
        (ENNReal.continuous_ofReal.comp_continuousOn (hI l hl)) continuousOn_const hK₀.isClosed.measurableSet
      rwa [Set.piecewise_eq_indicator] at this
    have hint : IntegrableOn (fun x : Mt k r => ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2) (ψ '' Q) μG :=
      (hI l hl).integrableOn_compact hK₀
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => by positivity),
      ← lintegral_indicator hK₀.isClosed.measurableSet, ← hφ, ← hB φ hφm]
    refine le_trans ?_ (setLIntegral_le_lintegral Q _)
    refine setLIntegral_mono (hφm.comp hψc.measurable) fun y hy => ?_
    have hψy : ψ y ∈ ψ '' Q := ⟨y, hy, rfl⟩
    have hφy : φ (ψ y) = ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of (ψ y))‖ ^ 2) := by
      rw [hφ]; exact Set.indicator_of_mem hψy _
    show _ ≤ φ (ψ y)
    rw [hφy]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    have : (Matrix.of (ψ y) : Mat k r) = cj (umat y) := by
      change Matrix.of (Matrix.of.symm (cj (umat y))) = _
      exact Equiv.apply_symm_apply _ _
    rw [this]
    refine (ℓ.le_opNorm _).trans ?_
    rw [hℓ1, one_mul]
  have hsum := List.sum_le_sum hstep
  rw [List.sum_map_mul_left, ← ofReal_list_sum S _ (fun l => integral_nonneg fun _ => by positivity)] at hsum
  have htot : ENNReal.ofReal (‖f 1‖ ^ 2) ≤ ENNReal.ofReal C * (c * ENNReal.ofReal
      ((S.map fun l => ∫ x in ψ '' Q, ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2 ∂μG).sum)) := key.trans (by gcongr)
  conv_rhs at htot => rw [← ENNReal.ofReal_toReal hc]
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hC, ← mul_assoc] at htot
  rw [List.map_map] at hnn ⊢
  exact (ENNReal.ofReal_le_ofReal_iff hnn).1 htot

end GlobalTheory.SobAtOne

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.cmFieldFiniteAdeleTensorEquiv_mem_integralAdeles : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E), a ∈ ReciprocityTheory.Aut.ALint D.host.E → GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
  first | exact @GlobalTheory.FixedConj.adeleEquiv_mem_intAf | exact GlobalTheory.FixedConj.adeleEquiv_mem_intAf | (intros; apply GlobalTheory.FixedConj.adeleEquiv_mem_intAf <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.concrete_gram_hermitian_nondegenerate_lattice_selfDual : ∀ (D : D7) (X : HidaSetting D), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND D.sp.cm.sig (Jc X) ∧ GlobalTheory.SgGlob.SelfDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) := by
  first | exact @GlobalTheory.CovDom.herm_selfDual | exact GlobalTheory.CovDom.herm_selfDual | (intros; apply GlobalTheory.CovDom.herm_selfDual <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bessel_transport_isometry_frame_adapted : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), GlobalTheory.SnMass.IsModelAt (Jc X) (Ac X C) ∧ GlobalTheory.SnMass.Adapted (Ac X C) (Pc X u) (fc X) (sc D) := by
  first | exact @GlobalTheory.CovDom.ModelIso.model_adapted | exact GlobalTheory.CovDom.ModelIso.model_adapted | (intros; apply GlobalTheory.CovDom.ModelIso.model_adapted <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wordFrame_dualTuple_gram_integrality : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.SgAlg.IsFrame (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (algebraMap D.host.F D.host.E (Tc u)) (Pc X u) ∧ GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) ∧ GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X := by
  first | exact @GlobalTheory.CovDom.frame_dual_lat | exact GlobalTheory.CovDom.frame_dual_lat | (intros; apply GlobalTheory.CovDom.frame_dual_lat <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fundamental_domain_normalising_constants : ∀ (D : D7), (∀ a, 0 < sc D a) ∧ |(NumberField.discr D.host.F : ℝ)| ^ (-(((D.R.k : ℝ) + 1) * (D.R.rS : ℝ) ^ 2) - 4 * ((D.R.rS : ℝ) ^ 3 - D.R.rS) / 3 - 3 * (D.R.rS : ℝ) / 2) * (∏ a : Fin D.R.rS, sc D a ^ (4 * (D.R.rS - (a : ℕ)) + 2 * D.R.k)) ^ Fintype.card (InfinitePlace D.host.E) = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  first | exact @GlobalTheory.CovDom.normalising_constants | exact GlobalTheory.CovDom.normalising_constants | (intros; apply GlobalTheory.CovDom.normalising_constants <;> assumption)
end

section


theorem _root_.GlobalTheory.T.stabilizerTube_gaugeMass_asymptotic : PI.RhsWLim.W.TubeLimK := by
  first | exact @GlobalTheory.StabTube.tubeLimK | exact GlobalTheory.StabTube.tubeLimK | (intros; apply GlobalTheory.StabTube.tubeLimK <;> assumption)
end
