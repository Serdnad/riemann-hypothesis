module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle057
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle045
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
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

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

namespace GlobalTheory.ConjKill


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isLinearMap_cfOf {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (K₁ : Type) [Field K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) :
    IsLinearMap T.Q.c.F fun F : (recB h).Cusp j ka => cfOf d.yF d.μ d.jj F.1 := by
  obtain ⟨φ, hφ⟩ := (GlobalTheory.T.arcDatum_coefficientFunctional_linear_degree GlobalTheory.T.arithmeticCMKnownTheorems_proof _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n).1
  have hle : ∀ F : (recB h).Cusp j ka, F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n := fun F =>
    cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j ka F.2)
  have e : ∀ F : (recB h).Cusp j ka, cfOf d.yF d.μ d.jj F.1 = φ ⟨F.1, hle F⟩ := fun F => (hφ ⟨F.1, hle F⟩).symm
  refine ⟨fun F G => ?_, fun a F => ?_⟩
  · rw [e, e, e, ← map_add (f := _)]; rfl
  · rw [e, e, ← map_smul]; rfl




theorem mggOnto_of_rdOnto : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), (j < D.R.m → DetectQ h.toLawsCore j ka CR Tt cc) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  intro D T h j hj ka CR Tt cc hD hR
  by_cases hlt : j < D.R.m
  · refine GlobalTheory.T.forms_vanishing_low_coeff_spanned_by_rational D T h j ka CR Tt cc
      (fun K₁ _ _ _ φ => ∃ d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁, FamQ T.toCore j ka CR Tt cc K₁ d ∧
        φ = fun F => cfOf d.yF d.μ d.jj F.1) ?_ ?_ hR
    · rintro K₁ _ _ _ φ ⟨d, hd, rfl⟩
      exact ⟨isLinearMap_cfOf h.toLawsCore j ka K₁ d, GlobalTheory.T.arcDatum_functional_kills_complexCombinations D T h j hj ka CR Tt cc K₁ d hd⟩
    · intro F hF
      exact hD hlt F fun K₁ _ _ _ d hd => hF K₁ _ ⟨d, hd, rfl⟩
  · have hρ : WeightFamilies.rho D j = 0 := by
      unfold WeightFamilies.rho Ranks.sigW
      exact Nat.sub_eq_zero_of_le (not_lt.1 hlt)
    intro f hf
    obtain ⟨m, a, F, -, hF⟩ := hR f fun k => (hf k).1
    refine ⟨m, a, F, fun i => ?_, hF⟩
    rw [SetLike.mem_coe, Formalism.MainNotions.Gaps.EtaleWeightGaps.MggK_eq_top_of_rho hρ]
    trivial

end GlobalTheory.ConjKill
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.recursive_page_lattice_bound : ∃ Cq : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → LatAt (recB h.toLawsCore) j ka → QAt large₂ (recB h.toLawsCore) j ka 7 H.CK 1 4 (Cq H.CA H.CK) 4 Tn (cc D large₂ C2 A2 7 wL) := by
  first | exact @GlobalTheory.RunJoin.qAt_run | exact GlobalTheory.RunJoin.qAt_run | (intros; apply GlobalTheory.RunJoin.qAt_run <;> assumption)
end

end

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

theorem _root_.GlobalTheory.T.vanishing_low_coefficient_readings_span_models : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), (j < D.R.m → DetectQ h.toLawsCore j ka CR Tt cc) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  first | exact @GlobalTheory.ConjKill.mggOnto_of_rdOnto | exact GlobalTheory.ConjKill.mggOnto_of_rdOnto | (intros; apply GlobalTheory.ConjKill.mggOnto_of_rdOnto <;> assumption)

end
end
