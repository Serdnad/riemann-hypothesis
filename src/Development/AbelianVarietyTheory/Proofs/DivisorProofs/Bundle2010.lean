module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim

namespace GlobalTheory.ClassCount


end GlobalTheory.ClassCount

end
end

section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

theorem _root_.GlobalTheory.T.harishChandraInduction_cuspidalParabolicProduct : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → Monotone b → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x)) := by
  first | exact @GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep | exact GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep | (intros; apply GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SignedHC

namespace GlobalTheory.GridWtBound

theorem natW_dual_wtOf_le (n : ℕ) (E : Finset ℚ) (M : ℝ) (hM : 0 ≤ M) (hE : ∀ x ∈ E, |(x : ℝ)| ≤ M) (a : Fin n) :
    (((wtOf n E).dual.natW a : ℕ) : ℝ) ≤ 2 * M + 1 := by
  have hn : 0 < n := a.pos
  have hrev : Fin.rev (⟨n - 1, by omega⟩ : Fin n) = ⟨0, hn⟩ := by ext; simp; omega
  have key : (wtOf n E).dual.natW a = ((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat := by
    simp only [DomWeight.natW, DomWeight.detShift, DomWeight.dual, dif_pos hn, hrev]
    congr 1; ring
  have hd : (((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev : ℤ) : ℝ) ≤ 2 * M + 1 := by
    unfold wtOf
    split_ifs with h
    · have e0 := hE _ (descEnum_mem E h.1 ⟨0, hn⟩)
      have e1 := hE _ (descEnum_mem E h.1 a.rev)
      have f0 : ((⌊highestWeight E h.1 ⟨0, hn⟩⌋ : ℤ) : ℝ) ≤ ((highestWeight E h.1 ⟨0, hn⟩ : ℚ) : ℝ) := by
        exact_mod_cast Int.floor_le _
      have f1 : ((highestWeight E h.1 a.rev : ℚ) : ℝ) - 1 < ((⌊highestWeight E h.1 a.rev⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.sub_one_lt_floor _
      have hr : (0 : ℝ) ≤ ((a.rev : ℕ) : ℝ) := Nat.cast_nonneg _
      have g0 : ((highestWeight E h.1 ⟨0, hn⟩ : ℚ) : ℝ) ≤ M - ((n : ℝ) - 1) / 2 := by
        simp only [highestWeight]; push_cast; linarith [(abs_le.1 e0).2]
      have g1 : -M - ((n : ℝ) - 1) / 2 ≤ ((highestWeight E h.1 a.rev : ℚ) : ℝ) := by
        simp only [highestWeight]; push_cast; linarith [(abs_le.1 e1).1]
      push_cast
      linarith
    · simp; linarith
  rw [key]
  have c : (((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat : ℝ) =
      (((((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat : ℤ)) : ℝ) := (Int.cast_natCast _).symm
  rw [c, Int.toNat_eq_max]
  push_cast
  exact max_le (by push_cast at hd; exact hd) (by linarith)

end GlobalTheory.GridWtBound

namespace GlobalTheory.GridWtBound

theorem extend_bounds {n : ℕ} (d : ℕ) (f : Fin n → ℚ) (h : ℝ) (hh : 0 ≤ h)
    (hf : ∀ i, 0 ≤ ((f i : ℚ) : ℝ) ∧ ((f i : ℚ) : ℝ) ≤ h) (j : ℕ) :
    0 ≤ ((GridData.extend d f j : ℤ) : ℝ) ∧ ((GridData.extend d f j : ℤ) : ℝ) ≤ h := by
  unfold GridData.extend
  split_ifs with hj
  · obtain ⟨h1, h2⟩ := hf ⟨j - d, hj⟩
    have a1 : (0 : ℚ) ≤ f ⟨j - d, hj⟩ := by exact_mod_cast h1
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 a1, le_trans ?_ h2⟩
    exact_mod_cast Int.floor_le _
  · simp [hh]

variable {D : D7}

end GlobalTheory.GridWtBound

namespace GlobalTheory.GridWtBound

theorem one_le_b {D : D7} (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : (1 : ℝ) ≤ large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hsg : sLen D < gap D 1 := sLen_lt_gap D 1
  have hg1 : (1 : ℝ) ≤ (gap D 1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ gap D 1)
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  nlinarith

end GlobalTheory.GridWtBound
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GridFrameExistence

open GlobalTheory.SquareComm GlobalTheory.SquareDict GlobalTheory.SquareAgree GlobalTheory.Grid

variable {D : D7}

theorem fr_eq_of_onb {V : HSp D} {A A' : Fr V} (h : ∀ τ, A.onb τ = A'.onb τ) : A = A' := by
  have hf : A.fr = A'.fr := funext fun τ => by
    have h1 := congrArg (·⁻¹) (h τ)
    simp only [Fr.onb] at h1
    rwa [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)),
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A'.fr_unit τ))] at h1
  have he : A.ε = A'.ε := funext fun τ => by
    have h1 : (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ = (A.fr τ)ᴴ * Formalism.REAL.Jm (A'.ε τ) * A.fr τ := by
      rw [A.fr_gram, hf, A'.fr_gram]
    have u := A.fr_unit τ
    have u' : IsUnit (A.fr τ)ᴴ := (Matrix.isUnit_conjTranspose _).2 u
    have h2 := u'.mul_left_cancel (u.mul_right_cancel h1)
    funext a
    have h3 := congrFun (congrFun h2 a) a
    cases h4 : A.ε τ a <;> cases h5 : A'.ε τ a <;> simp [Formalism.REAL.Jm, h4, h5] at h3 ⊢ <;> norm_num at h3
  cases A
  cases A'
  simp only at hf he
  subst hf he
  rfl

theorem gridFr_unique {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {X : Node} {A A' : Fr (G.V X)}
    (h : IsGridFr W X A) (h' : IsGridFr W X A') : A = A' :=
  fr_eq_of_onb fun τ => (h τ).1.trans (h' τ).1.symm




open GlobalTheory.SquareConv in
theorem standing_of_size {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hx : 11 ≤ D.host.splitBound) {T : Type}
    {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) {sc : Consts} (G : GridData L sc) (t : T) : SquareStanding G t := by
  classical
  have hcc : D.host.ccK = ⊤ := hs.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hs
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hpp (P.level_split p hp)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hL.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

end GlobalTheory.GridFrameExistence

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.SizesOfRows

theorem sizes_of_sizeRows : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → (bigN D : ℝ) ≤ large₂.sc.b ∧ (D.R.f : ℝ) ≤ large₂.sc.b ∧ 1 ≤ bigN D ∧ 1 ≤ D.R.f ∧ 2 ≤ D.R.m ∧ 1 ≤ D.host.rdE ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b / 100 ∧ 12 ≤ large₂.sc.b := by
  intro D large₂ h
  obtain ⟨_, _, hm4, hm44, _, hb, _, _, _, hrd, hcond, _, _, _⟩ := h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have ht : D.R.k + D.R.m - 1 + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hf : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
  have hbig2 : bigN D ≤ 2 * D.R.N D.R.m := by
    simp only [bigN, sLen, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r]
    have h1 : D.R.k + D.R.m - 1 + 6 ≤ D.R.t + 1 := by omega
    have h2 : D.R.m * (D.R.k + D.R.m - 1 + 6) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_left _ h1
    have e : D.R.m * (D.R.t + (D.R.k + D.R.m - 1 + 6) + 1) = D.R.m * (D.R.t + 1) + D.R.m * (D.R.k + D.R.m - 1 + 6) := by ring
    omega
  have hmR : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hNR : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN1
  have hdR : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast hd
  have hbigR : (bigN D : ℝ) ≤ 2 * (D.R.N D.R.m : ℝ) := by exact_mod_cast hbig2
  have hN2 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
  have hP1 : (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have a : (D.R.N D.R.m : ℝ) ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      have : D.R.f * (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by nlinarith
      linarith
    have := mul_le_mul_of_nonneg_left a (by linarith : (0:ℝ) ≤ D.R.m)
    linarith
  have hP2 : (D.R.f : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (1:ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have hmN : 2 * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
  have hrd1 : 1 ≤ D.host.rdE := Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.one_le_rdE D
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := by
    show Real.log (Real.exp large₂.sc.L) = large₂.sc.L
    exact Real.log_exp _
  refine ⟨by linarith, by linarith, by simp only [bigN]; omega, hf, by omega, hrd1, ?_, ?_⟩
  · rw [hlogb]; linarith
  · have : (12 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
    linarith

end GlobalTheory.SizesOfRows
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.darbouxPhase_mul_box_eq_heisenbergTranslates : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j), Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e → ∀ (ψ : AddChar (AF D.host.F) ℂ) (F₁ : WO (negSp (spW G i j)) (spV G i j) → ℂ) (F₂ : WO (spV₁ G i j) (spW G i j) → ℂ) (v w : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)), ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e w).2 - (Γ.M.co.e w).1 ⬝ᵥ (Γ.M.co.e v).2)) * (F₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e (v + w))ᵀ) * F₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e (v + w))) = heisO ψ (negSp (spW G i j)) (spV G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e w)ᵀ) F₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e v)ᵀ) * heisO ψ (spV₁ G i j) (spW G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e w) F₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e v) := by
  first | exact @GlobalTheory.BoxPhase.phase_box_heis | exact GlobalTheory.BoxPhase.phase_box_heis | (intros; apply GlobalTheory.BoxPhase.phase_box_heis <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.RestComplement

theorem exists_rest_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (f : (κ → Fv F v) → ℂ), f ∈ GlobalTheory.WeilM.SB (κ → Fv F v) →
    ∃ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r ∧ ∃ x₀, r x₀ ≠ 0 := by
  intro F _ _ v κ _ φ hφ
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let φs : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ r := by
    refine ⟨hr, ?_⟩
    rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  refine ⟨r, hRest, 0, ?_⟩
  have e := congrFun (hrt (fun _ => 1)) 0
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at e
  rw [e]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  have hI : (fun i : κ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
    funext i
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : AF F).1 = 0
    exact map_zero _
  have hP : (∏ᶠ w, Function.update φs v (fun _ => 1) w fun i => evFin F w ((0 : κ → AF F) i)) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]
    · rw [Function.update_of_ne hw]
      simp only [φs, Pi.zero_apply, map_zero]
      rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
      rfl
  rw [hI, hP, mul_one]
  exact hf

end GlobalTheory.RestComplement
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.RestWitness

theorem exists_rest : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ R := by
  intro F _ _ κ _ v
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let φs : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  refine ⟨r, ?_, fun φ hφ => ⟨hr, ?_⟩⟩
  · have e := congrFun (hrt (fun _ => 1)) 0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at e
    rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have hI : (fun i : κ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
      funext i
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : AF F).1 = 0
      exact map_zero _
    have hP : (∏ᶠ w, Function.update φs v (fun _ => 1) w fun i => evFin F w ((0 : κ → AF F) i)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]
      · rw [Function.update_of_ne hw]
        simp only [φs, Pi.zero_apply, map_zero]
        rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
        rfl
    rw [hI, hP, mul_one]
    exact hf
  · rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w

end GlobalTheory.RestWitness
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (φ φ₁ φ₂ : (κ → Fv F v) → ℂ), φ ∈ GlobalTheory.WeilM.SB _ →
    (∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ₁ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ₂ r) →
    φ₁ = φ₂ := by
  first | exact @GlobalTheory.TensUniq.eq_of_tens_eq | exact GlobalTheory.TensUniq.eq_of_tens_eq | (intros; apply GlobalTheory.TensUniq.eq_of_tens_eq <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

theorem _root_.GlobalTheory.T.adelic_schwartz_finite_pure_tensors : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (Ψ : (κ → AF F) → ℂ), Ψ ∈ schA F κ →
    ∃ (T : Finset (Pl (F := F))) (m : ℕ) (f : Fin m → SInf F κ) (φ : Fin m → ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
      (∀ i v, φ i v ∈ SB (κ → Fv F v)) ∧
      (∀ i v, v ∉ T → φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) ∧
      Ψ = ∑ i, pure (f i) (φ i) := by
  first | exact @GlobalTheory.SchADecomp.exists_sum_pure | exact GlobalTheory.SchADecomp.exists_sum_pure | (intros; apply GlobalTheory.SchADecomp.exists_sum_pure <;> assumption)
end
