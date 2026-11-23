module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle123
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle110
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle019
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle040
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle155
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle129
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Deep

theorem farModerate_e_one_nonneg (B : RowsAut) : 0 ≤ (B.e 1).re := by
  obtain ⟨-, -, -, hpos, -⟩ := B.e_adm
  have h := hpos 1 (fun _ => 1) (fun _ => 1)
  simp at h
  simpa using (Complex.le_def.1 h).1

private theorem epN_pos_and_le_inv_sqrt_and_mul_le_log_two (n f q : ℕ) (hn : 8 ≤ n) (hf : 1 ≤ f) (hq : 1 ≤ q)
    (hqn : q ^ 2 ≤ n) :
    0 < 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ∧
      1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 / Real.sqrt (2 * (q : ℝ)) ∧
      2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) ≤ Real.log 2 := by
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : (q : ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hqn
    exact_mod_cast this
  have hD : 0 < (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by positivity
  have hn8 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hf2 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := one_le_pow₀ hf'
  have hnD : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by nlinarith
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩
  · have hs : Real.sqrt (2 * (q : ℝ)) ≤ 2 * q :=
      calc Real.sqrt (2 * (q : ℝ)) ≤ Real.sqrt ((2 * (q : ℝ)) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 * q := Real.sqrt_sq (by linarith)
    have hspos : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by linarith)
    calc 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 / (2 * q) := by
          rw [div_le_div_iff₀ hD (by linarith)]
          nlinarith
      _ ≤ 1 / Real.sqrt (2 * (q : ℝ)) := one_div_le_one_div_of_le hspos hs
  · have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h1 : (n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 := (div_le_one hD).2 hnD
    have h2 : 2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) =
        2 / 10 ^ 6 * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) := by ring
    rw [h2]
    linarith

theorem farModerate_of_farBound :
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.FarBound → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate := by
  intro hFM hFB Cg hCg
  refine ⟨8, fun B d p q b hq hCH => ?_⟩
  obtain ⟨-, hrd, hf1, -, -, h2q, -, hmin, hdpos, -, htpos, htq, h, hh, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl hCH
  obtain ⟨hDS, hSig, hn0, hqn, -, hlf, hb2, -, -, hg1, hgb, -, -, -, -⟩ := hCH
  have htq' : tauStar B q b < 1 / 2 := (htq hq).1
  have he1 : 0 ≤ (B.e 1).re := farModerate_e_one_nonneg B
  have hK : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hdpos.le he1
  obtain ⟨hep0, hepq, heplog⟩ := epN_pos_and_le_inv_sqrt_and_mul_le_log_two B.I.n B.I.f q hn0 hf1 hq hqn
  obtain ⟨hA, hB, hC⟩ := GlobalTheory.gap_threshold_pays_far_terms Cg B.I.n B.I.f q B.I.rd (B.g : ℝ) b h
    (tauStar B q b) hCg (by omega) hf1 hq hqn hrd hlf hb2 (Nat.one_le_cast.2 hg1) hgb hh.ge le_rfl htq'.le
  obtain ⟨-, -, hfin, -⟩ := hFM B.I B.μf B.fund B.fund_spec p q hSig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  have hpt : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ≤
      ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) := by
    intro x hx
    obtain ⟨hs, hsum⟩ := hFB B d p q h (epN B) hDS hSig hmin.symm hq hgap hep0 hepq heplog hA hB h120 x
    have hx1 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x = ENNReal.ofReal
        (∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
      simp only [ofReal_norm]
      rfl
    have hlat : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x ≤
        (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) := by
      have ht1 : tauStar B q b ≤ tau1 B.I x := le_min htq'.le hx.2
      unfold GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos htpos 2)
        (pow_le_pow_left₀ htpos.le ht1 2)
    have hC0 : 0 ≤ 2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16)) := by positivity
    rw [hx1]
    apply ENNReal.ofReal_le_ofReal
    calc ∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖
        ≤ (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))) := hsum
      _ ≤ (∏ v, d v) * (B.e 1).re *
            (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlat hK) hC0
      _ = (∏ v, d v) * (B.e 1).re *
            ((3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16)))) := by ring
      _ ≤ (∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) :=
          mul_le_mul_of_nonneg_left hC hK
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ∂(B.I.muA B.μf)
      ≤ ∫⁻ _ in GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b,
          ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))))
          ∂(B.I.muA B.μf) := setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) *
          B.I.muA B.μf (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) *
          B.I.muA B.μf B.fund := mul_le_mul_of_nonneg_left (measure_mono fun x hx => hx.1) (by simp)
    _ = ENNReal.ofReal (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d) := by
      rw [← ENNReal.ofReal_toReal hfin.ne,
        ← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_pos _).le)]
      congr 1
      show _ = Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) *
        ((∏ v, d v) * ((B.I.muA B.μf) B.fund).toReal * (B.e 1).re)
      ring

end GlobalTheory.Deep
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.NearElement

theorem conj_pow_of_mul_eq_one {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]
    (X Y G : Matrix n n A) (h : X * Y = 1) (m : ℕ) : (Y * G * X) ^ m = Y * G ^ m * X := by
  induction m with
  | zero => simp [mul_eq_one_comm.1 h]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    calc Y * G ^ m * X * (Y * G * X) = Y * G ^ m * (X * Y) * G * X := by simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc, mul_one, one_mul]

theorem trace_conj_pow {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]
    (X Y G : Matrix n n A) (h : X * Y = 1) (m : ℕ) : ((Y * G * X) ^ m).trace = (G ^ m).trace := by
  rw [conj_pow_of_mul_eq_one X Y G h, Matrix.trace_mul_cycle, h, one_mul]

theorem trace_pow_cong (E : Type) [Field E] [NumberField E] (n g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E))
    (G : Matrix (Fin n) (Fin n) E) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hrad : (Ideal.span {(g : 𝓞 E)}).IsRadical) (hg : 1 ≤ g) (hG : ∀ y ∈ Λ, G *ᵥ y ∈ Λ)
    (hU : ∀ y ∈ Λ, ∃ z ∈ Λ, ((G - 1) ^ n) *ᵥ y = (g : E) • z) (j : ℕ) :
    ∃ t : 𝓞 E, (G ^ j).trace - n = (g : E) * (t : E) := by
  have hpow : ∀ (M : Matrix (Fin n) (Fin n) E), (∀ y ∈ Λ, M *ᵥ y ∈ Λ) → ∀ m : ℕ, ∀ y ∈ Λ, (M ^ m) *ᵥ y ∈ Λ := by
    intro M hM m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih => intro y hy; rw [pow_succ, ← mulVec_mulVec]; exact ih _ (hM y hy)
  set S := ∑ i ∈ Finset.range j, G ^ i with hS
  have hSΛ : ∀ y ∈ Λ, S *ᵥ y ∈ Λ := by
    intro y hy
    rw [hS, Matrix.sum_mulVec]
    exact Λ.sum_mem fun i _ => hpow G hG i y hy
  have e : G ^ j - 1 = (G - 1) * S := (mul_geom_sum G j).symm
  have hc : Commute (G - 1) S := by
    show (G - 1) * S = S * (G - 1)
    rw [hS, mul_geom_sum, geom_sum_mul]
  obtain ⟨t, ht⟩ := GlobalTheory.trace_mem_of_nilpotent_mod_radical E n n g Λ (G ^ j - 1) hfg hsp hrad hg
    (fun y hy => by rw [sub_mulVec, one_mulVec]; exact Λ.sub_mem (hpow G hG j y hy) hy)
    (fun y hy => by rw [e, hc.mul_pow, ← mulVec_mulVec]; exact hU _ (hpow S hSΛ n y hy))
  exact ⟨t, by rw [← ht]; simp⟩

theorem embedding_eq_or_conj (I : AutInst) (ι : I.E →+* ℂ) :
    ∃ v, ι = I.φ v ∨ ι = ComplexEmbedding.conjugate (I.φ v) := by
  refine ⟨(InfinitePlace.mk ι).comap (algebraMap I.F I.E), ?_⟩
  rcases GlobalTheory.Count.Test.embedding_cases I (InfinitePlace.mk ι) with h | h <;>
    rcases InfinitePlace.embedding_mk_eq ι with h' | h'
  · exact Or.inl (h'.symm.trans h)
  · right
    rw [← h, h']; simp
  · exact Or.inr (h'.symm.trans h)
  · left
    exact star_injective (h'.symm.trans h)

theorem radius_bounds (c : ℝ) (hc : 0 < c) (hc' : c ≤ 1 / 10 ^ 5) (n f : ℝ) (hn : 1 ≤ n) (hf : 1 ≤ f) :
    n * (c / (n ^ 8 * f ^ 2)) ≤ 1 / 4 ∧ 3 * Real.sqrt (n * (c / (n ^ 8 * f ^ 2))) < 1 / 4 ∧
      ∀ q : ℝ, 0 ≤ q → q ^ 2 ≤ n → 3 * Real.sqrt (n * (c / (n ^ 8 * f ^ 2))) * q * n * f ≤ 1 / 100 := by
  have key : n * (c / (n ^ 8 * f ^ 2)) * (n ^ 3 * f ^ 2) ≤ c := by
    have e : n * (c / (n ^ 8 * f ^ 2)) * (n ^ 3 * f ^ 2) = c / n ^ 4 := by field_simp
    rw [e]
    exact div_le_self hc.le (one_le_pow₀ hn)
  have h0 : 0 ≤ n * (c / (n ^ 8 * f ^ 2)) := by positivity
  generalize n * (c / (n ^ 8 * f ^ 2)) = a at key h0
  have h1 : 1 ≤ n ^ 3 * f ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn) (one_le_pow₀ hf)
  have ha : a ≤ c := le_trans (le_mul_of_one_le_right h0 h1) key
  refine ⟨by linarith, ?_, fun q hq hqn => ?_⟩
  · have : Real.sqrt a < 1 / 12 := by
      rw [Real.sqrt_lt' (by norm_num)]; linarith
    linarith
  · refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 ?_
    have e : (3 * Real.sqrt a * q * n * f) ^ 2 = 9 * (a * (q ^ 2 * n ^ 2 * f ^ 2)) := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt h0]; ring
    have h2 : a * (q ^ 2 * n ^ 2 * f ^ 2) ≤ a * (n ^ 3 * f ^ 2) := by
      rw [pow_succ' n 2]; gcongr
    rw [e]; linarith

theorem near_unipotent : NearUnip := by
  intro B d c hc hc' hn hg hrad ep δ hep hδ
  have hf : 1 ≤ B.I.f := Module.finrank_pos
  obtain ⟨r1, r2, r3⟩ := radius_bounds c hc hc' B.I.n B.I.f (by exact_mod_cast hn) (by exact_mod_cast hf)
  rw [← hep] at r1 r2 r3
  rw [← hδ] at r2 r3
  refine ⟨?_, r2, fun q hq => r3 q (Nat.cast_nonneg q) (by exact_mod_cast hq)⟩
  rintro x a ⟨ha, hne, hd⟩
  have hep0 : 0 ≤ ep := by rw [hep]; positivity
  have he : B.e (x⁻¹ * a * x).2 ≠ 0 := right_ne_zero_of_mul hne
  have hK := B.e_adm.2.2.2.2.1 _ he
  have hU := B.e_adm.2.2.2.2.2.2 _ he
  obtain ⟨γ, -, hinf, hfin⟩ := id ha
  have hg1 : 1 ≤ B.g₀ := by omega
  obtain ⟨hG, hGU⟩ := GlobalTheory.PointLattice.lamX_unipMod B.I x a γ B.g₀ hg1 hfin hK hU
  obtain ⟨-, hfg, hsp, -⟩ := GlobalTheory.PointLattice.lamX_selfDual B.I x
  generalize (γ : Matrix (Fin B.I.n) (Fin B.I.n) B.I.E) = G at hinf hfin hG hGU
  have hP : ∀ v, B.I.P v * (B.I.P v)⁻¹ = 1 := fun v =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (B.I.P_unit v))
  have htr : ∀ v j, (uMat ((x⁻¹ * a * x).1 v) ^ j).trace = B.I.φ v (G ^ j).trace := by
    intro v j
    have e : uMat ((x⁻¹ * a * x).1 v) = uMat (x.1 v)⁻¹ * uMat (a.1 v) * uMat (x.1 v) := rfl
    rw [e, trace_conj_pow _ _ _ (Units.mul_inv _), hinf, trace_conj_pow _ _ _ (hP v), AddMonoidHom.map_trace]
    congr 1
    exact (map_pow (B.I.φ v).mapMatrix G j).symm
  have harch : ∀ v, (∀ j : ℕ, j ≤ B.I.n → ‖(uMat ((x⁻¹ * a * x).1 v) ^ j).trace - B.I.n‖ ≤ 3 * B.I.n) ∧
      ((uMat ((x⁻¹ * a * x).1 v)).trace = B.I.n →
        Real.sqrt (hs (uMat ((x⁻¹ * a * x).1 v) - 1)) ≤ 3 * Real.sqrt (B.I.n * ep)) := by
    intro v
    obtain ⟨k, X, hk, hX, e⟩ := (polar B.I.n (B.I.ε v)).1 (uMat ((x⁻¹ * a * x).1 v)) ((x⁻¹ * a * x).1 v).2
    have h1 := hd v
    rw [e, (GlobalTheory.Count.Cartan.cartan_distances _ _).1 k X hk hX] at h1
    rw [e]
    exact GlobalTheory.NearUnitaryExp.near_arch _ k X ep hk.1 ((pChar _ _ X).1.1 hX).1 hep0 h1 r1
  have htn : ∀ j, j ≤ B.I.n → (G ^ j).trace = B.I.n := by
    intro j hj
    obtain ⟨t, ht⟩ := trace_pow_cong B.I.E B.I.n B.g₀ _ G hfg hsp hrad hg1 hG hGU j
    have e : (((B.g₀ : 𝓞 B.I.E) * t : 𝓞 B.I.E) : B.I.E) = (G ^ j).trace - B.I.n := by rw [ht]; simp
    have h0 := GlobalTheory.ringOfIntegers_eq_zero_of_natCast_dvd_of_norm_embedding_le B.I.E B.g₀ (3 * B.I.n)
      ((B.g₀ : 𝓞 B.I.E) * t) (dvd_mul_right _ _) (fun ι => ?_) ?_
    · rw [h0] at e
      exact sub_eq_zero.1 (by simpa using e.symm)
    · obtain ⟨v, hv⟩ := embedding_eq_or_conj B.I ι
      have h2 := (harch v).1 j hj
      rw [htr, ← map_natCast (B.I.φ v), ← map_sub, ← e] at h2
      rcases hv with rfl | rfl
      · exact h2
      · rwa [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
    · have : 3 * B.I.n < B.g₀ := by omega
      exact_mod_cast this
  have hnil := (GlobalTheory.unipotent_of_trace_pow_eq_size B.I.E B.I.n G fun j _ hj => htn j hj).2
  have hmap : ∀ {A : Type} [CommRing A] (ι : B.I.E →+* A), (G.map ι - 1) ^ B.I.n = 0 := by
    intro A _ ι
    have := congrArg ι.mapMatrix hnil
    rw [map_pow, map_sub, map_one, map_zero] at this
    exact this
  refine ⟨by rw [hfin]; exact hmap _, fun v => ?_, ha, hK, fun v => ?_⟩
  · have e : uMat (a.1 v) - 1 = (B.I.P v)⁻¹ * (G.map (B.I.φ v) - 1) * B.I.P v := by
      rw [hinf, mul_sub, sub_mul, mul_one, mul_eq_one_comm.1 (hP v)]
    rw [e, conj_pow_of_mul_eq_one _ _ _ (hP v), hmap, mul_zero, zero_mul]
  · rw [hδ]
    apply (harch v).2
    have := htr v 1
    rw [htn 1 hn, pow_one, map_natCast] at this
    exact this

end GlobalTheory.NearElement
end
end

section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.SubReal

theorem cnorm_sq_eq {ι : Type} [Fintype ι] (u : ι → ℂ) :
    ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  rw [Complex.ofReal_sum, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem cnorm_mulVec_isometry {m k : Type} [Fintype m] [Fintype k] [DecidableEq k]
    (P : Matrix m k ℂ) (h : Pᴴ * P = 1) (u : k → ℂ) :
    cnorm (P *ᵥ u) = cnorm u := by
  have hsum : (∑ i, ‖(P *ᵥ u) i‖ ^ 2 : ℝ) = ∑ i, ‖u i‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [cnorm_sq_eq, cnorm_sq_eq, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      h, Matrix.vecMul_one]
  unfold cnorm
  rw [hsum]

theorem exists_isometry_factor {n j : ℕ} (Y : Matrix (Fin n) (Fin j) ℂ)
    (L : Matrix (Fin j) (Fin n) ℂ) (hL : L * Y = 1) :
    ∃ (Z : Matrix (Fin j) (Fin j) ℂ) (P : Matrix (Fin n) (Fin j) ℂ),
      IsUnit Z.det ∧ Pᴴ * P = 1 ∧ Y = P * Z⁻¹ := by
  classical
  have hG0 : (0 : Matrix (Fin j) (Fin j) ℂ) ≤ Yᴴ * Y := (Matrix.posSemidef_conjTranspose_mul_self Y).nonneg
  obtain ⟨S, hSS, hSh⟩ : ∃ S : Matrix (Fin j) (Fin j) ℂ, S * S = Yᴴ * Y ∧ Sᴴ = S :=
    ⟨CFC.sqrt (Yᴴ * Y), CFC.sqrt_mul_sqrt_self _ hG0, (CFC.sqrt_nonneg (Yᴴ * Y)).isSelfAdjoint⟩
  have hker : ∀ x : Fin j → ℂ, (Yᴴ * Y) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hYx : Y *ᵥ x = 0 := (Matrix.conjTranspose_mul_self_mulVec_eq_zero Y x).mp hx
    have hback : L *ᵥ (Y *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
    rw [← hback, hYx, Matrix.mulVec_zero]
  have hGu : IsUnit (Yᴴ * Y).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hv (hker v hv0)
  have hSu : IsUnit S.det := by
    have h2 : IsUnit (S * S).det := by rw [hSS]; exact hGu
    rw [Matrix.det_mul] at h2
    exact isUnit_of_mul_isUnit_left h2
  refine ⟨S⁻¹, Y * S⁻¹, ?_, ?_, ?_⟩
  · rw [Matrix.det_nonsing_inv]
    exact hSu.ringInverse
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hSh, Matrix.mul_assoc,
      ← Matrix.mul_assoc Yᴴ, ← hSS, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hSu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hSu]
  · rw [Matrix.nonsing_inv_nonsing_inv _ hSu, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu,
      Matrix.mul_one]

theorem fcoord_std {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (x : Fin d → K) :
    fcoord (Pi.basisFun K (Fin d)) X v x = (X v)⁻¹ *ᵥ (fun i => v.embedding (x i)) := by
  unfold fcoord vecAt
  simp only [Pi.basisFun_repr]

end GlobalTheory.SubReal


open GlobalTheory.SubReal in
theorem GlobalTheory.exists_isometric_realisation_of_sublattice : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (R : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → R.FG → ∃ (j : ℕ) (i : Matrix (Fin n) (Fin j) K) (X' : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (P : InfinitePlace K → Matrix (Fin n) (Fin j) ℂ) (B : Submodule (𝓞 K) (Fin j → K)), j = rkK R ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, (P w)ᴴ * P w = 1) ∧ (∀ w, (X w)⁻¹ * i.map w.embedding = P w * (X' w)⁻¹) ∧ B.FG ∧ Submodule.span K (B : Set (Fin j → K)) = ⊤ ∧ (∀ y ∈ B, i *ᵥ y ∈ R) ∧ (∀ r ∈ R, ∃ y ∈ B, i *ᵥ y = r) ∧ largestSize (Pi.basisFun K (Fin j)) X' B = largestSize (Pi.basisFun K (Fin n)) X R := by
  intro K _ _ _ _ n X R hX hR
  classical
  let bS := Module.finBasis K (Submodule.span K (R : Set (Fin n → K)))
  let ψ : (Fin (Module.finrank K (Submodule.span K (R : Set (Fin n → K)))) → K) →ₗ[K] (Fin n → K) :=
    (Submodule.span K (R : Set (Fin n → K))).subtype ∘ₗ bS.equivFun.symm.toLinearMap
  have hinj : Function.Injective ψ :=
    (Submodule.injective_subtype _).comp bS.equivFun.symm.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ψ (LinearMap.ker_eq_bot.mpr hinj)
  have hgψ : ∀ y, g (ψ y) = y := fun y => LinearMap.congr_fun hg y
  have hψS : ∀ y, ψ y ∈ Submodule.span K (R : Set (Fin n → K)) := fun y => Submodule.coe_mem _
  have hψg : ∀ r ∈ Submodule.span K (R : Set (Fin n → K)), ψ (g r) = r := by
    intro r hr
    obtain ⟨y, rfl⟩ : ∃ y, ψ y = r := ⟨bS.equivFun ⟨r, hr⟩, by simp [ψ]⟩
    rw [hgψ]
  have hψR : ∀ r ∈ R, ψ (g r) = r := fun r hr => hψg r (Submodule.subset_span hr)
  have hi : ∀ y, LinearMap.toMatrix' ψ *ᵥ y = ψ y := fun y => LinearMap.toMatrix'_mulVec ψ y
  have hLi : LinearMap.toMatrix' g * LinearMap.toMatrix' ψ = 1 := by
    rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hLY : ∀ w : InfinitePlace K,
      ((LinearMap.toMatrix' g).map w.embedding * X w) *
        ((X w)⁻¹ * (LinearMap.toMatrix' ψ).map w.embedding) = 1 := by
    intro w
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (X w), Matrix.mul_nonsing_inv _ (hX w), Matrix.one_mul,
      ← Matrix.map_mul, hLi, Matrix.map_one _ (map_zero _) (map_one _)]
  choose Z P hZ hP hY using fun w => exists_isometry_factor _ _ (hLY w)
  have hmap : (R.map (g.restrictScalars (𝓞 K))).map (ψ.restrictScalars (𝓞 K)) = R := by
    ext r
    constructor
    · rintro ⟨y, ⟨r', hr', rfl⟩, rfl⟩
      simpa [hψR r' hr'] using hr'
    · intro hr
      exact ⟨g r, ⟨r, hr, rfl⟩, hψR r hr⟩
  have hnorm : ∀ (v : InfinitePlace K) (x : Fin (Module.finrank K (Submodule.span K (R : Set (Fin n → K)))) → K),
      normAt (Pi.basisFun K (Fin n)) X v (ψ x) = normAt (Pi.basisFun K _) Z v x := by
    intro v x
    unfold normAt
    rw [fcoord_std, fcoord_std]
    have hcomp : (fun k => v.embedding (ψ x k)) =
        (LinearMap.toMatrix' ψ).map v.embedding *ᵥ fun k => v.embedding (x k) := by
      funext k
      rw [← hi x, RingHom.map_mulVec]
      rfl
    rw [hcomp, Matrix.mulVec_mulVec, hY v, ← Matrix.mulVec_mulVec, cnorm_mulVec_isometry _ (hP v)]
  have hRR := (Formalism.HN.rerealize K _ _ (Fin n → K) (Fin n) (Pi.basisFun K _) Z (Pi.basisFun K (Fin n)) X ψ
    hZ hX hinj hnorm (R.map (g.restrictScalars (𝓞 K))) (hR.map _)).2.2.2.2.2.2
  refine ⟨Module.finrank K (Submodule.span K (R : Set (Fin n → K))), LinearMap.toMatrix' ψ, Z, P,
    R.map (g.restrictScalars (𝓞 K)), rfl, hZ, hP, hY, hR.map _, ?_, ?_, ?_, ?_⟩
  · rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, eq_top_iff]
    intro y _
    exact ⟨ψ y, hψS y, hgψ y⟩
  · rintro y ⟨r, hr, rfl⟩
    rw [hi]
    simpa [hψR r hr] using hr
  · intro r hr
    exact ⟨g r, ⟨r, hr, rfl⟩, by rw [hi]; exact hψR r hr⟩
  · rw [← hRR, hmap]
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive : ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)), H * H = 1 → (x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0) := by
  first | exact @GlobalTheory.TubeLie.mem_lieE_UH_of_sq | exact GlobalTheory.TubeLie.mem_lieE_UH_of_sq | (intros; apply GlobalTheory.TubeLie.mem_lieE_UH_of_sq <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.exists_smooth_compactSupport_fix_lowestKType : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ, SmoothOnG ε α ∧ HasCompactSupport (fun g : UJ ε => α (umat g)) ∧ ∀ s ∈ lowKSub ε lam σ, ∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ := by
  first | exact @GlobalTheory.exists_smooth_fix_lowKSub | exact GlobalTheory.exists_smooth_fix_lowKSub | (intros; apply GlobalTheory.exists_smooth_fix_lowKSub <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.self_dual_measure_real_diagonal : ∀ (κ : Type) [Fintype κ] (d : κ → ℝ), (∀ k, d k ≠ 0) → ∀ μ : Measure (κ → ℝ), SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) → μ = ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)) := by
  first | exact @GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag | exact GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag | (intros; apply GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag <;> assumption)
end
