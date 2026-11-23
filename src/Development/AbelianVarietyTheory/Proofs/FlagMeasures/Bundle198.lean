module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionExponents
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle160
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureLeCardMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
public import Formalism.HarderNarasimhan.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientLatticeRealizedIsometrically
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle003
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle176
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle162
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.TauLipschitz

theorem trunc_pos (I : AutInst) (hn : 1 ≤ I.n) (x : I.GA) : 0 < tau1 I x :=
  lt_min (by norm_num) ((GlobalTheory.CountSteps.steps I x 1 one_pos).2.2.2.2.2.2.2.2 hn).1

theorem log_trunc_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 ∈ I.Kset) :
    Real.log (tau1 I x) - dSum I g.1 / I.f ≤ Real.log (tau1 I (x * g)) := by
  have h := GlobalTheory.LeastVar.truncatedLeastLatticeSize_rightTranslate_lower_bound I hn x g hg
  have hx := trunc_pos I hn x
  have h2 := Real.log_le_log (mul_pos hx (Real.exp_pos _)) h
  rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  unfold dSum
  linarith

theorem dSum_inv (I : AutInst) (hn : 1 ≤ I.n) (g : I.GA) : dSum I (g⁻¹).1 = dSum I g.1 := by
  unfold dSum
  refine Finset.sum_congr rfl fun v _ => ?_
  exact ((GlobalTheory.Count.Cartan.cartan_distances I.n (I.ε v)).2.1 (g.1 v) (g.1 v) hn).2.1

theorem tauLip : TauLip := by
  intro I hn
  refine ⟨trunc_pos I hn, (GlobalTheory.LeastVar.least_variation_continuity I hn).2.2, ?_, ?_⟩
  · rintro a ⟨γ, h1, h2, h3⟩ x
    unfold tau1
    rw [(GlobalTheory.PointEquivariance.equivariance I x γ a h1 h2 h3).2.2.1]
  · intro x g hg
    obtain ⟨-, -, -, -, -, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
    have hg' : (g⁻¹).2 ∈ I.Kset := by
      rw [← hK] at hg ⊢
      exact K.inv_mem hg
    have h1 := log_trunc_le I hn x g hg
    have h2 := log_trunc_le I hn (x * g) g⁻¹ hg'
    rw [mul_inv_cancel_right, dSum_inv I hn] at h2
    rw [abs_le]
    constructor <;> linarith

end GlobalTheory.TauLipschitz
end
end

section

open MeasureTheory NumberField Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.DeepArith

theorem one_le_f (I : AutInst) : 1 ≤ I.f := Module.finrank_pos

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  refine Real.one_le_rpow ?_ (by positivity)
  have h := Int.one_le_abs (discr_ne_zero I.E)
  exact_mod_cast h

theorem deep_mul_volume_le (hV : GlobalTheory.FlagMeas.AbsoluteVolume) (B : RowsAut) (Cg : ℝ) (n₀ : ℕ)
    (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA)
    (hn₀ : 8 ≤ n₀) (hq : 1 ≤ q) (hC : CountHyp B Cg n₀ d p q b) (hc : ∀ v, IsGauge (B.I.ε v) (c v))
    (hx : least B.I x < tauStar B q b) :
    B.I.muA B.μf B.fund < ⊤ ∧
    (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b
        (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) *
      (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^
        GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f *
      (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (∏ v, c v) /
      (B.μf (B.I.Kg B.g)).toReal * (B.I.muA B.μf B.fund).toReal ≤
      Real.exp (-((B.I.n : ℝ) ^ 2 * B.I.f)) := by
  obtain ⟨-, hsig, hn', hq2, -, -, hb, -, -, hg, -⟩ := hC
  have hn : 8 ≤ B.I.n := hn₀.trans hn'
  have hc0 : ∀ v, 0 < c v := fun v => by
    obtain ⟨c', h0, -, hu⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge B.I.n (B.I.ε v)
    rw [hu _ (hc v)]; exact h0
  have hf := one_le_f B.I
  have hrd := one_le_rd B.I
  have hnR : (8 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf
  have hgR : (1 : ℝ) ≤ B.g := by exact_mod_cast hg
  have hfr : B.I.rd ≤ B.I.f * B.I.rd := by nlinarith
  have hX : 2 * (B.I.f * B.I.rd) ≤ bigX B b := by
    have h1 : (2 : ℝ) ≤ B.g * b := by nlinarith
    have h2 : (2 : ℝ) ≤ B.I.n * (B.g * b) := by nlinarith
    have : bigX B b = (B.I.n * (B.g * b)) * (B.I.f * B.I.rd) := by unfold bigX; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h2 (by linarith)
  have hX2 : 2 ≤ bigX B b := by linarith
  have hvol := hV B.I p q hsig hq2 hn (bigX B b) hX2 (by linarith) (by nlinarith) c B.μf hc
  obtain ⟨hcov, -⟩ := GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter B.I B.μf B.fund Set.univ B.fund_spec MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _)
  obtain ⟨hidx, hKg0, hKfin⟩ := GlobalTheory.CongIndex.measure_Kset_le B.I B.μf B.g hg
  have hKgfin : B.μf (B.I.Kg B.g) ≠ ⊤ :=
    ne_top_of_le_ne_top hKfin.ne (measure_mono fun _ h => h.1)
  unfold GlobalTheory.FlagMeas.gaugeVol at hvol
  rw [hcov, Set.univ_inter, ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl hKfin.ne)] at hvol
  set N : ℕ := B.I.n ^ 2 * B.I.f with hN
  set m : ℝ := (B.μf (B.I.Kg B.g)).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hKg0.ne' hKgfin
  have hcp : 0 < ∏ v, c v := Finset.prod_pos fun v _ => hc0 v
  have hXp : 0 < bigX B b := by linarith
  have hgp : (0 : ℝ) < B.g := by linarith
  set Y : ℝ := (B.g : ℝ) ^ (2 * N) * bigX B b ^ N with hY
  have hY0 : 0 < Y := by positivity
  have hv2 : ENNReal.ofReal (∏ v, c v) * B.I.muA B.μf B.fund ≤ ENNReal.ofReal (Y * m) := by
    refine (hvol.trans (mul_le_mul' le_rfl hidx)).trans_eq ?_
    rw [show Y * m = bigX B b ^ N * ((B.g : ℝ) ^ (2 * N) * m) by rw [hY]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      hm, ENNReal.ofReal_toReal hKgfin, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hfin : B.I.muA B.μf B.fund < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hcp).ne'] at hv2
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hv2)
  refine ⟨hfin, ?_⟩
  have hv3 : (∏ v, c v) * (B.I.muA B.μf B.fund).toReal ≤ Y * m := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcp.le, ENNReal.toReal_ofReal (by positivity)] at this
  have hl : 0 < least B.I x := ((GlobalTheory.CountSteps.steps B.I x 1 one_pos).2.2.2.2.2.2.2.2 (by omega)).1
  have ha := (GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn hf hq hq2 hrd hb hgR hl
    hx.le).2
  have hbe : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * N + N) =
      Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe
    have : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) = B.I.n * Real.sqrt B.I.n := by
      rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [this]; norm_num
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B = N := rfl
  rw [hd, hbe, show 16 * q * N = 2 * (8 * q * N) by ring]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh
  rw [← hN] at ha
  generalize (2 * ((B.I.n : ℝ) ^ 2 * Real.sqrt B.I.f * B.g * B.I.rd * (2 * least B.I x) ^ ((1 : ℝ) / q) / 4) *
    Real.sqrt B.I.f * (Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) +
      3 * ((8 * q * N + N : ℕ) : ℝ))) ^ (2 * (8 * q * N)) = u at ha ⊢
  generalize (6 * (Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) +
      3 * ((8 * q * N + N : ℕ) : ℝ))) ^ N = v at ha ⊢
  generalize (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * N) = w at ha ⊢
  have h1 : u * v * Real.exp B.I.f * w ≤ Real.exp (-(N : ℝ)) / Y := by
    rw [le_div_iff₀ hY0]
    refine le_of_eq_of_le ?_ ha
    rw [hY]; unfold bigX; ring
  have hNc : (N : ℝ) = (B.I.n : ℝ) ^ 2 * (B.I.f : ℝ) := by rw [hN]; push_cast; ring
  calc u * v * Real.exp B.I.f * w * (∏ v, c v) / m * (B.I.muA B.μf B.fund).toReal
      ≤ Real.exp (-(N : ℝ)) / Y * (∏ v, c v) / m * (B.I.muA B.μf B.fund).toReal := by gcongr
    _ = Real.exp (-(N : ℝ)) / Y / m * ((∏ v, c v) * (B.I.muA B.μf B.fund).toReal) := by ring
    _ ≤ Real.exp (-(N : ℝ)) / Y / m * (Y * m) := by gcongr
    _ = Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) := by
        rw [hNc]; field_simp

end GlobalTheory.DeepArith
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FlagPush

open GlobalTheory.FlagMeas

theorem simplex_meas (a : ℕ) : MeasurableSet (simplexH a) := by
  have h : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, {τ : Fin a → ℝ | i < k → τ i < τ k}) ∩
      ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ | τ i < 1 / 2}) := by
    ext τ
    simp only [simplexH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun i k hik => h1 hik, fun i => h2 i⟩,
      fun ⟨h1, h2⟩ => ⟨fun i k hik => h1 i k hik, fun i => h2 i⟩⟩
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_)
    (MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const))
  by_cases hik : i < k
  · simpa [hik] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k)
  · simp [hik]

theorem dens_meas (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) : Measurable (FlagMeas.dens n f j) := by
  show Measurable fun τ => FlagMeas.dens n f j τ
  simp only [FlagMeas.dens, layerProd, id]
  fun_prop

theorem mem_simplex {I : AutInst} {x : I.GA} {a : ℕ} {j : Fin a → ℕ} {τ : Fin a → ℝ}
    (h : HasType I x j τ) : τ ∈ simplexH a := by
  obtain ⟨S, ⟨-, -, -, hmono, hτ, -⟩, -⟩ := h
  exact ⟨hmono, fun i => ⟨(hτ i).1, (hτ i).2.1⟩⟩

theorem lintegral_type_le : GlobalTheory.FlagMeas.FlagMeasureBound → ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → 2 * q + 2 ≤ B.I.n → ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∀ (G : (Fin a → ℝ) → ENNReal) (Φ : B.I.GA → ENNReal), Measurable G → (∀ x τ, HasType B.I x j τ → Φ x ≤ G τ) → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) * ∫⁻ τ in GlobalTheory.FlagMeas.simplexH a, G τ * ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
  intro hFMB B p q hSig hn a j ha hj hsum G Φ hG hΦ
  have := B.haar
  have := B.sf
  obtain ⟨s, hs, hT, hsτ⟩ := GlobalTheory.FlagMeas.type_measurable B.I a j
  set T : Set B.I.GA := {x | ∃ τ, HasType B.I x j τ} with hTdef
  set μ := B.I.muA B.μf with hμ
  set K : ENNReal := μ B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) with hK
  set ρ : Measure (Fin a → ℝ) := (volume.restrict (GlobalTheory.FlagMeas.simplexH a)).withDensity
    (fun τ => ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) with hρ
  have hd : Measurable (fun τ => ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) :=
    (dens_meas B.I.n B.I.f j).ennreal_ofReal

  have h1 : ∫⁻ x in T ∩ B.fund, Φ x ∂μ ≤ ∫⁻ x in T ∩ B.fund, G (s x) ∂μ := by
    rw [← Measure.restrict_restrict hT]
    refine lintegral_mono_ae ?_
    refine (ae_restrict_iff' hT).2 (Filter.Eventually.of_forall ?_)
    rintro x ⟨τ, hx⟩
    rw [hsτ x τ hx]
    exact hΦ x τ hx

  have h2 : Measure.map s (μ.restrict (T ∩ B.fund)) ≤ K • ρ := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.map_apply hs hA, Measure.restrict_apply (hs hA), Measure.smul_apply, smul_eq_mul,
      hρ, withDensity_apply _ hA, Measure.restrict_restrict hA]
    have hsub : s ⁻¹' A ∩ (T ∩ B.fund) ⊆
        GlobalTheory.FlagMeas.typeSet B.I j (A ∩ GlobalTheory.FlagMeas.simplexH a) ∩ B.fund := by
      rintro x ⟨hxA, ⟨τ, hx⟩, hxf⟩
      refine ⟨⟨τ, ⟨?_, mem_simplex hx⟩, hx⟩, hxf⟩
      have hxs : s x = τ := hsτ x τ hx
      rw [← hxs]
      exact hxA
    obtain ⟨-, h0, htop, hle⟩ := hFMB B.I B.μf B.fund B.fund_spec p q hSig hn a j ha hj hsum
      (A ∩ GlobalTheory.FlagMeas.simplexH a) (hA.inter (simplex_meas a)) Set.inter_subset_right
    calc μ (s ⁻¹' A ∩ (T ∩ B.fund))
        ≤ μ (GlobalTheory.FlagMeas.typeSet B.I j (A ∩ GlobalTheory.FlagMeas.simplexH a) ∩ B.fund) := measure_mono hsub
      _ ≤ ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            (∫⁻ τ in A ∩ GlobalTheory.FlagMeas.simplexH a, ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) *
            μ B.fund := (ENNReal.div_le_iff h0.ne' htop.ne).1 hle
      _ = K * ∫⁻ τ in A ∩ GlobalTheory.FlagMeas.simplexH a, ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
          rw [hK]; ring
  calc ∫⁻ x in T ∩ B.fund, Φ x ∂μ ≤ ∫⁻ x in T ∩ B.fund, G (s x) ∂μ := h1
    _ = ∫⁻ τ, G τ ∂(Measure.map s (μ.restrict (T ∩ B.fund))) := (lintegral_map hG hs).symm
    _ ≤ ∫⁻ τ, G τ ∂(K • ρ) := lintegral_mono' h2 le_rfl
    _ = K * ∫⁻ τ in GlobalTheory.FlagMeas.simplexH a, G τ * ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
        rw [lintegral_smul_measure, hρ, lintegral_withDensity_eq_lintegral_mul _ hd hG, smul_eq_mul]
        congr 1
        exact lintegral_congr fun τ => mul_comm _ _

end GlobalTheory.FlagPush
end

section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

theorem _root_.GlobalTheory.T.quotient_lattice_realized_isometrically : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → ∃ (m : ℕ) (q : Matrix (Fin m) (Fin n) K) (X' : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (Q : InfinitePlace K → Matrix (Fin m) (Fin n) ℂ), m + rkK S = rkK A ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, Q w * (Q w)ᴴ = 1) ∧ (∀ w, ∀ y ∈ A, fcoord (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) = Q w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ (∀ w z, (Q w)ᴴ *ᵥ z ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K)))) ∧ (∀ w, ∀ u ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K))), u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))) ∧ (∀ y ∈ S, q *ᵥ y = 0) ∧ Submodule.span K (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K)) = ⊤ ∧ ∀ N', N' ≤ A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) → N' ≠ ⊥ → ∃ N, S < N ∧ N ≤ A ∧ sizeQ (Pi.basisFun K (Fin n)) X N S = size (Pi.basisFun K (Fin m)) X' N' := by
  intro K _ _ _ _ n X A S hX hA hSat
  have hSA : S ≤ A := hSat.1
  have hUU : Submodule.span K (S : Set (Fin n → K)) ≤ Submodule.span K (A : Set (Fin n → K)) :=
    Submodule.span_mono hSA
  obtain ⟨m, q, hm, hker, hsurj⟩ := GlobalTheory.QuotCoord.exists_quot_matrix _ _ hUU
  have hS : ∀ y ∈ S, q *ᵥ y = 0 := fun y hy =>
    (hker y (Submodule.subset_span (hSA hy))).2 (Submodule.subset_span hy)
  have htop : Submodule.span K
      (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K)) = ⊤ := by
    rw [← hsurj, Submodule.map_coe]
    exact Submodule.span_image (Matrix.toLin' q)
  have hQ := fun w => GlobalTheory.QuotCoord.exists_coisometry (m := m)
    (QuotientRealization.pv (Pi.basisFun K (Fin n)) X (Submodule.span K (S : Set (Fin n → K))) w)
    (QuotientRealization.pv (Pi.basisFun K (Fin n)) X (Submodule.span K (A : Set (Fin n → K))) w)
    (Submodule.span_mono (Set.image_mono hUU))
    (by rw [QuotientRealization.finrank_pv _ _ hX, QuotientRealization.finrank_pv _ _ hX]; exact hm)
  choose Q hQ1 hQ2 hQ3 hQ4 using hQ
  have hQ3' : ∀ w, ∀ u ∈ Submodule.span ℂ
      (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K))), u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈
      Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) :=
    fun w u hu => QuotientRealization.pv_le _ X S w _ (hQ3 w _ (GlobalTheory.QuotCoord.toLp_mem_pv X A w u hu))
  have hY := fun w => GlobalTheory.QuotCoord.exists_frame X w (hX w) q A S hS htop (Q w) (hQ3' w)
  choose X' hX' hc using hY
  refine ⟨m, q, X', Q, hm, hX', hQ1, hc, fun w z => QuotientRealization.pv_le _ X A w _ (hQ2 w z), hQ3', hS, htop, ?_⟩
  intro N' hN' hne
  have hmap : (A ⊓ N'.comap ((Matrix.toLin' q).restrictScalars (𝓞 K))).map
      ((Matrix.toLin' q).restrictScalars (𝓞 K)) = N' := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := hN' hz
      exact ⟨y, ⟨hy, hz⟩, rfl⟩
  have hSN : S ≤ A ⊓ N'.comap ((Matrix.toLin' q).restrictScalars (𝓞 K)) := by
    intro y hy
    refine ⟨hSA hy, ?_⟩
    show q *ᵥ y ∈ N'
    rw [hS y hy]
    exact N'.zero_mem
  refine ⟨_, lt_of_le_of_ne hSN ?_, inf_le_left, ?_⟩
  · intro h
    apply hne
    rw [← hmap, ← h, eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact hS y hy
  have sizeQ_eq_size (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ w, IsUnit (X w).det)
      (X' : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (hX' : ∀ w, IsUnit (X' w).det)
      (q : Matrix (Fin m) (Fin n) K) (A S N : Submodule (𝓞 K) (Fin n → K)) (hA : A.FG)
      (hSat : IsSat (realize (Pi.basisFun K (Fin n)) X) A S) (hSN : S ≤ N) (hNA : N ≤ A)
      (hker : ∀ y ∈ Submodule.span K (A : Set (Fin n → K)),
        q *ᵥ y = 0 ↔ y ∈ Submodule.span K (S : Set (Fin n → K)))
      (hnorm : ∀ w, ∀ y ∈ A, normAt (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) =
        ‖(QuotientRealization.pv (Pi.basisFun K (Fin n)) X (Submodule.span K (S : Set (Fin n → K))) w)ᗮ.starProjection
          (WithLp.toLp 2 (fcoord (Pi.basisFun K (Fin n)) X w y))‖) :
      sizeQ (Pi.basisFun K (Fin n)) X N S = size (Pi.basisFun K (Fin m)) X'
        (N.map ((Matrix.toLin' q).restrictScalars (𝓞 K))) := by
    classical
    set U := Submodule.span K (S : Set (Fin n → K)) with hU
    set b := Pi.basisFun K (Fin n)
    set b'' := Pi.basisFun K (Fin m)
    have hNfg : N.FG := Submodule.FG.of_le hA hNA
    set N'' := N.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) with hN''
    have hUle : U ≤ Submodule.span K (N : Set (Fin n → K)) := Submodule.span_mono hSN
    have hrk : rkK N'' + rkK S = rkK N := by
      have hspan : Submodule.span K (N'' : Set (Fin m → K)) =
          (Submodule.span K (N : Set (Fin n → K))).map (Matrix.toLin' q) := by
        rw [hN'', Submodule.map_coe]
        exact Submodule.span_image (Matrix.toLin' q)
      let W := Submodule.span K (N : Set (Fin n → K))
      let fW : W →ₗ[K] (Fin m → K) := Matrix.toLin' q ∘ₗ W.subtype
      have h1 := LinearMap.finrank_range_add_finrank_ker fW
      have hr : LinearMap.range fW = W.map (Matrix.toLin' q) := by
        rw [LinearMap.range_comp, Submodule.range_subtype]
      have hk : LinearMap.ker fW = U.comap W.subtype := by
        ext y
        exact hker y (Submodule.span_mono hNA y.2)
      rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hUle).finrank_eq] at h1
      unfold rkK
      rw [hspan]
      exact h1
    have hrkR : ((rkK N : ℝ) - rkK S) = rkK N'' := by
      rw [← hrk]; push_cast; ring
    let ρ := realize b X
    let ρ'' := realize b'' X'
    have hNlat := plLat K _ _ b X hX N hNfg
    have hN''lat := plLat K _ _ b'' X' hX' N'' (hNfg.map _)
    have : DiscreteTopology (zl ρ N) := hNlat.1.2
    have hsatN : Formalism.F.IsSaturated (zl ρ N) (zl ρ S) :=
      ⟨QuotientRealization.zl_mono ρ hSN, fun x hx hxs => hSat.2.2 x (QuotientRealization.zl_mono ρ hNA hx) hxs⟩
    have : DiscreteTopology (Formalism.F.quot (zl ρ N) (zl ρ S)) :=
      (Formalism.F.degQuot _ _ _ inferInstance hsatN).1
    have : DiscreteTopology (zl ρ'' N'') := hN''lat.1.2
    let W := Submodule.span ℝ (zl ρ S : Set (EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2)))
    let f : N →+ EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2) :=
      (Wᗮ.starProjection.toLinearMap.toAddMonoidHom).comp (ρ.comp N.subtype.toAddMonoidHom)
    let g : N →+ EuclideanSpace ℝ (InfinitePlace K × Fin m × Fin 2) :=
      ρ''.comp (((Matrix.toLin' q).toAddMonoidHom).comp N.subtype.toAddMonoidHom)
    have h1 : ∀ y, y ∈ Formalism.F.quot (zl ρ N) (zl ρ S) ↔ ∃ m : N, f m = y := by
      intro y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨⟨x, hx⟩, rfl⟩
        exact ⟨ρ x, ⟨x, hx, rfl⟩, rfl⟩
    have h2 : ∀ y, y ∈ zl ρ'' N'' ↔ ∃ m : N, g m = y := by
      intro y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨⟨x, hx⟩, rfl⟩
        exact ⟨Matrix.toLin' q x, ⟨x, hx, rfl⟩, rfl⟩
    have hn : ∀ m, ‖f m‖ = ‖g m‖ := by
      rintro ⟨x, hx⟩
      have hsq : ‖f ⟨x, hx⟩‖ ^ 2 = ‖g ⟨x, hx⟩‖ ^ 2 := by
        show ‖Wᗮ.starProjection (ρ x)‖ ^ 2 = ‖ρ'' (q *ᵥ x)‖ ^ 2
        rw [QuotientRealization.proj_norm_sq b X S x, PlaceOperatorNorms.norm_sq_realize]
        simp only [hnorm _ x (hNA hx)]
        rfl
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
    have hcov := QuotientRealization.covol_eq_of_norm_eq f g _ _ h1 h2 hn
    have hht : htQ b X N S = ht b'' X' N'' := by
      unfold htQ ht
      rw [hcov, hrkR, ← Nat.cast_mul, Real.rpow_natCast]
    unfold sizeQ size
    rw [hht, hrkR]
  · rw [sizeQ_eq_size X hX X' hX' q A S _ hA hSat hSN inf_le_left hker ?_, hmap]
    intro w y hy
    rw [hQ4 w _ (GlobalTheory.QuotCoord.toLp_mem_pv X A w _ (Submodule.subset_span ⟨y, hy, rfl⟩)), normAt]
    exact congrArg cnorm (hc w y hy)

end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

namespace GlobalTheory.MatMulDet

theorem det_real_mul_mul (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ)
    (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] (ι → Fin j → Fin j → ℂ))
    (hL : ∀ h w, Matrix.of (L h w) = A w * Matrix.of (h w) * B w) :
    LinearMap.det L = ∏ w, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | exact @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family
  | (apply _root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DeterminantRealSandwich.det_real_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DeterminantRealSandwich.det_real_family ..)

end GlobalTheory.MatMulDet
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.complex_coordinates_measure_preserving : ∀ (ι : Type) [Fintype ι] (n : ℕ), ∃ T : (ι → Fin n → ℂ) ≃ₜ+ (ι × Fin n × Bool → ℝ), MeasurePreserving T volume volume ∧ ∀ y v i, T y (v, i, true) = (y v i).re ∧ T y (v, i, false) = (y v i).im := by
  first | exact @GlobalTheory.ReImVolume.exists_reIm_measurePreserving | exact GlobalTheory.ReImVolume.exists_reIm_measurePreserving | (intros; apply GlobalTheory.ReImVolume.exists_reIm_measurePreserving <;> assumption)
end
