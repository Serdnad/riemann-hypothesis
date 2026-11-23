module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle406
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle261
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle367
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle209
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle413
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle330
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle399
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle380
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle400
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle349
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemColumnLevelIffMemLinkedFrameLevel
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle411
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle401
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle412
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.SplitPlaceDistinct

theorem not_mem_both {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (h2 : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : ((a : 𝓞 E)) * ((p : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((q : ℕ) : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
  rw [← e]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h1) (w.asIdeal.mul_mem_left _ h2)

theorem splitPlace_v_ne : ∀ (D : D7) (s s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (kv kv' : Σ k : Fin 2, D.nd.PlG k),
    s.w = D.naut.plGw kv.1 kv.2 → s'.w = D.naut.plGw kv'.1 kv'.2 → kv ≠ kv' → s.v ≠ s'.v := by
  intro D s s' kv kv' hs hs' hne hv
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  have hgk : ∀ a b : Fin 2, a ≠ b → D.host.g a ≠ D.host.g b := by
    intro a b hab
    have h01 := D.host.g_ne
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact h01
    · exact h01.symm
    · exact absurd rfl hab
  have hover := D.naut.plGw_over
  rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s s'.w
      (s'.w_under.trans (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hv.symm)) with e | e
  · rw [hs, hs'] at e
    by_cases hk : k = k'
    · subst hk
      exact hne (congrArg (Sigma.mk k) (D.naut.plGw_inj k e))
    · exact not_mem_both (D.host.g_prime k) (D.host.g_prime k') (hgk k k' hk) _ (hover k v)
        (e ▸ hover k' v')
  · rw [hs, hs'] at e
    by_cases hk : k = k'
    · subst hk
      exact D.naut.plGw_nconj k v' v e
    · have hm : ((D.host.g k' : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal :=
        (e _ _ (by simp)).1 (hover k' v')
      exact not_mem_both (D.host.g_prime k) (D.host.g_prime k') (hgk k k' hk) _ (hover k v) hm

end GlobalTheory.SplitPlaceDistinct
end

section

noncomputable section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covN_haarLie_smul {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (κ : ℝ≥0∞) :
    haarLie S κ = κ • haarLie S 1 := by
  unfold haarLie; rw [one_smul]

theorem covN_muNB_one (D : D7) : muNB D 1 =
    (kapN D 1 * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • GlobalTheory.Amp.lebN D.R.k D.R.rS := by
  rw [muNB, covN_haarLie_smul, GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue, smul_smul]

theorem covN_pi_smul {ι : Type} [Fintype ι] {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (c : ℝ≥0) : Measure.pi (fun _ : ι => (c : ℝ≥0∞) • μ) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  haveI : SigmaFinite ((c : ℝ≥0∞) • μ) := by
    first
    | (have h : ((c : ℝ≥0∞) • μ) = c • μ := (ENNReal.smul_def c μ).symm
       rw [h]; infer_instance)
    | (rw [← ENNReal.smul_def]; infer_instance)
  refine (Measure.pi_eq fun s hs => ?_)
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem covN_arith (v : ℝ) (hv : 1 ≤ v) (r k f : ℕ) :
    1 ≤ ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * v ^ (k * r * f) := by
  have hv0 : 0 < v := by linarith
  have h2v : 0 < 2 * v := by linarith
  have hA : (2 * v) ^ (-((r : ℝ) * k)) * v ^ (k * r) = ((2 : ℝ) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg h2v.le, show ((r : ℝ) * k) = ((r * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, mul_pow,
      show k * r = r * k from Nat.mul_comm k r]
    have : (0 : ℝ) < v ^ (r * k) := pow_pos hv0 _
    field_simp
  have hB : ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * v ^ (k * r * f) =
      (((2 : ℝ) ^ (r * k))⁻¹ * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f := by
    rw [← hA, pow_mul, ← mul_pow]
    ring
  rw [hB]
  apply one_le_pow₀
  rw [← div_eq_inv_mul, one_le_div (by positivity)]
  apply pow_le_pow_right₀ (by norm_num)
  nlinarith [Nat.zero_le (r * (r - 1))]

theorem covNC_holds : CovNC := by
  intro D large₂ X Y u C hS
  obtain ⟨hCM, hPl, hv, hv1, -, hcard, -, -, -, hnorm, hfin, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N, hF, hF', hj, hT, h𝔡, hTerm, hRef, hist⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hS (VS D).L0 (Or.inr rfl)
  obtain ⟨hU, -, hz, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive D.host.E (VS D).V (HV D) hCM D.R.rS N (gS D) (VS D).L0 (by omega) hTerm
  have hzL : N.F.z ∈ GlobalTheory.HermLat.latL N.F N.F' (VS D).L0 := by
    have h := (hz 1).2 (by simp)
    simpa using h
  have hFr := GlobalTheory.T.baseNormalForm_realFrames_at_realPlaces D large₂ X u C hS N hF hF' hj hT (hist rfl)
  have hN𝔡 : (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) ^ (2 * Fintype.card D.what₂.Tau) := by
    rw [h𝔡, hnorm, hv, hcard]
  have hv1' : 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E := by rw [hv]; exact hv1
  obtain ⟨Ω, hΩ, hlo, hhi⟩ := GlobalTheory.T.covolume_referenceLattice_stabiliser_bounds D.host.E (VS D).V (HV D) hCM D.R.rS N D.R.k D.what₂.Tau (embS D)
    (fun _ => 0) (fun τ => phiV C τ) (fun τ => zB X (C.Qi τ) u τ) (fun τ => zB X (C.Qi τ) u τ) (fun _ => 1)
    hPl hfin hFr hN𝔡 hv1' _ hU hzL
  rw [hRef, GlobalTheory.T.real_points_base_lattice_stabilizer_fixed_frame_unipotent D large₂ X Y u C hS N hF hF'] at hΩ
  have hsw := (GlobalTheory.T.lebesgueCommonStabilizer_eq_radical_levi_map D.R.k D.R.rS N.j (fun _ => 0) monotone_const (by intro a b _; simp [hj])).2.2.2 hj
  rw [hsw, hj, hv, hcard, Nat.sub_zero] at hlo hhi
  obtain ⟨hc, h1, hmul, hinv, hNs⟩ := GlobalTheory.T.realIntegralUnipotent_besselModels_countable_subgroup D X Y u C
  have heq := GlobalTheory.T.measure_eq_of_strictFundamentalSetsPlacewise D.what₂.Tau D.R.k D.R.rS _ _ _ hc h1 hmul hinv hNs hΩ (GlobalTheory.T.strictFundamentalSet_unipotent_on_besselModels D X Y u C)
  haveI : SigmaFinite (GlobalTheory.Amp.lebN D.R.k D.R.rS) := (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn D.R.k D.R.rS).1
  set c : ℝ≥0 := ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1).toNNReal *
    2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) with hc_def
  have hk : kapN D 1 * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) = (c : ℝ≥0∞) := by
    rw [hc_def, kapN, ENNReal.ofReal]
    push_cast
    rfl
  have hcov : covN C Y u = (c : ℝ≥0∞) ^ D.R.f * Measure.pi (fun _ : D.what₂.Tau => GlobalTheory.Amp.lebN D.R.k D.R.rS) Ω := by
    rw [covN, covN_muNB_one, hk, covN_pi_smul, Measure.smul_apply, smul_eq_mul, hcard, ← heq]
  have hfinΩ : Measure.pi (fun _ : D.what₂.Tau => GlobalTheory.Amp.lebN D.R.k D.R.rS) Ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  have hne : covN C Y u ≠ ⊤ := by
    rw [hcov]; exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hfinΩ
  refine ⟨hne, ?_⟩
  have hlo' := (ENNReal.ofReal_le_iff_le_toReal hfinΩ).1 hlo
  have hlpos : 0 < lossV D := by
    unfold lossV; exact pow_pos (by linarith) _
  have hcr : ((c : ℝ≥0∞) ^ D.R.f).toReal = ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f := by
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, hc_def, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    push_cast; ring
  rw [hcov, ENNReal.toReal_mul, hcr]
  have key := covN_arith D.host.v hv1 D.R.rS D.R.k D.R.f
  have hpos : 0 ≤ ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f := by positivity
  have hq : D.host.v ^ (D.R.k * D.R.rS * D.R.f) / (8 * D.host.v) ^ (2 * (D.R.rS + 1) ^ 2 * D.R.f) * lossV D =
      D.host.v ^ (D.R.k * D.R.rS * D.R.f) := by
    unfold lossV; field_simp
  calc (1 : ℝ) ≤ ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f * D.host.v ^ (D.R.k * D.R.rS * D.R.f) := key
    _ = ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f *
        (D.host.v ^ (D.R.k * D.R.rS * D.R.f) / (8 * D.host.v) ^ (2 * (D.R.rS + 1) ^ 2 * D.R.f) * lossV D) := by rw [hq]
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hlpos.le
      exact mul_le_mul_of_nonneg_left hlo' hpos

end GlobalTheory.TypeAsm
end
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameLink

theorem frame_exists : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∃ Fr : FrQ D wt, FrLink X u wt ιA Fr := by
  intro D X u wt ιA hW hI
  obtain ⟨c, p, hc, hrng, hid, hLf, hkill, hkz, hcl⟩ := GlobalTheory.T.exists_coprime_projection_adelic_lattice_into_columns D X u wt ιA hW hI
  have hmhat := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  have hY : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ X.B.I.Lf ∧ X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ X.B.I.Lf := fun i =>
    ⟨(X.xu_K u (X.bw i)).1 (X.vectorsInLattice.2.2 i).1, (X.xu_K u (X.bwd i)).1 (X.vectorsInLattice.2.2 i).2⟩
  have hb0 : ∀ i, ∃ x, embA X wt ιA x = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) := fun i => by
    obtain ⟨x, hx⟩ := hrng ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ X.bw i))
    exact ⟨x, by rw [← hx, map_smul]⟩
  have hbd0 : ∀ i, ∃ x, embA X wt ιA x = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) := fun i => by
    obtain ⟨x, hx⟩ := hrng ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))
    exact ⟨x, by rw [← hx, map_smul]⟩
  choose b hb using hb0
  choose bd hbd using hbd0
  have hclose := GlobalTheory.T.projection_moves_typeVectors_modLevel D X u wt ιA hW hI c p hcl
  have hbe := GlobalTheory.T.transported_type_vectors_fixed_by_chosen_places_idempotent D X u wt ιA hW hI c p b bd hb hbd
  refine ⟨{ eps := ιA X.ew
            eps_idem := by rw [← map_mul, X.ew_idem]
            eps_orth := by rw [← GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hI, ← map_mul, X.ew_orth, map_zero]
            eps_int := (hI.2 _).1 X.ew_int
            eps_full := GlobalTheory.T.adelic_columns_lattice_divisible_by_level_away_chosen D X u wt ιA hW hI
            b := b
            bd := bd
            b_mem := fun i => (hmhat.1 (b i)).2 (by rw [hb i]; exact hLf _ (hY i).1)
            bd_mem := fun i => (hmhat.1 (bd i)).2 (by rw [hbd i]; exact hLf _ (hY i).2)
            b_eps := hbe.1
            bd_eps := hbe.2
            dual := GlobalTheory.T.transported_type_vectors_dual_mod_level D X u wt ιA hW hI c p b bd hb hbd hclose
            span := GlobalTheory.T.transportedTypeVectors_span_adelicLattice_modLevel D X u wt ιA hW hI c p hc hid hLf hkill hkz b bd hb hbd
            psi := fun a => X.psiEf (ιA.symm a)
            psi_add := fun x y => by
              show X.psiEf (ιA.symm (x + y)) = X.psiEf (ιA.symm x) * X.psiEf (ιA.symm y)
              rw [RingEquiv.map_add (e := _), X.psiEf_add]
            psi_int := fun x hx => X.psiEf_int _ ((hI.2 _).2 (by simpa using hx))
            psi_rat := GlobalTheory.T.transportedFiniteCharacter_inverse_exp_trace D X ιA hI }, rfl, fun i => ?_, fun i => ?_, fun a => rfl⟩
  · show embA X wt ιA (b i) - _ ∈ _
    rw [hb i]; exact (hclose i).1
  · show embA X wt ιA (bd i) - _ ∈ _
    rw [hbd i]; exact (hclose i).2

end GlobalTheory.St.G.FrameLink
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_columnLevel_iff_mem_linkedFrameLevel : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (hK : X.LevelSubgroupCharacter) (Fr : FrQ D wt), FrLink X u wt ιA Fr → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → (h ∈ Ku X u hK ↔ Fr.InK y.1) := by
  first | exact @GlobalTheory.St.G.ColLevel.level_link | exact GlobalTheory.St.G.ColLevel.level_link | (intros; apply GlobalTheory.St.G.ColLevel.level_link <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOrbit

theorem mem_ngSet_iff {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u') :
    t ∈ (Y.tO u u').ngSet ↔ t.G ≠ 0 ∧ ¬ t.generic := by
  show (if t.G = 0 then (0:ℝ) else 1) ≠ 0 ∧ ¬ t.generic ↔ _
  by_cases h : t.G = 0 <;> simp [h]

theorem mem_genSet_iff {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u') :
    t ∈ (Y.tO u u').genSet ↔ t.G ≠ 0 ∧ t.generic := by
  show (if t.G = 0 then (0:ℝ) else 1) ≠ 0 ∧ t.generic ↔ _
  by_cases h : t.G = 0 <;> simp [h]

theorem finrank_Vp_eq (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Ranks.r, Ranks.rS]
  omega

theorem img_inv_img {D : D7} (Z : LocDat D) (p : PlF D) (h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
    (A : Submodule (Z.M p).L.O (Vp D p)) : LocNG.img h⁻¹ (LocNG.img h A) = A := by
  ext x
  simp only [LocNG.img, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨h x, ⟨x, hx, rfl⟩, by simp⟩

theorem noBB_of_moved {D : D7} (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D)
    (hRel : (FP p).RelG (LocNG.theta (Z.M p))) (h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hh : h ∈ (FP p).UW0)
    (A B : Submodule (Z.M p).L.O (Vp D p)) (hAB : LocNG.img h A = B)
    (hB : ∀ d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = B → ¬ LocNG.BBne (H := locH Z p) τ) :
    ∀ d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = A → ¬ LocNG.BBne (H := locH Z p) τ := by
  intro d τ hτ hL hbb
  obtain ⟨act, hmv, -⟩ := GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_eq D p) hRel
  have hm : LocNG.Datum.Moves h d (act.smul ⟨h, hh⟩ d) := (hmv ⟨h, hh⟩ d _).2 rfl
  obtain ⟨h1, h2⟩ := GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_eq D p) hRel h hh d _ τ hτ hm
  exact hB _ _ h1 (by show LocNG.img h τ.abelian₂ = B; rw [hL, hAB]) (h2.2 hbb)

theorem closed_ng_gen : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → LocClosed F F' Z FP (Y.tO u u').ngSet ∧ LocClosed F F' Z FP (Y.tO u u').genSet ∧ (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ ∀ t ∈ (Y.tO u u').genSet, t.G ≠ 0 := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel
  have gen := fun t Λ hT => GlobalTheory.T.isGenericTerm_iff_no_localDefect_baseFrames D X Y u u' F F' w hw hG Z FP hB hRel t Λ hT
  have pt := fun t Λ hT => (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hw hG t Λ hT).1
  have back : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D), TG F F' t Λ → TG F F' t' Λ' →
      (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ') → t'.generic → t.generic := by
    intro t t' Λ Λ' hT hT' hloc hg
    rw [gen t Λ hT]
    rw [gen t' Λ' hT'] at hg
    intro p
    obtain ⟨h, hh, hAB⟩ := hloc p
    exact noBB_of_moved Z FP p (hRel p) h hh _ _ hAB (hg p)
  have fwd : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D), TG F F' t Λ → TG F F' t' Λ' →
      (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ') → t.generic → t'.generic := by
    intro t t' Λ Λ' hT hT' hloc hg
    rw [gen t' Λ' hT']
    rw [gen t Λ hT] at hg
    intro p
    obtain ⟨h, hh, hAB⟩ := hloc p
    exact noBB_of_moved Z FP p (hRel p) h⁻¹ (inv_mem hh) _ _ (by rw [← hAB, img_inv_img]) (hg p)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t t' Λ Λ' hT hT' hloc ht
    rw [mem_ngSet_iff] at ht ⊢
    exact ⟨pt t' Λ' hT', fun hg => ht.2 (back t t' Λ Λ' hT hT' hloc hg)⟩
  · intro t t' Λ Λ' hT hT' hloc ht
    rw [mem_genSet_iff] at ht ⊢
    exact ⟨pt t' Λ' hT', fwd t t' Λ Λ' hT hT' hloc ht.2⟩
  · intro t ht
    exact ((mem_ngSet_iff Y u u' t).1 ht).1
  · intro t ht
    exact ((mem_genSet_iff Y u u' t).1 ht).1

end GlobalTheory.LocOrbit
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.matching_translate_same_row_double_coset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', ∀ s : TauC Y u u', s.lam = t₀.lam → s.lam' = t₀.lam' → (∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u')), s.lin = n * (a * t₀.lin * a'⁻¹) * n') → key s = key t := by
  first | exact @GlobalTheory.Unfold.TgKey.translate_key | exact GlobalTheory.Unfold.TgKey.translate_key | (intros; apply GlobalTheory.Unfold.TgKey.translate_key <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowLattice_of_locally_standard_frame : ∀ (D : D7) (Tn : ℕ), Tn ≠ 0 → ∀ (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ g, Adapt g (lf D F0) G ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  first | exact @GlobalTheory.RowLatAdapt.row_lattice_of_local_standard | exact GlobalTheory.RowLatAdapt.row_lattice_of_local_standard | (intros; apply GlobalTheory.RowLatAdapt.row_lattice_of_local_standard <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lintegral_hilbertSchmidtNormSq_besselAmplitude_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (v₀ : H) (a d c₀ : ℝ) (μG μS μS' νS νS' ν : Measure (Mt k r)) (z z' : (Fin (2 * r + k + 1) → ℂ)) (c c' : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (B : H → Wp) (B' : H → Wq), v₀ ≠ 0 → StdSm σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀) a μG d → SideIrr z π μS → SideIrr z' π' μS' → IsQuotMeas μG μS νS → IsQuotMeas μG μS' νS' → MultOne z (psiGen k r z c) σ π → MultOne z' (psiGen k r z' c') σ π' → IsBesselMapSm z (psiGen k r z c) σ π B → IsBesselMapSm z' (psiGen k r z' c') σ π' B' → 0 < c₀ → l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wp) → l2SG νS' (fun g => B' (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wq) → (∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → (∀ v ∈ smoothVecs σ, l2SG νS' (fun g => B' (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS' (fun g => B' (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → IsDis (Greg k r z z') μG μS μS' ν → ∫⁻ γ, ENNReal.ofReal (hsNormSq (ampJ μG c₀ (fun g => B (σ g v₀)) (fun g => B' (σ g v₀)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal ((Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq / d) := by
  first | exact @GlobalTheory.Amp.SchurNorm.lintegral_hsNormSq_ampJ_le | exact GlobalTheory.Amp.SchurNorm.lintegral_hsNormSq_ampJ_le | (intros; apply GlobalTheory.Amp.SchurNorm.lintegral_hsNormSq_ampJ_le <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

theorem _root_.GlobalTheory.T.analyticConstantGenericBound_of_normalisedSteps : StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → StepAnalyticCGP := by
  first | exact @GlobalTheory.SnPos.stepAnalyticCGP_of_steps | exact GlobalTheory.SnPos.stepAnalyticCGP_of_steps | (intros; apply GlobalTheory.SnPos.stepAnalyticCGP_of_steps <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

theorem _root_.GlobalTheory.T.analyticGenericBound_of_choiceStep_positive : TieOfCtx → StepChoiceConstantsC → StepAnalyticCGP → StepAnalyticGP := by
  first | exact @GlobalTheory.SnPos.stepAnalyticGP_of | exact GlobalTheory.SnPos.stepAnalyticGP_of | (intros; apply GlobalTheory.SnPos.stepAnalyticGP_of <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

theorem _root_.GlobalTheory.T.equalWordGenericBound_of_cutBound_positive : PN.NGChain → MeanAmpGen → GenCutP → GlobalTheory.SnPos.RowMainEqP := by
  first | exact @GlobalTheory.SnPos.rowMainEqP_of_cut | exact GlobalTheory.SnPos.rowMainEqP_of_cut | (intros; apply GlobalTheory.SnPos.rowMainEqP_of_cut <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

theorem _root_.GlobalTheory.T.generic_height_bound_of_local_estimates : StepSizes → StepClassG → StepNormalsG → StepPointsG → StepHeightG → StepAnalyticGP → GenCutP := by
  first | exact @GlobalTheory.SnPos.genCutP_of_steps | exact GlobalTheory.SnPos.genCutP_of_steps | (intros; apply GlobalTheory.SnPos.genCutP_of_steps <;> assumption)
end
