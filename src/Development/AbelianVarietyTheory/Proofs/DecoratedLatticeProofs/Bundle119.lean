module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle058
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsRange

variable {D : D7}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.n
    omega
  exact_mod_cast this

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem nuRow_zero_le_three_mul (large₂ : SizeData₂ D) (P : ParameterChoice' D large₂) (hb : ∀ t, (large₂.bT t : ℝ) ≤ 2 * large₂.sc.b')
    (hT : ThickUp large₂) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    DV.nuRow D u (i + 1) τ 0 ≤ 3 * large₂.sc.a := by
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk0 : 0 < D.R.k := by omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hkN : (D.R.k : ℝ) ≤ D.R.N i := by
    have : D.R.k ≤ D.R.N i := by unfold Ranks.N; omega
    exact_mod_cast this
  have hx := large₂.sc.one_lt_alt
  have hb1 := one_le_b large₂
  have hb' := b'_pos large₂
  have hba : large₂.sc.b ≤ large₂.sc.a := le_mul_of_one_le_left (by linarith) hx.le
  have hX : 2 ≤ large₂.sc.X' := by
    have h1 : 1 ≤ large₂.sc.x ^ (large₂.sc.eps / 3) := Real.one_le_rpow hx.le (by linarith [large₂.sc.eps_pos])
    have h2 := Real.add_one_le_exp (large₂.sc.x ^ (large₂.sc.eps / 3))
    unfold Scale.X'
    linarith
  have hb'a : large₂.sc.b' ≤ large₂.sc.a / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hX
  have hw : large₂.sc.w'' D.R.n ≤ large₂.sc.b' :=
    div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx.le (one_le_n D))
  have he := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have heta : 2 * large₂.etaSz ≤ large₂.sc.b' := by
    have h1 : (2 : ℝ) ≤ D.R.m * ((D.R.t : ℝ) + 1) := by nlinarith
    linarith [P.mteta, mul_le_mul_of_nonneg_right h1 he.le]
  have hSc : 5 * large₂.Sc ≤ large₂.sc.b' := by
    linarith [P.kS_le, mul_le_mul_of_nonneg_right hk' hS.le]
  have hwj : wj D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (by simpa using hi)]
    rfl
  rw [RowWeightLemmas.nuRow_head D u i hi τ 0 hk0, D.hcW_first u τ hk0, D.hcW_e]
  push_cast
  rw [← hwj]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, htt⟩ := exists_top ha
    rw [(large₂.top_u τ t hk0 htt).1]
    have a1 := (large₂.win_top (i + 1) (by omega) hi τ t htt).2
    have a2 := (large₂.aT_win t).2
    have a3 : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)))
    have a4 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : large₂.sc.b' / large₂.sc.x ≤ large₂.sc.b' := div_le_self hb'.le hx.le
    linarith [hb t]
  · have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := (large₂.cloud_v τ ⟨0, by omega⟩).2
    push_cast at h1
    by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have a1 := hT (i + 1) (by omega) hi τ hc
      linarith
    · have a1 := (large₂.win_thin (i + 1) (by omega) hi τ ⟨(D.eTau τ).2, ha, hc⟩).2
      linarith

end GlobalTheory.CoreHt.RowsRange
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OffIdemDen
open GlobalTheory.IdemSupport

variable {D : D7}

theorem cP_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem conjP_eq_cP (Q : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ Q = cP Q :=
  HeightOneSpectrum.ext (Ideal.ext fun _ => Iff.rfl)

def evQ (Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    AE D →+* Q.adicCompletion D.host.E where
  toFun z := Φ z Q
  map_one' := by rw [map_one]; rfl
  map_mul' a b := ev_mul a b Q
  map_zero' := ev_zero Q
  map_add' a b := ev_add a b Q

theorem delta_mem {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)}
    {x : AE D} (h : IsDelta Φ P x) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ x Q ∈ Q.adicCompletionIntegers D.host.E := by
  by_cases hQ : Q = P
  · subst hQ; rw [h.2.1]; exact (Q.adicCompletionIntegers D.host.E).one_mem
  · rw [h.2.2 Q hQ]; exact (Q.adicCompletionIntegers D.host.E).zero_mem

end GlobalTheory.OffIdemDen
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StdSteps

theorem even_N (R : Ranks) (j : ℕ) : Even (R.N j) :=
  R.k_even.add (R.t_odd.add_one.mul_left j)

theorem N_lt_succ (R : Ranks) (j : ℕ) : R.N j < R.N (j + 1) := by
  unfold Ranks.N
  rw [Nat.add_mul]
  omega

theorem realPlace_cmTrace_zero_element_eq_I_mul_abs (D : D7) (h : D.host.ccK = ⊤) (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have h2 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have h3 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  rw [Host.xi0, h, Ideal.absNorm_top, map_div₀, map_neg, map_one, map_mul, h1, Nat.cast_one, map_one, one_mul, Complex.ofReal_inv]
  field_simp
  rw [Complex.I_sq]

theorem scale_eq (D : D7) {δ : ℂ} (hδ : δ ≠ 0) :
    (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D ⊤ δ))⁻¹ * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹ := by
  have h2 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have h3 : ‖δ‖ ≠ 0 := norm_ne_zero_iff.2 hδ
  rw [GlobalTheory.MomDict.area_lamOf D ⊤ δ top_ne_bot, Ideal.absNorm_top, Complex.normSq_eq_norm_sq]
  field_simp
  simp

end GlobalTheory.AdForm.StdSteps
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharConjFixed

theorem nontrivial_AF (D : D7) : Nontrivial (AF D.host.F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))

theorem finrank_AE (D : D7) : Module.finrank (AF D.host.F) (AE D) = 2 := by
  haveI := nontrivial_AF D
  rw [Module.finrank_baseChange]; exact D.sp.cm.deg2

theorem cA_tmul (D : D7) (a : AF D.host.F) (e : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl



theorem trace_mem (D : D7) (y : AE D) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y + cA D y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    rw [map_add (f := _), hu, hv, map_add (f := _)]; abel
  | tmul a e =>
    have hfix : star (e + star e) = e + star e := by
      rw [star_add, star_star, add_comm]
    obtain ⟨f, hf⟩ := (D.sp.cm.fixed _).1 hfix
    refine ⟨f • a, ?_⟩
    rw [cA_tmul, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one (A := D.host.E) f,
      ← TensorProduct.smul_tmul]
    rfl

theorem fixed_mem (D : D7) (y : AE D) (hy : cA D y = y) :
    ∃ b : AF D.host.F, algebraMap (AF D.host.F) (AE D) b = y := by
  obtain ⟨b, hb⟩ := trace_mem D y
  refine ⟨algebraMap D.host.F (AF D.host.F) (2⁻¹) * b, ?_⟩
  have h2 : algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (2⁻¹)) * 2 = 1 := by
    rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) 2) by rw [map_ofNat, map_ofNat],
      ← map_mul, ← map_mul, inv_mul_cancel₀ (two_ne_zero : (2 : D.host.F) ≠ 0), map_one, map_one]
  rw [map_mul, hb, hy, ← two_mul, ← mul_assoc, h2, one_mul]

theorem norm_scalar (D : D7) (b : AF D.host.F) :
    Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) b) = b ^ 2 := by
  rw [Algebra.norm_algebraMap, finrank_AE]

theorem fixed_unit (D : D7) (x : (AE D)ˣ) (hx : cA D (x : AE D) = x) :
    ∃ a : (AF D.host.F)ˣ, idF D a = x := by
  obtain ⟨b, hb⟩ := fixed_mem D x hx
  have hn : IsUnit (Algebra.norm (AF D.host.F) (x : AE D)) := x.isUnit.map _
  rw [← hb, norm_scalar] at hn
  obtain ⟨a, ha⟩ := (isUnit_pow_iff two_ne_zero).1 hn
  refine ⟨a, Units.ext ?_⟩
  rw [← hb, ← ha]; rfl

end GlobalTheory.CharConjFixed


open GlobalTheory.CharConjFixed in
theorem GlobalTheory.char_conj_fixed_eq_one : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n →
    ∀ (V : HSp D) (x : (AE D)ˣ), IsDetRoot V 1 x → μ x = 1 := by
  intro D μ n hμ hn V x hx
  have hfix : cA D (x : AE D) = x := by
    have h := hx
    simp only [IsDetRoot, map_one, Units.val_one, Matrix.det_one, one_mul] at h
    exact h.symm
  obtain ⟨a, ha⟩ := fixed_unit D x hfix
  obtain ⟨⟨η, hη⟩, hall⟩ := hμ
  have hμa : μ (idF D a) = η a ^ n := hall η hη a
  have hsq : η a ^ 2 = 1 := by
    rw [← map_pow]
    have : Units.map (↑(Algebra.norm (AF D.host.F)) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
      ext
      exact norm_scalar D (a : AF D.host.F)
    rw [← this]; exact hη.2.2.1 _
  obtain ⟨k, rfl⟩ := hn
  rw [← ha, hμa, ← two_mul, pow_mul, hsq, one_pow]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitRootProd

theorem mu_root_mul : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (n : ℕ), Even n → ResEta D μ n → ∀ e, IsSplitIdem D e → ∀ (s g : GA D V), SuppAt e V s → ∀ x₀ x x₁, IsDetAt e V s x₀ → IsDetRoot V g x → IsDetRoot V (s * g) x₁ → μ x₁ = μ x₀ * μ x := by
  intro D V μ n hn hres e he s g hs x₀ x x₁ h0 hx hx1
  have r0 : IsDetRoot V s x₀ := Formalism.L2.Theta.isDetAt_root he V s hs x₀ h0
  have r : IsDetRoot V (s * g) (x₀ * x) := GlobalTheory.Member.isDetRoot_mul V s g x₀ x r0 hx
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 (s * g) (x₀ * x) x₁ r hx1
  obtain ⟨⟨η, hη⟩, hall⟩ := hres
  have hμ := hall η hη a
  obtain ⟨k, hk⟩ := hn
  rw [ha, map_mul, hμ, hk, ← two_mul, pow_mul, Formalism.L2.Theta.eta_sq hη a, one_pow, mul_one, map_mul]

end GlobalTheory.SplitRootProd
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemSumInt

theorem finPart_idemSum_mul_inv_mem : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ t : 𝓞 D.host.E, (∀ Q ∈ SS, t ∉ Q.asIdeal) → finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D := by
  intro D e SS hS t ht
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hS
  by_cases h0 : t = 0
  · subst h0
    simp

  · rw [Finset.sum_mul, map_sum]
    refine AddSubgroup.sum_mem _ fun PP hPP => ?_
    by_contra hn
    exact ht PP hPP (((hes PP hPP).2 t h0).2 hn)

end GlobalTheory.IdemSumInt
end
