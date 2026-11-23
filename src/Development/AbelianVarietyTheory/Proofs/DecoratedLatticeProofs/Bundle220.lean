module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle150
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle193
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Pointwise

noncomputable section

namespace GlobalTheory.MajSum

variable {D : D7}

theorem realSize_add_le (θ : InfFam D) {m n : ℕ} (x y : Mx D m n) :
    realSize θ (x + y) ≤ realSize θ x + realSize θ y := by
  unfold realSize
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have : Formalism.IndefR.Datum.compAt θ τ (x + y) i j =
      Formalism.IndefR.Datum.compAt θ τ x i j + Formalism.IndefR.Datum.compAt θ τ y i j := by
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add (infPart D), RingHom.map_add (θ τ)]
  rw [this]
  exact norm_add_le _ _

theorem maj_le_shift (θ : InfFam D) {m n : ℕ} (K C : Set (Mx D m n)) (N : ℕ) (γ w : Mx D m n)
    (hwC : w ∈ C) (hw : realSize θ w ≤ 1) :
    maj θ K N γ ≤ 2 ^ N * maj θ (K + C) N (γ + w) := by
  unfold maj
  by_cases hγ : InBox K γ
  · have hbox : InBox (K + C) (γ + w) := by
      obtain ⟨k, hk, hk0⟩ := hγ
      refine ⟨k + w, Set.add_mem_add hk hwC, ?_⟩
      have : γ + w - (k + w) = γ - k := by abel
      rw [this]; exact hk0
    rw [if_pos hγ, if_pos hbox]
    have h0 := realSize_nonneg θ γ
    have h1 := realSize_nonneg θ (γ + w)
    have h2 : 1 + realSize θ (γ + w) ≤ 2 * (1 + realSize θ γ) := by
      have := realSize_add_le θ γ w; linarith
    have hp : (0:ℝ) < (1 + realSize θ (γ + w)) ^ N := by positivity
    have hq : (0:ℝ) < (1 + realSize θ γ) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]
    calc (1 + realSize θ (γ + w)) ^ N ≤ (2 * (1 + realSize θ γ)) ^ N := by gcongr
      _ = 2 ^ N * (1 + realSize θ γ) ^ N := by rw [mul_pow]
  · rw [if_neg hγ]
    have := maj_nonneg θ (K + C) N (γ + w)
    unfold maj at this
    positivity

end GlobalTheory.MajSum

namespace GlobalTheory.MajSum

theorem realSize_zero {D : D7} (θ : InfFam D) {m n : ℕ} : realSize θ (0 : Mx D m n) = 0 := by
  have h : ∀ τ (i : Fin m) (j : Fin n), Formalism.IndefR.Datum.compAt θ τ (0 : Mx D m n) i j = 0 := by
    intro τ i j
    show θ τ (infPart D 0) = 0
    rw [RingHom.map_zero (infPart D), RingHom.map_zero (θ τ)]
  unfold realSize
  simp only [h, norm_zero, Finset.sum_const_zero]


set_option synthInstance.maxHeartbeats 400000 in
theorem tsum_maj_ne_top : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K →
    (∑' y : ratMx D m n, ENNReal.ofReal (maj θ K N y)) ≠ ⊤ := by
  intro D θ hθ m n
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let μ : Measure (Mx D m n) := Measure.addHaar
  have hcont : Continuous (realSize θ : Mx D m n → ℝ) :=
    ((GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ).1 m n ∅ isCompact_empty).2.1
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_majorant_coordinate_coset_measure D θ hθ m n (fun _ _ => True) 0 μ inferInstance
    (Filter.Eventually.of_forall fun x i j h => (h trivial).elim)
    (fun t _ => by
      have e : (fun x : Mx D m n => x + t) = fun x => t + x := funext fun x => add_comm x t
      rw [e]; exact map_add_left_eq_self μ t)
  refine ⟨N, fun K hK => ?_⟩

  obtain ⟨U, hUo, hU⟩ : ∃ U : Set (Mx D m n), IsOpen U ∧ ∀ γ ∈ ratMx D m n, γ ∈ U ↔ γ = 0 := by
    have h0 : IsOpen ({0} : Set (ratMx D m n)) := @isOpen_discrete (ratMx D m n) _ i5 _
    obtain ⟨U, hUo, hUe⟩ := isOpen_induced_iff.mp h0
    refine ⟨U, hUo, fun γ hγ => ?_⟩
    have := Set.ext_iff.mp hUe ⟨γ, hγ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    rw [this]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h0U : (0 : Mx D m n) ∈ U := (hU 0 (zero_mem _)).2 rfl
  have hsub : {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} ∈ nhds ((0 : Mx D m n), (0 : Mx D m n)) := by
    have hc : Continuous fun p : Mx D m n × Mx D m n => p.1 - p.2 := continuous_fst.sub continuous_snd
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hUo.mem_nhds h0U
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hsub
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (0 : Mx D m n)
  have hR : {w : Mx D m n | realSize θ w < 1} ∈ nhds (0 : Mx D m n) := by
    refine (isOpen_lt hcont continuous_const).mem_nhds ?_
    show realSize θ (0 : Mx D m n) < 1
    rw [realSize_zero]; exact one_pos
  set W := interior (A ∩ B ∩ C ∩ {w : Mx D m n | realSize θ w < 1}) with hWdef
  have hW0 : (0 : Mx D m n) ∈ W :=
    mem_interior_iff_mem_nhds.2 (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hA hB) hC) hR)
  have hμW : μ W ≠ 0 := (isOpen_interior.measure_pos μ ⟨0, hW0⟩).ne'

  let s : ratMx D m n → Set (Mx D m n) := fun γ => (fun x => -(γ : Mx D m n) + x) ⁻¹' W
  have hs : ∀ γ, MeasurableSet (s γ) := fun γ =>
    (isOpen_interior.preimage (continuous_const.add continuous_id)).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro γ γ' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    have hxA : -(γ : Mx D m n) + x ∈ A := (interior_subset hx).1.1.1
    have hxB : -(γ' : Mx D m n) + x ∈ B := (interior_subset hx').1.1.2
    have hmem : (-(γ : Mx D m n) + x, -(γ' : Mx D m n) + x) ∈ {p : Mx D m n × Mx D m n | p.1 - p.2 ∈ U} :=
      hAB ⟨hxA, hxB⟩
    simp only [Set.mem_setOf_eq] at hmem
    have e : -(γ : Mx D m n) + x - (-(γ' : Mx D m n) + x) = (γ' : Mx D m n) - γ := by abel
    rw [e] at hmem
    have := (hU _ (sub_mem γ'.2 γ.2)).1 hmem
    exact Subtype.ext (sub_eq_zero.1 this).symm
  set K' := K + C
  have hK' : IsCompact K' := hK.add hCc
  have hfin : ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ < ⊤ := (hN K' hK').lintegral_lt_top
  have key : ∀ γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ) * μ W ≤
      2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := by
    intro γ
    calc ENNReal.ofReal (maj θ K N γ) * μ W = ∫⁻ _x in s γ, ENNReal.ofReal (maj θ K N γ) ∂μ := by
          rw [setLIntegral_const]
          congr 1
          exact (measure_preimage_add μ (-(γ : Mx D m n)) W).symm
      _ ≤ ∫⁻ x in s γ, 2 ^ N * ENNReal.ofReal (maj θ K' N x) ∂μ := by
          refine setLIntegral_mono' (hs γ) fun x hx => ?_
          have hw := interior_subset hx
          have h1 := maj_le_shift θ K C N (γ : Mx D m n) (-(γ : Mx D m n) + x) hw.1.2 (le_of_lt hw.2)
          rw [add_neg_cancel_left] at h1
          calc ENNReal.ofReal (maj θ K N γ) ≤ ENNReal.ofReal (2 ^ N * maj θ K' N x) :=
                ENNReal.ofReal_le_ofReal h1
            _ = 2 ^ N * ENNReal.ofReal (maj θ K' N x) := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      _ = 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hsum : (∑' γ : ratMx D m n, ENNReal.ofReal (maj θ K N γ)) * μ W ≤
      2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ := by
    rw [← ENNReal.tsum_mul_right]
    calc _ ≤ ∑' γ : ratMx D m n, 2 ^ N * ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ :=
          ENNReal.tsum_le_tsum key
      _ = 2 ^ N * ∑' γ : ratMx D m n, ∫⁻ x in s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := ENNReal.tsum_mul_left
      _ = 2 ^ N * ∫⁻ x in ⋃ γ, s γ, ENNReal.ofReal (maj θ K' N x) ∂μ := by rw [lintegral_iUnion hs hdisj]
      _ ≤ 2 ^ N * ∫⁻ x, ENNReal.ofReal (maj θ K' N x) ∂μ := by
          gcongr; exact Measure.restrict_le_self
  intro htop
  rw [htop, ENNReal.top_mul hμW] at hsum
  exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hfin).ne (top_le_iff.1 hsum)

end GlobalTheory.MajSum
end
end

section

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittFrameOfDec

theorem form_mulVec {D : D7} {n m : ℕ} (A : Matrix (Fin n) (Fin m) D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E)
    (w : Fin m → D.host.E) : star (A *ᵥ w) ⬝ᵥ (G *ᵥ (A *ᵥ w)) = star w ⬝ᵥ ((Aᴴ * G * A) *ᵥ w) := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem isWittFrame_of_hypDec (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (h : IsAniso T₀) :
    IsWittFrame D.sp.cm.sig T.gram d.e d.e' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cT_sig]; exact d.ee
  · rw [cT_sig]; exact d.e'e'
  · rw [cT_sig]
    have h1 := congrArg Matrix.conjTranspose d.e'e
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h1
    exact h1
  · intro z hX hY hz
    rw [cT_sig] at hX hY
    have hqY : d.qY *ᵥ z = 0 := hX
    have hqX : d.qX *ᵥ z = 0 := hY
    have hz0 : z = d.i₀ *ᵥ (d.q0 *ᵥ z) := by
      have := congrArg (fun M => M *ᵥ z) d.sum_eq_one_rat
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hqX, hqY,
        Matrix.mulVec_zero, zero_add, add_zero] at this
      exact this.symm
    obtain ⟨z₀, hz₀⟩ : ∃ w, w = d.q0 *ᵥ z := ⟨_, rfl⟩
    rw [← hz₀] at hz0
    by_cases h0 : z₀ = 0
    · rw [hz0, h0, Matrix.mulVec_zero]
    exfalso
    have e1 : hE D.sp.cm.sig T.gram z z = star z ⬝ᵥ (T.gram *ᵥ z) := by
      simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc]; rfl
    have hzz : star z₀ ⬝ᵥ (T₀.gram *ᵥ z₀) = 0 := by
      rw [← d.iso, ← form_mulVec, ← hz0, ← e1, hz]
    let C : Matrix (Fin T₀.rank) (Fin 1) D.host.E := Matrix.of fun i _ => z₀ i
    apply h 1 C
    refine ⟨Nat.one_pos, ?_, ?_⟩
    · change LinearIndependent D.host.E (fun _ : Fin 1 => z₀)
      exact linearIndependent_unique_iff.2 h0
    · rw [cT_sig]
      ext a b
      fin_cases a; fin_cases b
      have : (Cᴴ * T₀.gram * C) 0 0 = star z₀ ⬝ᵥ (T₀.gram *ᵥ z₀) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, C, Matrix.of_apply, dotProduct, Matrix.mulVec,
          Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      simpa using this.trans hzz

end GlobalTheory.WittFrameOfDec
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.ChainOnto
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.RankZeroVac

variable {D : D7}

theorem incA_tmul' (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

theorem continuous_wittExtendByZero : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const

theorem heisenbergOperator_wittExtendByZero (ψ : AddChar (AF D.host.F) ℂ) (u : WO W₀ T) (f : WO W T → ℂ) :
    heisO ψ W₀ T u (fun w => f (d.ext0 T w)) = fun w => heisO ψ W T (d.ext0 T u) f (d.ext0 T w) := by
  funext w
  simp only [heisO, map_add (f := _), d.wittDecomp_sympl_extAnisotropic_extAnisotropic]

theorem isThetaFunction_comp_wittExtendByZero {ψ : AddChar (AF D.host.F) ℂ} {f : WO W T → ℂ} (hf : IsThetaFunO ψ W T f) :
    IsThetaFunO ψ W₀ T (fun w => f (d.ext0 T w)) := {
  quasi γ w := by
    have h := hf.quasi (γ * d.q0) (d.ext0 T w)
    have hr : ratW T W (γ * d.q0) = d.ext0 T (ratW T W₀ γ) := by
      rw [ratW_eq, ratW_eq, rat_mul, d.matrixExtendByZero_apply]; rfl
    rw [hr, d.wittDecomp_sympl_extAnisotropic_extAnisotropic] at h
    simp only [map_add (f := _)]
    exact h
  level := by
    obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (d.ext0 T), hU.preimage (continuous_wittExtendByZero d T), fun u hu hinf => ?_⟩
    rw [heisenbergOperator_wittExtendByZero]
    have h0 : (d.ext0 T u).map (infPart D) = 0 := by
      rw [d.matrixExtendByZero_apply, Matrix.map_mul, hinf, Matrix.zero_mul]
    rw [hfix _ hu h0]
  cont := hf.cont.comp (continuous_wittExtendByZero d T)
  smooth k L hL hLf w := by
    have h := hf.smooth k ((d.ext0 T).comp L) ((continuous_wittExtendByZero d T).comp hL) (fun t => by
      show (d.ext0 T (L t)).map (finPart D) = 0
      rw [d.matrixExtendByZero_apply, Matrix.map_mul, hLf t, Matrix.zero_mul]) (d.ext0 T w)
    simpa only [AddMonoidHom.comp_apply, map_add (f := _)] using h }

theorem isHalf_wittHyperbolicExtendByZero_apply {e : AE D} {u : WO W₀ T} (h : IsHalf e u) : IsHalf e (d.ext0 T u) := by
  intro i j
  have hl : ∀ l, e * ((u : Matrix (Fin T.rank) (Fin W₀.rank) (AE D)) i l * d.p0 l j) =
      (u : Matrix (Fin T.rank) (Fin W₀.rank) (AE D)) i l * d.p0 l j := fun l => by rw [← mul_assoc, h i l]
  rw [d.matrixExtendByZero_apply, Matrix.mul_apply]
  show e * ∑ l, _ = _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => hl l

end

end GlobalTheory.RankZeroVac

namespace GlobalTheory.RankZeroVac

variable {D : D7}

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

theorem wittDecomposition_gram_projection_identity (s : Fin W₀.rank → D.host.E) (j : Fin W.rank) :
    ∑ l, (∑ k, star (s k) * W₀.gram k l) * d.q0 l j = ∑ m, star ((Matrix.mulVec d.i₀ s) m) * W.gram m j := by
  have h : Matrix.vecMul (Matrix.vecMul (star s) W₀.gram) d.q0 = Matrix.vecMul (star (Matrix.mulVec d.i₀ s)) W.gram := by
    rw [Matrix.vecMul_vecMul, HypDec.q0, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det W₀),
      Matrix.one_mul, ← Matrix.vecMul_vecMul, Matrix.star_mulVec]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

end

end GlobalTheory.RankZeroVac

namespace GlobalTheory.RankZeroVac

variable {D : D7}

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

end

end GlobalTheory.RankZeroVac
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc


theorem _root_.GlobalTheory.T.symplectic_form_inert_supported_points_antidiagonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsConjAt D.sp.cm.sig h c → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), ψ (symplOH S T (uPt hw h k aS aT x) (uPt hw h k aS aT y)) = thW ψ hw h (k * c k) (2⁻¹ * GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y) := by
  first | exact @GlobalTheory.InertFrameSympl.symplOH_uPt | exact GlobalTheory.InertFrameSympl.symplOH_uPt | (intros; apply GlobalTheory.InertFrameSympl.symplOH_uPt <;> assumption)
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc


theorem _root_.GlobalTheory.T.inert_supported_point_integral_frames_mem_lattice : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → uPt hw h k aS aT x ∈ latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  first | exact @GlobalTheory.InertFrameLoc.uPt_mem_latO | exact GlobalTheory.InertFrameLoc.uPt_mem_latO | (intros; apply GlobalTheory.InertFrameLoc.uPt_mem_latO <;> assumption)
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc


theorem _root_.GlobalTheory.T.local_group_action_inert_supported_points_frames : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)) (gS : Gv S v) (gT : Gv T v) (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)), actO S T (embV S v gS) (embV T v gT) (uPt hw h k aS aT x) = uPt hw h k aS aT ((aT⁻¹ * locMat D.sp.cm.sig T.gram h gT * aT).1 * x * (aS⁻¹ * locMat D.sp.cm.sig S.gram h gS⁻¹ * aS).1) := by
  first | exact @GlobalTheory.InertFrameAct.actO_uPt | exact GlobalTheory.InertFrameAct.actO_uPt | (intros; apply GlobalTheory.InertFrameAct.actO_uPt <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.selfDualLatticeAtPlace_smul_integral_mem : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ → ∀ a ∈ intAt D (· = v), ∀ y ∈ Λ, a • y ∈ Λ := by
  first | exact @GlobalTheory.IwaPlace.SDStable.smul_mem | exact GlobalTheory.IwaPlace.SDStable.smul_mem | (intros; apply GlobalTheory.IwaPlace.SDStable.smul_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_integralAdele_atPlace_with_component : ∀ (D : D7) (v : Pl D) (z : Fv D.host.F v ⊗[D.host.F] D.host.E), z ∈ intV D v → ∃ x ∈ intAt D (· = v), compAt D v x = z := by
  first | exact @GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq | exact GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq | (intros; apply GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.tsum_adelicMatrixSchwartzMajorant_rational_ne_top : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K → (∑' y : ratMx D m n, ENNReal.ofReal (maj θ K N y)) ≠ ⊤ := by
  first | exact @GlobalTheory.MajSum.tsum_maj_ne_top | exact GlobalTheory.MajSum.tsum_maj_ne_top | (intros; apply GlobalTheory.MajSum.tsum_maj_ne_top <;> assumption)

end
end
