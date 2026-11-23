module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle048
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.UpperBlockRankOneUpdate
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle044
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle034
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoOrth
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle037
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle053
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle008
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem pad_j_k (g : G2 σ L.Y) : Pad (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (L.j g)) := by
  intro r c h
  rcases h with h | h | h | h
  · exact (L.j_out g r (by simp [h]) c).1
  · exact (L.j_out g r (by simp [h]) c).1
  · exact (L.j_out g c (by simp [h]) r).2
  · exact (L.j_out g c (by simp [h]) r).2
def bp_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  Matrix.of fun i k => if i = L.i₀ ∨ k = L.i₀ then 0 else β i k
theorem padM_n_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (Matrix.fromBlocks 1 (-(β.submatrix L.em L.em)) 0 1) = Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β)) 0 1 := by
  refine Matrix.ext fun r c => ?_
  rcases r with i | i <;> rcases c with k | k
  all_goals
    by_cases hi : i = L.i₀
    · first
        | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L i hi)]
        | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L i hi)]
      subst hi
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply]
    · by_cases hk : k = L.i₀
      · first
          | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L k hk)]
          | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L k hk)]
        subst hk
        simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, hi]
      · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
        obtain ⟨a', rfl⟩ := (L.rng k).1 hk
        first
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inl a) (Sum.inl a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inl a) (Sum.inr a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inr a) (Sum.inl a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inr a) (Sum.inr a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
theorem unipotentEntry_eq_zero (u : Fin L.n → AE F E) (a k : Fin d.n) (h : a ≠ L.i₀ ∨ k = L.i₀) : _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u a k = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.single_apply_of_ne]
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · exact h h1.symm
  · exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L j (h2.trans h)
theorem nq_q_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) (u : Fin L.n → AE F E) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀)
      (Matrix.fromBlocks 1 β 0 1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β)) 0 1) := by
  set A := 1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u with hA
  set D := ((1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ).map (cA σ) with hD
  have e : Matrix.fromBlocks 1 β 0 1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β)) 0 1 =
      Matrix.fromBlocks A (-(A * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β) + β * D) 0 D := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.mul_neg, hA, hD]
    congr 1
    abel
  have hA1 : ∀ a k, a ≠ L.i₀ ∨ k = L.i₀ → (A - 1) a k = 0 := fun a k h => by
    rw [hA, add_sub_cancel_left, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.unipotentEntry_eq_zero L u a k h]
  have hD1 : ∀ a k, k ≠ L.i₀ → D a k = (1 : Matrix _ _ (AE F E)) a k := fun a k hk => by
    simp only [hD, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.unipotentEntry_eq_zero L u k a (Or.inl hk), sub_zero]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h : k = a
    · subst h; simp [map_one]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  rw [e]
  refine Bq.NQ.of_blocks (fun a => hA1 a L.i₀ (Or.inr rfl)) (fun a k ha => hA1 a k (Or.inl ha)) (fun a k ha hk => ?_)
    (fun a k hk => by rw [Matrix.sub_apply, hD1 a k hk, sub_self])
  have h1 : (A * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β) a k = β a k := by
    rw [Matrix.mul_apply]
    have : ∀ m, A a m * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β m k = if m = a then β a k else 0 := fun m => by
      have hAm : A a m = (1 : Matrix _ _ (AE F E)) a m := by
        have := hA1 a m (Or.inl ha); rwa [Matrix.sub_apply, sub_eq_zero] at this
      rw [hAm, Matrix.one_apply]
      by_cases hm : a = m
      · subst hm; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, ha, hk]
      · simp [hm, Ne.symm hm]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : (β * D) a k = β a k := by
    rw [Matrix.mul_apply]
    simp only [hD1 _ k hk, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Matrix.add_apply, Matrix.neg_apply, h1, h2, neg_add_cancel]
theorem isPar_of_nq_k {p : d.G} (h : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b p)) :
    ∃ t, IsPar p t ∧ Matrix.GeneralLinearGroup.det t = 1 := by
  obtain ⟨-, t₀, ht₀⟩ := d.ok.frame
  set M := inFrame d.b p
  set T0 := incM F t₀.1
  set T0i := incM F (t₀⁻¹).1
  have e1 : T0 * T0i = 1 := by
    simp only [T0, T0i, incM, ← Matrix.map_mul]
    rw [show t₀.1 * (t₀⁻¹).1 = 1 from t₀.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdet : (T0 * M.toBlocks₁₁ * T0i).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, h.upper_block_det_one, mul_one, ← Matrix.det_mul, e1, Matrix.det_one]
  have hu : IsUnit (T0 * M.toBlocks₁₁ * T0i) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact isUnit_one)
  refine ⟨hu.unit, (kunf.isPar_frame ht₀ p hu.unit).2 ⟨h.projected_block_lower_sum, rfl⟩, ?_⟩
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, hdet]
end Bq
theorem key_id_pf_k {nb : nA σ d.Y d.b → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb : IsNMap d.b nb)
    (hnb' : IsNMap L.b nb') {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (h : G2 σ L.Y) (β : nA σ d.Y d.b) (u : Fin L.n → AE F E)
    (x : d.G) : ∃ p t, IsPar p t ∧ Matrix.GeneralLinearGroup.det t = 1 ∧
      L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x) := by
  set q : d.G := nb β * uM u * L.j (nb' (-_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) with hq
  set p : d.G := L.j h * q * L.j h⁻¹ with hp
  have hinv : L.j (nb' (-_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) = (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)))⁻¹ := by
    rw [kunf.nb_neg hnb', map_inv]
  have hid : L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x) := by
    simp only [hp, hq, hinv, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  have hQ : inFrame d.b q = Matrix.fromBlocks 1 β.1 0 1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β.1)) 0 1 := by
    rw [hq, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hnb β, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.inFrame_uM_k L hU u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k,
      hnb' (-_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β), ← _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padM_n_k L β.1]
    rfl
  have hJJ : inFrame d.b (L.j h) * inFrame d.b (L.j h⁻¹) = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hnq : Bq.NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b p) := by
    rw [hp, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hQ]
    exact Bq.NQ.conj (by simp) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.pad_j_k L h) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.pad_j_k L h⁻¹) hJJ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.nq_q_k L β.1 u)
  obtain ⟨t, ht, hdt⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.isPar_of_nq_k L hnq
  exact ⟨p, t, ht, hdt, hid⟩
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem stepA_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : nA σ d.Y d.b → d.G}
    (hnb : IsNMap (σ := σ) (Y := d.Y) d.b nb) (x : d.G) (β : nA σ d.Y d.b) (g : UA σ d.A.J) :
    thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X : Matrix (Fin d.m) (Fin d.n) E,
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram (incM F X) (incM F X)))) * d.T (d.om x Φ) (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X) := by
  have hΨ : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hΨg : d.S g (d.om x Φ) ∈ d.sch := d.ok.dbl.lin.pres g _ hΨ
  have hn : d.om (nb β) (d.S g (d.om x Φ)) ∈ d.sch := d.ok.dbl.weil.2.1.pres (nb β) _ hΨg
  rw [map_mul, Module.End.mul_apply, (hT F E σ d Φ hΦ).2 x g, ← ((hT F E σ d _ hn).1).tsum_eq]
  refine tsum_congr fun X => ?_
  rw [(hP F E σ d _ hΨg).1 (nb β) β.1 (hnb β) (incM F X), (hP F E σ d _ hΨ).2.2 g (incM F X)]
  rfl
theorem meas_tr_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) (X : Matrix (Fin d.m) (Fin d.n) E) :
    AEMeasurable (fun g => ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ₑ) (d.μ.restrict d.D) :=
  ((_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_tr_k d hf X).enorm.measurable).aemeasurable
theorem tbdd_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) :
    ∃ K : ℝ, ∀ g : UA σ d.A.J, Summable (fun X => ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖) ∧ ∑' X, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ ≤ K := by
  obtain ⟨K, hK⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.thetaBdd_of_k hS F E σ d f hf
  exact ⟨K, hK⟩
theorem pt_bdd_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (g : UA σ d.A.J) (s : Set (Matrix (Fin d.m) (Fin d.n) E)) {K : ℝ}
    (hsum : Summable (fun X => ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖)) (hle : ∑' X, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ ≤ K) :
    ∑' X : s, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1)‖ₑ ≤ ENNReal.ofReal K := by
  calc ∑' X : s, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1)‖ₑ ≤ ∑' X, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun X => ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ₑ)
    _ = ∑' X, ENNReal.ofReal ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ := tsum_congr fun X => (ofReal_norm _).symm
    _ = ENNReal.ofReal (∑' X, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hle
theorem lint_fin_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    (s : Set (Matrix (Fin d.m) (Fin d.n) E)) :
    ∑' X : s, ∫⁻ g in d.D, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1)‖ₑ ∂d.μ ≠ ⊤ := by
  haveI := countable_mat (E := E) d.m d.n
  obtain ⟨K, hK⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.tbdd_k hS d hf
  have hfin : d.μ d.D < ⊤ := (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom
  rw [← lintegral_tsum (f := fun (X : s) g => ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1)‖ₑ) fun X => _root_.PositivityTheory.SiegelWeilFormula.Tauto.meas_tr_k d hf X.1]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
    ((lintegral_mono fun g => _root_.PositivityTheory.SiegelWeilFormula.Tauto.pt_bdd_k d g s (hK g).1 (hK g).2).trans (setLIntegral_const _ _).le)
theorem lint_fin_all_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) :
    ∑' X, ∫⁻ g in d.D, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ₑ ∂d.μ ≠ ⊤ := by
  have := _root_.PositivityTheory.SiegelWeilFormula.Tauto.lint_fin_k hS d hf Set.univ
  rwa [tsum_univ (f := fun X => ∫⁻ g in d.D, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ₑ ∂d.μ)] at this
theorem continuous_tt_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Continuous (d.tt) := by
  have h1 : Continuous (Algebra.trace (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact h1.comp (continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i)
theorem thetaCoef_at_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
    {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = d.orb T (d.om x Φ) := by
  haveI := countable_mat (E := E) d.m d.n
  have hΨ : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hf : d.T (d.om x Φ) ∈ d.schM := (hB F E σ d).1 _ hΨ
  have hen : ∀ a, ‖d.B.ψ a‖ₑ = 1 := fun a => by
    rw [← ofReal_norm_eq_enorm, GlobalTheory.StdCharFromIsStd.norm_psi d.std, ENNReal.ofReal_one]
  have hψc : Continuous d.B.ψ := d.std.1
  set f : Mx F E d.m d.n → ℂ := d.T (d.om x Φ) with hfdef
  set c : ℝ := (d.μ.real d.D)⁻¹ with hcdef
  set G : Matrix (Fin d.m) (Fin d.n) E → Matrix (Fin d.n) (Fin d.n) (AE F E) :=
    fun X => d.gram (incM F X) (incM F X) with hG
  set e : nA σ d.Y d.b → Matrix (Fin d.m) (Fin d.n) E → ℂ :=
    fun β X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * G X))) with he
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(d.tt (T.1.1 * β.1))) with hχ
  set H : Matrix (Fin d.m) (Fin d.n) E → ℂ := fun X => ∫ g in d.D, f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X) ∂d.μ with hH
  have hmeas : ∀ X, AEStronglyMeasurable (fun g => f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)) (d.μ.restrict d.D) :=
    fun X => (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_tr_k d hf X).aestronglyMeasurable
  have hcb : Continuous fun β : nA σ d.Y d.b => β.1 := continuous_subtype_val
  have hec : ∀ X, Continuous fun β => e β X := fun X =>
    hψc.comp ((continuous_const.mul ((_root_.PositivityTheory.SiegelWeilFormula.Tauto.continuous_tt_k d).comp (hcb.matrix_mul continuous_const))).neg)
  have hχc : Continuous χ := hψc.comp (((_root_.PositivityTheory.SiegelWeilFormula.Tauto.continuous_tt_k d).comp (continuous_const.matrix_mul hcb)).neg)
  have hI : ∀ β, d.I Φ (nb β * x) = c • ∑' X, e β X * H X := fun β => by
    show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ (nb β * x) = _
    rw [PositivityTheory.SiegelWeilFormula.thetaMean, setAverage_eq]
    congr 1
    have hA' : ∀ g, thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X, e β X * f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X) :=
      fun g => _root_.PositivityTheory.SiegelWeilFormula.Tauto.stepA_k hP hT d hΦ hc.1 x β g
    simp only [hA']
    rw [integral_tsum (f := fun X g => e β X * f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)) (fun X => (hmeas X).const_mul _) ?_]
    · exact tsum_congr fun X => integral_const_mul _ _
    · simpa only [he, enorm_mul, hen, one_mul] using _root_.PositivityTheory.SiegelWeilFormula.Tauto.lint_fin_all_k hS d hf
  have hO : ∀ X, ∫ β in 𝓖, e β X * χ β ∂lam = if G X = (-2 : ℤ) • T.1.1 then 1 else 0 := fun X => by
    obtain ⟨hm, S₀, hS₀⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.gram_mem_k d X T
    simp only [he, hχ, _root_.PositivityTheory.SiegelWeilFormula.Tauto.chr_comb_k]
    refine (_root_.PositivityTheory.SiegelWeilFormula.Tauto.orth_k d hc _ hm ⟨S₀, hS₀⟩).trans ?_
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Tauto.half_eq_iff_k]
    rfl
  have h1 : ∀ β, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      c • ∑' X, e β X * χ β * H X := fun β => by
    rw [hI β, smul_mul_assoc, ← tsum_mul_right]
    congr 1
    exact tsum_congr fun X => by simp only [hχ, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt]; ring
  have hlam : lam 𝓖 = 1 := hc.2.2.2
  have h2 : ∑' X, ∫⁻ β in 𝓖, ‖e β X * χ β * H X‖ₑ ∂lam ≠ ⊤ := by
    simp only [he, hχ, enorm_mul, hen, one_mul, lintegral_const, Measure.restrict_apply_univ, hlam, mul_one]
    refine ne_top_of_le_ne_top (_root_.PositivityTheory.SiegelWeilFormula.Tauto.lint_fin_all_k hS d hf) (ENNReal.tsum_le_tsum fun X => ?_)
    exact enorm_integral_le_lintegral_enorm _
  have h3 : ∑' X, (if G X = (-2 : ℤ) • T.1.1 then (1 : ℂ) else 0) * H X =
      ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1 := by
    show _ = ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), H X.1
    rw [tsum_subtype {X | G X = (-2 : ℤ) • T.1.1} H]
    exact tsum_congr fun X => by simp only [Set.indicator_apply, Set.mem_setOf_eq, ite_mul, one_mul, zero_mul]
  have h4 : d.orb T (d.om x Φ) = c • ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E //
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1 := by
    haveI : Countable {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} :=
      Subtype.countable
    show (⨍ g in d.D, ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)),
      f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1) ∂d.μ) = c • ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), H X.1
    rw [setAverage_eq, integral_tsum (f := fun (X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E))) g =>
      f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1)) (fun X => hmeas X.1) (_root_.PositivityTheory.SiegelWeilFormula.Tauto.lint_fin_k hS d hf {X | G X = (-2 : ℤ) • T.1.1})]
  show ∫ β in 𝓖, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) ∂lam = _
  rw [integral_congr_ae (Eventually.of_forall h1), integral_smul,
    integral_tsum (f := fun X β => e β X * χ β * H X)
      (fun X => (((hec X).mul hχc).mul continuous_const).aestronglyMeasurable) h2, h4, ← h3]
  congr 1
  exact tsum_congr fun X => by rw [integral_mul_const, hO X]
theorem thetaCoef_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k :=
  fun _ _ _ _ _ _ _ _ d _ hΦ _ _ _ hc T x => _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaCoef_at_k hS hB hP hT d hΦ hc T x
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def padZeroAlt (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then β h.1.choose h.2.choose else 0
theorem pad_zero_embedding (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (a c : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β (L.em a) (L.em c) = β a c := by
  have h : (∃ a', L.em a' = L.em a) ∧ ∃ c', L.em c' = L.em c := ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_pos h]
  rw [L.inj h.1.choose_spec, L.inj h.2.choose_spec]
theorem pad_zero_outside (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i k : Fin d.n)
    (h : ¬ ((∃ a, L.em a = i) ∧ ∃ c, L.em c = k)) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β i k = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_neg h]
theorem pad_zero_cases (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (P : AE F E → AE F E → Prop) (h0 : P 0 0)
    (h1 : ∀ a c, P (β a c) (β c a)) (i k : Fin d.n) : P (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β i k) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β k i) := by
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    exact h1 a c
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L β i k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L β k i (fun h' => h ⟨h'.2, h'.1⟩)]
    exact h0
theorem eps_common_k : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  exact ⟨ε, hε, hε'⟩
theorem pad_zero_mem_unipotent (β : nA σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1 ∈ nA σ d.Y d.b := by
  obtain ⟨ε, hε, hε'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.eps_common_k L
  rw [kunf.mem_nA_iff hε]
  have hβ := (kunf.mem_nA_iff hε' β.1).1 β.2
  ext i k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_cases L β.1 (fun u v => v = -((((ε : ℤ) : AE F E)) • cA σ u)) (by simp) (fun a c => ?_) i k
  have := congrFun (congrFun hβ a) c
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] using this
def padN_k : nA σ L.Y L.b →+ nA σ d.Y d.b where
  toFun β := ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_mem_unipotent L β⟩
  map_zero' := by
    apply Subtype.ext
    ext i k
    refine _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_cases L (0 : nA σ L.Y L.b).1 (fun u _ => u = (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k) rfl
      (fun a c => rfl) i k
  map_add' β β' := by
    apply Subtype.ext
    ext i k
    by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
    · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
      simp only [AddSubgroup.coe_add, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    · simp only [AddSubgroup.coe_add, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L _ i k h, add_zero]
theorem prj_padN_k (β : nA σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L β) = β := by
  apply Subtype.ext
  ext a c
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, Matrix.submatrix_apply]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding L β.1 a c
theorem continuous_padN_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun k => ?_
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    exact (continuous_apply c).comp ((continuous_apply a).comp continuous_subtype_val)
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L _ i k h]
    exact continuous_const
theorem prj_nF_k {β : nA σ d.Y d.b} (h : β ∈ nF σ d.Y d.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β ∈ nF σ L.Y L.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, hT]
  rfl
theorem padN_nF_k {β : nA σ L.Y L.b} (h : β ∈ nF σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L β ∈ nF σ d.Y d.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨Matrix.of fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then
    T h.1.choose h.2.choose else 0, ?_⟩
  ext i k
  show _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1 i k = _
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_pos h, hT]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_pos h]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_neg h]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_neg h, map_zero]
theorem fiber_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)}
    {𝓖' : Set (nA σ L.Y L.b)} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (G : nA σ L.Y L.b → ℂ) (hG : Continuous G) (hper : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β') :
    ∫ β in 𝓖, G (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam = ∫ β' in 𝓖', G β' ∂lam' := by
  obtain ⟨ε, hε, hε'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.eps_common_k L
  obtain ⟨h1, h2⟩ := nA_inst d.n d.Y d.b ε hε
  obtain ⟨h3, h4⟩ := nA_inst L.n L.Y L.b ε hε'
  exact GlobalTheory.T.haar_measure_split_exact_sequence (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.continuous_prj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.continuous_padN_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_padN_k L)
    (nF σ d.Y d.b) (nF σ L.Y L.b) (countable_nF _ _ _) (countable_nF _ _ _) (fun γ hγ => _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_nF_k L hγ)
    (fun γ hγ => _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_nF_k L hγ) lam lam' hc.2.1 hc'.2.1 𝓖 𝓖' hc.2.2.1 hc.2.2.2 hc'.2.2.1 hc'.2.2.2 G hG
    (fun γ hγ x => hper γ hγ x)
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end
