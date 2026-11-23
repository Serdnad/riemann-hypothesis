module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle081
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle096
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle084
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle095
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle015
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TransNorm

variable {q : ℕ} [Fact q.Prime]

lemma bd_add {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bd B f) (hg : Bd B g) : Bd B (f + g) := by
  simpa using ((sup_norm_laws q).1 f g B B hf hg).1

lemma bd_mul_one {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bd B f) (hg : Bd 1 g) : Bd B (f * g) := by
  simpa using ((sup_norm_laws q).1 f g B 1 hf hg).2

lemma bd_C {a : ℂ_[q]} {B : ℝ} (ha : ‖a‖ ≤ B) : Bd B (C a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · simpa using (norm_nonneg a).trans ha

lemma bd_one : Bd 1 (1 : ℂ_[q]⟦X⟧) := by
  simpa using (bd_C (a := (1 : ℂ_[q])) (B := 1) (by simp))

lemma bd_X : Bd 1 (X : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_X]
  split_ifs <;> simp

lemma bd_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero => simpa using bd_one
  | succ n ih => rw [pow_succ]; exact bd_mul_one ih hf

lemma bd_sum {α : Type} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, Bd B (f i)) : Bd B (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (Bd B) (fun _ _ => bd_add) ?_ hf
  intro n
  simpa using hB

lemma bd_prod {α : Type} (s : Finset α) (f : α → ℂ_[q]⟦X⟧)
    (hf : ∀ i ∈ s, Bd 1 (f i)) : Bd 1 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (Bd 1) (fun _ _ => bd_mul_one) bd_one hf

lemma bd_sub_C {f : ℂ_[q]⟦X⟧} {a : ℂ_[q]} (hf : Bd 1 f) (ha : ‖a‖ ≤ 1) : Bd 1 (f - C a) := by
  have := bd_add hf (bd_C (a := -a) (by simpa using ha))
  simpa [sub_eq_add_neg] using this

lemma bd_cancel {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bdd f) (hg : Bd 1 g)
    (hg' : ∀ r : ℝ, r < 1 → ∃ n, r < ‖coeff n g‖) (h : Bd B (f * g)) : Bd B f := by
  intro i
  have key := (sup_norm_laws q).2.2.2.1 f g B hf ⟨1, hg⟩ h i
  by_contra hlt
  push Not at hlt
  have hB : 0 ≤ B := (norm_nonneg _).trans (h 0)
  have hpos : 0 < ‖coeff i f‖ := hB.trans_lt hlt
  obtain ⟨n, hn⟩ := hg' (B / ‖coeff i f‖) ((div_lt_one hpos).2 hlt)
  have := key n
  rw [div_lt_iff₀ hpos] at hn
  nlinarith

lemma bd_cancel_prod {α : Type} (s : Finset α) (g : α → ℂ_[q]⟦X⟧) {B : ℝ}
    (hg : ∀ i, Bd 1 (g i)) (hg' : ∀ i, ∀ r : ℝ, r < 1 → ∃ n, r < ‖coeff n (g i)‖)
    {f : ℂ_[q]⟦X⟧} (hf : Bdd f) (h : Bd B (f * ∏ i ∈ s, g i)) : Bd B f := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    apply ih
    rw [Finset.prod_insert ha, mul_comm (g a), ← mul_assoc] at h
    obtain ⟨C, hC⟩ := hf
    exact bd_cancel ⟨C, bd_mul_one hC (bd_prod s g fun i _ => hg i)⟩ (hg a) (hg' a) h

lemma analyticAt_eval (p : Polynomial ℂ) {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (fun z => p.eval (F z)) z := by
  simp only [Polynomial.eval_eq_sum_range]
  exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (hF.pow i)

lemma hat_eval (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) (p : Polynomial ℂ)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    hat ι ℓ (fun z => p.eval (F z)) =
      p.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (ι : ℂ →+* ℂ_[q])) (hat ι ℓ F) := by
  obtain ⟨h1, h2, -⟩ := TaylorRead.hat_laws q ι ℓ hℓ
  induction p using Polynomial.induction_on with
  | C a => simpa using h2 a
  | add p r hp hr =>
    simp only [Polynomial.eval_add, Polynomial.eval₂_add]
    rw [(h1 _ _ (analyticAt_eval p hF) (analyticAt_eval r hF)).1, hp, hr]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc]
    simp only [Polynomial.eval_mul (q := Polynomial.X), Polynomial.eval_X, Polynomial.eval₂_mul_X]
    rw [(h1 _ _ (analyticAt_eval _ hF) hF).2.1, ih]

lemma bd_eval₂ (ι : ℂ ≃+* ℂ_[q]) (p : Polynomial ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ i ≤ p.natDegree, ‖ι (p.coeff i)‖ ≤ B) {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) :
    Bd B (p.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (ι : ℂ →+* ℂ_[q])) f) := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine bd_sum _ _ hB fun i hi => bd_mul_one (bd_C ?_) (bd_pow hf i)
  exact hp i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

lemma norm_coeff_prod (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (a : Fin m → ℂ) (ha : ∀ i, ‖ι (a i)‖ ≤ 1) (n : ℕ) :
    ‖ι ((∏ i, (Polynomial.X - Polynomial.C (a i))).coeff n)‖ ≤ 1 := by
  have h : Bd 1 (∏ i, (X - C (ι (a i)) : ℂ_[q]⟦X⟧)) :=
    bd_prod _ _ fun i _ => bd_sub_C bd_X (ha i)
  have e : (∏ i, (X - C (ι (a i)) : ℂ_[q]⟦X⟧)) =
      Polynomial.coeToPowerSeries.ringHom
        ((∏ i, (Polynomial.X - Polynomial.C (a i))).map (ι : ℂ →+* ℂ_[q])) := by
    simp [Polynomial.map_prod, map_prod]
  have := h n
  rw [e] at this
  simpa only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, Polynomial.coeff_map, RingHom.coe_coe] using this

lemma analyticAt_x_of_not_mem_lattice (M : Mdl q) {t : ℂ} (ht : t ∉ M.L.lattice) : AnalyticAt ℂ M.x t := by
  have := M.L.analyticOnNhd_weierstrassP t ht
  unfold Mdl.x
  fun_prop

lemma analyticAt_y (M : Mdl q) {t : ℂ} (ht : t ∉ M.L.lattice) : AnalyticAt ℂ M.y t := by
  have := M.L.analyticOnNhd_derivWeierstrassP t ht
  have := analyticAt_x_of_not_mem_lattice M ht
  unfold Mdl.y
  fun_prop

lemma analyticAt_shift {F : ℂ → ℂ} {t : ℂ} (hF : AnalyticAt ℂ F t) :
    AnalyticAt ℂ (fun z => F (z + t)) 0 :=
  AnalyticAt.comp_of_eq (g := F) (f := fun z => z + t) hF (by fun_prop) (by simp)

theorem translate_norm_le : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ) (t : ℂ) (B : ℝ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → AnalyticAt ℂ φ t → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → ¬ M.Small t → Bdd (hat M.ι ℓ (fun z => φ (z + t))) → Bd B (hat M.ι ℓ φ) → Bd B (hat M.ι ℓ (fun z => φ (z + t))) := by
  intro q _ M ℓ φ t B hc hE h0 ht hpole hts hbdd hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hℓ := hc.2.1
  obtain ⟨hl1, hl2, -⟩ := TaylorRead.hat_laws q M.ι ℓ hℓ
  obtain ⟨m, P, A, B', hP, hid⟩ := GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy q M φ hc.1 hE
  have hPx : ∀ i, ‖M.ι (M.x (P i))‖ ≤ 1 := fun i =>
    not_lt.1 fun h => hpole _ (hP i).2 (Or.inr h)
  obtain ⟨-, v, xs, ys, -, hxs, hys, -, hxs0, hys0, -, -, -, hread⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M ℓ hc
  set D : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hD
  set k := max A.natDegree B'.natDegree with hk
  have e0 := hread φ A B' k h0 (le_max_left _ _) (le_max_right _ _) (fun _ => 1) analyticAt_const
    D D.natDegree le_rfl (by simpa only [one_mul] using hid 0)
  have hS : Bd B (∑ i ∈ Finset.range (k + 1),
      (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * xs ^ i +
        C (M.ι (B'.coeff i)) * X ^ (2 * (k - i)) * xs ^ i * ys)) := by
    refine (sup_norm_laws q).2.2.2.2.2 _ 1 (2 * D.natDegree) B bd_one (by simp) ?_
    rw [hl2, map_one, map_one, one_mul] at e0
    rw [mul_one, ← e0]
    refine bd_mul_one (bd_mul_one hB (bd_pow bd_X _)) (bd_sum _ _ zero_le_one fun i _ => ?_)
    exact bd_mul_one (bd_mul_one (bd_C (norm_coeff_prod M.ι _ hPx i)) (bd_pow bd_X _)) (bd_pow hxs _)
  have hco := Triang.coeff_norm_le q xs ys k (fun i => M.ι (A.coeff i)) (fun i => M.ι (B'.coeff i)) B
    hxs hys hxs0 hys0 hS
  obtain ⟨hxt, hyt, hbig⟩ := GlobalTheory.T.chart_hat_coeff_bounds q M ℓ t hc hts
  have htl : t ∉ M.L.lattice := fun h => hts (Or.inl h)
  have ax := analyticAt_shift (analyticAt_x_of_not_mem_lattice M htl)
  have ay := analyticAt_shift (analyticAt_y M htl)
  have aφ := analyticAt_shift ht
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), φ (z + t) * D.eval (M.x (z + t)) =
      A.eval (M.x (z + t)) + B'.eval (M.x (z + t)) * M.y (z + t) := by
    have tt : Filter.Tendsto (fun z : ℂ => z + t) (𝓝[≠] 0) (𝓝[≠] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Filter.Tendsto (fun z : ℂ => z + t) (𝓝 0) (𝓝 (0 + t)) :=
          (continuous_id.add continuous_const).tendsto 0
        rw [zero_add] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    exact tt.eventually (hid t)
  have e1 := (hl1 _ _ (aφ.mul (analyticAt_eval D ax))
    ((analyticAt_eval A ax).add ((analyticAt_eval B' ax).mul ay))).2.2.1 hev
  have e2 := (hl1 _ _ aφ (analyticAt_eval D ax)).2.1
  have e3 := (hl1 _ _ (analyticAt_eval A ax) ((analyticAt_eval B' ax).mul ay)).1
  have e4 := (hl1 _ _ (analyticAt_eval B' ax) ay).2.1
  have e5 : hat M.ι ℓ (fun z => φ (z + t)) * hat M.ι ℓ (fun z => D.eval (M.x (z + t))) =
      hat M.ι ℓ (fun z => A.eval (M.x (z + t))) +
        hat M.ι ℓ (fun z => B'.eval (M.x (z + t))) * hat M.ι ℓ (fun z => M.y (z + t)) := by
    rw [← e2, ← e4]
    exact e1.trans e3
  rw [hat_eval _ _ hℓ D ax, hat_eval _ _ hℓ A ax, hat_eval _ _ hℓ B' ax] at e5
  have e6 : D.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (M.ι : ℂ →+* ℂ_[q]))
      (hat M.ι ℓ (fun z => M.x (z + t))) =
      ∏ i, (hat M.ι ℓ (fun z => M.x (z + t)) - C (M.ι (M.x (P i)))) := by
    rw [hD, Polynomial.eval₂_finsetProd]
    simp
  rw [e6] at e5
  refine bd_cancel_prod Finset.univ _ (fun i => bd_sub_C hxt (hPx i)) (fun i r hr => ?_) hbdd ?_
  · obtain ⟨n, hn, hn'⟩ := hbig r hr
    refine ⟨n, ?_⟩
    rwa [map_sub, coeff_C, if_neg hn.ne', sub_zero]
  · rw [e5]
    exact bd_add (bd_eval₂ _ _ hB0 (fun i hi => (hco i (hi.trans (le_max_left _ _))).1) hxt)
      (bd_mul_one (bd_eval₂ _ _ hB0 (fun i hi => (hco i (hi.trans (le_max_right _ _))).2) hxt) hyt)

end GlobalTheory.MomOne.TransNorm
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besPhInt_bilin {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp) :
    ∃ T : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wq) →L[ℂ] ℂ, ∀ P Q, T P Q = B.hsInner (P.comp (X.comp Q)) X' := by
  refine ⟨∑ i, ((ContinuousLinearMap.compL ℂ (Wq →L[ℂ] Wq) Wp ℂ (innerSL ℂ (X' (stdOrthonormalBasis ℂ Wq i)))).comp
    ((ContinuousLinearMap.compL ℂ (Wq →L[ℂ] Wq) Wp Wp).flip
      (X.comp (ContinuousLinearMap.apply ℂ Wq (stdOrthonormalBasis ℂ Wq i))))), fun P Q => ?_⟩
  simp [B.hsInner, B.hsVec, PiLp.inner_apply]

theorem besPhInt_rank {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp)
    (a a' : Wp) (b b' : Wq) :
    B.hsInner (((innerSL ℂ a).smulRight a').comp (X.comp ((innerSL ℂ b').smulRight b))) X' =
      ⟪a, X b⟫_ℂ * star ⟪a', X' b'⟫_ℂ := by
  have hb : X' b' = ∑ i, ⟪stdOrthonormalBasis ℂ Wq i, b'⟫_ℂ • X' (stdOrthonormalBasis ℂ Wq i) := by
    conv_lhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' b']

    simp [map_sum]
  have h2 : star ⟪a', X' b'⟫_ℂ = ⟪X' b', a'⟫_ℂ := inner_conj_symm _ _
  rw [h2, hb, sum_inner, Finset.mul_sum]
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul,
    inner_smul_right, inner_smul_left, inner_conj_symm]
  ring

theorem besPhInt_xi {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    B.xiTau D (1, 1) p = Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of p.1.2) *
      star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of p.2.2)) := by
  unfold B.xiTau Formalism.QuantumDeterminants.psi B.lam
  rw [show ∀ x : ℂ, star x = (starRingEnd ℂ) x from fun _ => rfl, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem besPhInt_xi_cont {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) :
    Continuous (B.xiTau D (1, 1)) := by
  have h : ∀ z, Continuous (fun m : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.ell k r z (Matrix.of m)) := by
    intro z
    unfold Formalism.QuantumDeterminants.ell
    refine continuous_finsetSum _ fun a _ => ?_
    split_ifs
    · simp only [Matrix.of_apply]
      fun_prop
    · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      fun_prop
  have h1 := (h D.z).comp (continuous_snd.comp (continuous_fst (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (Y := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)))
  have h2 := (h D.z').comp (continuous_snd.comp (continuous_snd (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (Y := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)))
  unfold B.xiTau B.lam
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h1))).sub
    (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h2)))

theorem integral_xi_mul_Ph : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' dd hDS _ _ hl hl' hdd x hx y hy x' hx' y' hy' X X'
  obtain ⟨hmul, hone, hinn, -, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  have hsf : ∀ {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}, B.IsHaarOn U μ → SigmaFinite μ := by
    intro U μ h
    have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    infer_instance
  haveI := hsf D.haarW
  haveI := hsf D.haarN
  haveI := hsf D.haarW'
  have hN := (GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN
  have hW := ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW).2.2 D.z D.z_mem D.T_pos D.k_pos).2 D.haarW
  have hW' := ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW').2.2 D.z' D.z'_mem D.T'_pos D.k_pos).2 D.haarW'
  obtain ⟨-, -, -, -, mA, aeA⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos hW hN
  obtain ⟨-, -, -, mB, -, aeB⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos hW' hN
  obtain ⟨psn, -, psinv, -, -, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  obtain ⟨psn', -, -, pscj, -, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  obtain ⟨iA, eA⟩ := hl.2 x' (hTK x' hx') x hx
  obtain ⟨iB, eB⟩ := hl'.2 y (hTK y hy) y' hy'
  have iA' := mA.integrable_comp_of_integrable iA
  have iB' := mB.integrable_comp_of_integrable iB
  have eA' := integral_map mA.measurable.aemeasurable (mA.map_eq.symm ▸ iA.aestronglyMeasurable)
  have eB' := integral_map mB.measurable.aemeasurable (mB.map_eq.symm ▸ iB.aestronglyMeasurable)
  rw [mA.map_eq] at eA'
  rw [mB.map_eq] at eB'
  unfold be at eA eB
  rw [eA] at eA'
  rw [eB] at eB'
  obtain ⟨T, hT⟩ := besPhInt_bilin X X'
  have hI := integral_prod_bilin T iA' iB'
  have hInt := iA'.op_fst_snd (op := fun P Q => T P Q) (by fun_prop) ⟨‖T‖, T.le_opNorm₂⟩ iB'
  simp only [Function.comp_apply] at hI hInt
  rw [← eA', ← eB', hT, besPhInt_rank] at hI
  have hae : ∀ᵐ p ∂D.μSS, D.inSS p := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae aeA,
      (Measure.quasiMeasurePreserving_snd (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae aeB] with p h1 h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have key : ∀ p : B.SS k r, D.inSS p →
      B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p =
      T (beInt D.z Formalism.QuantumDeterminants.cStd D.π R.σ x' x
          (((fun i j => ((Matrix.of p.1.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.1.2)⁻¹ : Mx k r) i j))))
        (beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y y'
          (((fun i j => (Matrix.of p.2.1 : Mx k r) i j),
            (fun i j => ((Matrix.of p.2.1)⁻¹ * Matrix.of p.2.2 * Matrix.of p.2.1 : Mx k r) i j)))) / (dd : ℂ) := by
    intro p hp
    rw [(GlobalTheory.T.bessel_formal_degree_identity hH k r ε mu R Wp Wq D dd hDS hdd x y x' y' X X' p hp).2, besPhInt_xi, ← hT]
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have hof : ∀ M : Mx k r, Matrix.of (fun i j => M i j) = M := fun M => rfl
    unfold beInt JF.sL JF.sR
    simp only [hof]
    generalize Matrix.of p.1.1 = a at *
    generalize Matrix.of p.1.2 = n at *
    generalize Matrix.of p.2.1 = a' at *
    generalize Matrix.of p.2.2 = n' at *
    obtain ⟨ai, aa, aa'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h1.1
    obtain ⟨ni, nn, nn'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h2.1
    obtain ⟨bi, bb, bb'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h3.1
    have e1 : a⁻¹⁻¹ = a := Matrix.inv_eq_right_inv aa'
    have e2 : a' * (a'⁻¹ * n' * a') = n' * a' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, bb, Matrix.one_mul]
    have e3 : ⟪x, R.σ (a⁻¹ * n⁻¹) x'⟫_ℂ = ⟪R.σ (n * a) x, x'⟫_ℂ := by
      have hna := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul h2.1 h1.1
      have hna' := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul ai ni
      rw [← hinn _ hna, ← hmul _ hna _ hna']
      have : n * a * (a⁻¹ * n⁻¹) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, aa, Matrix.one_mul, nn]
      rw [this, hone]
    rw [e1, e2, e3, (psinv n h2).2, (pscj a' h3 n' h4).2.2.2, star_star]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hae' := hae.mono key
  have hInt' : Integrable (fun p => B.xiTau D (1, 1) p *
      B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p) D.μSS :=
    (hInt.div_const (dd : ℂ)).congr (hae'.mono fun p hp => hp.symm)
  have hn : ∀ p, ‖B.xiTau D (1, 1) p‖ = 1 := by
    intro p
    rw [besPhInt_xi, norm_mul, norm_star, psn, psn', one_mul]
  refine ⟨?_, ?_⟩
  · have := hInt'.bdd_mul (c := 1) (f := fun p => star (B.xiTau D (1, 1) p))
      (besPhInt_xi_cont D).star.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by rw [norm_star, hn])
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    have h1 : star (B.xiTau D (1, 1) p) * B.xiTau D (1, 1) p = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hn]; simp
    simp only
    rw [← mul_assoc, h1, one_mul]
  · rw [integral_congr_ae hae', integral_div]
    exact congrArg (· / (dd : ℂ)) hI

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KappaDual

theorem mul_mem_GG {k r : ℕ} {g h : Mx k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r := by
  simp only [GG, Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hg hh ⊢
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem ae_pair {k r : ℕ} {U V : Set (Mx k r)} {μ ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : PI.BesselPeriodGGP.IsHaarOn V ν) :
    ∀ᵐ p ∂(μ.prod ν), Matrix.of p.1 ∈ U ∧ Matrix.of p.2 ∈ V := by
  haveI := hμ.1
  haveI := hν.1
  have h1 : ∀ᵐ x ∂μ, Matrix.of x ∈ U := ae_iff.2 hμ.2.2.1
  have h2 : ∀ᵐ x ∂ν, Matrix.of x ∈ V := ae_iff.2 hν.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)

theorem kappa_dual : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (l : R.H → Wp), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → IsBeL R z π μW μN l → NzOn R l → ∀ I lI, IsBeL (RI I) z π μW μN lI → (∃ κ₀ : ℂ, ∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ ∀ κ₀ : ℂ, (∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = ((ep I : ℂ) * star κ₀) • lI y := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ z π u μW μN μG νq om l hR hRI hF hT hS hom
    hl hnz I lI hlI
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hbes, hS_eq, hsm⟩ :=
    GlobalTheory.T.isBes_tensor_projection_and_ev_equivariant_smooth hK k r ι κ ρ Γ d R RI io pr ε mu muI Wp z π om hR hRI hF hT.raw hom I
  refine ⟨GlobalTheory.T.bessel_functional_side_growth hH k r ε mu R Wp z π u μW μN μG νq l _ hR hS hl.1 hnz (hbes lI hlI.1), ?_⟩
  intro κ₀ hκ y hy
  obtain ⟨v, hvTK, hv0⟩ := GlobalTheory.T.exists_K_type_nonzero_bessel hH k r ε mu R Wp z π l hR hl.1 hnz
  obtain ⟨-, -, -, -, hTKsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε mu R hR
  obtain ⟨-, -, -, hIsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε (muI I) (RI I) (hRI I)
  obtain ⟨hadj, -, hev, -⟩ := GlobalTheory.T.frep_discrete_series_sum hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT
  obtain ⟨-, -, -, hprTK⟩ := GlobalTheory.T.tensor_raw_of_frep hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw
  have hvsm : v ∈ R.sm := hTKsm v hvTK
  have htmTK : ∀ c, tm R om v c ∈ R.TK := fun c => R.TK.smul_mem _ hvTK
  have hPTK : (∑ c, pr I c (tm R om v c)) ∈ (RI I).TK :=
    Submodule.sum_mem _ fun c _ => hprTK I c _ (htmTK c)
  have h1 := (hl.2 _ (hsm.mem y hy) v hvTK).2
  have h2 := (hlI.2 y hy _ hPTK).2
  have h3 : be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (ev Γ R om (fun c => io I c y)) v =
      (ep I : ℂ) • be z Formalism.QuantumDeterminants.cStd π (RI I).σ μW μN y (∑ c, pr I c (tm R om v c)) := by
    unfold be
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [ae_pair hS.2.2.2.2.1 hS.2.2.2.2.2.1] with p hp
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Sset k r z := ⟨_, hp.1, _, hp.2, rfl⟩
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := mul_mem_GG hp.1.1 hp.2.1
    unfold beInt
    rw [← hS_eq _ hs y hy, ← hev, hadj I _ (hIsm _ hg y hy) _ (fun c => hTKsm _ (htmTK c)), smul_smul, mul_assoc]
  rw [h1, h2, hκ v hvsm] at h3
  have h4 := congrArg (fun T : Wp →L[ℂ] Wp => T (l v)) h3
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_left] at h4
  have hne : ⟪l v, l v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  apply smul_right_injective Wp hne
  simp only
  rw [h4, smul_smul, smul_smul]
  congr 1
  simp only [starRingEnd_apply]
  ring

end GlobalTheory.KappaDual
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.liesOverFramed_of_square_levelMoves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂ ≫ r' = d.r ≫ ρ → ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrMove ρ ν y y' → FrMove ρ₂ ν₂ y₂ y₂' → FrOver { d with r := r', m := m' } y₂' y' := by
  first | exact @GlobalTheory.frOver_of_square_of_frMove | exact GlobalTheory.frOver_of_square_of_frMove | (intros; apply GlobalTheory.frOver_of_square_of_frMove <;> assumption)
end
