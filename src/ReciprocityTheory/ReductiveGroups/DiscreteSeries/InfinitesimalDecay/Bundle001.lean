module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KsetMulConj

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem inG_rsum {ι : Type*} (s : Finset ι) (r : ι → ℝ) (X : ι → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ i ∈ s, inG ε (X i)) : inG ε (∑ i ∈ s, (r i : ℂ) • X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SmDerA.inG_zero ε
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact smc_inG_add (smc_inG_rsmul (hX a (Finset.mem_insert_self a s)) (r a))
      (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

theorem dS_rsum (hσ : IsURepOn (UJset ε) σ) {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (X : ι → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ i ∈ s, inG ε (X i)) {v : H} (hv : IsSmoothVecU ε σ v) :
    dS σ (∑ i ∈ s, (r i : ℂ) • X i) v = ∑ i ∈ s, (r i : ℂ) • dS σ (X i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SmDerA.dS_zero_mat (σ := σ) v
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, inG ε (X i) := fun i hi => hX i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, dS_add_smul hσ (inG_rsum s r X hs)
      (hX a (Finset.mem_insert_self a s)) (r a) hv, ih hs, add_comm]

theorem dS_vsum (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (v : ι → H) (hv : ∀ i ∈ s, IsSmoothVecU ε σ (v i)) :
    dS σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dS σ X (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dS_smul_vec (σ := σ) 0 X 0
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, IsSmoothVecU ε σ (v i) := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hsum : IsSmoothVecU ε σ (∑ i ∈ s, c i • v i) := by
      clear ih
      induction s using Finset.induction_on with
      | empty => simpa using (isSmoothVecU_zero : IsSmoothVecU ε σ (0 : H))
      | insert b t hb ih2 =>
        rw [Finset.sum_insert hb]
        exact ((hs b (Finset.mem_insert_self b t)).smul (c b)).add
          (ih2 (fun h => ha (Finset.mem_insert_of_mem h)) (fun i hi => hv i (by
            rcases Finset.mem_insert.1 hi with rfl | hi
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)))
            (fun i hi => hs i (Finset.mem_insert_of_mem hi)))
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dS_add_vec hσ hX ((hv a (Finset.mem_insert_self a s)).smul _)
      hsum, dS_smul_vec, ih hs]

theorem inG_expand {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) :
    Y = ∑ p : (Fin n × Fin n) × Bool, ((cond p.2 (Y p.1.1 p.1.2).re (-(Y p.1.1 p.1.2).im) : ℝ) : ℂ) •
      cond p.2 (S7.cpart1 ε (Matrix.single p.1.1 p.1.2 1)) (S7.cpart2 ε (Matrix.single p.1.1 p.1.2 1)) := by
  classical
  have hY1 : S7.cpart1 ε Y = Y := ((smc_cpart Y).2.2.2 hY).1
  set L : Matrix (Fin n) (Fin n) ℂ →+ Matrix (Fin n) (Fin n) ℂ :=
    { toFun := S7.cpart1 ε, map_zero' := by simpa using smc_cpart1_real (ε := ε) 0 0,
      map_add' := smc_cpart1_add }
  have hdec : Y = ∑ p : Fin n × Fin n, (((Y p.1 p.2).re : ℂ) • Matrix.single p.1 p.2 1 +
      ((Y p.1 p.2).im : ℂ) • (Complex.I • Matrix.single p.1 p.2 1)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    rw [smul_smul, ← add_smul, Complex.re_add_im, Matrix.smul_single, smul_eq_mul, mul_one]
  have h2 : Y = ∑ p : Fin n × Fin n, (((Y p.1 p.2).re : ℂ) • S7.cpart1 ε (Matrix.single p.1 p.2 1) +
      ((-(Y p.1 p.2).im : ℝ) : ℂ) • S7.cpart2 ε (Matrix.single p.1 p.2 1)) := by
    conv_lhs => rw [← hY1, hdec]
    change L (∑ p : Fin n × Fin n, _) = _

    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    change S7.cpart1 ε _ = _
    rw [smc_cpart1_add, smc_cpart1_real, smc_cpart1_real, smc_cpart1_I, Complex.ofReal_neg, smul_neg, neg_smul]
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [h2]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_bool]
  simp only [cond_true, cond_false]

def FinCont (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (z : S7.KG ε → H) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (d : ι → S7.KG ε → ℂ) (v : ι → H),
    (∀ i, Continuous (d i)) ∧ (∀ i, IsSmoothVecU ε σ (v i)) ∧ ∀ k, z k = ∑ i, d i k • v i

theorem finCont_step (hσ : IsURepOn (UJset ε) σ) {z : S7.KG ε → H} (hz : FinCont ε σ z)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    FinCont ε σ (fun k => dS σ ((S7.toMK k)ᴴ * X * S7.toMK k) (z k)) := by
  classical
  obtain ⟨ι, _, d, v, hd, hv, hz⟩ := hz
  set Y : S7.KG ε → Matrix (Fin n) (Fin n) ℂ := fun k => (S7.toMK k)ᴴ * X * S7.toMK k
  have hYc : Continuous Y := by
    have hc := S7.IdA.continuous_toMK (ε := ε)
    exact (hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc
  have hYg : ∀ k, inG ε (Y k) := fun k => inG_conj_K k.2 hX
  set B : (Fin n × Fin n) × Bool → Matrix (Fin n) (Fin n) ℂ := fun p =>
    cond p.2 (S7.cpart1 ε (Matrix.single p.1.1 p.1.2 1)) (S7.cpart2 ε (Matrix.single p.1.1 p.1.2 1))
  have hB : ∀ p, inG ε (B p) := by
    rintro ⟨q, _ | _⟩
    · exact (smc_cpart _).2.1
    · exact (smc_cpart _).1
  set r : S7.KG ε → (Fin n × Fin n) × Bool → ℝ := fun k p =>
    cond p.2 (Y k p.1.1 p.1.2).re (-(Y k p.1.1 p.1.2).im)
  refine ⟨ι × ((Fin n × Fin n) × Bool), inferInstance, fun q k => d q.1 k * (r k q.2 : ℂ),
    fun q => dS σ (B q.2) (v q.1), fun q => ?_, fun q => dS_smooth hσ (hB q.2) (hv q.1), fun k => ?_⟩
  · refine (hd q.1).mul (Complex.continuous_ofReal.comp ?_)
    have hent : Continuous fun k => Y k q.2.1.1 q.2.1.2 :=
      (continuous_apply q.2.1.2).comp ((continuous_apply q.2.1.1).comp hYc)
    rcases q with ⟨i, q, _ | _⟩
    · exact (Complex.continuous_im.comp hent).neg
    · exact Complex.continuous_re.comp hent
  · show dS σ (Y k) (z k) = _
    rw [hz k, dS_vsum hσ (hYg k) _ _ _ fun i _ => hv i, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [inG_expand (hYg k)]
    rw [dS_rsum hσ _ _ _ (fun p _ => hB p) (hv i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only [r]
    rw [smul_smul, mul_comm]

theorem finCont_dSW (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {u : H} (hu : IsSmoothVecU ε σ u) :
    FinCont ε σ (fun k => dSW σ (w.map fun X => (S7.toMK k)ᴴ * X * S7.toMK k) u) := by
  induction w with
  | nil => exact ⟨Unit, inferInstance, fun _ _ => 1, fun _ => u, fun _ => continuous_const, fun _ => hu,
      fun k => by simp [dSW]⟩
  | cons X w ih =>
    exact finCont_step hσ (ih fun Y hY => hw Y (List.mem_cons_of_mem X hY)) (hw X List.mem_cons_self)

theorem continuous_dSW_orbit (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)}
    (hw : ∀ X ∈ w, inG ε X) {u : H} (hu : IsSmoothVecU ε σ u) :
    Continuous fun k : S7.KG ε => dSW σ w (σ (S7.toMK k) u) := by
  obtain ⟨ι, _, d, v, hd, -, hz⟩ := finCont_dSW hσ hw hu
  have e : (fun k : S7.KG ε => dSW σ w (σ (S7.toMK k) u)) =
      fun k => ∑ i, d i k • σ (S7.toMK k) (v i) := by
    funext k

    rw [dSW_conj hσ (k := S7.toMK k) k.2 hw hu, show dSW σ (w.map fun X => (S7.toMK k)ᴴ * X * S7.toMK k) u = _ from hz k, map_sum]
    simp only [map_smul]
  rw [e]
  refine continuous_finsetSum _ fun i _ => (hd i).smul ?_
  exact (hσ.2.2 (v i)).comp_continuous S7.IdA.continuous_toMK fun k => smd_inUJ_of_Kset k.2
end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section

set_option autoImplicit false

noncomputable section

open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem br_facts {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) :
    P⁻¹ = Pᴴ ∧ P * Pᴴ = 1 ∧ Pᴴ * P = 1 ∧ Jm ε = P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
  obtain ⟨⟨_, hJ⟩, hU⟩ := hP
  have h1 : P * Pᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : Pᴴ * P = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hU
    rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨Matrix.inv_eq_left_inv h2, h1, h2, ?_⟩
  have hJe : Jm ε = Formalism.REAL.Jm ε := rfl
  rw [hJe, ← hJ]
  calc Formalism.REAL.Jm ε = (P * Pᴴ) * Formalism.REAL.Jm ε * (P * Pᴴ) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by simp only [Matrix.mul_assoc]

theorem bridge_group {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ↔ P * g * P⁻¹ ∈ UJset ε := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have hJ' : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have key : ∀ Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Y * Pᴴ) * P = Y := fun Y => by
    calc Pᴴ * (P * Y * Pᴴ) * P = (Pᴴ * P) * Y * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  have e : (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = P * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * Pᴴ := by
    rw [hinv, ← hJ']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  show gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r ↔ inUJ ε (P * g * P⁻¹)
  unfold inUJ
  rw [e, hJ]
  constructor
  · intro h
    rw [h]
  · intro h
    have := congrArg (fun M => Pᴴ * M * P) h
    simp only [key] at this
    exact this

theorem bridge_lie {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.MainNotions.S.InLieHpk k r X ↔ inG ε (P * X * P⁻¹) := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have h2' : ∀ Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have key : ∀ Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Y * Pᴴ) * P = Y := fun Y => by
    calc Pᴴ * (P * Y * Pᴴ) * P = (Pᴴ * P) * Y * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  have e : (P * X * P⁻¹)ᴴ * Jm ε + Jm ε * (P * X * P⁻¹) =
      P * (Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X) * Pᴴ := by
    rw [hinv, hJ]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc, h2']
  show Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 ↔ inG ε (P * X * P⁻¹)
  unfold inG
  rw [e]
  constructor
  · intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    have := congrArg (fun M => Pᴴ * M * P) h
    simp only [key, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this

theorem bridge_gN {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g = Real.sqrt (S7.hs (P * g * P⁻¹)) := by
  obtain ⟨hi, h2, h1, -⟩ := br_facts hP
  have key : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      ∑ i, ∑ j, ‖M i j‖ ^ 2 = (Matrix.trace (Mᴴ * M)).re := by
    intro M
    rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.mul_re]
  unfold Formalism.FourierDecayAlt.B.gN S7.hs
  congr 1
  have e1 : ∑ i, ∑ j, Complex.normSq (g i j) = ∑ i, ∑ j, ‖g i j‖ ^ 2 := by
    simp [Complex.normSq_eq_norm_sq]
  have e2 : (P * g * Pᴴ)ᴴ * (P * g * Pᴴ) = P * ((gᴴ * g) * Pᴴ) := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul]
  have L : ∑ i, ∑ j, ‖g i j‖ ^ 2 = (gᴴ * g).trace.re := key g
  have R : ∑ i, ∑ j, ‖(P * g * Pᴴ) i j‖ ^ 2 = ((P * g * Pᴴ)ᴴ * (P * g * Pᴴ)).trace.re := key _
  rw [e1, hi, L, R, e2, Matrix.trace_mul_comm P, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem bridge_smooth {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v : H) :
    v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ ↔ IsSmoothVecU ε (fun g => σ (P⁻¹ * g * P)) v := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have hPu : IsUnit P := hP.1.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  let cA : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ P⁻¹).comp (LinearMap.mulRight ℝ P))
  let cB : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ P).comp (LinearMap.mulRight ℝ P⁻¹))
  have hcA : ∀ g, cA g = P⁻¹ * g * P := fun g => by simp [cA, Matrix.mul_assoc]
  have hcB : ∀ g, cB g = P * g * P⁻¹ := fun g => by simp [cB, Matrix.mul_assoc]
  have hAB : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul P hPd, Matrix.mul_one]
  have hBA : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P hPd, Matrix.mul_one]
  have hmem : ∀ g, Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) g ↔ inUJ ε (P * g * P⁻¹) := fun g => bridge_group hP g
  simp only [Formalism.MainNotions.S.smoothVecs, Set.mem_setOf_eq, Formalism.MainNotions.S.IsSmoothVec, IsSmoothVecU]
  constructor
  · intro hv g₀ hg₀
    have hg₁ : Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) (P⁻¹ * g₀ * P) := (hmem _).2 (by rw [hBA]; exact hg₀)
    obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hv _ hg₁
    refine ⟨cA ⁻¹' U, F ∘ cA, hU.preimage cA.continuous, by simp [hcA, hxU],
      hF.comp cA.contDiff.contDiffOn (fun x hx => hx), fun g hg hgJ => ?_⟩
    have hgH : Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) (P⁻¹ * g * P) := (hmem _).2 (by rw [hBA]; exact hgJ)
    have h3 := hfF _ (by simpa [hcA] using hg) hgH
    simp only at h3
    simp only [Function.comp_apply, hcA]
    exact h3
  · intro hv g₀ hg₀
    have hg₁ : inUJ ε (P * g₀ * P⁻¹) := (hmem g₀).1 hg₀
    obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hv _ hg₁
    refine ⟨cB ⁻¹' U, F ∘ cB, hU.preimage cB.continuous, by simp [hcB, hxU],
      hF.comp cB.contDiff.contDiffOn (fun x hx => hx), fun g hg hgH => ?_⟩
    have h3 := hfF _ (by simpa [hcB] using hg) ((hmem g).1 hgH)
    simp only at h3
    simp only [Function.comp_apply, hcB]
    rw [← h3, hAB]

theorem bridge_dsigW {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v =
      dSW (fun g => σ (P⁻¹ * g * P)) (w.map fun X => P * X * P⁻¹) v := by
  have hPu : IsUnit P := hP.1.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hE : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (t : ℝ),
      P⁻¹ * NormedSpace.exp ((t : ℂ) • (P * X * P⁻¹)) * P = NormedSpace.exp ((t : ℂ) • X) := by
    intro X t
    have e1 : ((t : ℂ) • (P * X * P⁻¹)) = P * ((t : ℂ) • X) * P⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, Matrix.exp_conj P ((t : ℂ) • X) hPu]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.mul_one]
  have hconj : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (u : H),
      Formalism.MainNotions.S.dsig (k := k) (r := r) σ X u = dS (fun g => σ (P⁻¹ * g * P)) (P * X * P⁻¹) u := by
    intro X u
    unfold Formalism.MainNotions.S.dsig dS
    simp only [hE]
  induction w generalizing v with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v) =
      dS (fun g => σ (P⁻¹ * g * P)) (P * X * P⁻¹) (dSW (fun g => σ (P⁻¹ * g * P)) (w.map fun X => P * X * P⁻¹) v)
    rw [ih, hconj]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
