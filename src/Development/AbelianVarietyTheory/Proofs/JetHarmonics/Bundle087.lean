module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.LocalToGlobal.CharacterGerms.Bundle002
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle083
public import Mathlib.Algebra.Field.ZMod
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMatrixStandardToHyperbolicInertPlace
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle081
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle082
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

private lemma inv_conj_mul_conj {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q)
    (A B : Matrix (Fin n) (Fin n) ℂ) : (Q⁻¹ * A * Q) * (Q⁻¹ * B * Q) = Q⁻¹ * (A * B) * Q := by
  have h : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
  calc (Q⁻¹ * A * Q) * (Q⁻¹ * B * Q) = Q⁻¹ * A * (Q * Q⁻¹) * B * Q := by
        simp only [Matrix.mul_assoc]
    _ = Q⁻¹ * (A * B) * Q := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private lemma single_one_mul_single_one_jet_harmonics {n : ℕ} (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · simp [h]

theorem conj_single_comm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
      (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q) =
    (if b = c then Q⁻¹ * Matrix.single a d 1 * Q else 0) -
      (if d = a then Q⁻¹ * Matrix.single c b 1 * Q else 0) := by
  rw [inv_conj_mul_conj Q hQ, inv_conj_mul_conj Q hQ, ← Matrix.sub_mul, ← Matrix.mul_sub,
    single_one_mul_single_one_jet_harmonics, single_one_mul_single_one_jet_harmonics]
  split_ifs <;> simp [Matrix.mul_sub, Matrix.sub_mul]

theorem smooth_gl_module : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  intro hK k r ε mu R hDS Q hQ
  obtain ⟨hmem, hlin, hadd, -, hbr, -⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hDS
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hz : ∀ Y, R.dC Y 0 = 0 := fun Y => by
    have h := hlin Y 1 0 h0 0 h0
    simpa using h
  have hY0 : ∀ v ∈ R.sm, R.dC 0 v = 0 := fun v hv => by
    have h := hadd 0 0 1 v hv
    simpa using h
  have hsub : ∀ Y Z, ∀ v ∈ R.sm, R.dC (Y - Z) v = R.dC Y v - R.dC Z v := fun Y Z v hv => by
    have h := hadd Z (Y - Z) 1 v hv
    simp only [one_smul, add_sub_cancel] at h
    rw [h, add_sub_cancel_left]
  let E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub := fun a b =>
    { toFun := fun v => ⟨R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v, hmem _ v v.2⟩
      map_add' := fun v w => Subtype.ext (by simpa using hlin _ 1 v v.2 w w.2)
      map_smul' := fun c v => Subtype.ext (by simpa [hz] using hlin _ c v v.2 0 h0) }
  refine ⟨E, fun a b v => rfl, ?_⟩
  intro a b c d
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have lhs : (((E a b * E c d - E c d * E a b) v : R.smSub) : R.H) =
      R.dC ((Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
        (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q)) v := by
    rw [← hbr _ _ v v.2]; rfl
  rw [lhs, conj_single_comm Q hQ a b c d, hsub _ _ v v.2]
  split_ifs <;> simp [E, hY0 v v.2]

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem conj_expand_units {n : ℕ} (Q Y : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) :
    Y = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have h2 : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q)
      = Q⁻¹ * (∑ a, ∑ b, Matrix.single a b ((Q * Y * Q⁻¹) a b)) * Q := by
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h2, ← Matrix.matrix_eq_sum_single]
  calc Y = (Q⁻¹ * Q) * Y * (Q⁻¹ * Q) := by rw [h1]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

theorem conj_units_mul {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = (if b = c then (1 : ℂ) else 0) • (Q⁻¹ * Matrix.single a d (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have : (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = Q⁻¹ * (Matrix.single a b (1 : ℂ) * (Q * Q⁻¹) * Matrix.single c d (1 : ℂ)) * Q := by
    simp only [Matrix.mul_assoc]
  rw [this, h1, Matrix.mul_one]
  by_cases h : b = c
  · subst h
    simp [Matrix.single_mul_single_same]
  · simp [h, Matrix.single_mul_single_of_ne _ _ _ _ h]

theorem dC_expand_units : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  intro hK k r ε mu R hR Q E hQ hE
  obtain ⟨-, -, hlin, hX, hbr, -⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hL : ∀ v : R.smSub, ∃ L : Mx k r →ₗ[ℂ] R.H, ∀ Y, L Y = R.dC Y v := by
    intro v
    have hv : (v : R.H) ∈ R.sm := v.2
    have h0 : R.dC 0 v = 0 := by
      have := hlin 0 0 1 v hv
      simpa using this
    refine ⟨{ toFun := fun Y => R.dC Y v, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
    · intro Y Z
      simpa using hlin Y Z 1 v hv
    · intro a Y
      simpa [h0] using hlin Y 0 a v hv
  have hexp : ∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
    intro Y v
    obtain ⟨L, hLv⟩ := hL v
    rw [← hLv]
    conv_lhs => rw [conj_expand_units Q Y hQ]

    simp only [map_sum, map_smul]
    simp only [hLv, hE _ _ v]
  refine ⟨?_, hexp, fun X hXl v => ?_⟩
  · intro a b c d
    ext v
    obtain ⟨L, hLv⟩ := hL v
    have := hbr (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v v.2
    rw [conj_units_mul Q hQ, conj_units_mul Q hQ, ← hLv (_ - _), map_sub, map_smul, map_smul, hLv, hLv,
      ← hE, ← hE, ← hE, ← hE, ← hE, ← hE] at this
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
    rw [this]
    congr 1 <;> split_ifs <;> simp_all
  · rw [← hX X hXl v v.2, hexp]

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNilp

variable {k r : ℕ}

theorem H_ne {i j : Fin (2 * r + k + 1)} (h : Formalism.QuantumDeterminants.Hpk k r i j ≠ 0) :
    (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨
      (r ≤ i.val ∧ i.val ≤ r + k ∧ i.val = j.val) := by
  unfold Formalism.QuantumDeterminants.Hpk at h
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · exact Or.inl h1
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · exact Or.inr (Or.inl h2)
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · exact Or.inr (Or.inr ⟨h3.1, h3.2.1, congrArg Fin.val h3.2.2⟩)
  · rw [if_neg h1, if_neg h2, if_neg h3] at h
    exact absurd rfl h

theorem H_herm : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, Formalism.QuantumDeterminants.Hpk]
  have hi := i.isLt
  have hj := j.isLt
  simp only [Fin.ext_iff]
  split_ifs <;> first | omega | simp

theorem H_sq : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply]
  by_cases hm : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · simp only [Formalism.QuantumDeterminants.Hpk, Matrix.one_apply, Fin.ext_iff, and_true]
      split_ifs <;> first | omega | simp
    · intro b _ hb
      have : Formalism.QuantumDeterminants.Hpk k r i b = 0 := by
        by_contra hne
        have h1 := H_ne hne
        have : b.val ≠ i.val := fun e => hb (Fin.ext e)
        omega
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · simp only [Formalism.QuantumDeterminants.Hpk, Matrix.one_apply, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · intro b _ hb
      have : Formalism.QuantumDeterminants.Hpk k r i b = 0 := by
        by_contra hne
        have h1 := H_ne hne
        have : b.val ≠ 2 * r + k - i.val := fun e => hb (Fin.ext e)
        omega
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

def Pat (Y : Mx k r) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → Y i j = 0

theorem pat_theta {Y : Mx k r} (hY : Pat Y) : Pat (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : Formalism.QuantumDeterminants.Hpk k r b j = 0
  · rw [hb, mul_zero]
  rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
  intro a _
  by_cases ha : Formalism.QuantumDeterminants.Hpk k r i a = 0
  · rw [ha, zero_mul]
  have h1 := H_ne ha
  have h2 := H_ne hb
  have : Y b a = 0 := by
    apply hY
    rw [Fin.lt_def] at hij ⊢
    omega
  rw [conjTranspose_apply, this, star_zero, mul_zero]

theorem ell_add (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    Formalism.QuantumDeterminants.ell k r z (A + B) = Formalism.QuantumDeterminants.ell k r z A + Formalism.QuantumDeterminants.ell k r z B := by
  unfold Formalism.QuantumDeterminants.ell
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rfl
  · rw [Matrix.add_mulVec]; rfl

theorem ell_smul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (A : Mx k r) :
    Formalism.QuantumDeterminants.ell k r z (c • A) = c * Formalism.QuantumDeterminants.ell k r z A := by
  unfold Formalism.QuantumDeterminants.ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rfl
  · rw [Matrix.smul_mulVec]; rfl

theorem ell_sub (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    Formalism.QuantumDeterminants.ell k r z (A - B) = Formalism.QuantumDeterminants.ell k r z A - Formalism.QuantumDeterminants.ell k r z B := by
  have : A - B = A + (-1 : ℂ) • B := by simp [sub_eq_add_neg]
  rw [this, ell_add, ell_smul]; ring

theorem theta_key (Y : Mx k r) :
    (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * Y ∧
    Formalism.QuantumDeterminants.Hpk k r * (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r) = Yᴴ * Formalism.QuantumDeterminants.Hpk k r := by
  constructor
  · rw [conjTranspose_mul, conjTranspose_mul, H_herm, conjTranspose_conjTranspose, Matrix.mul_assoc,
      Matrix.mul_assoc, H_sq, Matrix.mul_one]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, H_sq, Matrix.one_mul]

theorem lie_re (Y : Mx k r) : PI.UpqRep.InLieHpk k r
    ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  show _ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * _ = 0
  obtain ⟨h1, h2⟩ := theta_key Y
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, conjTranspose_add,
    conjTranspose_neg, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, h1, h2]
  simp

theorem lie_im (Y : Mx k r) : PI.UpqRep.InLieHpk k r
    ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  show _ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * _ = 0
  obtain ⟨h1, h2⟩ := theta_key Y
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
  rw [conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, neg_smul, neg_add_eq_zero, sub_neg_eq_add,
    conjTranspose_add, Matrix.add_mul, Matrix.mul_add, h1, h2, add_comm (Yᴴ * _)]

theorem on_real (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDS ε mu) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {l : R.H → Wp}
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hπ : ∀ x, π 1 x = x) (hl : IsBes R z π l) {X : Mx k r}
    (hX : PI.UpqRep.InLieHpk k r X) (hP : Pat X) {v : R.H} (hv : v ∈ R.sm) :
    l (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) =
      (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) • l v := by
  obtain ⟨hadd, hsmul, heq, hc⟩ := hl
  obtain ⟨hN, hd⟩ := GlobalTheory.T.exp_mem_unipotent_and_hasDerivAt_character k r z X hz hX hP
  have h1 := (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hadd hsmul hc v hv).2 X hX
  have h2 := hd.smul_const (l v)
  have hone : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z := by
    refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
    show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  have e : (fun t : ℝ => l (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) =
      fun t : ℝ => Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (NormedSpace.exp ((t : ℂ) • X)) • l v := by
    funext t
    have := heq 1 hone _ (hN t) v hv
    rwa [Matrix.one_mul, hπ] at this
  rw [e] at h1
  exact h1.unique h2

theorem bessel_dC : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), Formalism.QuantumDeterminants.inWb k r z → (∀ x, π 1 x = x) → IsBes R z π l → ∀ Y : Mx k r, (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → Y i j = 0) → ∀ v ∈ R.sm, l (R.dC Y v) = (Formalism.QuantumDeterminants.ell k r z Y - star (Formalism.QuantumDeterminants.ell k r z (-((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r))))) • l v := by
  intro hK k r ε mu R hR Wp _ _ _ _ z π l hz hπ hl Y hY v hv
  have hθ := pat_theta (Y := Y) hY
  have p1 : Pat ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
    intro i j hij
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, hY i j hij, hθ i j hij]
    simp
  have p2 : Pat ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
    intro i j hij
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, hY i j hij, hθ i j hij]
    simp
  have s1 := GlobalTheory.DerivedAction.dsig_smooth hR.2 (lie_re Y) hv
  have s2 := GlobalTheory.DerivedAction.dsig_smooth hR.2 (lie_im Y) hv
  have e1 := on_real hK hR hz hπ hl (lie_re Y) p1 hv
  have e2 := on_real hK hR hz hπ hl (lie_im Y) p2 hv
  unfold Rep.dC
  rw [hl.1 _ s1 _ (R.smSub.smul_mem Complex.I s2), hl.2.1 _ _ s2, e1, e2, smul_smul, ← add_smul,
    ell_smul, ell_smul, ell_add, ell_sub]
  congr 1
  have hI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
    field_simp
    simp
  rw [hI]
  simp only [star_mul', star_add, star_sub, star_neg, star_div₀, star_one, star_ofNat, Complex.star_def,
    Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

end GlobalTheory.BesselNilp
end
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem entire_eq_of_eq_on_reals {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (p q : ℂ → E) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (h : ∀ y : ℝ, p y = q y) : p = q := by
  have hp' : AnalyticOnNhd ℂ p Set.univ := fun z _ => hp.analyticAt z
  have hq' : AnalyticOnNhd ℂ q Set.univ := fun z _ => hq.analyticAt z
  refine AnalyticOnNhd.eq_of_frequently_eq (z₀ := ((0 : ℝ) : ℂ)) hp' hq' ?_
  have ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (nhdsWithin 0 {0}ᶜ)
      (nhdsWithin ((0 : ℝ) : ℂ) {((0 : ℝ) : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      intro h0
      exact hy (Complex.ofReal_injective h0)
  exact ht.frequently (Filter.Frequently.of_forall h)

theorem capelli_eigen_real_to_complex :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) f → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∀ Y : ℂ, ∀ g ∈ B.GV k r, Q.CV k r Y f g = (∏ s, (Y + (lam s : ℂ))) • f g := by
  intro k r Wp Wq _ _ _ _ _ _ lam f hf hR Y g hg
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hs : Q.SmoothLev k r 0 Set.univ f := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀.1.1
    exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hff g hg hgl.1⟩
  have hg0 : g ∈ Q.Glev k r 0 := ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  have h0 : Formalism.QuantumDeterminants.inWb k r 0 := by
    unfold Formalism.QuantumDeterminants.inWb
    simp
  obtain ⟨A, hA⟩ := Formalism.FourierDecayAlt.P.leading_term_alt (Wq →L[ℂ] Wp) k r 0 0 0 h0 h0
  have hpoly : (fun Y : ℂ => Q.CV k r Y f g) = fun Y : ℂ => Y ^ Q.mdim k r 0 • f g +
      ∑ j ∈ Finset.range (Q.mdim k r 0), Y ^ j • A 0 0 j f g := by
    funext Y
    exact (hA Set.univ f isOpen_univ hs g ⟨hg0, trivial⟩ Y).1
  have key := entire_eq_of_eq_on_reals (fun Y : ℂ => Q.CV k r Y f g)
    (fun Y : ℂ => (∏ s, (Y + (lam s : ℂ))) • f g) (by rw [hpoly]; fun_prop)
    (by
      refine Differentiable.smul_const ?_ _
      exact Differentiable.fun_finsetProd fun s _ => by fun_prop)
    (fun y => by
      show Q.CV k r (y : ℂ) f g = _
      rw [hR y g hg]; push_cast; rfl)
  exact congrFun key Y

end GlobalTheory
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.mvPowerSeries_lthPower_of_pderiv_vanish_mod_maximal : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) [Fintype σ], (∀ b : MvPowerSeries σ C, IntS V b → (∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv (R := C) i b))) → ∃ b' : MvPowerSeries σ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (b - b' ^ V.l))) ∧ (∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → (∀ μ, V.MM (MvPowerSeries.coeff μ (f ^ V.l - g ^ V.l))) → ∀ μ, V.MM (MvPowerSeries.coeff μ (f - g))) ∧ ∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → ∀ μ, V.MM (MvPowerSeries.coeff μ ((f + g) ^ V.l - f ^ V.l - g ^ V.l)) ∧ V.MM (MvPowerSeries.coeff μ ((f - g) ^ V.l - (f ^ V.l - g ^ V.l))) := by
  first | exact @GlobalTheory.SeriesFrobRoot.main | exact GlobalTheory.SeriesFrobRoot.main | (intros; apply GlobalTheory.SeriesFrobRoot.main <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_matrix_standard_to_hyperbolic_inertPlace : ∀ (C : Type) [Field C] [CharZero C] [IsAlgClosed C] (V : VF C), V.l ≠ 2 → (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → ∀ (O : Type) [CommRing O] [StarRing O] (em : ZMod 2 → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∃ x, V.v (em 0 x - em 1 x) = 0) → (∀ a x, em a (star x) = em (a + 1) x) → ∃ gm : ZMod 2 → Matrix (Fin 2) (Fin 2) C, (∀ N : ℕ, ∃ M : Matrix (Fin 2) (Fin 2) O, ∀ a r s, V.Ge N (gm a r s - em a (M r s))) ∧ ∀ a (s s' : Fin 2), ∑ r, gm (a + 1) r s * gm a r s' = if s = s' then 0 else 1 := by
  first | exact @GlobalTheory.InertHyperbolic.main | exact GlobalTheory.InertHyperbolic.main | (intros; apply GlobalTheory.InertHyperbolic.main <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.flag_of_letterNumbering_rowData : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (A : Fin 2 → Type) [∀ g, Fintype (A g)] (m : ∀ g, A g → ℕ) (ty : ∀ g, A g ≃ ZMod d) (J : Fin 2 → Type) [∀ g, Fintype (J g)] (X : RowData C V d (fun g => Σ s : A g, Fin (m g s)) J), (∀ g x, (X.G g).ty (Sum.inl x) = ty g x.1) → (∀ g s, X.rkF g (ty g s) = m g s) ∧ ∃ F : RF.Flag X, ∀ g a c, (F.en g a c).1 = (ty g).symm a ∧ ((F.en g a c).2 : ℕ) = c := by
  first | exact @GlobalTheory.flag_of_numbering | exact GlobalTheory.flag_of_numbering | (intros; apply GlobalTheory.flag_of_numbering <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant : ∀ (k r : ℕ), PI.IsMatGroup (GG k r) ∧ ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → PI.IsHaarOnM (GG k r) μG ∧ PI.IsRightInvM (GG k r) μG := by
  first | exact @GlobalTheory.unitaryGroup_matGroup_unimodular | exact GlobalTheory.unitaryGroup_matGroup_unimodular | (intros; apply GlobalTheory.unitaryGroup_matGroup_unimodular <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusExtension_over_completeLocal_dvr : Laws → Laws4 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (O : Type) [CommRing O] [IsLocalRing O] (f : V →+* O), IsLocalHom f → IsAdicComplete ((maximalIdeal V).map f) O → (∀ a ∈ maximalIdeal O, ∃ n : ℕ, a ^ n ∈ (maximalIdeal V).map f) → ∃ (Ex : SplitExt (Spec (CommRingCat.of O))) (B : PolAV (Spec (CommRingCat.of O))) (_ : B.A = Ex.B) (_ : HEq B.grp Ex.grpB) (Gt : Over (Spec (CommRingCat.of O))) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (ρ : RingAct Gt (𝓞 E)) (J : ∀ (A : Type) [CommRing A] [Algebra O A], ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → (specO O A ⟶ Gt) → (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G)), Ex.IsGt Gt ∧ (∀ N : ℕ, 1 ≤ N → IsFinite (torsion Ex.B N).hom ∧ Flat (torsion Ex.B N).hom) ∧ (∀ (A A' : Type) [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A'] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)) (hA' : ((Module.Finite O A' ∧ Module.Free O A') ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A' (f a) = 0)) (φ : A →ₐ[O] A') (x : specO O A ⟶ Gt), (J A' hA' (ptMap φ ≫ x)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J A hA x).left) ∧ ∀ (A : Type) [CommRing A] [Algebra O A] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)), (∀ x x', J A hA (x * x') = J A hA x * J A hA x') ∧ (∀ x (a : 𝓞 E), J A hA (x ≫ ρ.act a) = J A hA x ≫ t.act.act a) ∧ Function.Injective (J A hA) ∧ ((∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → Function.Surjective (J A hA)) ∧ ∀ (I : Ideal A) (g : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G), IsNilpotent I → Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g.left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (1 : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G).left → ∃ x, J A hA x = g := by
  first | exact @GlobalTheory.TorusModel.main | exact GlobalTheory.TorusModel.main | (intros; apply GlobalTheory.TorusModel.main <;> assumption)
end
