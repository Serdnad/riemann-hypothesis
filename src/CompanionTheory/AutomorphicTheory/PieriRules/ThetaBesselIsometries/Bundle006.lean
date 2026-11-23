module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle004
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle005
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TorusWeightEigenAndRootShift
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
import Mathlib.RingTheory.Finiteness.Lattice
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

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.ComplexifiedAction

open PI.UpqRep GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gram_herm (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1

theorem gram_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1

theorem lie_iff {X : Mx k r} : InLieHpk k r X ↔ Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := Iff.rfl

theorem adj_of_lie {X : Mx k r} (hX : InLieHpk k r X) :
    Formalism.QuantumDeterminants.Hpk k r * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X := by
  have h := eq_neg_of_add_eq_zero_left (lie_iff.1 hX)
  rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, gram_sq, Matrix.one_mul]

theorem lie_of_adj {X : Mx k r} (h : Formalism.QuantumDeterminants.Hpk k r * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X) : InLieHpk k r X := by
  rw [lie_iff]
  have h2 := congrArg (fun A => Formalism.QuantumDeterminants.Hpk k r * A) h
  simp only [← Matrix.mul_assoc, gram_sq, Matrix.one_mul, Matrix.mul_neg] at h2
  rw [h2, neg_add_cancel]

theorem adj_adj (Y : Mx k r) :
    Formalism.QuantumDeterminants.Hpk k r * (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Y := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, gram_herm, ← Matrix.mul_assoc, gram_sq, Matrix.one_mul]
  rw [Matrix.mul_assoc, gram_sq, Matrix.mul_one]

theorem lie_re (Y : Mx k r) :
    InLieHpk k r ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  apply lie_of_adj
  have e : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, adj_adj, e]
  module

theorem lie_im (Y : Mx k r) :
    InLieHpk k r ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  apply lie_of_adj
  have e : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, adj_adj, e]
  module

theorem exists_decomp (Y : Mx k r) : ∃ X₁ X₂, InLieHpk k r X₁ ∧ InLieHpk k r X₂ ∧ Y = X₁ + Complex.I • X₂ := by
  refine ⟨_, _, lie_re Y, lie_im Y, ?_⟩
  have e : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [smul_smul, e]
  module

theorem adj_decomp {X₁ X₂ : Mx k r} (h₁ : InLieHpk k r X₁) (h₂ : InLieHpk k r X₂) :
    Formalism.QuantumDeterminants.Hpk k r * (X₁ + Complex.I • X₂)ᴴ * Formalism.QuantumDeterminants.Hpk k r = -X₁ + Complex.I • X₂ := by
  have e : star Complex.I = -Complex.I := by simp
  rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    adj_of_lie h₁, adj_of_lie h₂, e]
  module

theorem dC_decomp (R : Rep k r) {X₁ X₂ : Mx k r} (h₁ : InLieHpk k r X₁) (h₂ : InLieHpk k r X₂) (v : R.H) :
    R.dC (X₁ + Complex.I • X₂) v =
      dsig (k := k) (r := r) R.σ X₁ v + Complex.I • dsig (k := k) (r := r) R.σ X₂ v := by
  have e : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1 := by field_simp
  have e1 : (1 / 2 : ℂ) • (X₁ + Complex.I • X₂ + -(-X₁ + Complex.I • X₂)) = X₁ := by module
  have e2 : (1 / (2 * Complex.I)) • (X₁ + Complex.I • X₂ - -(-X₁ + Complex.I • X₂)) = X₂ := by
    have : X₁ + Complex.I • X₂ - -(-X₁ + Complex.I • X₂) = (2 * Complex.I) • X₂ := by module
    rw [this, smul_smul, e, one_smul]
  unfold Rep.dC
  rw [adj_decomp h₁ h₂, e1, e2]

theorem lie_zero : InLieHpk k r 0 := by rw [lie_iff]; simp

theorem lie_add {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) : InLieHpk k r (X + Y) := by
  apply lie_of_adj
  rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, adj_of_lie hX, adj_of_lie hY, neg_add]

theorem lie_smul (a : ℝ) {X : Mx k r} (hX : InLieHpk k r X) : InLieHpk k r (a • X) := by
  apply lie_of_adj
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, adj_of_lie hX, star_trivial, smul_neg]

theorem lie_neg {X : Mx k r} (hX : InLieHpk k r X) : InLieHpk k r (-X) := by
  simpa using lie_smul (-1) hX

theorem lie_br {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) : InLieHpk k r (X * Y - Y * X) := by
  have h1 := eq_neg_of_add_eq_zero_left (lie_iff.1 hX)
  have h2 := eq_neg_of_add_eq_zero_left (lie_iff.1 hY)
  rw [lie_iff]
  generalize Formalism.QuantumDeterminants.Hpk k r = H at h1 h2 ⊢
  have e1 : (X * Y)ᴴ * H = H * (Y * X) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.neg_mul, neg_neg,
      Matrix.mul_assoc]
  have e2 : (Y * X)ᴴ * H = H * (X * Y) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, h2, Matrix.mul_neg, ← Matrix.mul_assoc, h1, Matrix.neg_mul, neg_neg,
      Matrix.mul_assoc]
  rw [conjTranspose_sub, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel

theorem dsig_add_left (R : Rep k r) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (X + Y) v =
      dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ Y v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  rw [(hL _ hX).1, (hL _ hY).1, (hL _ (lie_add hX hY)).1, map_add (f := _)]

theorem dsig_smul_left (R : Rep k r) (a : ℝ) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (a • X) v = (a : ℂ) • dsig (k := k) (r := r) R.σ X v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  rw [(hL _ hX).1, (hL _ (lie_smul a hX)).1, map_smul, Complex.coe_smul]

theorem dsig_neg_left (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (-X) v = -dsig (k := k) (r := r) R.σ X v := by
  simpa using dsig_smul_left R (-1) hX hv

theorem dC_lie (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    R.dC X v = dsig (k := k) (r := r) R.σ X v := by
  have h := dC_decomp R hX lie_zero v
  have h0 := dsig_smul_left R 0 hX hv
  rw [zero_smul] at h0
  rw [smul_zero, add_zero, h0] at h
  simpa using h

theorem dC_lin_left (R : Rep k r) (Y Z : Mx k r) (a : ℂ) {v : R.H} (hv : v ∈ R.sm) :
    R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v := by
  obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
  obtain ⟨Z₁, Z₂, h3, h4, rfl⟩ := exists_decomp Z
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, a = x + y * Complex.I := ⟨a.re, a.im, (Complex.re_add_im a).symm⟩
  have e : ((x : ℂ) + y * Complex.I) • (Y₁ + Complex.I • Y₂) + (Z₁ + Complex.I • Z₂) =
      (x • Y₁ + (-y) • Y₂ + Z₁) + Complex.I • (y • Y₁ + x • Y₂ + Z₂) := by
    simp only [← Complex.coe_smul]
    push_cast
    linear_combination (norm := module) (y * Complex.I_mul_I) • Y₂
  have a1 := lie_smul x h1
  have a2 := lie_smul (-y) h2
  have a3 := lie_smul y h1
  have a4 := lie_smul x h2
  rw [e, dC_decomp R (lie_add (lie_add a1 a2) h3) (lie_add (lie_add a3 a4) h4), dC_decomp R h1 h2,
    dC_decomp R h3 h4, dsig_add_left R (lie_add a1 a2) h3 hv, dsig_add_left R a1 a2 hv,
    dsig_add_left R (lie_add a3 a4) h4 hv, dsig_add_left R a3 a4 hv, dsig_smul_left R _ h1 hv,
    dsig_smul_left R _ h2 hv, dsig_smul_left R _ h1 hv, dsig_smul_left R _ h2 hv]
  push_cast
  linear_combination (norm := module) (-(y : ℂ) * Complex.I_mul_I) • dsig (k := k) (r := r) R.σ Y₂ v

theorem complexified_action : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → (∀ Y, ∀ v ∈ R.sm, R.dC Y v ∈ R.sm) ∧ (∀ Y (a : ℂ), ∀ v ∈ R.sm, ∀ w ∈ R.sm, R.dC Y (a • v + w) = a • R.dC Y v + R.dC Y w) ∧ (∀ Y Z (a : ℂ), ∀ v ∈ R.sm, R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v) ∧ (∀ X, PI.UpqRep.InLieHpk k r X → ∀ v ∈ R.sm, R.dC X v = PI.UpqRep.dsig (k := k) (r := r) R.σ X v) ∧ (∀ Y Z, ∀ v ∈ R.sm, R.dC Y (R.dC Z v) - R.dC Z (R.dC Y v) = R.dC (Y * Z - Z * Y) v) ∧ ∀ Y, ∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪R.dC Y v, w⟫_ℂ = ⟪v, R.dC ((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r)) w⟫_ℂ := by
  intro hK k r ε mu R hR
  have hsm : ∀ {X}, InLieHpk k r X → ∀ {v}, v ∈ R.sm → dsig (k := k) (r := r) R.σ X v ∈ R.sm :=
    fun hX _ hv => dsig_smooth hR.2 hX hv
  have hlin : ∀ {X}, InLieHpk k r X → ∀ (a : ℂ) {v w}, v ∈ R.sm → w ∈ R.sm →
      dsig (k := k) (r := r) R.σ X (v + a • w) =
        dsig (k := k) (r := r) R.σ X v + a • dsig (k := k) (r := r) R.σ X w := by
    intro X hX a v w hv hw
    rw [dsig_add hX hv (R.smSub.smul_mem a hw), dsig_smul hX a hw]
  refine ⟨fun Y v hv => ?_, fun Y a v hv w hw => ?_, fun Y Z a v hv => dC_lin_left R Y Z a hv,
    fun X hX v hv => dC_lie R hX hv, fun Y Z v hv => ?_, fun Y v hv w hw => ?_⟩
  · exact R.smSub.add_mem (hsm (lie_re Y) hv) (R.smSub.smul_mem _ (hsm (lie_im Y) hv))
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    rw [dC_decomp R h1 h2, dC_decomp R h1 h2, dC_decomp R h1 h2, add_comm (a • v) w, hlin h1 a hw hv,
      hlin h2 a hw hv]
    module
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    obtain ⟨Z₁, Z₂, h3, h4, rfl⟩ := exists_decomp Z
    have e : (Y₁ + Complex.I • Y₂) * (Z₁ + Complex.I • Z₂) - (Z₁ + Complex.I • Z₂) * (Y₁ + Complex.I • Y₂) =
        ((Y₁ * Z₁ - Z₁ * Y₁) + -(Y₂ * Z₂ - Z₂ * Y₂)) + Complex.I • ((Y₁ * Z₂ - Z₂ * Y₁) + (Y₂ * Z₁ - Z₁ * Y₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
      linear_combination (norm := module) Complex.I_mul_I • (Y₂ * Z₂ - Z₂ * Y₂)
    have b := GlobalTheory.DerivedBracket.derived_action_bracket hK k r ε mu R hR
    rw [e, dC_decomp R (lie_add (lie_br h1 h3) (lie_neg (lie_br h2 h4))) (lie_add (lie_br h1 h4) (lie_br h2 h3)),
      dsig_add_left R (lie_br h1 h3) (lie_neg (lie_br h2 h4)) hv, dsig_neg_left R (lie_br h2 h4) hv,
      dsig_add_left R (lie_br h1 h4) (lie_br h2 h3) hv, ← b _ _ h1 h3 v hv, ← b _ _ h2 h4 v hv,
      ← b _ _ h1 h4 v hv, ← b _ _ h2 h3 v hv]
    simp only [dC_decomp R h1 h2, dC_decomp R h3 h4]
    rw [hlin h1 _ (hsm h3 hv) (hsm h4 hv), hlin h2 _ (hsm h3 hv) (hsm h4 hv), hlin h3 _ (hsm h1 hv) (hsm h2 hv),
      hlin h4 _ (hsm h1 hv) (hsm h2 hv)]
    linear_combination (norm := module) Complex.I_mul_I • (dsig (k := k) (r := r) R.σ Y₂ (dsig (k := k) (r := r) R.σ Z₂ v) -
      dsig (k := k) (r := r) R.σ Z₂ (dsig (k := k) (r := r) R.σ Y₂ v))
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    rw [adj_decomp h1 h2, dC_decomp R h1 h2, dC_decomp R (lie_neg h1) h2, dsig_neg_left R h1 hw, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, inner_neg_right, dsig_skew hR.2 h1 hv hw,
      dsig_skew hR.2 h2 hv hw, Complex.conj_I]
    ring

end GlobalTheory.ComplexifiedAction
end
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensorKFinite

variable {k r : ℕ} {ι : Type} [Fintype ι]

theorem smMap_zero {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) : T 0 = 0 := by
  have h := hT.smul 0 0 R.smSub.zero_mem
  simpa using h

theorem kfin_of_family {R R' : Rep k r} (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c))
    (hK : ∀ v, R.KFin v → v ∈ R.sm)
    (hA : ∀ g ∈ GG k r, ∀ c, ∀ y ∈ R.sm, ∃ a : ι → ℂ, R'.σ g (T c y) = ∑ i, a i • T i (R.σ g y))
    (c : ι) (y : R.H) (hy : R.KFin y) : R'.KFin (T c y) := by
  obtain ⟨S, hfd, hyS, hst⟩ := hy
  have hsm : ∀ x ∈ S, x ∈ R.sm := fun x hx => hK x ⟨S, hfd, hx, hst⟩
  let L : ι → (S →ₗ[ℂ] R'.H) := fun i =>
    { toFun := fun x => T i x
      map_add' := fun x x' => (hT i).add _ (hsm _ x.2) _ (hsm _ x'.2)
      map_smul' := fun a x => (hT i).smul a _ (hsm _ x.2) }
  have hmem : ∀ i, ∀ x ∈ S, T i x ∈ ⨆ i, LinearMap.range (L i) := fun i x hx =>
    Submodule.mem_iSup_of_mem i ⟨⟨x, hx⟩, rfl⟩
  refine ⟨⨆ i, LinearMap.range (L i), inferInstance, hmem c y hyS, fun g hg x hx => ?_⟩
  have hle : (⨆ i, LinearMap.range (L i)) ≤
      (⨆ i, LinearMap.range (L i)).comap (R'.σ g : R'.H →ₗ[ℂ] R'.H) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, ha⟩ := hA g hg.1 i z (hsm _ z.2)
    have : R'.σ g (T i z) ∈ ⨆ i, LinearMap.range (L i) := by
      rw [ha]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j _ (hst g hg _ z.2))
    exact this
  exact hle hx

theorem tk_of_family {R R' : Rep k r} (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c))
    (hK : ∀ v, R.KFin v → v ∈ R.sm) (hTK : ∀ v ∈ R.TK, v ∈ R.sm)
    (hF : ∀ c y, R.KFin y → R'.KFin (T c y))
    (hB : ∀ g ∈ GG k r, ∀ c, ∀ y ∈ R.sm, ∃ a : ι → ℂ, T c (R.σ g y) = ∑ i, a i • R'.σ g (T i y))
    (c : ι) (y : R.H) (hy : y ∈ R.TK) : T c y ∈ R'.TK := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, v, hv, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hB g hg c v (hK v hv)
    rw [ha]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨g, hg, _, hF j v hv, rfl⟩)
  | zero => rw [smMap_zero (hT c)]; exact Submodule.zero_mem _
  | add x x' hx hx' h1 h2 =>
    rw [(hT c).add _ (hTK _ hx) _ (hTK _ hx')]; exact Submodule.add_mem _ h1 h2
  | smul a x hx h1 =>
    rw [(hT c).smul a _ (hTK _ hx)]; exact Submodule.smul_mem _ _ h1

theorem inv_rows [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Matrix ι ι ℂ) (h : A * B = 1)
    (u v : ι → V) (huv : ∀ i, u i = ∑ j, B i j • v j) (c : ι) : v c = ∑ i, A c i • u i := by
  simp_rw [huv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply]
  simp

end GlobalTheory.TensorKFinite


open GlobalTheory.TensorKFinite in
theorem GlobalTheory.tensor_decomposition_kfinite : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ I c y, (RI I).KFin y → R.KFin (io I c y)) ∧ (∀ I c x, R.KFin x → (RI I).KFin (pr I c x)) ∧ (∀ I c, ∀ y ∈ (RI I).TK, io I c y ∈ R.TK) ∧ (∀ I c, ∀ x ∈ R.TK, pr I c x ∈ (RI I).TK) := by
  intro hKS k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR hRI hF hT
  obtain ⟨-, -, -, hRσ, hRT, -, hRK, -, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε mu R hR
  have hIT : ∀ I, ∀ v ∈ (RI I).TK, v ∈ (RI I).sm := fun I =>
    (GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε (muI I) (RI I) (hRI I)).2.2.2.2.1
  have hIK : ∀ I, ∀ v, (RI I).KFin v → v ∈ (RI I).sm := fun I v hv =>
    hIT I v ((GlobalTheory.T.discreteSeries_unitary_smooth_basic hKS k r ε (muI I) (RI I) (hRI I)).2.2.2.2.2.2.1 v hv)
  have hRK' : ∀ v, R.KFin v → v ∈ R.sm := fun v hv => hRT v (hRK v hv)
  obtain ⟨-, -, h1, hmul, -⟩ := hF
  have hinv : ∀ g ∈ GG k r, ρ g⁻¹ * ρ g = 1 ∧ ρ g * ρ g⁻¹ = 1 := fun g hg => by
    obtain ⟨a, b, c⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    exact ⟨by rw [← hmul _ a _ hg, c, h1], by rw [← hmul _ hg _ a, b, h1]⟩
  have ioB : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ y ∈ (RI I).sm,
      io I c ((RI I).σ g y) = ∑ i, ρ g c i • R.σ g (io I i y) := fun I g hg c y hy =>
    congrFun (hT.io_eq I g hg y hy) c
  have ioA : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ y ∈ (RI I).sm,
      R.σ g (io I c y) = ∑ i, ρ g⁻¹ c i • io I i ((RI I).σ g y) := fun I g hg c y hy =>
    inv_rows _ _ (hinv g hg).1 (fun i => io I i ((RI I).σ g y)) (fun i => R.σ g (io I i y))
      (fun i => ioB I g hg i y hy) c
  have prA : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ x ∈ R.sm,
      (RI I).σ g (pr I c x) = ∑ i, (ρ g)ᵀ c i • pr I i (R.σ g x) := fun I g hg c x hx => by
    have hs : ∀ e, (Pi.single c x : ι → R.H) e ∈ R.sm := fun e => by
      by_cases he : e = c
      · subst he; simpa using hx
      · rw [Pi.single_eq_of_ne he]; exact R.smSub.zero_mem
    have h := hT.pr_eq I g hg (Pi.single c x) hs
    have e1 : ∑ e, pr I e ((Pi.single c x : ι → R.H) e) = pr I c x := by
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        rw [Pi.single_eq_of_ne he, smMap_zero (hT.pr_sm I e)]
      · simp
    have e2 : ∀ i, act ρ R g (Pi.single c x) i = ρ g i c • R.σ g x := fun i => by
      unfold act
      rw [Finset.sum_eq_single c]
      · simp
      · intro e _ he
        simp [Pi.single_eq_of_ne he]
      · simp
    rw [e1] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2, (hT.pr_sm I i).smul _ _ (hRσ g hg x hx), Matrix.transpose_apply]
  have prB : ∀ I, ∀ g ∈ GG k r, ∀ c, ∀ x ∈ R.sm,
      pr I c (R.σ g x) = ∑ i, (ρ g⁻¹)ᵀ c i • (RI I).σ g (pr I i x) := fun I g hg c x hx =>
    inv_rows _ _ (by rw [← Matrix.transpose_mul, (hinv g hg).2, Matrix.transpose_one])
      (fun i => (RI I).σ g (pr I i x)) (fun i => pr I i (R.σ g x)) (fun i => prA I g hg i x hx) c
  have K1 : ∀ I c y, (RI I).KFin y → R.KFin (io I c y) := fun I =>
    kfin_of_family (io I) (hT.io_sm I) (hIK I) fun g hg c y hy => ⟨_, ioA I g hg c y hy⟩
  have K2 : ∀ I c x, R.KFin x → (RI I).KFin (pr I c x) := fun I =>
    kfin_of_family (pr I) (hT.pr_sm I) hRK' fun g hg c y hy => ⟨_, prA I g hg c y hy⟩
  exact ⟨K1, K2,
    fun I => tk_of_family (io I) (hT.io_sm I) (hIK I) (hIT I) (K1 I) fun g hg c y hy => ⟨_, ioB I g hg c y hy⟩,
    fun I => tk_of_family (pr I) (hT.pr_sm I) hRK' hRT (K2 I) fun g hg c y hy => ⟨_, prB I g hg c y hy⟩⟩
end
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.k_finite_derivatives_finite_span : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ x ∈ R.TK, ∀ m : ℕ, ∃ (M : ℕ) (xs : Fin M → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : Fin M → ℝ, (∀ i, |co i| ≤ 1) ∧ PI.UpqRep.dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i := by
  first | exact @GlobalTheory.UnitBoxWords.box_words | exact GlobalTheory.UnitBoxWords.box_words | (intros; apply GlobalTheory.UnitBoxWords.box_words <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.tensor_bessel_transfer : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) := by
  first | exact @GlobalTheory.herm_smul_eq_sum_of_tensRaw | exact GlobalTheory.herm_smul_eq_sum_of_tensRaw | (intros; apply GlobalTheory.herm_smul_eq_sum_of_tensRaw <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.KStable_finiteDim_smooth_compactRoot_stable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → ∀ S : Submodule ℂ R.H, FiniteDimensional ℂ S → PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S → (∀ v ∈ S, R.KFin v ∧ v ∈ R.sm) ∧ ∀ a b, ε a = ε b → ∀ v ∈ S, R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v ∈ S := by
  first | exact @GlobalTheory.CompactStable.kStable_smooth_and_stable | exact GlobalTheory.CompactStable.kStable_smooth_and_stable | (intros; apply GlobalTheory.CompactStable.kStable_smooth_and_stable <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.matrix_coefficient_smooth_derivatives : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : V) (F : Mx k r → V), R.IsDG ε mu → ∀ x ∈ R.sm, ∀ y ∈ R.sm, (∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) → B.CkOn ⊤ (B.GV k r) F ∧ ∀ a b : List (Mx k r), (∀ Y ∈ a, B.inLie k r Y) → (∀ Y ∈ b, B.inLie k r Y) → ∀ g ∈ GG k r, B.dLR a b F g = ⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
  first | exact @GlobalTheory.CoeffDeriv.coeff_dLR | exact GlobalTheory.CoeffDeriv.coeff_dLR | (intros; apply GlobalTheory.CoeffDeriv.coeff_dLR <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.torusWeight_eigen_and_rootShift : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ (ν : Fin (2 * r + k + 1) → ℝ) (v : R.smSub), PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) ν (v : R.H) → Formalism.REAL.IsWeight E ν v ∧ ∀ a b, PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (ν + PI.UpqRep.root a b) ((E a b v : R.smSub) : R.H) := by
  first | exact @GlobalTheory.TorusWeight.torus_weight_action | exact GlobalTheory.TorusWeight.torus_weight_action | (intros; apply GlobalTheory.TorusWeight.torus_weight_action <;> assumption)
end Gp91
end
