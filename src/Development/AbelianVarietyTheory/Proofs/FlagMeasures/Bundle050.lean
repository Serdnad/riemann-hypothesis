module

public import Formalism.HermitianLattices.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.FormalDegreeBessel.StatementG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField

namespace GlobalTheory.TraceOnto

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_star (x : 𝓞 E) : ∃ t : 𝓞 E, (t : E) = star (x : E) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd E) x, rfl⟩

def normTraceIdeal (E : Type) [Field E] [NumberField E] [StarRing E] : Ideal (𝓞 E) where
  carrier := {x | ∃ w : 𝓞 E, (w : E) + star (w : E) = (x : E) * star (x : E)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨t, ht⟩ := exists_star b
    refine ⟨u + v + a * t, ?_⟩
    push_cast
    simp only [ht, star_add, star_mul', star_star]
    linear_combination hu + hv
  smul_mem' := by
    rintro c a ⟨u, hu⟩
    obtain ⟨t, ht⟩ := exists_star c
    refine ⟨c * t * u, ?_⟩
    simp only [smul_eq_mul]
    push_cast
    simp only [ht, star_mul', star_star]
    linear_combination ((c : E) * star (c : E)) * hu

theorem exists_trace_one : ∀ (E : Type) [Field E] [NumberField E] [StarRing E],
    Formalism.HermitianLatticesTheory.IsCMUnram E → ∃ w : 𝓞 E, (w : E) + star (w : E) = 1 := by
  intro E _ _ _ h
  have htop : normTraceIdeal E = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨θ, t, ht, hn⟩ := h.2.2 P hP
    apply hn
    apply hle
    have ht' : (t : E) = star (θ : E) := ht
    refine ⟨θ * t - θ * θ, ?_⟩
    push_cast
    simp only [ht', star_sub, star_mul', star_star]
    ring
  have h1 : (1 : 𝓞 E) ∈ normTraceIdeal E := htop ▸ Submodule.mem_top
  obtain ⟨w, hw⟩ := h1
  exact ⟨w, by simpa using hw⟩

end GlobalTheory.TraceOnto
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.UnitriangularCoeff

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

def hRight (x : Fin n → R ⊗[F] E) : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hR R σ J x y
  map_add' y z := by
    simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hRight_apply (x y : Fin n → R ⊗[F] E) : hRight R σ J x y = hR R σ J x y := rfl

theorem hR_add_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z := (hRight R σ J x).map_add y z

theorem hR_sub_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y - z) = hR R σ J x y - hR R σ J x z := (hRight R σ J x).map_sub y z

theorem hR_smul_right (x y : Fin n → R ⊗[F] E) (c : R ⊗[F] E) :
    hR R σ J x (c • y) = c * hR R σ J x y := (hRight R σ J x).map_smul c y

theorem hR_zero_right (x : Fin n → R ⊗[F] E) : hR R σ J x 0 = 0 := (hRight R σ J x).map_zero

theorem hR_ratV (x y : Fin n → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR R (hE σ J x y) := by

  simp only [hR, hE, Formalism.UG.hform, ratV, JR, Matrix.map_apply, map_sum, map_mul, sigR_inclR,
  AlgHom.coe_toRingHom, RingHom.coe_coe]

theorem hE_symm (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by

  simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ.1 b a]
  ring

variable {R σ J}

theorem hermitian_flag_dual_basis (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1)) :
    hE σ J (P.f a) (F0 P c) = if c = a.castSucc then 1 else 0 := by
  induction c using Fin.lastCases with
  | last =>
    rw [F0, Fin.snoc_last, hP.2.2.2.2.1 a, if_neg (Fin.castSucc_lt_last a).ne']
  | cast c =>
    rw [F0, Fin.snoc_castSucc, hE_symm σ J hσ hJ, hP.2.2.1 c a]
    by_cases h : c = a
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e)), map_zero]

theorem pairR (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1)) :
    hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (F0 P c)) = if c = a.castSucc then 1 else 0 := by
  rw [hR_ratV, hermitian_flag_dual_basis hσ hJ hP a c]
  split_ifs <;> simp only [map_one, map_zero]

theorem pair_sum (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1) → R ⊗[F] E) :
    hR R σ J (ratV (F := F) R (P.f a)) (∑ b, c b • ratV (F := F) R (F0 P b)) = c a.castSucc := by

  rw [← hRight_apply, map_sum]
  simp only [map_smul, hRight_apply, pairR hσ hJ hP, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem expand (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (b : Fin (r + 1)) (w : Fin n → R ⊗[F] E)
    (hw : w ∈ spanR (F := F) R (F0 P) {a | a < b}) :
    w = ∑ a, (if h : a < b then hR R σ J (ratV (F := F) R
      (P.f (a.castLT (lt_of_lt_of_le h (Fin.le_last b))))) w else 0) • ratV (F := F) R (F0 P a) := by
  unfold spanR at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    have hc' : c < b := hc
    symm
    rw [Finset.sum_eq_single c]
    · rw [dite_eq_left hc', pairR hσ hJ hP, Fin.castSucc_castLT, if_pos rfl, one_smul]
    · intro a _ hac
      split_ifs with h
      · rw [pairR hσ hJ hP, Fin.castSucc_castLT, if_neg (fun e => hac e.symm), zero_smul]
      · rw [zero_smul]
    · intro h; exact absurd (Finset.mem_univ c) h
  | zero =>
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs <;> simp [hR_zero_right]
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [hR_add_right, add_smul]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [hR_smul_right, smul_smul]

end Alg

theorem combine {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {r : ℕ} (b : Fin (r + 1))
    (G : Fin (r + 1) → M) (y : ∀ a : Fin (r + 1), a < b → A) :
    (∑ a, (if h : a < b then y a h else 0) • G a) + G b =
      ∑ a, (if a = b then 1 else if h : a < b then y a h else 0) • G a := by
  have key : ∀ a, (if a = b then (1 : A) else if h : a < b then y a h else 0) • G a =
      (if h : a < b then y a h else 0) • G a + (if a = b then G a else 0) := by
    intro a
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]

theorem exists_coeff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ ν : Ssub (Fv F v) σ J P → ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), Continuous ν ∧ ∀ (s : Ssub (Fv F v) σ J P) (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), x = ν s ↔ ∀ b, lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a) := by
  intro F E _ _ _ _ _ σ hσ n J hJ v r P T hP
  have hss : ∀ x, σ (σ x) = x := sigma_sigma σ hσ
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have ha : ∀ p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}, (p.1.1 : ℕ) < r :=
    fun p => lt_of_lt_of_le p.2 (Fin.le_last _)
  refine ⟨fun s p => hR (Fv F v) σ J (ratV (F := F) (Fv F v) (P.f (p.1.1.castLT (ha p))))
      (lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P p.1.2))), ?_, ?_⟩
  · refine continuous_pi fun p => ?_
    have hM : Continuous fun s : Ssub (Fv F v) σ J P =>
        ((HA.mat (Fv F v) σ J (s : HA (Fv F v) σ J) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hMij : ∀ i j, Continuous fun s : Ssub (Fv F v) σ J P =>
        ((HA.mat (Fv F v) σ J (s : HA (Fv F v) σ J) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp hM)
    simp only [hR, Formalism.UG.hform, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_finsetSum _ fun k _ => (hMij j k).mul continuous_const)
  · intro s x
    constructor
    · rintro rfl b
      have hU : lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b)) -
          ratV (F := F) (Fv F v) (F0 P b) ∈ spanR (F := F) (Fv F v) (F0 P) {a | a < b} := s.2 b
      have e1 := sub_eq_iff_eq_add.mp (expand hss hJ hP b _ hU)
      refine e1.trans ((combine b _ _).trans ?_)
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      split_ifs with h1 h2
      · rfl
      · rw [hR_sub_right, pairR hss hJ hP, Fin.castSucc_castLT, if_neg h2.ne', sub_zero]
      · rfl
    · intro H
      funext p
      obtain ⟨⟨a, b⟩, h⟩ := p
      symm
      show hR (Fv F v) σ J (ratV (F := F) (Fv F v) (P.f (a.castLT (lt_of_lt_of_le h (Fin.le_last b)))))
        (lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b))) = x ⟨(a, b), h⟩
      rw [H b, pair_sum hss hJ hP, Fin.castSucc_castLT, if_neg h.ne, dite_eq_left h]

end GlobalTheory.UnitriangularCoeff
end
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SnMass
open scoped ENNReal

namespace GlobalTheory.GramExp

def Sgn {a : ℕ} (d : Fin a → ℂ) : Prop := ∀ i, d i = 1 ∨ d i = -1

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.diag_sq {a : ℕ} {d : Fin a → ℂ}
    (hd : _root_.GlobalTheory.GramExp.Sgn d) : Matrix.diagonal d * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases hd i with h | h <;> simp [h]


open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.isMatGroup_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H * H = 1) : _root_.PI.IsMatGroup (_root_.Formalism.QuantumDeterminants.UH H) := by
  unfold _root_.PI.IsMatGroup _root_.Formalism.QuantumDeterminants.UH
  have hdetH : H.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hH
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hunit : ∀ a : Matrix (Fin N) (Fin N) ℂ, aᴴ * H * a = H → IsUnit a.det := by
    intro a ha
    have := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_mul] at this
    have h1 : aᴴ.det * a.det = 1 := by
      have : (aᴴ.det * a.det) * H.det = 1 * H.det := by linear_combination this
      exact mul_right_cancel₀ hdetH this
    exact isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · simp
  · intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [ha, hb]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hu := hunit a ha
    have hr : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
    refine ⟨?_, hr⟩
    have hc : (a⁻¹)ᴴ * aᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hr, Matrix.conjTranspose_one]
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha]
      _ = ((a⁻¹)ᴴ * aᴴ) * H * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hc, hr, Matrix.one_mul, Matrix.mul_one]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.exp_cont {n : ℕ} :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous


open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.GramExp.measurableSet_image_ball {X Y : Type} [PseudoMetricSpace X] [ProperSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {f : X → Y}
    (hf : Continuous f) (x : X) (ρ : ℝ) :
    MeasurableSet (f '' Metric.ball x ρ) := by
  have hb : Metric.ball x ρ = ⋃ k : ℕ, Metric.closedBall x (ρ - 1 / ((k : ℝ) + 1)) := by
    ext y
    simp only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hb, Set.image_iUnion]
  exact MeasurableSet.iUnion fun k =>
    ((isCompact_closedBall x _).image hf).isClosed.measurableSet

end GlobalTheory.GramExp
end
end
