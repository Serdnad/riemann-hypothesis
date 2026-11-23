module

public import Formalism.PeriodIntegrals.UpqRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

open MeasureTheory Matrix

noncomputable section

namespace CompanionTheory.D.gk.admitted

open PI.UpqRep

section Words

variable {R : Type*} [Ring R]

def word (E : R) (l : List R) : R := l.foldr (fun a w => E * a * w) E

@[simp] theorem word_nil (E : R) : word E [] = E := rfl

@[simp] theorem word_cons (E a : R) (l : List R) : word E (a :: l) = E * a * word E l := rfl

def stdPoly (E : R) {M : ℕ} (a : Fin M → R) : R :=
  ∑ π : Equiv.Perm (Fin M), ((Equiv.Perm.sign π : ℤ) : R) * word E (List.ofFn fun i => a (π i))

theorem map_word {R' : Type*} [Ring R'] (f : R →+* R') (E : R) (l : List R) :
    f (word E l) = word (f E) (l.map f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem map_stdPoly {R' : Type*} [Ring R'] (f : R →+* R') (E : R) {M : ℕ} (a : Fin M → R) :
    f (stdPoly E a) = stdPoly (f E) fun i => f (a i) := by
  simp [stdPoly, map_word, List.map_ofFn, Function.comp_def]

end Words

def RFin {K : Type} [Group K] [TopologicalSpace K] (e : K → ℂ) (d : ℕ) : Prop :=
  ∃ φ : Fin d → K → ℂ, (∀ i, Continuous (φ i)) ∧ ∀ k : K, ∃ c : Fin d → ℂ, ∀ x, e (x * k⁻¹) = ∑ i, c i * φ i x

structure IsGood {G : Type} [Group G] [TopologicalSpace G] (st : G → G) (S : Set G) {ι : Type} [Fintype ι]
    [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ) : Prop where
  cont : Continuous ρ
  adj : ∀ g, ρ (st g) = (ρ g)ᴴ
  tri : ∃ h : ι → ℕ, Function.Injective h ∧ ∀ s ∈ S, (ρ s).BlockTriangular h

def FinOfPI : Prop :=
  ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : G →* (H →L[ℂ] H)), (∀ g v, ‖σ g v‖ = ‖v‖) →
    (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤) →
    ∀ (E : H →L[ℂ] H) (M : ℕ), (∀ g : Fin M → G, stdPoly E (fun i => σ (g i)) = 0) →
      FiniteDimensional ℂ (LinearMap.range (E : H →ₗ[ℂ] H)) ∧ Module.finrank ℂ (LinearMap.range (E : H →ₗ[ℂ] H)) ≤ M

def SmallPI : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W Y : Submodule ℂ V) [FiniteDimensional ℂ Y], Y ≤ W →
    ∀ E : Module.End ℂ V, (∀ w ∈ W, E w ∈ Y) → ∀ M : ℕ, Module.finrank ℂ Y ^ 2 < M →
    ∀ a : Fin M → Module.End ℂ V, (∀ i, ∀ w ∈ W, a i w ∈ W) → ∀ w ∈ W, stdPoly E a w = 0

def GoodPI : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    (K : Subgroup G) [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsMulRightInvariant]
    (st : G → G) (S : Set G), (∀ g, ∃ k ∈ K, ∃ s ∈ S, g = k * s) →
    ∀ (e : K → ℂ) (d M : ℕ), Continuous e → RFin e d → d ^ 2 < M →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ), IsGood st S ρ →
    ∀ E : Module.End ℂ (ι → ℂ), (∀ u, E u = ∫ k : K, e k • (ρ k *ᵥ u) ∂μ) →
    ∀ g : Fin M → G, stdPoly E (fun i => Matrix.toLin' (ρ (g i))) = 0

def Transfer : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    (K : Subgroup G) [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (st : G → G) (S : Set G)
    (ι₀ : Type) [Fintype ι₀] [DecidableEq ι₀] (ρ₀ : G →* Matrix ι₀ ι₀ ℂ), IsGood st S ρ₀ → Function.Injective ρ₀ →
    ∀ (e : K → ℂ), Continuous e → ∀ (M : ℕ) (g : Fin M → G),
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ), IsGood st S ρ →
      ∀ E : Module.End ℂ (ι → ℂ), (∀ u, E u = ∫ k : K, e k • (ρ k *ᵥ u) ∂μ) →
        stdPoly E (fun i => Matrix.toLin' (ρ (g i))) = 0) →
    ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
      (∀ v, Continuous fun x => σ x v) → ∀ E : H →L[ℂ] H, (∀ u, E u = ∫ k : K, e k • σ k u ∂μ) →
        stdPoly E (fun i => σ (g i)) = 0

def ExistsAvg : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [SecondCountableTopology K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : K →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → (∀ v, Continuous fun x => σ x v) →
    ∀ (S : Submodule ℂ H) [FiniteDimensional ℂ S], (∀ k, ∀ v ∈ S, σ k v ∈ S) → ∀ v ∈ S,
      ∃ (e : K → ℂ) (E : H →L[ℂ] H), Continuous e ∧ RFin e (Module.finrank ℂ S) ∧
        (∀ u, E u = ∫ k, e k • σ k u ∂μ) ∧ E v = v

def Iwa {n : ℕ} (ε : Fin n → Bool) : Prop :=
  ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ UJset ε, ∃ k ∈ Kset ε, ∃ s ∈ UJset ε,
    g = k * s ∧ (Uᴴ * s * U).BlockTriangular id

def IwaHpk : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    IsCayleyU k r ε P → Iwa ε

def IwaAll : Prop := ∀ (n : ℕ) (ε : Fin n → Bool), Iwa ε

def GardingFin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ (Y : Submodule ℂ H) [FiniteDimensional ℂ Y],
      (∀ T : H →L[ℂ] H, (∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u)) → ∀ y ∈ Y, T y ∈ Y) →
      ∀ v ∈ Y, SmoothOnH (Jm ε) fun g => σ g v

def AdmUJ {n : ℕ} (ε : Fin n → Bool) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ (S : Submodule ℂ H) [FiniteDimensional ℂ S], IsKStableOn ε σ S → ∀ v ∈ S,
      ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ Module.finrank ℂ Y ≤ Module.finrank ℂ S ^ 2 + 1 ∧ v ∈ Y ∧
        ∀ T : H →L[ℂ] H, (∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u)) → ∀ y ∈ Y, T y ∈ Y

end CompanionTheory.D.gk.admitted
end
end

section

open Matrix Topology Set Filter
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted.Gard

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℂ => y i j :=
  contDiff_apply_apply ℝ i j

theorem contDiff_hs : ContDiff ℝ ∞ (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (contDiff_entry i j).norm_sq ℝ

theorem contDiff_mul :
    ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2 := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => ((contDiff_entry i k).comp contDiff_fst).mul ((contDiff_entry k j).comp contDiff_snd)

theorem hs_eq_trace (y : Matrix (Fin n) (Fin n) ℂ) : (hs y : ℂ) = (y * yᴴ).trace := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem hs_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (y : Matrix (Fin n) (Fin n) ℂ) : hs (kᴴ * y * k) = hs y := by
  have h1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  apply Complex.ofReal_injective
  rw [hs_eq_trace, hs_eq_trace]
  have : kᴴ * y * k * (kᴴ * y * k)ᴴ = kᴴ * (y * yᴴ * k) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc k kᴴ, h1, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem norm_le_of_hs {y : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 ≤ r) (h : hs y ≤ r ^ 2) : ‖y‖ ≤ r := by
  rw [Matrix.norm_le_iff hr]
  intro i j
  have h1 : ‖y i j‖ ^ 2 ≤ ∑ j, ‖y i j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖y i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j, ‖y i j‖ ^ 2 ≤ hs y :=
    Finset.single_le_sum (f := fun i => ∑ j, ‖y i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).1 (h1.trans (h2.trans h))

theorem exists_bump {W : Set (Matrix (Fin n) (Fin n) ℂ)} (hW : W ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (S : Set (Matrix (Fin n) (Fin n) ℂ)), ContDiff ℝ ∞ f ∧ 0 ≤ f ∧ f 1 ≠ 0 ∧
      IsCompact S ∧ S ⊆ W ∧ (∀ y, f y ≠ 0 → y ∈ S) ∧
      ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ y, f (kᴴ * y * k) = f y := by
  obtain ⟨r, hr, hrW⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hW
  refine ⟨fun y => expNegInvGlue (r ^ 2 - hs (y - 1)), Metric.closedBall 1 r, ?_, fun y => expNegInvGlue.nonneg _,
    ?_, isCompact_closedBall _ _, hrW, fun y hy => ?_, fun k hk y => ?_⟩
  · exact expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_hs.comp (contDiff_id.sub contDiff_const)))
  · refine (expNegInvGlue.pos_of_pos ?_).ne'
    simp only [sub_self, hs, Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, sub_zero]
    positivity
  · rw [mem_closedBall_iff_norm]
    refine norm_le_of_hs hr.le ?_
    by_contra h
    exact hy (expNegInvGlue.zero_of_nonpos (by linarith))
  · have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
    have : kᴴ * y * k - 1 = kᴴ * (y - 1) * k := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    simp only [this, hs_conj hk]

theorem isCompact_mul_inv {A S : Set (Matrix (Fin n) (Fin n) ℂ)} (hA : IsCompact A) (hS : IsCompact S)
    (hd : ∀ B ∈ S, B.det ≠ 0) :
    IsCompact ((fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2⁻¹) '' (A ×ˢ S)) := by
  refine (hA.prod hS).image_of_continuousOn fun p hp => ?_
  have h1 : ContinuousAt (Inv.inv : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) p.2 := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hd _ hp.2)
  exact (continuousAt_fst.mul (h1.comp continuousAt_snd)).continuousWithinAt

end CompanionTheory.D.gk.admitted.Gard
end
end
