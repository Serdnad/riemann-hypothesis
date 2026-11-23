module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle004
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.SD

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {n : ℕ}

def TK (n : ℕ) : Set (M2 n) := {M | Mᴴ * M = 1 ∧ InG M}

theorem isCompact_TK : IsCompact (TK n) := by
  have hsub : TK n ⊆ Set.pi univ fun _ => Set.pi univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    intro M hM i _ j _
    have hU : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hM.1
    simpa using entry_norm_bound_of_unitary hU i j
  refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset ?_ hsub
  have hc1 : IsClosed {M : M2 n | Mᴴ * M = 1} :=
    isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hc2 : IsClosed {M : M2 n | Mᴴ * JJ n * M = JJ n} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  exact hc1.inter hc2

def toGR (M : TK n) : GR n :=
  ⟨⟨M.1, M.1ᴴ, mul_eq_one_comm.mp M.2.1, M.2.1⟩, M.2.2⟩

theorem continuous_toGR : Continuous (toGR (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

theorem isCompact_KR : IsCompact ((KR n : Set (GR n))) := by
  have hset : (KR n : Set (GR n)) = Set.range (toGR (n := n)) := by
    ext k
    constructor
    · intro hk
      refine ⟨⟨mR k, hk.2, hk.1⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
    · rintro ⟨M, rfl⟩
      exact ⟨M.2.2, M.2.1⟩
  haveI : CompactSpace (TK n) := isCompact_iff_compactSpace.mp isCompact_TK
  rw [hset]
  exact isCompact_range continuous_toGR

instance compactSpace_KR : CompactSpace (KR n) := isCompact_iff_compactSpace.mp isCompact_KR

end PositivityTheory.Rg.Sw.AbsSt.SD
end
end

section

noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

lemma cell_decomp (y : GR n) (hy : ((mR y).toBlocks₂₁).det ≠ 0) :
    ∃ (p g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian ∧ mR g = JJ n * nU b ∧
      (mR p).toBlocks₂₁ = 0 ∧ y = p * g := by
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  have hyG : InG (mR y) := y.2
  have hrel : C * Dᴴ = D * Cᴴ := lowerDiagonalBlockAsGL hyG
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hy
  have hCHu : IsUnit (Cᴴ).det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hy)
  set b := C⁻¹ * D with hb
  have hbH : b.IsHermitian := by
    show bᴴ = b
    calc bᴴ = Dᴴ * (Cᴴ)⁻¹ := by
            rw [hb, conjTranspose_mul, conjTranspose_nonsing_inv]
      _ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
            rw [← Matrix.mul_assoc C⁻¹, nonsing_inv_mul _ hCu, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hrel]
      _ = b := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one, hb]
  obtain ⟨g, hg⟩ := exists_of_InG (InG_JJ_nU hbH)
  set N : M2 n := fromBlocks (-b) (-1) 1 0 with hN
  have h1 : mR g⁻¹ * mR g = 1 := by
    rw [← SZ.mR_mul, inv_mul_cancel]
    rfl
  have h2 : mR g * N = 1 := by
    rw [hg, hN]
    simp only [JJ, nU, fromBlocks_multiply]
    rw [← fromBlocks_one]
    congr 1 <;> simp
  have hM : mR g⁻¹ = N := by
    calc mR g⁻¹ = mR g⁻¹ * (mR g * N) := by rw [h2, Matrix.mul_one]
      _ = N := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨y * g⁻¹, g, b, hbH, hg, ?_, (inv_mul_cancel_right y g).symm⟩
  rw [SZ.mR_mul, hM, ← fromBlocks_toBlocks (mR y), hN, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  rw [← hC, ← hD, Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc, mul_nonsing_inv _ hCu,
    Matrix.one_mul, neg_add_cancel]

end PositivityTheory.Rg.Sw.AbsSt.SZ

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SZ

theorem secZero : NullIff → SecZero := by
  intro hN m n ε c t p q e sL ρ hL P
  have ht : t ≠ 0 := by
    rcases hL.sign with ⟨h, -, -⟩ | ⟨h, -, -⟩
    · rw [h]; exact hL.cpos.ne'
    · rw [h]; exact neg_ne_zero.2 hL.cpos.ne'
  obtain ⟨C, hC, hcell⟩ := hL.cell
  rw [hN m n ε c t hL.cpos ht P]
  constructor
  · intro h y
    have hS : {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} ⊆ {z | sL P z = 0} := by
      intro z hz
      obtain ⟨p', g, b, hb, hg, hp, rfl⟩ := cell_decomp z hz
      show sL P (p' * g) = 0
      rw [hL.law P p' g hp, hcell P g b hb hg, h b hb, mul_zero, mul_zero]
    have hcl : IsClosed {z : GR n | sL P z = 0} := isClosed_eq (hL.cont P) continuous_const
    exact hcl.closure_subset_iff.2 hS (dense_cell y)
  · intro h b hb
    obtain ⟨g, hg⟩ := exists_of_InG (InG_JJ_nU hb)
    have hh := hcell P g b hb hg
    rw [h g] at hh
    exact (mul_eq_zero.1 hh.symm).resolve_left hC

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw LocOpA

variable {n : ℕ}

def jLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (w : ℂ) (g : GR n) : ℂ :=
  ∫ x, ((hLoc (g * A * nbEl x * B) : ℂ) ^ w * F0 p q e (g * A * nbEl x * B)) * ψ x

def czLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) [MeasurableSpace (KR n)] (μ : Measure (KR n))
    (w : ℂ) : ℂ :=
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n) ∂μ

theorem eigen (hI : Iwa) (hM : Mult) (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] (w : ℂ) (y : GR n) :
    ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * A * nbEl x * B) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * A * nbEl x * B)) * ψ x) ∂μ =
      czLoc p q e A B ψ μ w * ((hLoc y : ℂ) ^ w * F0 p q e y) := by
  obtain ⟨p0, k0, hp, hk0, rfl⟩ := hI n y
  have hM1 := (hM n p q e).1
  have hM2 := (hM n p q e).2
  have hJ : ∀ g : GR n, jLoc p q e A B ψ w (p0 * g) =
      ((hLoc p0 : ℂ) ^ w * F0 p q e p0) * jLoc p q e A B ψ w g := by
    intro g
    unfold jLoc
    rw [← integral_const_mul]
    congr 1
    funext x
    have h1 : p0 * g * A * nbEl x * B = p0 * (g * A * nbEl x * B) := by simp only [mul_assoc]
    rw [h1, (hM2 p0 _ hp).1, (hM2 p0 _ hp).2]
    push_cast
    rw [Complex.mul_cpow_ofReal_nonneg (by unfold hLoc; positivity) (by unfold hLoc; positivity)]
    ring
  have hne : F0 p q e k0 ≠ 0 := by
    intro h0
    have h2 := (hM1 k0 k0⁻¹ (inv_mem hk0)).1
    rw [mul_inv_cancel, weight_factor_one, h0, zero_mul] at h2
    exact one_ne_zero h2
  let K0 : KR n := ⟨k0, hk0⟩
  have hK0 : (K0 : GR n) = k0 := rfl
  have hshift : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ =
      F0 p q e k0 * (F0 p q e ((K0 * k : KR n) : GR n))⁻¹ := by
    intro k
    rw [Subgroup.coe_mul, hK0, (hM1 k0 k k.2).1, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  calc _ = ∫ k : KR n, ((hLoc p0 : ℂ) ^ w * F0 p q e p0 * F0 p q e k0) *
        ((F0 p q e ((K0 * k : KR n) : GR n))⁻¹ * jLoc p q e A B ψ w ((K0 * k : KR n) : GR n)) ∂μ := by
        congr 1
        funext k
        show (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (p0 * k0 * (k : GR n)) = _
        rw [show p0 * k0 * (k : GR n) = p0 * ((K0 * k : KR n) : GR n) by
          rw [Subgroup.coe_mul, hK0, mul_assoc], hJ, hshift k]
        ring
    _ = ((hLoc p0 : ℂ) ^ w * F0 p q e p0 * F0 p q e k0) *
        ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n) ∂μ := by
        rw [integral_const_mul]
        congr 1
        exact integral_mul_left_eq_self
          (fun k : KR n => (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n)) K0
    _ = _ := by
        rw [(hM1 p0 k0 hk0).1, (hM1 p0 k0 hk0).2]
        unfold czLoc
        ring

theorem cz_zero (p q : ℕ) (e : ℤ) (a b : M2 n) (ha : InG a) (hb : InG b) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    [MeasurableSpace (KR n)] (μ : Measure (KR n)) :
    czLoc p q e (mkG a ha) (mkG b hb) ψ μ 0 = (a.det * b.det) ^ e *
      ∫ k : KR n, (∫ x, f0 p q (mR (k : GR n) * a * nU (herm x) * b) * ψ x) * (f0 p q (mR (k : GR n)))⁻¹ ∂μ := by
  have hmul : ∀ g h : GR n, mR (g * h) = mR g * mR h := fun _ _ => rfl
  have hdetN : ∀ x, (nU (herm x) : M2 n).det = 1 := by
    intro x
    simp [nU, det_fromBlocks_zero₂₁]
  unfold czLoc
  rw [← integral_const_mul]
  congr 1
  funext k
  have hk : (mR (k : GR n)).det ^ e ≠ 0 := by
    apply zpow_ne_zero
    have h1 : (mR (k : GR n)).det * (mR ((k : GR n)⁻¹)).det = 1 := by
      rw [← det_mul, ← hmul, mul_inv_cancel]
      exact det_one
    exact left_ne_zero_of_mul_eq_one h1
  unfold jLoc
  simp only [Complex.cpow_zero, one_mul, F0, hmul, mR_mkG, nbEl, det_mul, hdetN, mul_one, mul_zpow,
    mul_assoc, integral_const_mul]
  generalize (mR (k : GR n)).det ^ e = D at hk ⊢
  have hD := inv_mul_cancel₀ hk
  rw [mul_inv]
  linear_combination (det a ^ e * (det b ^ e *
    ((∫ (x : Fin n → Fin n → ℝ), f0 (↑p) (↑q) (mR (k : GR n) * (a * (nU (herm x) * b))) * ψ x) *
      (f0 (↑p) (↑q) (mR (k : GR n)))⁻¹))) * hD

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G]

def hz (Ht : G → ℝ≥0) (sec : PX m n →ₗ[ℂ] (G → ℂ)) (s₀ z : ℂ) (x : G) : ℂ := ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x

def Top [MeasurableSpace (KR n)] (μ : Measure (KR n)) (ι : GR n →* G) (p q : ℕ) (e : ℤ) (a b : GR n)
    (nb : (Fin n → Fin n → ℝ) → GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (F : G → ℂ) (g : G) : ℂ :=
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) ∂μ

variable [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem top_sing [MeasurableSpace (KR n)] (μ : Measure (KR n)) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n} {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    (hnb : ∀ x, mR (nb x) = nU (herm x)) (F : G → ℂ) (hF : Continuous F) (hinv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g)
    (hl : ∀ l ∈ Λ, l F = 0) (g : G) : Top μ ι p q e a b nb ψ F g = 0 := by
  unfold Top
  have : ∀ k : KR n, (∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) = 0 := fun k =>
    hG.Λsing F hF hinv hl ψ hψ nb hnb g ((k : GR n) * a) b
  simp only [this, mul_zero, integral_zero]

theorem hz_split (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (g : G) :
    ∃ (y : GR n) (K : ℂ) (r : ℝ), 0 < r ∧ ∀ (z : ℂ) (w : GR n), hz Ht sec s₀ z (g * ι w) =
      K * ((r : ℂ) ^ (z - s₀)) * (((hLoc (y * w) : ℝ) : ℂ) ^ (z - s₀) * F0 p q e (y * w)) := by
  obtain ⟨x0, y, S, r, hr, hg, hsp⟩ := hG.split g
  refine ⟨y, S, r, hr, fun z w => ?_⟩
  have h1 := hsp (y * w)
  have e1 : g * ι w = x0 * ι (y * w) := by rw [hg, map_mul, mul_assoc]
  rw [e1]
  simp only [hz]
  rw [h1.1, h1.2 1, hL.vac, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_nonneg _)]
  ring

theorem top_hz [MeasurableSpace (KR n)] (μ : Measure (KR n)) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n}
    {ψ : (Fin n → Fin n → ℝ) → ℂ} {cz : ℂ → ℂ}
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    (z : ℂ) (g : G) : Top μ ι p q e a b nb ψ (hz Ht sec s₀ z) g = cz (z - s₀) * hz Ht sec s₀ z g := by
  obtain ⟨y, K, r, hr, hsp⟩ := hz_split hL hG g
  have e1 : ∀ (k : KR n) x, hz Ht sec s₀ z (g * ι ((k : GR n) * a * nb x * b)) * ψ x =
      (K * (r : ℂ) ^ (z - s₀)) * ((((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) := by
    intro k x
    rw [hsp]
    simp only [mul_assoc]
  have e2 : hz Ht sec s₀ z g = K * (r : ℂ) ^ (z - s₀) * (((hLoc y : ℝ) : ℂ) ^ (z - s₀) * F0 p q e y) := by
    have := hsp z 1
    rwa [map_one, mul_one, mul_one] at this
  unfold Top
  simp_rw [e1, MeasureTheory.integral_const_mul]
  have e3 : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ * (K * (r : ℂ) ^ (z - s₀) * ∫ x, (((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) = (K * (r : ℂ) ^ (z - s₀)) * ((F0 p q e (k : GR n))⁻¹ * ∫ x, (((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) := fun k => by ring
  simp_rw [e3, MeasureTheory.integral_const_mul, hceig, e2]
  ring

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

section

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Real

namespace PositivityTheory.Rg.Sw.AbsSt

theorem clm_circleIntegral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) : L (∮ z in C(c, R), f z) = ∮ z in C(c, R), L (f z) := by
  unfold circleIntegral
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm L hf.out]
  congr 1
  funext θ
  exact L.map_smul _ _

theorem banachHol : BanachHol := by
  intro X _ _ U F hU hF hd
  have hG : Continuous (fun p : U × X => F p.1.1 p.2) :=
    hF.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.2, mem_univ _⟩)
  let K : C(U, C(X, ℂ)) := (⟨_, hG⟩ : C(U × X, ℂ)).curry
  classical
  let Φ : ℂ → C(X, ℂ) := fun z => if h : z ∈ U then K ⟨z, h⟩ else 0
  have hΦ : ∀ z ∈ U, ∀ x, Φ z x = F z x := by
    intro z hz x
    simp [Φ, K, hz]
  have hc : ContinuousOn Φ U := by
    rw [continuousOn_iff_continuous_restrict]
    convert K.continuous using 1
    funext z
    show Φ z = K z
    simp only [Φ, dif_pos z.2, Subtype.coe_eta]
  refine ⟨Φ, ?_, hΦ⟩
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨R, hR0, hRU⟩ : ∃ R > 0, closedBall w R ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU w hw
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  let R' : NNReal := ⟨R, hR0.le⟩
  have hsph : sphere w R ⊆ U := sphere_subset_closedBall.trans hRU
  have hint : CircleIntegrable Φ w R' := (hc.mono hsph).circleIntegrable hR0.le
  have hps := hasFPowerSeriesOn_cauchy_integral hint (show (0 : NNReal) < R' from hR0)
  have heq : Φ =ᶠ[𝓝 w] (fun v => (2 * ↑π * I)⁻¹ • ∮ z in C(w, ↑R'), (z - v)⁻¹ • Φ z) := by
    filter_upwards [ball_mem_nhds w hR0] with v hv
    ext x
    show Φ v x = ((2 * ↑π * I)⁻¹ • ∮ z in C(w, R), (z - v)⁻¹ • Φ z) x
    have ha : ContinuousOn (fun z : ℂ => (z - v)⁻¹) (sphere w R) := by
      apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro z hz h
      have hzv : z = v := sub_eq_zero.mp h
      subst hzv
      rw [mem_sphere] at hz
      rw [mem_ball] at hv
      linarith
    have hcv : ContinuousOn (fun z => (z - v)⁻¹ • Φ z) (sphere w R) :=
      ContinuousOn.smul (f := fun z : ℂ => (z - v)⁻¹) (g := Φ) ha (hc.mono hsph)
    have h1 := clm_circleIntegral (ContinuousMap.evalCLM ℂ x) (hcv.circleIntegrable hR0.le)
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply] at h1
    have h2 : (∮ z in C(w, R), (z - v)⁻¹ • Φ z) x = ∮ z in C(w, R), (z - v)⁻¹ • F z x := by
      rw [h1]
      apply circleIntegral.integral_congr hR0.le
      intro z hz
      simp only
      rw [hΦ z (hsph hz) x]
    have h3 := ((hd x).mono hRU).circleIntegral_sub_inv_smul hv
    rw [ContinuousMap.smul_apply, h2, h3, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul,
      hΦ v (hRU (ball_subset_closedBall hv))]
  exact hps.analyticAt.differentiableAt.congr_of_eventuallyEq heq

theorem dslopeFam : DslopeFam := by
  intro X _ _ U s₀ F hU hs hF hd h0
  have hU0 : U ∈ 𝓝 s₀ := hU.mem_nhds hs
  refine ⟨?_, fun x => (differentiableOn_dslope hU0).mpr (hd x)⟩
  rintro ⟨z₀, x₀⟩ hp
  have hz₀ : z₀ ∈ U := hp.1
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x₀
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hF' : ContinuousOn (fun y : ℂ × K => F y.1 y.2) (U ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := banachHol (↥K) U (fun z (y : ↥K) => F z y) hU hF' (fun y => hd y)
  have hD : ContinuousOn (dslope Φ s₀) U := ((differentiableOn_dslope hU0).mpr hΦd).continuousOn
  have hval : ∀ z ∈ U, ∀ y : K, dslope Φ s₀ z y = dslope (fun z => F z y) s₀ z := by
    intro z hz y
    have heqon : EqOn (fun z => F z y) ((ContinuousMap.evalCLM ℂ y) ∘ Φ) U := by
      intro u hu
      simp [hΦ u hu y]
    rw [show dslope Φ s₀ z y = ContinuousMap.evalCLM ℂ y (dslope Φ s₀ z) from rfl,
      ← ContinuousLinearMap.dslope_comp _ _ _ _ (fun _ => (hΦd s₀ hs).differentiableAt hU0)]
    by_cases hzs : z = s₀
    · rw [hzs, dslope_same, dslope_same]
      exact (Filter.eventuallyEq_of_mem hU0 heqon).deriv_eq.symm
    · rw [dslope_of_ne _ hzs, dslope_of_ne _ hzs]
      simp [slope_def_field, hΦ z hz y, hΦ s₀ hs y]
  have hcont : ContinuousOn (fun y : ℂ × X => dslope (fun z => F z y.2) s₀ y.1) (U ×ˢ K) := by
    rw [continuousOn_iff_continuous_restrict]
    have hDr : Continuous (fun q : ↥(U ×ˢ K) => dslope Φ s₀ q.1.1) :=
      hD.comp_continuous (continuous_fst.comp continuous_subtype_val) (fun q => q.2.1)
    have hKr : Continuous (fun q : ↥(U ×ˢ K) => (⟨q.1.2, q.2.2⟩ : K)) :=
      (continuous_snd.comp continuous_subtype_val).subtype_mk _
    convert continuous_eval.comp (hDr.prodMk hKr) using 1
    funext q
    exact (hval q.1.1 q.2.1 ⟨q.1.2, q.2.2⟩).symm
  have hmem : U ×ˢ K ∈ 𝓝[U ×ˢ univ] (z₀, x₀) := by
    have hsub : (U ×ˢ univ) ∩ (univ ×ˢ K) ⊆ U ×ˢ K := fun q hq => ⟨hq.1.1, hq.2.2⟩
    exact mem_of_superset (inter_mem_nhdsWithin _ (prod_mem_nhds univ_mem hKn)) hsub
  exact (hcont (z₀, x₀) ⟨hz₀, mem_of_mem_nhds hKn⟩).mono_of_mem_nhdsWithin hmem

end PositivityTheory.Rg.Sw.AbsSt
end
end
