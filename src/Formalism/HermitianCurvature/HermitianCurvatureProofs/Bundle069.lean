module

public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section peel

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem sign_last (m : ℕ) : ((((-1 : ℤ) ^ (m + m) : ℤ) : A)) = 1 := by
  rw [← two_mul, pow_mul]
  norm_num

theorem smul_mem' (I : Ideal A) (c : ℂ) {x : A} (hx : x ∈ I) : c • x ∈ I := by
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ hx

theorem peel_core {m : ℕ} (I : Ideal A) {ι : Type} [Fintype ι] (η : ι → ℂ) (Q : Fin (m + 1) → A)
    (T : Fin (m + 1) → ι → A) (κ : ℂ)
    (hT : ∀ l, (∑ w, η w • T l w) - algebraMap ℂ A (if l = Fin.last m then κ else 0) ∈ I) :
    (∑ w, η w • ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) * (Q l * T l w)) -
      κ • Q (Fin.last m) ∈ I := by
  have key : (∑ w, η w • ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) * (Q l * T l w)) -
      κ • Q (Fin.last m) = ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) *
        (Q l * ((∑ w, η w • T l w) - algebraMap ℂ A (if l = Fin.last m then κ else 0))) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
    congr 1
    · exact Finset.sum_comm
    · rw [Finset.sum_eq_single (Fin.last m)]
      · rw [if_pos rfl, Fin.val_last, sign_last, one_mul, Algebra.smul_def, Algebra.commutes]
      · intro l _ hl
        rw [if_neg hl, map_zero, mul_zero, mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
  rw [key]
  exact Submodule.sum_mem _ fun l _ => I.mul_mem_left _ (I.mul_mem_left _ (hT l))

theorem peel_col {n m : ℕ} (I : Ideal A) (E : Fin n → Fin n → A) {ι : Type} [Fintype ι] (η : ι → ℂ)
    (a : Fin (m + 1) → Fin n) (b0 : Fin m → Fin n) (bw : ι → Fin n) (u κ : ℂ)
    (hT : ∀ l, (∑ w, η w • Tm E (u - (m : ℂ)) (a l) (bw w)) - algebraMap ℂ A (if l = Fin.last m then κ else 0) ∈ I) :
    (∑ w, η w • qminor E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u) - κ • qminor E (a ∘ Fin.castSucc) b0 u ∈ I := by
  have hexp : ∀ w, qminor E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u =
      ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) *
        (qminor E (a ∘ l.succAbove) b0 u * Tm E (u - (m : ℂ)) (a l) (bw w)) := by
    intro w
    rw [Formalism.FourierDecayAlt.P.expansion_last_column A n m E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u]
    congr 1; ext l
    have h1 : (Fin.snoc (α := fun _ => Fin n) b0 (bw w) : Fin (m + 1) → Fin n) ∘ Fin.castSucc = b0 := by
      funext x; simp [Fin.snoc_castSucc]
    rw [h1, Fin.snoc_last]
  simp_rw [hexp]
  have := peel_core I η (fun l => qminor E (a ∘ l.succAbove) b0 u) (fun l w => Tm E (u - (m : ℂ)) (a l) (bw w)) κ hT
  simpa [Fin.succAbove_last] using this

theorem hT_of (I : Ideal A) {ι : Type} [Fintype ι] (η : ι → ℂ) (X : ι → A) (d : ι → ℂ) (c : ℂ)
    (hX : ∀ w, X w - algebraMap ℂ A (d w) ∈ I) (hc : ∑ w, η w * d w = c) :
    (∑ w, η w • X w) - algebraMap ℂ A c ∈ I := by
  have e : (∑ w, η w • X w) - algebraMap ℂ A c = ∑ w, η w • (X w - algebraMap ℂ A (d w)) := by
    rw [← hc]

    simp only [smul_sub, Finset.sum_sub_distrib, map_sum, map_mul, Algebra.smul_def, mul_sub]
  rw [e]
  exact Submodule.sum_mem _ fun w _ => smul_mem' I _ (hX w)

end peel

def pe (k r p : ℕ) : Fin (2 * r + k + 1) := ⟨min p (2 * r + k), by omega⟩
def ps (k r p : ℕ) : Fin (2 * r + k + 1) := ⟨2 * r + k - p, by omega⟩

@[simp] theorem pe_val (k r p : ℕ) : (pe k r p).val = min p (2 * r + k) := rfl
@[simp] theorem ps_val (k r p : ℕ) : (ps k r p).val = 2 * r + k - p := rfl

theorem mem_gen {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ} {z' : Fin (2 * r + k + 1) → ℂ}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {p q : Fin (2 * r + k + 1)} (h : InNp k r p q) :
    E p q - algebraMap ℂ A (dpsiP k r z' p q) ∈ Ideal.span (rgen k r z' E) := Ideal.subset_span ⟨p, q, h, rfl⟩

theorem tm_offdiag {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) {p q : Fin n}
    (h : p ≠ q) : Tm E u p q = E p q := by
  simp [Tm, h]

theorem last_iff {m : ℕ} (l : Fin (m + 1)) : l = Fin.last m ↔ l.val = m := by
  rw [Fin.ext_iff, Fin.val_last]

theorem first_peeling_minor_mem_ideal {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (u : ℂ) : ∀ (m i : ℕ), i ≤ m → m + 1 ≤ r →
    qminor E (fun l : Fin m => pe k r l.val) (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u -
      qminor E (fun l : Fin i => pe k r l.val) (fun l : Fin i => pe k r l.val) u ∈ Ideal.span (rgen k r z' E) := by
  intro m
  induction m with
  | zero =>
    intro i hi _
    have hi0 : i = 0 := by omega
    subst hi0
    have e : (fun l : Fin 0 => pe k r (if l.val < 0 then l.val else l.val + 1)) = fun l : Fin 0 => pe k r l.val :=
      funext fun l => l.elim0
    rw [e, sub_self]
    exact Submodule.zero_mem _
  | succ m ih =>
    intro i hi hr
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · have hih := ih i (by omega) (by omega)
      have hstep : qminor E (fun l : Fin (m + 1) => pe k r l.val)
            (fun l : Fin (m + 1) => pe k r (if l.val < i then l.val else l.val + 1)) u -
          qminor E (fun l : Fin m => pe k r l.val)
            (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u ∈
            Ideal.span (rgen k r z' E) := by
        have hc := peel_core (Ideal.span (rgen k r z' E)) (ι := Unit) (fun _ => (1 : ℂ))
          (fun l : Fin (m + 1) => qminor E ((fun l : Fin (m + 1) => pe k r l.val) ∘ l.succAbove)
              (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u)
          (fun l _ => Tm E (u - (m : ℂ)) (pe k r l.val) (pe k r (m + 1))) 1 ?_
        · rw [Formalism.FourierDecayAlt.P.expansion_last_column A (2 * r + k + 1) m E]
          have hm : ¬ (m < i) := by omega
          simpa [Fin.succAbove_last, Fin.val_last, hm, Function.comp_def, Fin.coe_castSucc] using hc
        · intro l
          have hl := l.isLt
          have h1 : min (l.val) (2 * r + k) = l.val := Nat.min_eq_left (by omega)
          have h2 : min (m + 1) (2 * r + k) = m + 1 := Nat.min_eq_left (by omega)
          have hne : pe k r l.val ≠ pe k r (m + 1) := by
            intro e
            have := congrArg Fin.val e
            simp only [pe_val, h1, h2] at this
            omega
          have hin : InNp k r (pe k r l.val) (pe k r (m + 1)) := by
            simp only [InNp, pe_val, h1, h2]
            omega
          have hd : dpsiP k r z' (pe k r l.val) (pe k r (m + 1)) = if l.val = m then 1 else 0 := by
            simp only [dpsiP, pe_val, h1, h2]
            rw [if_pos ⟨by omega, by omega⟩]
            split_ifs <;> first | rfl | (exfalso; omega)
          simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, last_iff]
          rw [tm_offdiag _ _ hne, ← hd]
          exact mem_gen hin
      have hsum := (Ideal.span (rgen k r z' E)).add_mem hstep hih
      rwa [sub_add_sub_cancel] at hsum
    · have hi1 : i = m + 1 := by omega
      subst hi1
      have e : (fun l : Fin (m + 1) => pe k r (if l.val < m + 1 then l.val else l.val + 1)) =
          fun l : Fin (m + 1) => pe k r l.val := by
        funext l
        rw [if_pos l.isLt]
      rw [e, sub_self]
      exact Submodule.zero_mem _

theorem first_peeling_identity : PeelingOmittedColumn := by
  intro A _ _ k r z' E m hm i u
  have e1 : ∀ (j : ℕ) (hj : j ≤ r), xR k r j hj = fun l : Fin j => pe k r l.val := by
    intro j hj
    funext l
    apply Fin.ext
    simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, pe_val]
    have := l.isLt
    omega
  have e2 : (fun l : Fin m => xR k r (m + 1) hm (i.succAbove l)) =
      fun l : Fin m => pe k r (if l.val < i.val then l.val else l.val + 1) := by
    funext l
    apply Fin.ext
    simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, pe_val, succAbove_val]
    have := l.isLt
    split_ifs <;> omega
  rw [e2, e1, e1]
  exact first_peeling_minor_mem_ideal k r z' E u m i.val (by have := i.isLt; omega) hm

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Qb1

variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]

theorem ckOn_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (h : CkOn m (GV k r) f) : CkOn m (GV k r) f' := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  exact ⟨U, F, a, b, c, fun g hg hgG => (he g hgG).symm.trans (d g hg hgG)⟩

variable {σ : Mx k r → (Vs →L[ℂ] Vs)}

theorem lie1 (Z : Mx k r) : inLie k r (hpart1 (Hpk k r) Z) := Qx2.hpart1_lie Z

theorem lie2 (Z : Mx k r) : inLie k r (hpart2 (Hpk k r) Z) := Qx2.hpart2_lie Z

end Qb1

end Formalism.FourierDecayAlt.P
end
end

section

theorem Formalism.FourierDecayAlt.P.rtt_level_from_upper : Formalism.FourierDecayAlt.Q.RTTLevelFromUpper := by
  intro hU hLT hGI hFF _ k r i
  induction i using Fin.cases with
  | succ l => exact hU k r l
  | zero =>
    intro Wp Wq _ _ _ _ z z' π π' D hz hz' hD J hJ g hg u v a b c d
    obtain ⟨π₁, π₁', D₁, f, hw, hw', hD₁, hf, hfJ⟩ := hFF Wp Wq k r z z' π π' D hz hz' hD J hJ
    have key : ∀ (Y Y' : ℂ) (p q p' q' : Fin 2),
        Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z') ⟨1, by omega⟩
                  Y p q (Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z')
                    ⟨1, by omega⟩ Y' p' q' f) (Formalism.QuantumDeterminants.ιLev k 1 r g) =
          Formalism.FourierDecayAlt.Q.tL k r z z' 0 Y p q (Formalism.FourierDecayAlt.Q.tL k r z z' 0 Y' p' q' J) g := by
      intro Y Y' p q p' q'
      rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y p q _ g hg.1.1]
      refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y p q).loc _ _ ?_ g hg
      intro x hx
      rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y' p' q' f x hx.1.1]
      refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y' p' q').loc _ _ ?_ x hx
      intro y hy
      exact (hfJ y hy.1.1).2
    have hιg : Formalism.QuantumDeterminants.ιLev k 1 r g ∈ Formalism.FourierDecayAlt.Q.Glev k (1 + r) ⟨1, by omega⟩ ∩ D₁ := by
      refine ⟨?_, (hfJ g hg.1.1).1.mpr hg.2⟩
      rw [hGI k 1 r]
      exact ⟨g, hg.1.1, rfl⟩
    have h1 : Formalism.FourierDecayAlt.Q.RTTAt k (1 + r) ⟨1, by omega⟩ := hU k (1 + r) ⟨0, by omega⟩
    have h := h1 Wp Wq _ _ π₁ π₁' D₁ hw hw' hD₁ f hf _ hιg u v a b c d
    simp only [key] at h
    exact h
end

section

open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem gnLower : GNLower := fun _ _ _ hg => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg

theorem ae_mem {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ g ∂μ, Matrix.of g ∈ U := by
  rw [ae_iff]
  exact h.conc

end Formalism.FourierDecayAlt.P.NormBallVolumes

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.NormBallVolumes

theorem matrix_coefficient_bound_by_norm : Formalism.FourierDecayAlt.B2.CCFromGN := by
  intro k r Wp Wq _ _ _ _ D A h F c _ hb
  have hae : ∀ᵐ g ∂D.μG, ‖F (Matrix.of g)‖ₑ ≤ ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) := by
    filter_upwards [ae_mem D.haarG] with g hg
    have h1 := hb _ hg
    have hpos : 0 < gN (Matrix.of g) := lt_of_lt_of_le one_pos (gnLower k r _ hg)
    have hp : 0 < gN (Matrix.of g) ^ A := Real.rpow_pos_of_pos hpos A
    rw [← ENNReal.ofReal_mul (abs_nonneg c), ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ hp]
    calc ‖F (Matrix.of g)‖ * gN (Matrix.of g) ^ A = gN (Matrix.of g) ^ A * ‖F (Matrix.of g)‖ := mul_comm _ _
      _ ≤ c := h1
      _ ≤ |c| := le_abs_self c
  calc (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g : Mt k r, ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG := lintegral_mono_ae hae
    _ = ENNReal.ofReal |c| * ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem matrix_coefficient_integrable_of_parts : Formalism.FourierDecayAlt.B2.AssembleCCInt := by
  intro h1 h2 k r Wp Wq _ _ _ _ D A hA
  exact h1 k r Wp Wq D A (h2 k r D.μG A D.haarG hA)

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

end Formalism.FourierDecayAlt.P.NormBallVolumes
end
end
