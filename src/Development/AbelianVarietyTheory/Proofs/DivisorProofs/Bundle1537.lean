module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadratic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.MovedLat

open Formalism.UG

theorem htFin_bc_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (g : GL n (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) :
    htFin F v (bc (compFin F E v) g⁻¹) = htFin F v (bc (compFin F E v) g) := by
  rw [map_inv]; exact htOf_inv _ _

theorem finprod_htFin_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (g : GL n (AF F ⊗[F] E)) :
    ∏ᶠ v, htFin F v (bc (compFin F E v) g) ≤ heightGL F g :=
  le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)

end GlobalTheory.MovedLat

open Formalism.UG

theorem GlobalTheory.MovedLat.exists_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (N : ℕ), 1 ≤ N →
    ∃ (C : ℝ) (k : ℕ), ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ m : ℕ, 1 ≤ m ∧
      (m : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ^ k ∧ ∀ i j : κ,
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j) ∧
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j) := by
  intro F E _ _ _ _ _ n d κ _ _ e N hN
  classical
  let f1 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) := fun j =>
    (LinearMap.proj j).comp ((LinearMap.fst (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)
  let f2 : κ → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) := fun j =>
    (LinearMap.proj j).comp ((LinearMap.snd (AF F) (κ → AF F) (κ → AF F)).comp e.toLinearMap)
  choose K1 hK1f hK1 hK1b using fun j => GlobalTheory.LinFormBound.main (f1 j)
  choose K2 hK2f hK2 hK2b using fun j => GlobalTheory.LinFormBound.main (f2 j)
  let Y : κ → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) := fun i => e.symm (0, Pi.single i 1)
  choose Kx hKxf hKx hKxb using fun i => GlobalTheory.FixedBound.exists_entry_absFin_bound (Y i)
  let Kc : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => (∏ j, K1 j v * K2 j v) * ∏ i, Kx i v
  have hKc1 : ∀ v, 1 ≤ Kc v := fun v =>
    one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.one_le_prod' fun i _ => hKx i v)
  have hKcf : (Function.mulSupport Kc).Finite := by
    refine ((Set.finite_iUnion fun j => (hK1f j).union (hK2f j)).union (Set.finite_iUnion hKxf)).subset ?_
    refine (Function.mulSupport_mul _ _).trans (Set.union_subset_union ?_ ?_)
    · refine (Finset.mulSupport_prod _ _).trans ?_
      intro v hv
      simp only [Set.mem_iUnion] at hv ⊢
      obtain ⟨j, -, hj⟩ := hv
      exact ⟨j, Function.mulSupport_mul _ _ hj⟩
    · refine (Finset.mulSupport_prod _ _).trans ?_
      intro v hv
      simp only [Set.mem_iUnion] at hv ⊢
      obtain ⟨i, -, hi⟩ := hv
      exact ⟨i, hi⟩
  have hP1 : ∀ v, ∏ j, K1 j v * K2 j v ≤ Kc v := fun v =>
    le_mul_of_one_le_right' (Finset.one_le_prod' fun i _ => hKx i v)
  have hP2 : ∀ v, ∏ i, Kx i v ≤ Kc v := fun v =>
    le_mul_of_one_le_left' (Finset.one_le_prod' fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
  have hK1c : ∀ v i j, K1 j v * Kx i v ≤ Kc v := fun v i j => by
    refine le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))
    exact mul_le_mul' (le_mul_of_one_le_right' (hK2 j v)) le_rfl
  have hK2c : ∀ v i j, K2 j v * Kx i v ≤ Kc v := fun v i j => by
    refine le_trans ?_ (mul_le_mul' (Finset.single_le_prod' (fun j _ => one_le_mul_of_one_le_of_one_le (hK1 j v) (hK2 j v))
      (Finset.mem_univ j)) (Finset.single_le_prod' (fun i _ => hKx i v) (Finset.mem_univ i)))
    exact mul_le_mul' (le_mul_of_one_le_left' (hK1 j v)) le_rfl
  let C0 : ℝ≥0 := ∏ᶠ v, Kc v
  refine ⟨N * C0, 1, fun g h => ?_⟩
  let Hg : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => htFin F v (bc (compFin F E v) g)
  let Hh : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => htFin F v (bc (compFin F E v) h)
  have hgf : (Function.mulSupport Hg).Finite := finite_mulSupport_htFin F g
  have hhf : (Function.mulSupport Hh).Finite := finite_mulSupport_htFin F h
  let Z : κ → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) := fun i =>
    ((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * Y i *
      (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ
  have hsup : ∀ i v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Z i p.1 p.2))) ≤
      Kx i v * (Hg v * Hh v) := fun i v => by
    refine Finset.sup_le fun p _ => (GlobalTheory.absFin_mul_mul_transpose_le g⁻¹ (Y i) h⁻¹ v p.1 p.2).trans ?_
    rw [GlobalTheory.MovedLat.htFin_bc_inv, GlobalTheory.MovedLat.htFin_bc_inv]
    calc _ ≤ Hg v * Kx i v * Hh v := mul_le_mul' (mul_le_mul' le_rfl (hKxb i v)) le_rfl
      _ = Kx i v * (Hg v * Hh v) := by ring
  have hloc1 : ∀ i j v, ‖evFin F v ((e (Z i)).1 j)‖₊ ≤ Kc v * (Hg v * Hh v) := fun i j v => by
    have := hK1b j (Z i) v
    calc _ ≤ K1 j v * (Kx i v * (Hg v * Hh v)) := this.trans (mul_le_mul' le_rfl (hsup i v))
      _ = (K1 j v * Kx i v) * (Hg v * Hh v) := by ring
      _ ≤ Kc v * (Hg v * Hh v) := mul_le_mul' (hK1c v i j) le_rfl
  have hloc2 : ∀ i j v, ‖evFin F v ((e (Z i)).2 j)‖₊ ≤ Kc v * (Hg v * Hh v) := fun i j v => by
    have := hK2b j (Z i) v
    calc _ ≤ K2 j v * (Kx i v * (Hg v * Hh v)) := this.trans (mul_le_mul' le_rfl (hsup i v))
      _ = (K2 j v * Kx i v) * (Hg v * Hh v) := by ring
      _ ≤ Kc v * (Hg v * Hh v) := mul_le_mul' (hK2c v i j) le_rfl
  let H : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => Kc v * (Hg v * Hh v)
  have hH1 : ∀ v, 1 ≤ H v := fun v =>
    one_le_mul_of_one_le_of_one_le (hKc1 v) (one_le_mul_of_one_le_of_one_le (one_le_htOf _ _) (one_le_htOf _ _))
  have hHf : (Function.mulSupport H).Finite :=
    (hKcf.union (hgf.union hhf)).subset ((Function.mulSupport_mul _ _).trans
      (Set.union_subset_union le_rfl (Function.mulSupport_mul _ _)))
  obtain ⟨M, hM0, hMb, hMv⟩ := GlobalTheory.SmoothForms.denom_global H hH1 hHf
  have hfin : ∀ x : AF F, (∀ v, ‖evFin F v x‖₊ ≤ H v) → GlobalTheory.FinSupp.FinDiv F N (((N * M : ℕ) : AF F) * x) := by
    intro x hx v
    refine ⟨(M : Fv F v) * evFin F v x, Valued.toNormedField.norm_le_one_iff.1 (hMv v _ (hx v)), ?_⟩
    rw [map_mul, map_natCast]
    push_cast
    ring
  refine ⟨N * M, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun i j => ⟨hfin _ (hloc1 i j), hfin _ (hloc2 i j)⟩⟩
  have hMH : (M : ℝ≥0) ≤ C0 * (heightGL F g * heightGL F h) := by
    refine hMb.trans (le_of_eq_of_le (finprod_mul_distrib hKcf ((hgf.union hhf).subset (Function.mulSupport_mul _ _))) ?_)
    refine mul_le_mul' le_rfl ?_
    rw [finprod_mul_distrib hgf hhf]
    exact mul_le_mul' (GlobalTheory.MovedLat.finprod_htFin_le g) (GlobalTheory.MovedLat.finprod_htFin_le h)
  have := NNReal.coe_le_coe.2 hMH
  push_cast at this ⊢
  rw [pow_one, mul_assoc]
  exact mul_le_mul_of_nonneg_left this (by positivity)
end
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.QuadFockD

open GlobalTheory.RealLift.QuadFock

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

abbrev MD (P Q R S : ι → ℕ) (w : ι) : Type := Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ

theorem sumPl_singleD (w : ι) (M : MD P Q R S w) :
    sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w))
      (fun w' => heisOp ((Pi.single w M : ∀ w', MD P Q R S w') w')) = atPl w (heisOp M) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro b _ hb
    dsimp only
    rw [Pi.single_eq_of_ne hb, heisOp_zero, atPl_zero]
  · simp

def eS (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) : ∀ w', MD P Q R S w' :=
  Pi.single w (Matrix.single a b x)

theorem eS_ne (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) {w' : ι} (h : w' ≠ w) :
    eS w a b x w' = 0 := by
  simp [eS, Pi.single_eq_of_ne h]

theorem eS_same (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) :
    eS w a b x w = Matrix.single a b x := by
  simp [eS]

theorem sum_eS (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) (c : ∀ w', MD P Q R S w') :
    (∑ w', ∑ a', ∑ b', lineSign a' b' * eS w a b x w' a' b' * star (c w' a' b')) =
      lineSign a b * x * star (c w a b) := by
  rw [Finset.sum_eq_single w]
  · rw [eS_same, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp [Matrix.single_apply]
    · intro y _ hy; simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun b' _ => ?_
      simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
  · intro y _ hy
    simp [eS_ne w a b x hy]
  · simp

theorem decomp (c : ∀ w, MD P Q R S w) :
    c = ∑ w, ∑ a, ∑ b, ((c w a b).re • eS w a b 1 + (c w a b).im • eS w a b Complex.I) := by
  funext w
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [Finset.sum_eq_single w]
  · simp only [eS_same]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp only [Matrix.single_apply, and_self, if_true, Complex.real_smul, mul_one]
      exact (Complex.re_add_im _).symm
    · intro y _ hy; simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun b' _ => ?_
      simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => ?_
    simp [eS_ne _ _ _ _ (Ne.symm hy)]
  · simp

abbrev Idx (P Q R S : ι → ℕ) : Type := Σ w : ι, Ix (P w) (Q w) × Ix (R w) (S w) × Bool

def cu (i : Idx P Q R S) : ∀ w, MD P Q R S w :=
  if i.2.2.2 then (sgn i.2.1 i.2.2.1 / 2) • eS i.1 i.2.1 i.2.2.1 1
  else (-(sgn i.2.1 i.2.2.1 / 2)) • eS i.1 i.2.1 i.2.2.1 Complex.I

def cv (i : Idx P Q R S) : ∀ w, MD P Q R S w :=
  if i.2.2.2 then eS i.1 i.2.1 i.2.2.1 Complex.I else eS i.1 i.2.1 i.2.2.1 1

theorem sum_idx {M : Type} [AddCommMonoid M] (f : Idx P Q R S → M) :
    ∑ i, f i = ∑ w, ∑ a, ∑ b, (f ⟨w, a, b, true⟩ + f ⟨w, a, b, false⟩) := by
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]

theorem dual {l : Type} [Fintype l] (φ : (∀ w, MD P Q R S w) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (hφ : ∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im)
    (x : l ⊕ l → ℝ) : ∑ i, sympl (φ (cv i)) x • φ (cu i) = x := by
  obtain ⟨c, rfl⟩ := φ.surjective x
  have e1 : ∀ i, sympl (φ (cv i)) (φ c) • φ (cu i) = φ (sympl (φ (cv i)) (φ c) • cu i) :=
    fun i => (map_smul φ _ _).symm

  simp only [e1, ← map_sum]
  congr 1
  conv_rhs => rw [decomp c]
  rw [sum_idx]
  simp only [cu, cv, if_true, Bool.false_eq_true, if_false, hφ, sum_eS]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul, lineSign_eq_sgn]
  have h2 := sgn_mul_self a b
  congr 2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).re * h2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).im * h2

end GlobalTheory.HoweD.QuadFockD

namespace GlobalTheory.HoweD.QuadFockD

open GlobalTheory.RealLift.QuadFock

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

theorem cu_true_mul (Y : ∀ w, Mat (R w) (S w)) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (w' : ι) :
    cu (P := P) (Q := Q) ⟨w, a, b, true⟩ w' * (Y w')ᵀ =
      (Pi.single w ((sgn a b / 2) • (Matrix.single a b (1 : ℂ) * (Y w)ᵀ)) : ∀ w', MD P Q R S w') w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cu_false_mul (Y : ∀ w, Mat (R w) (S w)) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (w' : ι) :
    cu (P := P) (Q := Q) ⟨w, a, b, false⟩ w' * (Y w')ᵀ =
      (Pi.single w ((-(sgn a b / 2)) • (Matrix.single a b Complex.I * (Y w)ᵀ)) : ∀ w', MD P Q R S w') w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cv_true (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cv (P := P) (Q := Q) (R := R) (S := S) ⟨w, a, b, true⟩ =
      (Pi.single w (Matrix.single a b Complex.I) : ∀ w', MD P Q R S w') := by
  simp [cv, eS]

theorem cv_false (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cv (P := P) (Q := Q) (R := R) (S := S) ⟨w, a, b, false⟩ =
      (Pi.single w (Matrix.single a b (1 : ℂ)) : ∀ w', MD P Q R S w') := by
  simp [cv, eS]

end GlobalTheory.HoweD.QuadFockD

namespace GlobalTheory.HoweD

open GlobalTheory.RealLift.QuadFock GlobalTheory.HoweD.QuadFockD

theorem quad_fockD : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w)) T) := by
  intro ι l _ _ _ _ P Q R S φ hφ Ψ hΨ Y hY Z hZ T
  have hq := GlobalTheory.T.metaplecticQuadraticOperator_eq_sum_symplectic_dual l (Idx P Q R S) Z (fun i => φ (QuadFockD.cu i)) (fun i => φ (QuadFockD.cv i))
    (QuadFockD.dual φ hφ)
  have hop : sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w)) =
      (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i : Idx P Q R S, (1 / 2 : ℂ) •
        (sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cu i w * (Y w)ᵀ)) *
            sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cv i w)) +
          sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cv i w)) *
            sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cu i w * (Y w)ᵀ))) := by
    rw [sum_idx]
    simp only [QuadFockD.cu_true_mul, QuadFockD.cu_false_mul, QuadFockD.cv_true, QuadFockD.cv_false, sumPl_singleD,
      heisOp_smul]
    unfold sumPl
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    dsimp only
    rw [GlobalTheory.T.fockAct2_eq_symmetrised_heisenbergQuadratic (P w) (Q w) (R w) (S w) (Y w) (hY w)]

    simp only [← atPlLin_apply, map_smul, map_sum, map_sub, map_add (f := _), atPlLin_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [lineSign_eq_sgn]
    simp only [smul_mul_assoc, mul_smul_comm]
    push_cast
    module
  rw [hop, hq]
  clear hq hop hφ hY

  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
  ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
  LinearMap.add_apply, Module.End.mul_apply, map_smul, map_sum, map_add, hΨ, hZ]

end GlobalTheory.HoweD
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLiftComp

open Matrix GlobalTheory.RealLiftGen

theorem exists_comp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (InfinitePlace F → Mat R S), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) ∧ ∀ w (M M' : Mat R S), C w * M = C w * M' → M = M' := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC
  choose A' hA' using fun w => (hC w).2
  set K : InfinitePlace F → Matrix β β ℂ := fun w => b • J.map (piInf (τ w)) with hK
  have hF : ∀ w, (C w)ᵀ * K w * (C w).map star = Jm R S := fun w => (hC w).1
  have hAC : ∀ w, A' w * C w = 1 := by
    intro w
    have h1 : (Jm R S * (C w)ᵀ * K w) * (C w).map star = 1 := by
      rw [Matrix.mul_assoc (Jm R S), Matrix.mul_assoc (Jm R S), hF, Jm_mul_Jm]
    have h2 : (Jm R S * (C w)ᵀ * K w).map star * C w = 1 := by
      have := congrArg (fun X => X.map star) h1
      rw [map_star_mul, map_star_star] at this
      rw [this]; ext i j; simp [Matrix.one_apply]
    calc A' w * C w = ((Jm R S * (C w)ᵀ * K w).map star * C w) * A' w * C w := by rw [h2, Matrix.one_mul]
      _ = (Jm R S * (C w)ᵀ * K w).map star * C w := by rw [Matrix.mul_assoc _ (C w), hA', Matrix.mul_one]
      _ = 1 := h2
  set M : UG (cA σ) J → InfinitePlace F → Matrix β β ℂ :=
    fun g w => (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) with hM
  have hMmul : ∀ g h w, M (g * h) w = M g w * M h w := by
    intro g h w
    simp only [hM, Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul
  have hM1 : ∀ w, M 1 w = 1 := by
    intro w
    simp only [hM, OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hMu : ∀ g w, (M g w)ᵀ * K w * (M g w).map star = K w := by
    intro g w
    have hg := g.2
    change ((g.1 : Matrix β β (AE F E)))ᵀ * J * ((g.1 : Matrix β β (AE F E))).map (cA σ) = J at hg
    have h2 := congrArg (fun X => X.map (piInf (τ w))) hg
    simp only [Matrix.map_mul, Matrix.map_map] at h2
    have h3 : (piInf (τ w)) ∘ (cA σ) = star ∘ (piInf (τ w)) := funext fun x => piInf_cA hcm (τ w) x
    rw [h3, ← Matrix.map_map] at h2
    have h4 : (M g w)ᵀ * J.map (piInf (τ w)) * (M g w).map star = J.map (piInf (τ w)) := by
      simp only [hM]; rw [← Matrix.transpose_map]; exact h2
    simp only [hK, Matrix.mul_smul, Matrix.smul_mul]
    rw [h4]
  let k : UG (cA σ) J →* (InfinitePlace F → Mat R S) :=
    { toFun := fun g w => A' w * M g w * C w
      map_one' := by funext w; simp only [hM1, Matrix.mul_one, hAC, Pi.one_apply]
      map_mul' := by
        intro g h; funext w
        simp only [hMmul, Pi.mul_apply]
        calc A' w * (M g w * M h w) * C w = A' w * M g w * (C w * A' w) * M h w * C w := by
              rw [hA', Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hk : ∀ g w, k g w = A' w * M g w * C w := fun _ _ => rfl
  have hCk : ∀ g w, C w * k g w = M g w * C w := by
    intro g w; simp only [hk, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  refine ⟨k, ?_, fun g w => (hCk g w).symm, fun g w => ?_, fun w X X' h => ?_⟩
  · have h1 : Continuous (fun g : UG (cA σ) J => ((g.1 : Matrix β β (AE F E)))) :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_pi fun w => ?_
    exact (continuous_const.matrix_mul (h1.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (τ w)))).matrix_mul
      continuous_const
  · have hT : (k g w)ᵀ * Jm R S * (k g w).map star = Jm R S := by
      rw [← hF w]
      calc (k g w)ᵀ * ((C w)ᵀ * K w * (C w).map star) * (k g w).map star
          = (C w * k g w)ᵀ * K w * (C w * k g w).map star := by
            simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = (C w)ᵀ * ((M g w)ᵀ * K w * (M g w).map star) * (C w).map star := by
            simp only [hCk, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = _ := by rw [hMu]
    have h2 := congrArg (fun X => X.map star) hT
    simp only [map_star_mul, Jm_map_star, map_star_star] at h2
    exact h2
  · have := congrArg (fun Y => A' w * Y) h
    simpa only [← Matrix.mul_assoc, hAC, Matrix.one_mul] using this

end GlobalTheory.RealLiftComp
end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_signatureOrthonormalFrame_eigen_of_cartanInvolution : ∀ (n : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ), (∀ i j, star (M j i) = M i j) → M.det ≠ 0 → IsCartan M θ → ∃ (r s : ℕ) (A : Matrix (Fin n) (Ix r s) ℂ), IsFrame M A ∧ θ * A = A * Jm r s := by
  first | exact @GlobalTheory.HoweD.FrameCartan.frame_of_cartan | exact GlobalTheory.HoweD.FrameCartan.frame_of_cartan | (intros; apply GlobalTheory.HoweD.FrameCartan.frame_of_cartan <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.unitaryLieElements_generate_oneParamLines : GlobalTheory.RealLift.LineEx := by
  first | exact @GlobalTheory.RealLift.exists_line_of_upq | exact GlobalTheory.RealLift.exists_line_of_upq | (intros; apply GlobalTheory.RealLift.exists_line_of_upq <;> assumption)
end
