module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle628
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle670
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle671
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle654
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle290
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle555
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticesExistAllLayersOfBhattScholze
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section
variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

theorem cstW_mem_QSet_of_const (c : Wq l a) : cstW t K c ∈ QSet t K e := by
  refine ⟨fun p => if p = (0, 0) then c else 0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW]
  simp only [cstW, coeff_C]
  by_cases hi : i = 0
  · by_cases hn : n = 0
    · simp [hi, hn, dpDen]
    · simp [hi, hn, coeff_C]
  · simp [hi]

theorem exists_sigma_eq_pow_add (c : Wq l a) : ∃ d : Wq l a, sigma l a c = c ^ l + (l : Wq l a) * d := by
  have h : sigma l a c - c ^ l ∈ Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, coeff_sigma, sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h
  exact ⟨d, by rw [← hd]; ring⟩

end

theorem cstW_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ c : Wq l a, cstW t K c ∈ GoodSet t e φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _ c
  have h1 : frob2 φ₂ (cstW t K c) = cstW t K (sigma l a c) := by
    funext τ
    change φ₂ (cstW t K c (τ - 1)) = _
    simp only [cstW]
    rw [hC, frob_C, emb_sigma]
  refine ⟨cstW_mem_QSet_of_const t K e c, h1 ▸ cstW_mem_QSet_of_const t K e _, ?_⟩
  obtain ⟨d, hd⟩ := exists_sigma_eq_pow_add c
  refine ⟨cstW t K d, cstW_mem_QSet_of_const t K e d, ?_⟩
  rw [h1, hd]
  funext τ
  simp [cstW]

end GlobalTheory.CrysPrism
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem coeff_coeff_natCast_mul {K : Type} [CommRing K] (m i n : ℕ) (G : K⟦X⟧⟦X⟧) :
    coeff n (coeff i ((m : K⟦X⟧⟦X⟧) * G)) = (m : K) * coeff n (coeff i G) := by
  rw [← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul]

theorem goodSet_of_finite_of_local (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hfin : ∀ (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)),
      ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂)
    (hφ : ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)))
    (hpow : ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) →
      coeff n (coeff i (G ^ l)) = coeff n (coeff i (H ^ l))) :
    ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂ := by
  classical
  rintro z ⟨w, rfl⟩
  have key : ∀ p : ℕ × ℕ, ∃ v b : Wq l a, ∀ τ : ZMod a,
      coeff p.2 (coeff p.1 (frob2 φ₂ (ofW t K e w) τ)) =
        algebraMap O K (emb t τ v) / (dpDen e p.1 p.2 : K) ∧
      coeff p.2 (coeff p.1 (frob2 φ₂ (ofW t K e w) τ)) =
        coeff p.2 (coeff p.1 ((ofW t K e w τ) ^ l)) +
          (l : K) * (algebraMap O K (emb t τ b) / (dpDen e p.1 p.2 : K)) := by
    rintro ⟨i, n⟩
    set s : Finset (ℕ × ℕ) := Finset.range (i + 1) ×ˢ Finset.range (n + 1) with hs
    obtain ⟨-, ⟨v, hv⟩, B, ⟨b, rfl⟩, hB⟩ := hfin w s
    have hagree : ∀ τ : ZMod a, ∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' (ofW t K e w τ)) =
        coeff n' (coeff i' (ofW t K e (fun p => if p ∈ s then w p else 0) τ)) := by
      intro τ i' hi n' hn
      have hm : (i', n') ∈ s := by
        simp only [hs, Finset.mem_product, Finset.mem_range]
        omega
      rw [coeff_ofW, coeff_ofW, if_pos hm]
    refine ⟨v (i, n), b (i, n), fun τ => ?_⟩
    have h1 : coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) =
        coeff n (coeff i (frob2 φ₂ (ofW t K e (fun p => if p ∈ s then w p else 0)) τ)) :=
      hφ i n _ _ (hagree (τ - 1))
    refine ⟨?_, ?_⟩
    · rw [h1, ← hv, coeff_ofW]
    · rw [h1, hB, hpow i n _ _ (hagree τ), Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply,
        map_add, map_add, coeff_coeff_natCast_mul, coeff_ofW]
  choose v b hvb using key
  refine ⟨⟨w, rfl⟩, ⟨v, ?_⟩, ofW t K e b, ⟨b, rfl⟩, ?_⟩
  · funext τ
    ext i n
    rw [coeff_ofW]
    exact ((hvb (i, n) τ).1).symm
  · funext τ
    ext i n
    rw [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply,
        map_add, map_add, coeff_coeff_natCast_mul, coeff_ofW]
    exact (hvb (i, n) τ).2

end GlobalTheory.CrysPrism
end

section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.FinSupp

section
variable {K : Type} [CommRing K]

def Bd (M : ℕ) (F : K⟦X⟧⟦X⟧) : Prop := ∀ i n, M < i ∨ M < n → coeff n (coeff i F) = 0

theorem Bd.mono {M M' : ℕ} {F : K⟦X⟧⟦X⟧} (h : Bd M F) (hM : M ≤ M') : Bd M' F :=
  fun i n hin => h i n (by omega)

theorem Bd.mul {M M' : ℕ} {F G : K⟦X⟧⟦X⟧} (h : Bd M F) (h' : Bd M' G) : Bd (M + M') (F * G) := by
  intro i n hin

  rw [coeff_mul, map_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
  by_cases h1 : M < p.1 ∨ M < q.1
  · rw [h _ _ h1, zero_mul]
  · rw [h' _ _ (by omega), mul_zero]

theorem bd_CC (c : K) : Bd 0 (C (C c) : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_C]
  split_ifs with h
  · rw [coeff_C, if_neg (by omega)]
  · simp

theorem bd_CX : Bd 1 (C X : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_C]
  split_ifs with h
  · rw [coeff_X, if_neg (by omega)]
  · simp

theorem bd_X : Bd 1 (X : K⟦X⟧⟦X⟧) := by
  intro i n hin
  rw [coeff_X]
  split_ifs with h
  · rw [coeff_one, if_neg (by omega)]
  · simp


variable (K) in
def fin : Subring K⟦X⟧⟦X⟧ where
  carrier := {F | ∃ M, Bd M F}
  mul_mem' := by
    rintro F G ⟨M, h⟩ ⟨M', h'⟩
    exact ⟨_, h.mul h'⟩
  one_mem' := ⟨0, by simpa using bd_CC (1 : K)⟩
  add_mem' := by
    rintro F G ⟨M, h⟩ ⟨M', h'⟩
    exact ⟨M + M', fun i n hin => by
      rw [map_add (f := _), map_add (f := _), h i n (by omega), h' i n (by omega), add_zero]⟩
  zero_mem' := ⟨0, fun i n _ => by simp⟩
  neg_mem' := by
    rintro F ⟨M, h⟩
    exact ⟨M, fun i n hin => by rw [map_neg, map_neg, h i n hin, neg_zero]⟩

theorem Bd.eq_sum {M : ℕ} {F : K⟦X⟧⟦X⟧} (h : Bd M F) :
    F = ∑ i ∈ Finset.range (M + 1), C (∑ n ∈ Finset.range (M + 1),
      C (coeff n (coeff i F)) * X ^ n) * X ^ i := by
  ext i n

  simp only [map_sum (coeff i), coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hi : i < M + 1
  · simp only [if_pos hi]

    simp only [map_sum (coeff n), coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hn
    · rfl
    · exact h i n (by omega)
  · simp only [if_neg hi, map_zero]
    exact h i n (by omega)

theorem map_mem (φ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) (h1 : ∀ c : K, φ (C (C c)) ∈ fin K)
    (h2 : φ (C X) ∈ fin K) (h3 : φ X ∈ fin K) {F : K⟦X⟧⟦X⟧} (hF : F ∈ fin K) : φ F ∈ fin K := by
  obtain ⟨M, h⟩ := hF
  rw [h.eq_sum]

  simp only [map_sum, map_mul, map_pow]
  refine sum_mem fun i _ => mul_mem (sum_mem fun n _ => mul_mem (h1 _) (pow_mem h2 _)) (pow_mem h3 _)

theorem unif {ι : Type} [Finite ι] (F : ι → K⟦X⟧⟦X⟧) (h : ∀ τ, F τ ∈ fin K) : ∃ M, ∀ τ, Bd M (F τ) := by
  choose M hM using h
  obtain ⟨B, hB⟩ := (Set.finite_range M).bddAbove
  exact ⟨B, fun τ => (hM τ).mono (hB ⟨τ, rfl⟩)⟩

end

theorem exists_coeff_frob2_ofW_and_pow_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC hX N w hw
  have hF : ∀ τ, ofW t K e w τ ∈ fin K := fun τ => ⟨N, fun i n hin => by
    rw [coeff_ofW, hw i n hin]; simp⟩
  have hCX : (C X : K⟦X⟧⟦X⟧) ∈ fin K := ⟨_, bd_CX⟩
  have hX' : (X : K⟦X⟧⟦X⟧) ∈ fin K := ⟨_, bd_X⟩
  obtain ⟨M, hM⟩ := unif (frob2 φ₂ (ofW t K e w)) fun τ => by
    change φ₂ (ofW t K e w (τ - 1)) ∈ _
    refine map_mem φ₂ (fun c => ?_) ?_ ?_ (hF _)
    · have : frob K l (C c) = C c := (frob K l).commutes c
      rw [hC, this]; exact ⟨_, bd_CC c⟩
    · rw [hC, frob_X, map_pow]; exact pow_mem hCX _
    · rw [hX, map_pow]; exact sub_mem (pow_mem (add_mem hCX hX') _) (pow_mem hCX _)
  obtain ⟨M', hM'⟩ := unif (ofW t K e w ^ l) fun τ => pow_mem (hF τ) l
  exact ⟨M + M', fun τ i n hin => ⟨hM τ i n (by omega), hM' τ i n (by omega)⟩⟩

end GlobalTheory.CrysPrism.FinSupp
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

open GlobalTheory.Decompl

variable {l : ℕ} [Fact l.Prime]

theorem ι_smul_mem_FilD (C : GlobalTheory.MemLoc.Core l) {n : ℤ} (a : ℤ_[l]) {β : Per.Bcris l}
    (h : C.ι β ∈ Per.FilD l n) : C.ι (a • β) ∈ Per.FilD l n := by
  rw [Algebra.smul_def, map_mul]
  refine mul_mem_FilD_of_zero ?_ h
  have h1 : algebraMap ℤ_[l] (Per.Bcris l) a = acrisToBcris l (algebraMap ℤ_[l] (Per.Acris l) a) :=
    ((acrisToBcris l).commutes a).symm
  rw [h1]
  change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _
  rw [C.ι_j]
  exact (mem_FilD_zero_iff _).2 ⟨_, rfl⟩

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] {I : Type} [Fintype I] (b : Module.Basis I ℤ_[l] O)

theorem crd_smul_eq {W : Type} [CommRing W] [Algebra ℤ_[l] W] (o : O) (w : O ⊗[ℤ_[l]] W) (i : I) :
    crd b i (o • w) = ∑ k, b.repr (o * b k) i • crd b k w := by
  conv_lhs => rw [← sum_crd b w]

  simp only [Finset.smul_sum, smul_tmul', smul_eq_mul, map_sum, crd_tmul]

theorem crd_mem_of_mem_filO (C : GlobalTheory.MemLoc.Core l) {n : ℤ} {w : OB l O} (hw : w ∈ filO O C n)
    (i : I) : C.ι (crd b i w) ∈ Per.FilD l n := by
  induction hw using Submodule.span_induction generalizing i with
  | mem w hw =>
    obtain ⟨β, hβ, rfl⟩ := hw
    rw [crd_tmul]
    exact ι_smul_mem_FilD C _ hβ
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [map_add (f := _), map_add (f := _)]; exact add_mem (h i) (h' i)
  | smul o w _ h =>

    rw [crd_smul_eq, map_sum]
    exact Submodule.sum_mem _ fun k _ => ι_smul_mem_FilD C _ (h k)

theorem crd_toOB (x : OCr l O) (i : I) : crd b i (toOB l O x) = acrisToBcris l (crd b i x) :=
  crd_map b (acrisToBcris l) i x

theorem toOB_mem_filO_of_approx (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O)
    (h : ∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) :
    toOB l O x ∈ filO O C m := by
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hc : ∀ i, C.j (crd b i x) ∈ Per.FilP l m := by
    intro i
    refine j_mem_FilP_of_approx C m _ fun r => ?_
    obtain ⟨y, z, hxyz, hy⟩ := h r
    refine ⟨crd b i y, crd b i z, ?_, ?_⟩
    · rw [hxyz, map_add (f := _)]
      congr 1
      rw [show (l : OCr l O) ^ r = ((l ^ r : ℕ) : OCr l O) by push_cast; rfl, crd_natCast_mul]
      push_cast; rfl
    · have h1 := crd_mem_of_mem_filO b C hy i
      rw [crd_toOB] at h1
      change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _ at h1
      rw [C.ι_j] at h1
      exact (alg_mem_FilD_iff m _).1 h1

  rw [← sum_crd b x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : (b i ⊗ₜ[ℤ_[l]] crd b i x : OCr l O) = b i • ((1 : O) ⊗ₜ[ℤ_[l]] crd b i x) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (toOB_tmul_mem_filO (hc i))

end GlobalTheory.BKGal.TaylorFil
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisinPrism_crystal_basis_and_span : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∃ b : ι → E.M (ϖ.prism a), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) ∧ ∀ x : E.M (ϖ.prism a), ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → (ϖ.prism a).A), x = ∑ j, ∑ q, s j q • (oE (c j q)).u (ϖ.prism a) (b j) := by
  first | exact @GlobalTheory.BKBasis.main | exact GlobalTheory.BKBasis.main | (intros; apply GlobalTheory.BKBasis.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crystal_basis_transport_free_over_prism : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → (∀ i, (oE 1).u (ϖ.prism a) (b i) = b i) ∧ ∀ (P' : Obj l ↥(OL (ϖ.field a))) (f : GlobalTheory.Prism.Hom (ϖ.prism a) P') (Q Q' : Type) [Fintype Q] [Fintype Q'] (c : ι → Q → O) (y : ι → Q → P'.A) (c' : ι → Q' → O) (y' : ι → Q' → P'.A), ∑ i, ∑ q, y i q • (oE (c i q)).u P' (E.tr f (b i)) = ∑ i, ∑ q, y' i q • (oE (c' i q)).u P' (E.tr f (b i)) → ∀ (R : Type) [CommRing R] [Algebra O R] (ψ : P'.A →+* R), (∀ z : ℤ_[l], ψ (f.f (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) = algebraMap O R (algebraMap ℤ_[l] O z)) → ∀ i, ∑ q, c i q • ψ (y i q) = ∑ q, c' i q • ψ (y' i q) := by
  first | exact @GlobalTheory.CrysIndep.main | exact GlobalTheory.CrysIndep.main | (intros; apply GlobalTheory.CrysIndep.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crystal_changeOfBasis_frobenius_compat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), PP.I = Ideal.span {(l : PP.A)} → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ κ τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → (∀ τ y, κ τ (PP.D.φ y) = φ₂ (κ (τ - 1) y)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)) * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (Matrix.of fun i j => ∑ q, c i j q • κ (τ - 1) (y i j q)).map φ₂ := by
  first | exact @GlobalTheory.CrysEpsFrob.eps_frob_compat | exact GlobalTheory.CrysEpsFrob.eps_frob_compat | (intros; apply GlobalTheory.CrysEpsFrob.eps_frob_compat <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.eisensteinEval_nonZeroDivisor_natCast_isUnit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), (∀ y : OD l O, GlobalTheory.GalStep.ED K t ϖ * y = 0 → y = 0) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : OD l O) := by
  first | exact @GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit | exact GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit | (intros; apply GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∃ v : OD l O, IsUnit v ∧ GlobalTheory.GalStep.galOD O g (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v := by
  first | exact @GlobalTheory.GalStep.galOD_ED | exact GlobalTheory.GalStep.galOD_ED | (intros; apply GlobalTheory.GalStep.galOD_ED <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.SerSys.Bridge

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf
open scoped Classical

local instance factT (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

theorem trace_alg {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ τ (Representation.asAlgebraHom τ.ρ a) = tr a τ.character := by
  have e : Representation.asAlgebraHom τ.ρ a = ∑ x, a.coeff x • τ.ρ x :=
    LinearMap.ext fun w => by rw [alg_apply, LinearMap.sum_apply]; rfl

  rw [e, map_sum, tr]
  exact Finset.sum_congr rfl fun x _ => map_smul _ _ _

section Finite

variable {g : ℕ} [Fact g.Prime]

theorem tr_eSerC_eq (L : LabelDatum g) {n : ℕ} {χ : Gn g n → ℂ} {f : (ZMod g)[X]} (hχ : IsIrr χ)
    (hf : HasLabel L χ f) : tr (eSerC L n f) χ = χ 1 ∧ χ 1 ≠ 0 := by
  have hfin := (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)).1
  have hz : eSerC L n f * zOf χ = 1 * zOf χ := by
    rw [eSerC_eq_sum L n hfin, Finset.sum_mul, Finset.sum_eq_single_of_mem χ (by simp [hχ, hf]), one_mul]
    · simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).1
    · intro b hb hne
      have hb' : IsIrr b := by simpa using (Finset.mem_filter.1 hb).1
      rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ b χ hb' hχ).1, if_neg hne]
  have h := congrArg (fun a : MonoidAlgebra ℂ (Gn g n) => a.coeff 1) hz
  simp only [(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ _ χ).2.2] at h
  obtain ⟨d, hd, e⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ 1 χ).2.1 hχ
  have h1 : χ 1 ≠ 0 := e ▸ Nat.cast_ne_zero.2 hd.ne'
  rw [MonoidAlgebra.one_def, Opp.tr_single, one_mul] at h
  exact ⟨mul_left_cancel₀ (div_ne_zero h1 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) h, h1⟩

theorem hasLabel_of_isCuspOf (L : LabelDatum g) {d : ℕ} {P : (ZMod g)[X]} {χ : Gn g d → ℂ} (h : IsCuspOf L P χ) :
    HasLabel L χ P := by
  have hχ : IsIrr χ := h.2.1.2.1
  refine ⟨[(P, ⟨d, χ⟩)], fun p hp => by rw [List.mem_singleton.1 hp]; exact h, by simp [degL], by simp, ?_⟩
  have hc : IsClass χ := fun x y => by
    obtain ⟨V, -, hV⟩ := hχ
    rw [← hV, ← hV, FDRep.char_conj]
  have e : hcL ([(P, (⟨d, χ⟩ : Pc g))].map Prod.snd) d = χ := GLq.Model.hc_full χ hc
  rw [e, (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).2.2, if_pos rfl]
  exact one_ne_zero

theorem labelsCusp (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) :
    TameGen.LabelsCusp (OfLabel.ofLabel L h5 hG) L := fun d τ P hP h0 => by
  obtain ⟨h1, h2⟩ := tr_eSerC_eq L hP.2.1.2.1 (hasLabel_of_isCuspOf L hP)
  rw [← trace_alg] at h1
  exact h2 (h1.symm.trans ((congrArg _ h0).trans (map_zero _)))

end Finite

theorem five_le (D : D7) (k : Fin 2) : 5 ≤ D.host.g k := by
  have hc := D.ntypes.g_cond k
  have h4 : D.host.g k % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show 4 ∣ D.host.QS * D.host.q * D.host.d from
        ((((show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd).mul_right _).mul_right _)), hc]
  have := (D.host.g_prime k).two_le
  omega

end GlobalTheory.SerSys.Bridge
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.wachLatticesExistAllLayers_of_bhattScholze : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → WachEx AI := by
  first | exact @GlobalTheory.WachLattice.main | exact GlobalTheory.WachLattice.main | (intros; apply GlobalTheory.WachLattice.main <;> assumption)
end
