module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle217
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric.ColSplit

abbrev HiIx (a r k : ℕ) : Type := {t : UnipotentBlockColumnIndex a k k // r ≤ (t.1.1 : ℕ)}

abbrev LoIx (a r k : ℕ) : Type := {t : UnipotentBlockColumnIndex a k k // ¬ r ≤ (t.1.1 : ℕ)}

def colEquiv (a r k : ℕ) : HiIx a r k ⊕ LoIx a r k ≃ UnipotentBlockColumnIndex a k k := Equiv.sumCompl _

def blkEquiv (a r m : ℕ) (hr : r ≤ m + 1) : UnipotentBlockColumnIndex a r m ⊕ LoIx a r (m + 1) ≃ UnipotentBlockColumnIndex a r (m + 1) where
  toFun := Sum.elim (fun s : UnipotentBlockColumnIndex a r m => ⟨s.1, s.2.1, s.2.2.1, by have := s.2.2.2; omega⟩)
    (fun l : LoIx a r (m + 1) => ⟨l.1.1, by have := l.2; omega, by have := l.1.2; omega, by have := l.1.2; omega⟩)
  invFun := fun t => if h : (t.1.2 : ℕ) ≤ m then Sum.inl ⟨t.1, t.2.1, t.2.2.1, h⟩
    else Sum.inr ⟨⟨t.1, by have := t.2; omega, by have := t.2; omega, by have := t.2; omega⟩,
      show ¬ r ≤ (t.1.1 : ℕ) by have := t.2; omega⟩
  left_inv := by
    rintro (s | l)
    · simp [s.2.2.2]
    · have h1 := l.1.2
      have h2 : ¬ ((l.1.1.2 : ℕ) ≤ m) := by omega
      simp [h2]
  right_inv := by
    intro t
    by_cases h : (t.1.2 : ℕ) ≤ m
    · simp [h]
    · simp [h]

section Mat

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_apply_ne_zero {ι : Type} [Fintype ι] {p : ι → Fin a × Fin a} {x : ι → R} {i k : Fin a}
    (h : posM p x i k ≠ 0) : ∃ t, p t = (i, k) := by
  simp only [posM, Matrix.sum_apply] at h
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨t, ?_⟩
  rw [Matrix.single_apply] at ht
  split_ifs at ht with hc
  · exact Prod.ext hc.1 hc.2
  · exact absurd rfl ht

theorem posM_eq_of_support {ι : Type} [Fintype ι] {p : ι → Fin a × Fin a} (hp : Function.Injective p)
    (M : Matrix (Fin a) (Fin a) R) (hM : ∀ i k, M i k ≠ 0 → ∃ t, p t = (i, k)) :
    posM p (fun t => M (p t).1 (p t).2) = M := by
  ext i k
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  by_cases h : ∃ t, p t = (i, k)
  · obtain ⟨t, ht⟩ := h
    rw [Finset.sum_eq_single t]
    · simp [ht]
    · intro t' _ ht'
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact ht' (hp (by rw [ht]; exact Prod.ext e1 e2))
    · simp
  · have h0 : M i k = 0 := by
      by_contra h1
      exact h (hM i k h1)
    rw [h0]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    exact h ⟨t, Prod.ext e1 e2⟩

theorem posM_comp_symm {ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → Fin a × Fin a) (τ : κ ≃ ι) (w : κ → R) :
    posM p (w ∘ τ.symm) = posM (p ∘ τ) w := by
  simp only [posM]
  exact (Fintype.sum_equiv τ.symm _ _ (fun t => by simp)).trans rfl

theorem posM_sumElim {ι κ : Type} [Fintype ι] [Fintype κ] (p : ι ⊕ κ → Fin a × Fin a) (z : ι → R) (y : κ → R) :
    posM p (Sum.elim z y) = posM (p ∘ Sum.inl) z + posM (p ∘ Sum.inr) y := by
  simp only [posM, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp]

theorem posM_sub {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (x y : ι → R) :
    posM p (x - y) = posM p x - posM p y := by
  rw [eq_sub_iff_add_eq, ← posM_add, sub_add_cancel]

theorem posM_zero' {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) : posM p (0 : ι → R) = 0 := by
  simp [posM]

theorem posM_mul_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] {p : ι → Fin a × Fin a} {q : κ → Fin a × Fin a}
    (h : ∀ s t, (p s).2 ≠ (q t).1) (x : ι → R) (y : κ → R) : posM p x * posM q y = 0 := by
  simp only [posM, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  exact Matrix.single_mul_single_of_ne _ _ _ _ (h _ _) _

def corr {r m : ℕ} (n : UnipotentBlockColumnIndex a r m → R) (z : HiIx a r (m + 1) → R) : LoIx a r (m + 1) → R := fun l =>
  (posM Subtype.val n * posM (fun t : HiIx a r (m + 1) => t.1.1) z) l.1.1.1 l.1.1.2

theorem posM_corr {r m : ℕ} (n : UnipotentBlockColumnIndex a r m → R) (z : HiIx a r (m + 1) → R) :
    posM (fun l : LoIx a r (m + 1) => l.1.1) (corr n z) =
      posM Subtype.val n * posM (fun t : HiIx a r (m + 1) => t.1.1) z := by
  refine posM_eq_of_support (fun l l' e => Subtype.ext (Subtype.ext e)) _ fun i k hik => ?_
  obtain ⟨l, hl⟩ : ∃ l, posM Subtype.val n i l * posM (fun t : HiIx a r (m + 1) => t.1.1) z l k ≠ 0 := by
    rw [Matrix.mul_apply] at hik
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hik
    exact ⟨l, hl⟩
  obtain ⟨s, hs⟩ := posM_apply_ne_zero (left_ne_zero_of_mul hl)
  obtain ⟨t, ht⟩ := posM_apply_ne_zero (right_ne_zero_of_mul hl)
  have s2 := s.2
  have t2 := t.1.2
  rw [hs] at s2
  rw [ht] at t2
  simp only at s2 t2
  exact ⟨⟨⟨(i, k), show (i : ℕ) < m + 1 by omega, show m + 1 ≤ (k : ℕ) by omega, show (k : ℕ) ≤ m + 1 by omega⟩,
    show ¬ r ≤ (i : ℕ) by omega⟩, rfl⟩

end Mat

section Id

variable {R : Type} [CommRing R] {a : ℕ}

theorem blkU_col_mul_blkU {r m : ℕ} (hr : r ≤ m + 1) (n : UnipotentBlockColumnIndex a r m → R) (z : HiIx a r (m + 1) → R)
    (y : LoIx a r (m + 1) → R) :
    blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * blkU n =
      blkU (Sum.elim n (y - corr n z) ∘ (blkEquiv a r m hr).symm) *
        blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) := by
  apply Units.ext
  change (1 + posM Subtype.val (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) * (1 + posM Subtype.val n) =
    (1 + posM Subtype.val (Sum.elim n (y - corr n z) ∘ (blkEquiv a r m hr).symm)) *
      (1 + posM Subtype.val (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm))
  simp only [posM_comp_symm, posM_sumElim, posM_sub, posM_zero', add_zero]
  have e1 : ((Subtype.val ∘ colEquiv a r (m + 1)) ∘ Sum.inl) = fun t : HiIx a r (m + 1) => t.1.1 := rfl
  have e2 : ((Subtype.val ∘ colEquiv a r (m + 1)) ∘ Sum.inr) = fun t : LoIx a r (m + 1) => t.1.1 := rfl
  have e3 : ((Subtype.val ∘ blkEquiv a r m hr) ∘ Sum.inl) = (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) := rfl
  have e4 : ((Subtype.val ∘ blkEquiv a r m hr) ∘ Sum.inr) = fun t : LoIx a r (m + 1) => t.1.1 := rfl
  rw [e1, e2, e3, e4, posM_corr]
  set P := posM (fun t : HiIx a r (m + 1) => t.1.1) z
  set Q := posM (fun t : LoIx a r (m + 1) => t.1.1) y
  set N := posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) n
  have hPN : P * N = 0 := posM_mul_eq_zero (fun s t => by
    have := s.1.2; have := t.2; omega) _ _
  have hQN : Q * N = 0 := posM_mul_eq_zero (fun s t => by
    have := s.1.2; have := t.2; omega) _ _
  have hQP : Q * P = 0 := posM_mul_eq_zero (fun s t => by
    have := s.1.2; have := t.1.2; omega) _ _
  have hNPP : N * P * P = 0 := by
    rw [mul_assoc, posM_mul_eq_zero (fun s t => by have := s.1.2; have := t.1.2; omega) z z, mul_zero]
  simp only [mul_add, add_mul, mul_one, one_mul, mul_sub, sub_mul, hPN, hQN, hQP, hNPP]
  abel

end Id

end GlobalTheory.CuspGeneric.ColSplit
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem σC_root_of_unity {m n : ℕ} {g : GQ l} (hm : 0 < m) (hg : ∀ x : Om l, x ^ m = 1 → g x = x ^ n)
    {x : ℂ_[l]} (hx : x ^ m = 1) : Per.σC g x = x ^ n := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  have hζ' := hζ.map_of_injective (algebraMap (Om l) ℂ_[l]).injective
  obtain ⟨i, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hx
  have h1 : (ζ ^ i) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (ζ ^ i)) = algebraMap (Om l) ℂ_[l] (g (ζ ^ i)) :=
    GlobalTheory.RingBasics.σC_coe g (ζ ^ i)
  rw [← map_pow, h2, hg _ h1, map_pow]

theorem tilt_root_eq_one {c : Per.Fl l} {m : ℕ} (hlm : ¬ l ∣ m) (hc : c ^ m = 1)
    (h0 : PreTilt.coeff 0 c = 1) : c = 1 := by
  have : IsDomain (Per.Fl l) := inferInstance
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, c ^ i) * (c - 1) = 0 := by rw [geom_sum_mul, hc, sub_self]
  have h2 : (∑ i ∈ Finset.range m, c ^ i) = 0 :=
    (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg (PreTilt.coeff (O := Per.OC l) (p := l) 0) h2

  simp only [map_sum, map_pow, h0, one_pow, Finset.sum_const, Finset.card_range, map_zero,
  nsmul_eq_mul, mul_one] at h3
  exact hlm ((CharP.cast_eq_zero_iff _ l m).1 h3)

theorem tilt_root_inj {a b : Per.Fl l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (ha : a ^ m = 1)
    (hb : b ^ m = 1) (h : a.untilt = b.untilt) : a = b := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hb' : b * b ^ k = 1 := by rw [← pow_succ', hb]
  have h0 : PreTilt.coeff 0 a = PreTilt.coeff 0 b := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, ← PreTilt.mk_untilt_eq_coeff_zero, h]
  have h1 : a * b ^ k = 1 := by
    refine tilt_root_eq_one hlm ?_ ?_
    · rw [mul_pow, ha, ← pow_mul, mul_comm k, pow_mul, hb, one_pow, one_mul]
    · rw [map_mul, h0, ← map_mul, hb', map_one]
  calc a = a * (b * b ^ k) := by rw [hb', mul_one]
    _ = (a * b ^ k) * b := by ring
    _ = b := by rw [h1, one_mul]

theorem σF_root_of_unity (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l) (hm : 0 < m)
    (hlm : ¬ l ∣ m) (he : e ^ m = 1) (hg : ∀ x : Om l, x ^ m = 1 → g x = x ^ n) :
    Per.σF g e = e ^ n := by
  refine tilt_root_inj hm hlm ?_ ?_ ?_
  · rw [← map_pow, he, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, he, one_pow]
  · rw [GlobalTheory.RingBasics.untilt_σF, map_pow]
    have h1 : e.untilt ^ m = 1 := by rw [← map_pow, he, map_one]
    have h2 : ((e.untilt : Per.OC l) : ℂ_[l]) ^ m = 1 := by
      simpa using congrArg Subtype.val h1
    exact Subtype.ext ((GlobalTheory.RingIface.sigO_coe l g _).trans
      ((σC_root_of_unity hm hg h2).trans (by simp)))

end GlobalTheory.MemLoc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWLBeta

theorem exists_beta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ LL : FinExt l, ∃ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β := by
  intro l _ P AI T LL
  have hz := (GlobalTheory.TiedMu.tied_mu_units l P AI T).2.2.2
  let _ : Algebra ℤ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) :=
    ((algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  let f : ↥(OL LL) →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom).comp (OL LL).val.toRingHom
      commutes' := fun z => by
        show ((algebraMap ℤ_[l] ↥LL.1 z) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1] }
  let g : Ainf l →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)).toRingHom.comp AI.ιA
      commutes' := fun z => by
        show Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)
            (AI.ιA (algebraMap ℤ_[l] (Ainf l) z)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [hz, AlgHom.commutes]
        rfl }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, fun o w => ?_⟩
  show Algebra.TensorProduct.productMap f g (o ⊗ₜ[ℤ_[l]] w) = _
  rw [Algebra.TensorProduct.productMap_apply_tmul]
  show ((o : ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) * ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] AI.ιA w) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end GlobalTheory.HWLBeta
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.mem_unramified_of_frobenius_iterate_fixed_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : P.R.B), (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] c = c → (∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0) → ∃ a : ↥(K0 K), c = algebraMap ↥(K0 K) P.R.B a := by
  first | exact @GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt | exact GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt | (intros; apply GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.GaloisFromAdm

theorem placesOver_finite (D : D7) (l : ℕ) (hl : l ≠ 0) : (placesOver D.host.E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    simpa using hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

end GlobalTheory.GaloisFromAdm

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.GalIsoBC

theorem lpTw_lpZero (D : D7) (w : PlE D.host) (s : ℝ) : D.naut.lpTw (D.naut.lpZero w) s = D.naut.lpZero w := by
  have hu : D.naut.unr (D.naut.lpTw (D.naut.lpZero w) s) := (D.naut.unr_tw _ s).2 (D.naut.lpZero_unr w)
  have e3 : D.naut.frobEig (D.naut.lpTw (D.naut.lpZero w) s) = D.naut.frobEig (D.naut.lpZero w) := by
    rw [D.naut.frobEig_tw _ s (D.naut.lpZero_unr w), D.naut.frobEig_zero]; simp
  rw [D.naut.unr_eq_lpUnr _ hu, e3, ← D.naut.unr_eq_lpUnr _ (D.naut.lpZero_unr w)]

theorem lpTw_foldr (D : D7) (w : PlE D.host) {β : Type*} (f : β → D.naut.LP w) (s : ℝ) :
    ∀ L : List β, D.naut.lpTw (L.foldr (fun x acc => D.naut.lpSum (f x) acc) (D.naut.lpZero w)) s =
      L.foldr (fun x acc => D.naut.lpSum (D.naut.lpTw (f x) s) acc) (D.naut.lpZero w)
  | [] => lpTw_lpZero D w s
  | x :: L => by
      simp only [List.foldr_cons]
      rw [D.naut.lpTw_sum, lpTw_foldr D w f s L]

theorem map_list_sum {α γ : Type*} (h : α → γ) :
    ∀ L : List (Multiset α), L.sum.map h = (L.map fun x => x.map h).sum
  | [] => by simp
  | x :: L => by simp [Multiset.map_add (f := _), map_list_sum h L]

theorem le_list_sum {α : Type*} {x : Multiset α} : ∀ {L : List (Multiset α)}, x ∈ L → x ≤ L.sum
  | [], hx => by simp at hx
  | y :: L, hx => by
      rw [List.sum_cons]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Multiset.le_add_right _ _
      · exact le_trans (le_list_sum hx) (Multiset.le_add_left _ _)

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

theorem flatMap_single {γ : Type*} (f : ℕ → γ) : ∀ l : List ℕ, List.flatMap (fun a => [f a]) l = l.map f
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, flatMap_single f l]

theorem spehLoc_eq (D : D7) (p : Formalism.BasicNotions.Part D.naut.CG) (w : PlE D.host) :
    spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (k : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - (k : ℝ))) acc) (D.naut.lpZero w) := by
  unfold spehLoc
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℝ)), List.foldr_map]

theorem isoInf_eq (D : D7) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut Pa τ = (Pa.map fun p => ((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum).sum := by
  unfold isoInf
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℂ)), List.map_map]
  rfl

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

end GlobalTheory.GalIsoBC
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HubFon

theorem g_ne_q_d (D : D7) (k : Fin 2) : D.host.g k ≠ D.host.q ∧ D.host.g k ≠ D.host.d := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  constructor
  · intro h
    have h1 : D.host.g k % D.host.q = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.d, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega
  · intro h
    have h1 : D.host.g k % D.host.d = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.q, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega

end GlobalTheory.HubFon
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.PointRepAboveL

theorem place_unique {D : D7} {i : D.nd.Loc} {τ : D.host.E →+* Qbar (D.nd.l i)} {w w' : PlE D.host}
    (h : InducesW D.nd i τ w) (h' : InducesW D.nd i τ w') : w' = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [← h x, h' x]

end GlobalTheory.PointRepAboveL
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.EigenProjector

theorem HG_of_mem_Zgood (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) :
    HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩

end GlobalTheory.EigenProjector
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem weight_localisation_regular_algebraic : ∀ (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* ℂ),
    (D.naut.infWt i τ).Nodup ∧ ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
  intro D i P τ
  rw [D.nbc.embAV_inf i P]
  exact D.nbc.infW_alg _ _ τ

end GlobalTheory
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep : ∀ (k Γ : Type) [Field k] [CharZero k] [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) k), IsSSRep r → ∀ M ∈ Submodule.span k (Set.range fun g => ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)), (∀ g, (M * ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).trace = 0) → M = 0 := by
  first | exact @GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero | exact GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero | (intros; apply GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero <;> assumption)
end
