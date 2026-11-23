module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle685
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module Polynomial

namespace GlobalTheory.BadCount

open Classical

variable (D : D7)

theorem neZeroG (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem factG (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

attribute [local instance] neZeroG factG

def allTup (k : Fin 2) : Finset (Tup D k) :=
  Finset.univ.image fun a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) => fun v => Formalism.CyclotomicNorms.monicOf (a v)

theorem monicOf_injective (k : Fin 2) :
    Function.Injective (Formalism.CyclotomicNorms.monicOf : (Fin D.R.r → ZMod (D.host.g k)) → (ZMod (D.host.g k))[X]) := by
  intro a b h
  funext i
  rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt a i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]

theorem tupOf_injective (k : Fin 2) :
    Function.Injective fun a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) => fun v => Formalism.CyclotomicNorms.monicOf (a v) := by
  intro a b h
  funext v
  exact monicOf_injective D k (congrFun h v)

theorem badElt_coeff (k : Fin 2) (S : Finset (Tup D k)) (g : G0g D.nd) :
    (badElt D k S).coeff g = if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then
      ∑ t ∈ S, ∏ v : D.nd.PlG k, (D.ntypes.eSer k (t v)).coeff (g ⟨k, v⟩) else 0 := by
  unfold badElt
  rfl

theorem sum_eSer_monicOf (k : Fin 2) :
    ∑ b : Fin D.R.r → ZMod (D.host.g k), D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf b) = 1 := by
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum k
  rw [← hsum, ← Finset.sum_image (fun a _ b _ h => monicOf_injective D k h)]
  symm
  apply Finset.sum_subset
  · intro f hf
    obtain ⟨h1, h2, -⟩ := (hS f).1 hf
    exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, Formalism.CyclotomicNorms.Sqf.monicOf_coeffs f h1 h2⟩
  · intro f _ hf
    exact D.ntypes.eSer_zero k f fun h => hf ((hS f).2 h)

theorem badElt_all (k : Fin 2) : badElt D k (allTup D k) = 1 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [badElt_coeff, allTup, Finset.sum_image (fun a _ b _ h => tupOf_injective D k h)]
  have e : ∑ a : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)),
      ∏ v, (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf (a v))).coeff (g ⟨k, v⟩) =
      ∏ v, (1 : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))).coeff (g ⟨k, v⟩) := by
    refine (Fintype.prod_sum (fun v (b : Fin D.R.r → ZMod (D.host.g k)) =>
      (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf b)).coeff (g ⟨k, v⟩))).symm.trans ?_
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← sum_eSer_monicOf D k, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [e, MonoidAlgebra.one_def, MonoidAlgebra.one_def]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h1 : g = 1
  · subst h1; simp
  · rw [if_neg (Ne.symm h1)]
    split_ifs with hs
    · obtain ⟨kv, hkv⟩ := Function.ne_iff.1 h1
      obtain ⟨k', v⟩ := kv
      by_cases hk : k' = k
      · subst hk
        exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg fun h => hkv h.symm)
      · exact absurd (hs ⟨k', v⟩ hk) hkv
    · rfl

def goodSet (k : Fin 2) : Finset (Tup D k) := (allTup D k).filter (goodAt D k)

def badSet (k : Fin 2) : Finset (Tup D k) := (allTup D k).filter fun t => ¬ goodAt D k t

theorem badElt_good_add_bad (k : Fin 2) : badElt D k (goodSet D k) + badElt D k (badSet D k) = 1 := by
  rw [← badElt_all D k]
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, badElt_coeff, badElt_coeff, badElt_coeff]
  split_ifs
  · exact Finset.sum_filter_add_sum_filter_not _ _ _
  · simp

theorem badElt_coeff_off (k : Fin 2) (S : Finset (Tup D k)) (h : G0g D.nd)
    (hh : ∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k ∧ h kv ≠ 1) : (badElt D k S).coeff h = 0 := by
  rw [badElt_coeff, if_neg]
  obtain ⟨kv, h1, h2⟩ := hh
  exact fun hs => h2 (hs kv h1)

theorem coeff_mul_factors (x y : MonoidAlgebra ℂ (G0g D.nd))
    (hx : ∀ h : G0g D.nd, (∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 0 ∧ h kv ≠ 1) → x.coeff h = 0)
    (hy : ∀ h : G0g D.nd, (∃ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 1 ∧ h kv ≠ 1) → y.coeff h = 0)
    (g : G0g D.nd) :
    (x * y).coeff g = x.coeff (fun kv => if kv.1 = 0 then g kv else 1) *
      y.coeff (fun kv => if kv.1 = 0 then 1 else g kv) := by
  rw [MonoidAlgebra.coeff_mul_apply_left]
  rw [Finsupp.sum_eq_single (fun kv => if kv.1 = 0 then g kv else 1)]
  · congr 2
    funext kv
    by_cases h0 : kv.1 = 0
    · simp [h0]
    · simp [h0]
  · intro b hb hne
    have hb0 : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ 0 → b kv = 1 := by
      intro kv hkv
      by_contra hc
      exact hb (hx b ⟨kv, hkv, hc⟩)
    obtain ⟨kv, hkv⟩ := Function.ne_iff.1 hne
    by_cases h0 : kv.1 = 0
    · rw [hy _ ⟨kv, by rw [h0]; decide, ?_⟩, mul_zero]
      intro hc
      apply hkv
      simp only [h0, if_true]
      have : (b⁻¹ * g) kv = 1 := hc
      rw [Pi.mul_apply, Pi.inv_apply, inv_mul_eq_one] at this
      exact this
    · exact absurd (by simp [h0, hb0 kv h0]) hkv
  · intro _
    exact zero_mul _

theorem e0_eq : D.ntypes.e0 = badElt D 0 (goodSet D 0) * badElt D 1 (goodSet D 1) := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_factors D _ _ (fun h hh => badElt_coeff_off D 0 _ h hh) (fun h hh => badElt_coeff_off D 1 _ h hh),
    badElt_coeff, badElt_coeff, if_pos, if_pos]
  rotate_left
  · rintro ⟨k, v⟩ hk
    fin_cases k
    · simp
    · exact absurd rfl hk
  · rintro ⟨k, v⟩ hk
    fin_cases k
    · exact absurd rfl hk
    · simp
  have he : D.ntypes.e0.coeff g =
      ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
        (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
          ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0) := rfl
  rw [he, finsum_eq_sum_of_fintype, goodSet, goodSet, Finset.sum_filter, Finset.sum_filter, allTup, allTup,
    Finset.sum_image (fun a _ b _ h => tupOf_injective D 0 h),
    Finset.sum_image (fun a _ b _ h => tupOf_injective D 1 h),
    Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.piCurry fun k (_ : D.nd.PlG k) => Fin D.R.r → ZMod (D.host.g k)).trans
    (piFinTwoEquiv _)) _ _ fun a => ?_
  have hg : D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔
      goodAt D 0 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) ∧ goodAt D 1 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) :=
    Fin.forall_fin_two
  rw [Fintype.prod_sigma, Fin.prod_univ_two]
  by_cases h0 : goodAt D 0 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) <;>
  by_cases h1 : goodAt D 1 (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) <;>
  simp [hg, h0, h1, piFinTwoEquiv_apply, Equiv.piCurry_apply, Sigma.curry]

theorem one_sub_goodTypeIdempotent_eq_badTupleSums : ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧
    1 - D.ntypes.e0 = badElt D 0 (S 0) + badElt D 1 (S 1) - badElt D 0 (S 0) * badElt D 1 (S 1) := by
  refine ⟨badSet D, fun k t ht => (Finset.mem_filter.1 ht).2, ?_⟩
  rw [e0_eq, ← sub_eq_iff_eq_add'.2 (badElt_good_add_bad D 0).symm,
    ← sub_eq_iff_eq_add'.2 (badElt_good_add_bad D 1).symm]
  noncomm_ring

end GlobalTheory.BadCount
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount.IdemCen

variable (D : D7)

local instance neZeroTypePrime (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def fac (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  if h : kv.1 = k then h.symm ▸ D.ntypes.eSer k (t (h ▸ kv.2)) else 1

variable {D}

theorem fac_self (k : Fin 2) (t : Tup D k) (v : D.nd.PlG k) : fac D k t ⟨k, v⟩ = D.ntypes.eSer k (t v) := by
  simp [fac]

theorem fac_ne (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) (h : kv.1 ≠ k) : fac D k t kv = 1 := by
  simp [fac, h]


open Classical in
theorem prod_fac_coeff (k : Fin 2) (t : Tup D k) (g : G0g D.nd) :
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (fac D k t kv).coeff (g kv) =
      if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then
        ∏ v : D.nd.PlG k, (D.ntypes.eSer k (t v)).coeff (g ⟨k, v⟩) else 0 := by
  rw [Fintype.prod_sigma, Fintype.prod_eq_mul_prod_compl k]
  simp only [fac_self]
  have h2 : ∏ k' ∈ ({k}ᶜ : Finset (Fin 2)), ∏ v : D.nd.PlG k', (fac D k t ⟨k', v⟩).coeff (g ⟨k', v⟩) =
      if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then 1 else 0 := by
    have e : ∀ k' ∈ ({k}ᶜ : Finset (Fin 2)), ∏ v : D.nd.PlG k', (fac D k t ⟨k', v⟩).coeff (g ⟨k', v⟩) =
        if ∀ v : D.nd.PlG k', g ⟨k', v⟩ = 1 then 1 else 0 := by
      intro k' hk'
      have hk : k' ≠ k := by simpa using hk'
      have hv : ∀ v : D.nd.PlG k', (fac D k t ⟨k', v⟩).coeff (g ⟨k', v⟩) = if g ⟨k', v⟩ = 1 then 1 else 0 := by
        intro v
        rw [fac_ne k t ⟨k', v⟩ hk, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single_apply]
        by_cases hg : g ⟨k', v⟩ = 1
        · rw [if_pos hg.symm, if_pos hg]
        · rw [if_neg (Ne.symm hg), if_neg hg]
      simp only [hv]
      by_cases hc : ∀ v : D.nd.PlG k', g ⟨k', v⟩ = 1
      · rw [if_pos hc]
        exact Finset.prod_eq_one fun v _ => if_pos (hc v)
      · rw [if_neg hc]
        push_neg at hc
        obtain ⟨v, hv'⟩ := hc
        exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv')
    rw [Finset.prod_congr rfl e, Finset.prod_boole]
    by_cases hc : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1
    · rw [if_pos hc, if_pos]
      intro k' hk' v
      exact hc ⟨k', v⟩ (by simpa using hk')
    · rw [if_neg hc, if_neg]
      intro h
      apply hc
      rintro ⟨k', v⟩ hk
      exact h k' (by simpa using hk) v
  rw [h2]
  split_ifs <;> simp

theorem badElt_eq_sum (k : Fin 2) (S : Finset (Tup D k)) :
    badElt D k S = ∑ t ∈ S, Formalism.BasicNotions.Examples₂.NZ.tens (fac D k t) := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [Formalism.BasicNotions.Examples₂.NZ.tens_coeff, prod_fac_coeff]
  simp only [badElt, MonoidAlgebra.coeff_ofCoeff, Finsupp.equivFunOnFinite_symm_apply_apply]
  split_ifs with hc
  · rfl
  · simp

theorem fac_mul_self (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) :
    fac D k t kv * fac D k t kv = fac D k t kv := by
  rcases kv with ⟨k', v⟩
  by_cases h : k' = k
  · subst h
    rw [fac_self, D.ntypes.eSer_idem]
  · rw [fac_ne k t ⟨k', v⟩ h, one_mul]

theorem fac_central (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) (a) :
    fac D k t kv * a = a * fac D k t kv := by
  rcases kv with ⟨k', v⟩
  by_cases h : k' = k
  · subst h
    rw [fac_self, D.ntypes.eSer_central]
  · rw [fac_ne k t ⟨k', v⟩ h, one_mul, mul_one]

theorem tens_fac_mul_of_ne (k : Fin 2) {t t' : Tup D k} (h : t ≠ t') :
    Formalism.BasicNotions.Examples₂.NZ.tens (fac D k t) * Formalism.BasicNotions.Examples₂.NZ.tens (fac D k t') = 0 := by
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  rw [Formalism.BasicNotions.Examples₂.NZ.tens_mul]
  refine Formalism.BasicNotions.Examples₂.NZ.tens_eq_zero _ ⟨k, v⟩ ?_
  simp only [fac_self]
  exact D.ntypes.eSer_orth k _ _ hv

theorem badElt_idem_central : ∀ (D : D7) (k : Fin 2) (S : Finset (Tup D k)),
    badElt D k S * badElt D k S = badElt D k S ∧ ∀ a, badElt D k S * a = a * badElt D k S := by
  intro D k S
  rw [badElt_eq_sum]
  refine ⟨?_, fun a => ?_⟩
  · rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.sum_eq_single_of_mem t ht fun t' _ hne => tens_fac_mul_of_ne k (Ne.symm hne),
      Formalism.BasicNotions.Examples₂.NZ.tens_mul]
    exact congrArg _ (funext fun kv => fac_mul_self k t kv)
  · rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ =>
      Formalism.BasicNotions.Examples₂.NZ.tens_central _ (fun kv b => fac_central k t kv b) a

end GlobalTheory.BadCount.IdemCen
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.TwoFormSum

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

def coordPair (f g : Module.Dual B Ω[B⁄R]) : Module.Dual B (Om R B 2) :=
  exteriorPower.pairingDual B Ω[B⁄R] 2 (exteriorPower.ιMulti B 2 ![f, g])

theorem coordPair_wedge (f g : Module.Dual B Ω[B⁄R]) (a b : Ω[B⁄R]) :
    coordPair f g (wedge R B a b) = f a * g b - g a * f b := by
  rw [wedge_eq_ιMulti, coordPair, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp

theorem ιMulti_two (v : Fin 2 → Ω[B⁄R]) : exteriorPower.ιMulti B 2 v = wedge R B (v 0) (v 1) := by
  rw [wedge_eq_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem sum_sum_eq_lt {M : Type} [AddCommGroup M] {n : ℕ} (g : Fin n → Fin n → M) (hg : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j, (if i < j then g i j + g j i else 0) := by
  calc ∑ i, ∑ j, g i j
      = ∑ i, ∑ j, ((if i < j then g i j else 0) + (if j < i then g i j else 0)) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rcases lt_trichotomy i j with h | h | h
        · simp [h, not_lt.2 h.le]
        · subst h; simp [hg]
        · simp [h, not_lt.2 h.le]
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if j < i then g i j else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_add_distrib
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if i < j then g j i else 0) := by
        rw [Finset.sum_comm (f := fun i j ↦ if j < i then g i j else 0)]
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp

def expand {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R]) : Om R B 2 →ₗ[B] Om R B 2 :=
  ∑ i, ∑ j, if i < j then (coordPair (δ i) (δ j)).smulRight (wedge R B (w i) (w j)) else 0

theorem expand_apply {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R]) (x : Om R B 2) :
    expand w δ x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by
  simp only [expand, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

theorem eq_expand {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R])
    (hs : ∀ ω, ω = ∑ i, δ i ω • w i) (x : Om R B 2) :
    x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by
  rw [← expand_apply]
  have hx : x ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B 2 (M := Ω[B⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hL : wedge R B (v 0) (v 1) = ∑ i, ∑ j, (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j) := by
      conv_lhs => rw [hs (v 0), hs (v 1)]

      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_comm]
    rw [ιMulti_two, expand_apply]
    conv_lhs => rw [hL,
      sum_sum_eq_lt (fun i j ↦ (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j)) (fun i ↦ by simp)]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [coordPair_wedge, wedge_swap (w j) (w i), smul_neg, sub_smul]; abel
    · simp
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _), ← hy, ← hz]
  | smul c y _ hy => rw [map_smul, ← hy]

end Alg

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem coordPair_nat {n : ℕ} (Φ : Frame F n) (i j : Fin n) ⦃T T' : C⦄ (φ : T ⟶ T') (x : Om R (F.obj T) 2) :
    coordPair (Φ.δ i T') (Φ.δ j T') (pOm F 2 φ x) = mp F φ (coordPair (Φ.δ i T) (Φ.δ j T) x) := by
  have hx : x ∈ Submodule.span (F.obj T) (Set.range (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [ιMulti_two, pOm_wedge, coordPair_wedge, coordPair_wedge, Φ.nat, Φ.nat, Φ.nat, Φ.nat]
    simp only [map_sub, map_mul]
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add (f := _), hy, hz]
  | smul c y _ hy => rw [pOm_smul, map_smul, map_smul, hy, smul_eq_mul, smul_eq_mul, map_mul]

end GlobalTheory.AbCoh.TwoFormSum

namespace GlobalTheory.AbCoh


open TwoFormSum in
theorem twoForm_eq_wsum : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → ∀ ζ : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ζ T' = pOm F 2 φ (ζ T)) →
      ∃ (n : ℕ) (u v : Fin n → Glob1 F), ζ = wsum F u v := by
  intro R _ C _ F ⟨n, ⟨Φ⟩⟩ h0 ζ hζ
  let g : Fin n → Fin n → C0 F := fun i j T ↦ coordPair (Φ.δ i T) (Φ.δ j T) (ζ T)
  have hg : ∀ i j, d0 F (g i j) = 0 := by
    intro i j
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [g]
    rw [hζ φ, coordPair_nat, sub_self]
    rfl
  choose c hc using fun i j ↦ (h0 (g i j) (hg i j)).exists
  let e : Fin (n * n) ≃ Fin n × Fin n := finProdFinEquiv.symm
  refine ⟨n * n, fun k ↦ (if (e k).1 < (e k).2 then c (e k).1 (e k).2 else 0) • Φ.w (e k).1,
    fun k ↦ Φ.w (e k).2, ?_⟩
  funext T
  simp only [wsum]
  rw [Fintype.sum_equiv e _ (fun p ↦ wedge R (F.obj T)
      (((if p.1 < p.2 then c p.1 p.2 else 0) • Φ.w p.1 : Glob1 F).1 T) ((Φ.w p.2).1 T)) (fun k ↦ rfl),
    Fintype.sum_prod_type]
  conv_lhs => rw [eq_expand (fun i ↦ (Φ.w i).1 T) (fun i ↦ Φ.δ i T) (Φ.sum T) (ζ T)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Submodule.coe_smul, Pi.smul_apply, wedge_smul_left]
  split_ifs
  · have := hc i j T
    simp only [g] at this
    rw [this, algebraMap_smul]
  · simp

end GlobalTheory.AbCoh
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLogarithm_generation_of_division_step_padic : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E), (∀ i, QL μ ⊤ (e i)) → (∀ f, QL μ ⊤ f → ∃ (b : ι → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁) → ∀ f, QL μ ⊤ f → ∃ b : ι → O, In (⊤ : Ideal O) (f - comb b e) := by
  first | exact @GlobalTheory.QLog.Conv.generate_of_step | exact GlobalTheory.QLog.Conv.generate_of_step | (intros; apply GlobalTheory.QLog.Conv.generate_of_step <;> assumption)
end
