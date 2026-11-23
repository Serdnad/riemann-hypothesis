module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Flat.Basic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open IsDiscreteValuationRing

namespace GlobalTheory.PolyCycloValue

theorem card_double_min (S : Set ℕ) (a : ℕ → ℕ) (q : ℕ → ℝ) (w : ℕ) (hw : w ∈ S)
    (hq : ∀ k, 1 ≤ k → 0 < q k) (hqa : ∀ k k', 1 ≤ k → k < k' → q k' < q k) :
    ∃ BB : Finset ℕ, BB.card ≤ w + a w ∧ ∀ k, 1 ≤ k → k ∉ BB → ∀ i ∈ S, ∀ j ∈ S,
      (∀ m ∈ S, (a i : ℝ) + i * q k ≤ a m + m * q k) →
      (∀ m ∈ S, (a j : ℝ) + j * q k ≤ a m + m * q k) → i = j := by
  classical
  let M : ℕ → ℕ → Prop := fun k i => i ∈ S ∧ ∀ m ∈ S, (a i : ℝ) + i * q k ≤ a m + m * q k
  let B : Set ℕ := {k | 1 ≤ k ∧ ∃ i j, i < j ∧ M k i ∧ M k j}
  have hch : ∀ k, ∃ i j, k ∈ B → i < j ∧ M k i ∧ M k j := by
    intro k
    by_cases hk : k ∈ B
    · obtain ⟨-, i, j, h⟩ := hk
      exact ⟨i, j, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose I J hIJ using hch

  have hA : ∀ k, 1 ≤ k → ∀ i m, M k i → m ∈ S → m ≤ i → a i ≤ a m := by
    intro k hk i m hi hm hmi
    have h1 := hi.2 m hm
    have h2 : (m : ℝ) * q k ≤ i * q k :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmi) (hq k hk).le
    have : (a i : ℝ) ≤ a m := by linarith
    exact_mod_cast this
  have hA' : ∀ k, 1 ≤ k → ∀ i m, M k i → m ∈ S → m < i → a i < a m := by
    intro k hk i m hi hm hmi
    have h1 := hi.2 m hm
    have h2 : (m : ℝ) * q k < i * q k :=
      mul_lt_mul_of_pos_right (by exact_mod_cast hmi) (hq k hk)
    have : (a i : ℝ) < a m := by linarith
    exact_mod_cast this
  have hB : ∀ k k', 1 ≤ k → k < k' → ∀ m m', M k m → M k' m' → m ≤ m' := by
    intro k k' hk hkk m m' hm hm'
    by_contra hlt
    have hlt' : (m' : ℝ) < m := by exact_mod_cast (not_le.mp hlt)
    have h1 := hm.2 m' hm'.1
    have h2 := hm'.2 m hm.1
    have h3 := hqa k k' hk hkk
    nlinarith [mul_pos (sub_pos.mpr hlt') (sub_pos.mpr h3)]
  let φ : ℕ → ℕ := fun k => if I k < w then I k else w + a (J k)
  have hmaps : Set.MapsTo φ B (Finset.range (w + a w) : Set ℕ) := by
    intro k hk
    obtain ⟨hlt, hi, hj⟩ := hIJ k hk
    simp only [Finset.coe_range, Set.mem_Iio, φ]
    split_ifs with h
    · omega
    · have := hA' k hk.1 (J k) w hj hw (by omega)
      omega
  have hne : ∀ k ∈ B, ∀ k' ∈ B, k < k' → φ k ≠ φ k' := by
    intro k hk k' hk' hkk
    obtain ⟨hlt, hi, hj⟩ := hIJ k hk
    obtain ⟨hlt', hi', hj'⟩ := hIJ k' hk'
    have h1 := hB k k' hk.1 hkk _ _ hj hi'
    have h2 := hA' k' hk'.1 (J k') (J k) hj' hj.1 (by omega)
    simp only [φ]
    split_ifs <;> omega
  have hinj : Set.InjOn φ B := by
    intro k hk k' hk' h
    rcases lt_trichotomy k k' with h1 | h1 | h1
    · exact absurd h (hne k hk k' hk' h1)
    · exact h1
    · exact absurd h.symm (hne k' hk' k hk h1)
  have hfin : B.Finite := Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · have := Finset.card_le_card_of_injOn (s := hfin.toFinset) (t := Finset.range (w + a w)) φ
      (by simpa using hmaps) (by simpa using hinj)
    simpa using this
  · intro k hk hkB i hi j hj hmi hmj
    rw [Set.Finite.mem_toFinset] at hkB
    by_contra hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkB ⟨hk, i, j, h, ⟨hi, hmi⟩, ⟨hj, hmj⟩⟩
    · exact hkB ⟨hk, j, i, h, ⟨hj, hmj⟩, ⟨hi, hmi⟩⟩

section Val

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_ne_top {x : R} (hx : x ≠ 0) : addVal R x ≠ ⊤ := by
  rwa [Ne, addVal_eq_top_iff]

theorem toNat_addVal_pos {x : R} (hx : x ≠ 0) (hu : ¬ IsUnit x) : 0 < (addVal R x).toNat := by
  have h1 := addVal_ne_top hx
  have h2 : addVal R x ≠ 0 := by rwa [Ne, addVal_eq_zero_iff]
  exact Nat.pos_of_ne_zero (by simp [ENat.toNat_eq_zero, h1, h2])

theorem nval_mul_pow (l : ℕ) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (x * y ^ n) =
      Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x + n * Formalism.MainNotions.BlochKatoReduction.Gen.nval R l y := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hx)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hy)
  have : addVal R (x * y ^ n) = ((s + n * t : ℕ) : ℕ∞) := by
    rw [(addVal R).map_mul, (addVal R).map_pow, ← hs, ← ht]; simp
  rw [this, ← hs, ← ht]
  simp only [ENat.toNat_coe]
  push_cast
  ring

theorem addVal_lt_of_nval_lt (l : ℕ) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x < Formalism.MainNotions.BlochKatoReduction.Gen.nval R l y) : addVal R x < addVal R y := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval at h
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hx)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hy)
  rw [← hs, ← ht] at h ⊢
  simp only [ENat.toNat_coe] at h
  have : (s : ℝ) < t := lt_of_not_ge fun hge =>
    absurd h (not_lt.mpr (div_le_div_of_nonneg_right hge (Nat.cast_nonneg _)))
  exact_mod_cast this

theorem sum_unique_min (l : ℕ) (S : Finset ℕ) (t : ℕ → R) (ht : ∀ i ∈ S, t i ≠ 0) (i₀ : ℕ)
    (hi₀ : i₀ ∈ S)
    (h : ∀ i ∈ S, i ≠ i₀ → Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i₀) < Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i)) :
    ∑ i ∈ S, t i ≠ 0 ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (∑ i ∈ S, t i) = Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i₀) := by
  have h0 := addVal_ne_top (ht i₀ hi₀)
  have h1 : addVal R (t i₀) < addVal R (∑ i ∈ S.erase i₀, t i) :=
    (addVal R).map_lt_sum h0 fun i hi =>
      addVal_lt_of_nval_lt l (ht i₀ hi₀) (ht i (Finset.mem_of_mem_erase hi))
        (h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  have h2 : addVal R (∑ i ∈ S, t i) = addVal R (t i₀) := by
    rw [← Finset.add_sum_erase S t hi₀]
    exact (addVal R).map_add_eq_of_lt_left h1
  refine ⟨fun hz => h0 ?_, ?_⟩
  · rw [← h2, hz]; simp
  · unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval; rw [h2]

end Val

theorem value_at_root_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), l.Prime → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (h : Polynomial O) (w : ℕ), h.coeff w ≠ 0 → ∃ (BB : Finset ℕ) (c : ℕ → ℝ), BB.card ≤ w + (IsDiscreteValuationRing.addVal O (h.coeff w)).toNat ∧ ∀ k, 1 ≤ k → k ∉ BB → c k ≤ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff w) + w / (Nat.totient (l ^ k) : ℝ) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → Polynomial.aeval (ζ - 1) h ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (Polynomial.aeval (ζ - 1) h) = c k := by
  intro O _ _ _ l hl hl0 hlu h w hw
  set e : ℝ := ((addVal O (l : O)).toNat : ℝ) with he
  have hepos : 0 < e := by rw [he]; exact_mod_cast toNat_addVal_pos hl0 hlu
  have hphi : ∀ k, (0 : ℝ) < (Nat.totient (l ^ k) : ℝ) := fun k => by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hl.pos k)
  let a : ℕ → ℕ := fun i => (addVal O (h.coeff i)).toNat
  let q : ℕ → ℝ := fun k => e / (Nat.totient (l ^ k) : ℝ)
  have hwS : w ∈ h.support := Polynomial.mem_support_iff.mpr hw
  obtain ⟨BB, hcard, hBB⟩ := card_double_min (h.support : Set ℕ) a q w hwS
    (fun k _ => div_pos hepos (hphi k)) (by
      intro k k' hk hkk
      refine div_lt_div_of_pos_left hepos (hphi k) ?_
      rw [Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl (by omega)]
      have h1 : l ^ (k - 1) < l ^ (k' - 1) := Nat.pow_lt_pow_right hl.one_lt (by omega)
      have h2 : 0 < l - 1 := by have := hl.one_lt; omega
      exact_mod_cast Nat.mul_lt_mul_of_pos_right h1 h2)
  have hmin : ∀ k, ∃ i ∈ h.support, ∀ m ∈ h.support, (a i : ℝ) + i * q k ≤ a m + m * q k :=
    fun k => Finset.exists_min_image h.support (fun i => (a i : ℝ) + i * q k) ⟨w, hwS⟩
  choose I hIS hI using hmin
  have hform : ∀ k i : ℕ, Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff i) + i / (Nat.totient (l ^ k) : ℝ)
      = ((a i : ℝ) + i * q k) / e := by
    intro k i
    have := hphi k
    simp only [Formalism.MainNotions.BlochKatoReduction.Gen.nval, a, q, ← he]
    field_simp
  refine ⟨BB, fun k => ((a (I k) : ℝ) + I k * q k) / e, hcard, fun k hk hkB => ⟨?_, ?_⟩⟩
  · rw [hform]
    exact div_le_div_of_nonneg_right (hI k w hwS) hepos.le
  · intro O' _ _ _ _ _ hinj ζ hζ
    have hl0' : (l : O') ≠ 0 := by
      rw [← map_natCast (algebraMap O O')]
      exact fun h0 => hl0 (hinj (by rw [h0, map_zero]))
    have hlu' : ¬ IsUnit (l : O') := by
      rw [← map_natCast (algebraMap O O')]
      exact fun h0 => hlu (IsLocalHom.map_nonunit _ h0)
    obtain ⟨hz, hv⟩ := GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one O' l k hl hk hl0' hlu' ζ hζ
    have hc : ∀ i ∈ h.support, algebraMap O O' (h.coeff i) ≠ 0 := fun i hi h0 =>
      Polynomial.mem_support_iff.mp hi (hinj (by rw [h0, map_zero]))
    have hval : ∀ i ∈ h.support,
        Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' (h.coeff i) * (ζ - 1) ^ i)
          = ((a i : ℝ) + i * q k) / e := by
      intro i hi
      rw [nval_mul_pow l (hc i hi) hz, hv, GlobalTheory.T.normalizedValuation_algebraMap_eq O O' hinj, ← hform, mul_one_div]
    have key := sum_unique_min l h.support
      (fun i => algebraMap O O' (h.coeff i) * (ζ - 1) ^ i)
      (fun i hi => mul_ne_zero (hc i hi) (pow_ne_zero _ hz)) (I k) (hIS k) (by
        intro i hi hne
        rw [hval i hi, hval _ (hIS k)]
        refine div_lt_div_of_pos_right ?_ hepos
        refine lt_of_le_of_ne (hI k i hi) fun heq => hne ?_
        exact hBB k hk hkB i hi (I k) (hIS k) (fun m hm => heq ▸ hI k m hm) (hI k))
    rw [hval _ (hIS k)] at key
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    exact key

end GlobalTheory.PolyCycloValue
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section

namespace GlobalTheory.RedFixed

theorem exists_lift {Z O W k T : Type} [CommRing Z] [CommRing O] [CommRing W] [CommRing k] [CommRing T]
    [Algebra Z O] [Algebra Z W] [Algebra O k] (a : k →+* T) (b : W →+* T)
    (h : ∀ z : Z, a (algebraMap O k (algebraMap Z O z)) = b (algebraMap Z W z)) :
    ∃ F : k ⊗[O] (O ⊗[Z] W) →+* T, ∀ c o w, F (c ⊗ₜ (o ⊗ₜ w)) = a c * (a (algebraMap O k o) * b w) := by
  let _ : Algebra O T := (a.comp (algebraMap O k)).toAlgebra
  let _ : Algebra Z T := (b.comp (algebraMap Z W)).toAlgebra
  have : IsScalarTower Z O T := IsScalarTower.of_algebraMap_eq fun z => (h z).symm
  let b' : W →ₐ[Z] T := { b with commutes' := fun _ => rfl }
  let a' : k →ₐ[O] T := { a with commutes' := fun _ => rfl }
  let F₁ : O ⊗[Z] W →ₐ[O] T :=
    Algebra.TensorProduct.lift (Algebra.ofId O T) b' fun _ _ => Commute.all _ _
  exact ⟨(Algebra.TensorProduct.lift a' F₁ fun _ _ => Commute.all _ _).toRingHom, fun c o w => rfl⟩

variable {l : ℕ} [Fact l.Prime]

theorem map_padicInt {R : Type} [CommRing R] [CharP R l] [Algebra (ZMod l) R] (f : ℤ_[l] →+* R) (z : ℤ_[l]) :
    f z = algebraMap (ZMod l) R (PadicInt.toZMod z) := by
  have h := PadicInt.toZMod_spec z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨y, hy⟩ := h
  have h2 := congrArg f hy
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_sub, sub_eq_zero] at h2
  rw [h2]
  generalize PadicInt.toZMod z = n
  rw [ZMod.cast_eq_val, map_natCast, ← map_natCast (algebraMap (ZMod l) R), ZMod.natCast_zmod_val]

theorem perfect_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem fixed_tensor {k C : Type} [Field k] [Field C] [CharP C l] [Algebra (ZMod l) k] [Algebra (ZMod l) C]
    (f : C →ₗ[ZMod l] C) (hf : ∀ x, f x = x ^ l) (y : k ⊗[ZMod l] C) (hy : f.lTensor k y = y) :
    ∃ c : k, y = c ⊗ₜ[ZMod l] (1 : C) := by
  have hex : Function.Exact (Algebra.linearMap (ZMod l) C) (f - LinearMap.id : C →ₗ[ZMod l] C) := by
    intro x
    rw [LinearMap.sub_apply, hf, sub_eq_zero, LinearMap.id_apply]
    constructor
    · intro h
      have h2 := (Subfield.mem_bot_iff_pow_eq_self C l).2 h
      have h3 : (⊥ : Subfield C) ≤ (algebraMap (ZMod l) C).fieldRange := bot_le
      exact h3 h2
    · rintro ⟨a, rfl⟩
      rw [Algebra.linearMap_apply, ← map_pow, ZMod.pow_card]
  obtain ⟨t, ht⟩ := (Module.Flat.lTensor_exact k hex y).1 (by
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, hy, LinearMap.lTensor_id, LinearMap.id_apply, sub_self])
  refine ⟨TensorProduct.rid (ZMod l) k t, ?_⟩
  rw [← ht]
  clear ht
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  | add a b ha hb => simp [ha, hb, TensorProduct.add_tmul]

theorem fixed_witt {O k C : Type} [CommRing O] [Field k] [Field C] [CharP k l] [CharP C l] [PerfectRing C l]
    [Algebra ℤ_[l] O] [Algebra O k] [Algebra ℤ_[l] (WittVector l C)]
    (φ : WittVector l C →ₐ[ℤ_[l]] WittVector l C) (hφ0 : ∀ w, (φ w).coeff 0 = w.coeff 0 ^ l)
    (x : k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C))
    (hx : Algebra.TensorProduct.map (AlgHom.id k k) (Algebra.TensorProduct.map (AlgHom.id O O) φ) x = x) :
    ∃ c : k, x = algebraMap k (k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C)) c := by
  let _ : Algebra (ZMod l) k := ZMod.algebra k l
  let _ : Algebra (ZMod l) C := ZMod.algebra C l
  obtain ⟨F, hF⟩ := exists_lift (Z := ℤ_[l]) (O := O) (W := WittVector l C) (k := k) (T := k ⊗[ZMod l] C)
    Algebra.TensorProduct.includeLeftRingHom
    ((Algebra.TensorProduct.includeRight : C →ₐ[ZMod l] k ⊗[ZMod l] C).toRingHom.comp
      WittVector.constantCoeff) (fun z => by
      have h1 := map_padicInt ((algebraMap O k).comp (algebraMap ℤ_[l] O)) z
      have h2 := map_padicInt ((WittVector.constantCoeff : WittVector l C →+* C).comp (algebraMap ℤ_[l] (WittVector l C))) z
      rw [RingHom.comp_apply] at h1 h2
      rw [RingHom.comp_apply, h1, h2]
      simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
  have hF' : ∀ (c : k) (o : O) (w : WittVector l C),
      F (c ⊗ₜ (o ⊗ₜ w)) = (o • c) ⊗ₜ[ZMod l] w.coeff 0 := by
    intro c o w
    rw [hF]
    simp [Algebra.smul_def, mul_comm]
  let j : WittVector l C →+* k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C) :=
    (Algebra.TensorProduct.includeRight : O ⊗[ℤ_[l]] WittVector l C →ₐ[O] k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : WittVector l C →ₐ[ℤ_[l]] (O ⊗[ℤ_[l]] WittVector l C)).toRingHom
  have hl : ((l : ℕ) : k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C)) = 0 := by
    rw [← map_natCast (algebraMap k (k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C))), CharP.cast_eq_zero, map_zero]
  have hs : Function.Surjective (WittVector.constantCoeff : WittVector l C →+* C) := fun c =>
    ⟨WittVector.teichmuller l c, by simp⟩
  let g : C →+* k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C) := RingHom.liftOfSurjective _ hs ⟨j, by
    rw [WittVector.ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff]
    change j _ = 0
    rw [map_natCast, hl]⟩
  have hg : ∀ w : WittVector l C, g (w.coeff 0) = (1 : k) ⊗ₜ ((1 : O) ⊗ₜ w) := fun w =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ w
  let G : k ⊗[ZMod l] C →+ k ⊗[O] (O ⊗[ℤ_[l]] WittVector l C) := TensorProduct.liftAddHom
    { toFun := fun c =>
        { toFun := fun t => c • g t
          map_zero' := by simp
          map_add' := fun _ _ => by simp }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_smul] }
    (fun n c t => by
      obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective n
      change ((m : ZMod l) • c) • g t = c • g ((m : ZMod l) • t)
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul, smul_assoc, smul_comm])
  have hG : ∀ c t, G (c ⊗ₜ t) = c • g t := fun _ _ => rfl
  have hGF : ∀ y, G (F y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | tmul c r =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), ha, hb]
      | tmul o w =>
        rw [hF', hG, hg, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let f : C →ₗ[ZMod l] C := (frobenius C l).toAddMonoidHom.toZModLinearMap l
  have hφ : ∀ y, F (Algebra.TensorProduct.map (AlgHom.id k k) (Algebra.TensorProduct.map (AlgHom.id O O) φ) y) = f.lTensor k (F y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
    | tmul c r =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
      | tmul o w =>
        rw [hF']
        exact (hF' c o (φ w)).trans (by rw [hφ0]; rfl)
  obtain ⟨c, hc⟩ := fixed_tensor f (fun _ => rfl) (F x) (by rw [← hφ, hx])
  refine ⟨c, ?_⟩
  rw [← hGF x, hc, hG, map_one, Algebra.algebraMap_eq_smul_one]

theorem fixed_red : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) (k : Type) [Field k] [Algebra ↥(OL LL) k] [CharP k l] (x : k ⊗[↥(OL LL)] RW LL), Algebra.TensorProduct.map (AlgHom.id k k) (φRW LL) x = x → ∃ c : k, x = algebraMap k (k ⊗[↥(OL LL)] RW LL) c := by
  intro l _ LL k _ _ _ x hx
  have := perfect_Cb (l := l)
  exact fixed_witt (frobW l) (fun _ => rfl) x hx

end GlobalTheory.RedFixed
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.IdemVanish

theorem dvd_of_one_tmul_eq_zero {O k R : Type} [CommRing O] [CommRing k] [CommRing R]
    [Algebra O k] [Algebra O R] (lam : O) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) (x : R)
    (hx : ((1 : k) ⊗ₜ[O] x : k ⊗[O] R) = 0) : algebraMap O R lam ∣ x := by

  let f : O →ₐ[O] k := Algebra.ofId O k
  have hf : Function.Surjective f := hs
  have hker : RingHom.ker f = Ideal.span {lam} := by
    ext a
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    exact hk a
  let e : (O ⧸ RingHom.ker f) ≃ₐ[O] k := Ideal.quotientKerAlgEquivOfSurjective hf
  let φ : k ⊗[O] R ≃ₗ[O] R ⧸ (RingHom.ker f • (⊤ : Submodule O R)) :=
    (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl O R)).trans
      (TensorProduct.quotTensorEquivQuotSMul R (RingHom.ker f))
  have he : e.symm (1 : k) = Ideal.Quotient.mk (RingHom.ker f) 1 := by simp
  have h1 : φ ((1 : k) ⊗ₜ[O] x) = Submodule.Quotient.mk x := by
    simp only [φ, LinearEquiv.trans_apply, TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply,
      LinearEquiv.refl_apply, he, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have h2 : x ∈ RingHom.ker f • (⊤ : Submodule O R) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← h1, hx, map_zero]
  rw [hker, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨y, -, hy⟩ := h2
  exact ⟨y, by rw [← hy, Algebra.smul_def]⟩

theorem idem_eq_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (k : Type) [Field k] [Algebra ↥(OL LL) k] (lam : ↥(OL LL)), Function.Surjective (algebraMap ↥(OL LL) k) → (∀ x, algebraMap ↥(OL LL) k x = 0 ↔ lam ∣ x) → ∀ x : RW LL, IsIdempotentElem x → ((1 : k) ⊗ₜ[↥(OL LL)] x : k ⊗[↥(OL LL)] RW LL) = 0 → x = 0 := by
  intro l _ P LL k _ _ lam hs hk x hx h1

  have hd : algebraMap (↥(OL LL)) (RW LL) lam ∣ x := dvd_of_one_tmul_eq_zero lam hs hk x h1
  have hnu : ¬ IsUnit lam := by
    intro hu
    have h0 : algebraMap (↥(OL LL)) k 1 = 0 := (hk 1).2 hu.dvd
    simp at h0
  obtain ⟨m, hm⟩ := (GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL lam).resolve_left hnu
  apply GlobalTheory.EtaleExact.sep_RW LL x
  intro n
  calc (l : RW LL) ^ n = algebraMap (↥(OL LL)) (RW LL) (((l : ℕ) : ↥(OL LL)) ^ n) := by
        rw [map_pow, map_natCast]
    _ ∣ algebraMap (↥(OL LL)) (RW LL) (lam ^ (m * n)) :=
        map_dvd _ (by rw [pow_mul]; exact pow_dvd_pow_of_dvd hm n)
    _ ∣ algebraMap (↥(OL LL)) (RW LL) lam ^ (m * n + 1) := by
        rw [map_pow]; exact pow_dvd_pow _ (Nat.le_succ _)
    _ ∣ x ^ (m * n + 1) := pow_dvd_pow_of_dvd hd _
    _ = x := hx.pow_succ_eq _

end GlobalTheory.IdemVanish
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

theorem GlobalTheory.UseLoc.extendUnramEmb : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), K.1 ≤ MaximalUnramifiedExtension l → ∀ e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1, ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e ∧ ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ'.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e → τ' = τ := by
  intro l _ K LL hK e
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro y
    refine ⟨⟨y.1, ⟨y.2, hK y.2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  let φ : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨e.comp φ.symm.toAlgHom, ?_, ?_⟩
  · ext x
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((e z : ↥LL.1) : Om l)) this
  · intro τ' hτ'
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    have h1 := congrArg (fun f : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 => f x) hτ'
    simp only [AlgHom.comp_apply] at h1
    rw [h1]
    simp only [AlgHom.comp_apply]
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    exact (congrArg (fun z => ((e z : ↥LL.1) : Om l)) this).symm
end
