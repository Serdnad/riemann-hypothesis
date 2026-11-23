module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification

@[expose] public section

section

open scoped Topology

namespace GlobalTheory


open MeasureTheory AddCircle in
theorem circle_hom_eq_zpow :
    ∀ f : Circle →* Circle, Continuous f → ∃ n : ℤ, ∀ z, f z = z ^ n := by
  intro f hf
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let g : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x => (f (toCircle x) : ℂ),
      continuous_subtype_val.comp (hf.comp continuous_toCircle)⟩
  have hg : ∀ x, g x = (f (toCircle x) : ℂ) := fun _ => rfl
  have hex : ∃ n : ℤ, fourierCoeff g n ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : fourierCoeff g = fun _ => 0 := funext hcon
    have hs := has_pointwise_sum_fourier_series_of_summable (f := g)
      (by rw [h0]; exact summable_zero) 0
    simp only [hcon, zero_smul] at hs
    have := hs.unique hasSum_zero
    rw [hg] at this
    exact Circle.coe_ne_zero _ this
  obtain ⟨n, hn⟩ := hex
  refine ⟨n, fun z => ?_⟩
  obtain ⟨w, rfl⟩ : ∃ w : AddCircle (1 : ℝ), toCircle w = z := by
    obtain ⟨w, hw⟩ := (homeomorphCircle (T := 1) one_ne_zero).surjective z
    exact ⟨w, by rw [← homeomorphCircle_apply one_ne_zero, hw]⟩
  have key : fourierCoeff g n = (fourier (-n) w * g w) * fourierCoeff g n := by
    unfold fourierCoeff
    rw [← integral_const_mul]
    rw [← integral_add_left_eq_self (μ := haarAddCircle)
      (fun t : AddCircle (1 : ℝ) => fourier (-n) t • g t) w]
    congr 1
    ext t
    simp only [hg, fourier_apply, zsmul_add, toCircle_add, map_mul, Circle.coe_mul, smul_eq_mul]
    ring
  have h1 : fourier (-n) w * g w = 1 := by
    have := mul_right_cancel₀ hn (key.symm.trans (one_mul _).symm)
    exact this
  rw [hg, fourier_apply, toCircle_zsmul, ← Circle.coe_mul, ← Circle.coe_one] at h1
  have h2 : toCircle w ^ (-n) * f (toCircle w) = (1 : Circle) := Circle.ext h1
  rw [zpow_neg, inv_mul_eq_one] at h2
  exact h2.symm

end GlobalTheory
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
  UniqueFactorizationMonoid
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory


open UniqueFactorizationMonoid in
theorem exists_multiplicative_ideal_extension :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (c : HeightOneSpectrum (𝓞 K) → ℂ), (∀ P, ¬ m ≤ P.asIdeal → ‖c P‖ = 1) → ∃ X : Ideal (𝓞 K) → ℂ, X ⊥ = 0 ∧ X ⊤ = 1 ∧ (∀ I J, X (I * J) = X I * X J) ∧ (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) ∧ (∀ I, I ⊔ m ≠ ⊤ → X I = 0) ∧ ∀ P, ¬ m ≤ P.asIdeal → X P.asIdeal = c P := by
  intro K _ _ m c hc
  let d : Ideal (𝓞 K) → ℂ := fun Q =>
    if h : Q.IsPrime ∧ Q ≠ ⊥ then (if m ≤ Q then 0 else c ⟨Q, h.1, h.2⟩) else 0
  have hd : ∀ P : HeightOneSpectrum (𝓞 K), ¬ m ≤ P.asIdeal → d P.asIdeal = c P := by
    intro P hP
    simp only [d]
    rw [dite_eq_left ⟨P.isPrime, P.ne_bot⟩, if_neg hP]
  have hd0 : ∀ Q, m ≤ Q → d Q = 0 := by
    intro Q hQ
    simp only [d]
    split_ifs <;> rfl
  refine ⟨fun I => if I = ⊥ then 0 else ((normalizedFactors I).map d).prod, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · have : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
    simp only [if_neg this]
    rw [← Ideal.one_eq_top, normalizedFactors_one]
    simp
  · intro I J
    by_cases hI : I = ⊥
    · simp [hI]
    by_cases hJ : J = ⊥
    · simp [hJ]
    have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
    simp only [if_neg hI, if_neg hJ, if_neg hIJ]
    rw [normalizedFactors_mul hI hJ, Multiset.map_add (f := _), Multiset.prod_add]
  · intro I hI hm
    simp only [if_neg hI]
    refine Multiset.prod_induction (fun z : ℂ => ‖z‖ = 1) _ ?_ (by simp) ?_
    · intro a b ha hb
      simp [ha, hb]
    · intro a ha
      obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.1 ha
      have hp : Prime Q := prime_of_normalized_factor Q hQ
      have hle : I ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
      have hQp : Q.IsPrime := Ideal.isPrime_of_prime hp
      have hm' : ¬ m ≤ Q := fun h => hQp.ne_top (top_le_iff.1 (hm ▸ sup_le hle h))
      have := hd ⟨Q, hQp, hp.ne_zero⟩ hm'
      simp only at this
      rw [this]
      exact hc _ hm'
  · intro I hm
    by_cases hI : I = ⊥
    · simp [hI]
    simp only [if_neg hI]
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hm
    apply Multiset.prod_eq_zero
    refine Multiset.mem_map.2 ⟨Q, ?_, hd0 Q (le_sup_right.trans hle)⟩
    exact (Ideal.mem_normalizedFactors_iff hI).2 ⟨hQ.isPrime, le_sup_left.trans hle⟩
  · intro P hP
    simp only [if_neg P.ne_bot]
    rw [normalizedFactors_irreducible P.irreducible, normalize_eq]
    simp [hd P hP]

end GlobalTheory
end

section

namespace GlobalTheory.MinkowskiLinearForms

open MeasureTheory

theorem minkowski_linear_forms {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : Matrix.det A ≠ (0 : ℝ)) {t : ℝ} (ht : (0 : ℝ) < t)
    (hlt : |Matrix.det A| < t ^ Fintype.card ι) :
    ∃ (z : ι → ℤ), z ≠ (0 : ι → ℤ) ∧ ∀ (j : ι), |∑ i : ι, (↑(z i) : ℝ) * A i j| < t := by
  classical
  have hli : LinearIndependent ℝ (fun i => A i) := Matrix.linearIndependent_rows_of_det_ne_zero hA
  let b : Module.Basis ι ℝ (ι → ℝ) := basisOfPiSpaceOfLinearIndependent hli
  have hb : (⇑b : ι → ι → ℝ) = fun i => A i := coe_basisOfPiSpaceOfLinearIndependent hli
  let L : AddSubgroup (ι → ℝ) := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  have hF := ZSpan.isAddFundamentalDomain' b (volume : Measure (ι → ℝ))
  let s : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ioo (-t) t
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.neg_apply] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    exact ⟨by linarith, by linarith⟩
  have hconv : Convex ℝ s := convex_pi (fun i _ => convex_Ioo (-t) t)
  have hvolF : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal |Matrix.det A| := by
    rw [ZSpan.volume_fundamentalDomain]
    congr 3
  have hvols : volume s = ENNReal.ofReal ((2 * t) ^ Fintype.card ι) := by
    simp only [s, Real.volume_pi_Ioo]
    rw [Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (by linarith)]
    congr 2
    ring
  have hlt' : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (ι → ℝ) < volume s := by
    rw [hvolF, hvols, Module.finrank_fintype_fun_eq_card]
    rw [show (2 : ENNReal) ^ Fintype.card ι = ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [mul_pow, mul_comm ((2:ℝ) ^ _)]
    exact mul_lt_mul_of_pos_right hlt (by positivity)
  haveI hcount : Countable (Submodule.span ℤ (Set.range b)) := inferInstance
  haveI : Countable L := hcount
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF hsymm hconv hlt'
  have hxmem : (x : ι → ℝ) ∈ Submodule.span ℤ (Set.range b) := x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxmem
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    apply hx0
    ext1
    rw [← hc, hc0]
    simp
  · intro j
    have hxj := hxs j (Set.mem_univ j)
    rw [Set.mem_Ioo] at hxj
    have : (x : ι → ℝ) j = ∑ i, (c i : ℝ) * A i j := by
      rw [← hc, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hb, zsmul_eq_mul]
    rw [← this, abs_lt]
    exact hxj

end GlobalTheory.MinkowskiLinearForms
end

section

namespace GlobalTheory.NormOneInfinite

theorem normOne_infinite {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
    (c : Gal(E/F)) (hc : ∀ x : E, (c : E → E) ((c : E → E) x) = x) (h1 : c ≠ (1 : Gal(E/F))) :
    Set.Infinite {l : E | l * (c : E → E) l = (1 : E)} := by
  have hx : ∃ x : E, c x ≠ x := by
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    exact h1 (AlgEquiv.ext fun x => by rw [hall x, AlgEquiv.one_apply])
  obtain ⟨x, hx⟩ := hx
  have hcd : c (x - c x) = -(x - c x) := by
    rw [map_sub, hc x]
    ring
  have hd : x - c x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcn : ∀ n : ℕ, c (n : E) = n := fun n => map_natCast c n
  have h2d : ∀ y : E, y = -y → y = 0 := by
    intro y hy
    have h2 : (2 : E) * y = 0 := by linear_combination hy
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hsub : ∀ n : ℕ, (n : E) - (x - c x) ≠ 0 := by
    intro n h0
    have e : x - c x = n := (sub_eq_zero.mp h0).symm
    apply hd
    apply h2d
    calc x - c x = c (x - c x) := by rw [e, hcn]
      _ = -(x - c x) := hcd
  have hadd : ∀ n : ℕ, (n : E) + (x - c x) ≠ 0 := by
    intro n h0
    have e : x - c x = -(n : E) := by linear_combination h0
    apply hd
    apply h2d
    calc x - c x = c (x - c x) := by rw [e, map_neg, hcn]
      _ = -(x - c x) := hcd
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + (x - c x)) / ((n : E) - (x - c x))) ?_ ?_
  · intro n m hnm
    simp only at hnm
    rw [div_eq_div_iff (hsub n) (hsub m)] at hnm
    have h3 : (2 : E) * (x - c x) * ((m : E) - n) = 0 := by linear_combination hnm
    rcases mul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' two_ne_zero
      · exact absurd h' hd
    · exact (Nat.cast_injective (sub_eq_zero.mp h)).symm
  · intro n
    change ((n : E) + (x - c x)) / ((n : E) - (x - c x)) *
      c (((n : E) + (x - c x)) / ((n : E) - (x - c x))) = 1
    rw [map_div₀, map_add (f := _), map_sub c (n : E) (x - c x), hcn, hcd]
    have h4 : (n : E) + -(x - c x) = (n : E) - (x - c x) := by ring
    have h5 : (n : E) - -(x - c x) = (n : E) + (x - c x) := by ring
    rw [h4, h5, div_mul_div_comm, mul_comm ((n : E) - (x - c x))]
    exact div_self (mul_ne_zero (hadd n) (hsub n))

end GlobalTheory.NormOneInfinite
end

section

namespace GlobalTheory.ProductLeftMaps

open TensorProduct

theorem prodLeft_eq_maps {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : TensorProduct F (A × B) E) :
    TensorProduct.prodLeft F F A B E z =
      ((Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F A E) z,
       (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F B E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul x e =>
    obtain ⟨a, b⟩ := x
    simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    rw [map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
    rfl

theorem main : ∀ {F A B E : Type} [inst : Field F] [inst_1 : CommRing A] [inst_2 : CommRing B]
    [inst_3 : CommRing E] [inst_4 : Algebra F A] [inst_5 : Algebra F B] [inst_6 : Algebra F E]
    (z : TensorProduct F (A × B) E),
    (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F A E) z = (0 : TensorProduct F A E) →
    (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F B E) z = (0 : TensorProduct F B E) →
    z = (0 : TensorProduct F (A × B) E) := by
  intro F A B E _ _ _ _ _ _ _ z h1 h2
  apply (TensorProduct.prodLeft F F A B E).injective
  rw [prodLeft_eq_maps, h1, h2, map_zero]
  rfl

end GlobalTheory.ProductLeftMaps
end

section

open NumberField

namespace GlobalTheory.IntegralMultipleOfVectors

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ (e : ℕ) (b : RingOfIntegers E), 0 < e ∧ (e : E) * a = algebraMap (RingOfIntegers E) E b := by
  have h : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h.exists_integral_multiple
  have hi' : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rcases Int.natAbs_eq y with h1 | h1
    · have : (y.natAbs : E) * a = y • a := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi
    · have : (y.natAbs : E) * a = -(y • a) := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi.neg
  exact ⟨y.natAbs, ⟨_, hi'⟩, Int.natAbs_pos.mpr hy, rfl⟩

theorem exists_nsmul_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx e
    · rw [mul_smul]; exact nsmul_mem hy d
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, b, he, hb⟩ := exists_nat_mul_integral a
    refine ⟨e * d, Nat.mul_pos he hd, ?_⟩
    have : (e * d) • a • x = b • d • x := by
      rw [← algebraMap_smul E b, ← hb]
      ext i
      simp
      ring
    rw [this]
    exact L.smul_mem b hx

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • M.mulVec v ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hfg
  choose f hf hmem using fun v => exists_nsmul_mem L hL (M.mulVec v)
  refine ⟨∏ v ∈ s, f v, Finset.prod_pos fun v _ => hf v, fun v hv => ?_⟩
  have hv' : v ∈ Submodule.span (RingOfIntegers E) (s : Set (Fin n → E)) := by
    rw [hs]; exact hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul s f (Finset.mem_coe.mp hx), mul_smul]
    exact nsmul_mem (hmem x) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul E a, Matrix.mulVec_smul, algebraMap_smul, smul_comm]
    exact L.smul_mem a hx

end GlobalTheory.IntegralMultipleOfVectors
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem exists_integral_ideal_in_class_coprime :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)), m ≠ ⊥ → ∀ c : ClassGroup (𝓞 K), ∃ b : (Ideal (𝓞 K))⁰, ClassGroup.mk0 b = c ∧ (b : Ideal (𝓞 K)) ⊔ m = ⊤ := by
  intro K _ _ m hm c
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (Ideal.mul_le_inf.trans inf_le_left : (J : Ideal (𝓞 K)) * m ≤ J) (mul_ne_zero hJ0 hm)
  have haJ : a ∈ (J : Ideal (𝓞 K)) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨L, hL⟩ : (J : Ideal (𝓞 K)) ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haJ)
  have hcop : m ⊔ L = ⊤ := by
    have h1 : (J : Ideal (𝓞 K)) * (m ⊔ L) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hL, ha, Ideal.mul_top]
    exact mul_left_cancel₀ hJ0 h1
  by_cases hL0 : L = 0
  · have hmt : m = ⊤ := by simpa [hL0] using hcop
    obtain ⟨b, hb⟩ := ClassGroup.mk0_surjective c
    exact ⟨b, hb, by simp [hmt]⟩
  · refine ⟨⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩, ?_, by rw [sup_comm]; exact hcop⟩
    have hprod : ClassGroup.mk0 J * ClassGroup.mk0 ⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩ = 1 := by
      rw [← map_mul, ClassGroup.mk0_eq_one_iff]
      change ((J : Ideal (𝓞 K)) * L).IsPrincipal
      rw [← hL]
      exact ⟨⟨a, rfl⟩⟩
    rw [hJ] at hprod
    exact (inv_mul_eq_one.mp hprod).symm

end GlobalTheory
end

section

open NumberField IsDedekindDomain
open scoped Matrix WithZero

theorem GlobalTheory.LocalQuad.exists_ringHom_adicCompletion (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (φ : v.adicCompletion K →+* w.adicCompletion L),
      ∀ x : K, φ (algebraMap K (v.adicCompletion K) x) =
        algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  let v : HeightOneSpectrum (𝓞 K) := w.under (𝓞 K)
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L v w).continuous
  refine ⟨v, ((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom, fun x => ?_⟩
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
end
