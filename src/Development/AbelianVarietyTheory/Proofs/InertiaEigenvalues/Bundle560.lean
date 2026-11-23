module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem prime_mk_X_of_constantCoeff {W : Type} [CommRing W] [IsDomain W] {p : W} (hp : Prime p) (E : W⟦X⟧)
    (w : Wˣ) (hE : constantCoeff E = p * w) :
    Prime (Ideal.Quotient.mk (Ideal.span {E}) (X : W⟦X⟧)) := by
  have key : ∀ f : W⟦X⟧, Ideal.Quotient.mk (Ideal.span {E}) (X : W⟦X⟧) ∣ Ideal.Quotient.mk (Ideal.span {E}) f ↔
      p ∣ constantCoeff f := by
    intro f
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
      obtain ⟨d, hd⟩ := hc
      have h := congrArg constantCoeff hd
      simp only [map_sub, map_mul, constantCoeff_X, zero_mul, sub_zero, hE] at h
      exact ⟨w * constantCoeff d, by rw [h, mul_assoc]⟩
    · rintro ⟨c, hc⟩
      have h0 : constantCoeff (f - E * C (((w⁻¹ : Wˣ) : W) * c)) = 0 := by
        simp only [map_sub, map_mul, constantCoeff_C, hE, hc]
        rw [mul_assoc, ← mul_assoc (w : W), Units.mul_inv, one_mul, sub_self]
      obtain ⟨g, hg⟩ := X_dvd_iff.2 h0
      refine ⟨Ideal.Quotient.mk _ g, ?_⟩
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨C (((w⁻¹ : Wˣ) : W) * c), by rw [← hg]; ring⟩
  refine ⟨fun h => ?_, fun h => ?_, fun a b hab => ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h1 := congrArg constantCoeff hc
    simp only [map_mul, constantCoeff_X, hE] at h1
    have h2 : constantCoeff c = 0 :=
      (mul_eq_zero.1 h1.symm).resolve_left (mul_ne_zero hp.ne_zero w.ne_zero)
    obtain ⟨g, rfl⟩ := X_dvd_iff.2 h2
    have h3 : (1 : W⟦X⟧) = E * g := by
      apply mul_left_cancel₀ (X_ne_zero (R := W))
      rw [mul_one]
      linear_combination hc
    have h4 := congrArg constantCoeff h3
    simp only [map_mul, map_one, hE] at h4
    exact hp.not_isUnit (isUnit_of_dvd_one ⟨w * constantCoeff g, by rw [h4, mul_assoc]⟩)
  · have h1 := (key 1).1 h.dvd
    rw [map_one] at h1
    exact hp.not_isUnit (isUnit_of_dvd_one h1)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, key, map_mul] at hab
    rw [key, key]
    exact hp.dvd_or_dvd hab

theorem BK.prime_unif (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) :
    Prime (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) ∧
      intToOC K (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) = bk.flat.untilt := by
  constructor
  · obtain ⟨w, hw⟩ := bk.coeff_zero
    have hp : Prime (l : Wq l bk.a) := (WittVector.irreducible l).prime
    have hE : constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; exact Polynomial.constantCoeff_coe _
    exact (MulEquiv.prime_iff bk.str.symm).2 (prime_mk_X_of_constantCoeff hp bk.E w hE)
  · rw [← bk.θ_ev _ X (bk.str.apply_symm_apply _).symm, bk.ev_X]
    exact WittVector.fontaineTheta_teichmuller _

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.FrobMat

theorem isFrac_add {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k : ℕ} (h : IsFrac d y m k) (c : ℕ) :
    IsFrac d y (d ^ c • m) (k + c) := by
  unfold IsFrac at *
  rw [h, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, smul_smul, pow_add, mul_comm]

theorem isFrac_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k a : ℕ} (h : IsFrac d y m k) (hka : k ≤ a) :
    IsFrac d y (d ^ (a - k) • m) a := by
  have := isFrac_add h (a - k)
  rwa [Nat.add_sub_cancel' hka] at this

theorem isFrac_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k : ℕ} (h : IsFrac d y m k) :
    d ^ k • y = LocalizedModule.mk m 1 := by
  unfold IsFrac at h
  rw [h, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, OneMemClass.coe_one]

theorem exists_common_den {R : Type} [CommRing R] (x : R) {ι : Type} [Finite ι]
    (f : ι → Localization.Away x) : ∃ (n : ℕ) (g : ι → R), ∀ i, algebraMap R _ (g i) = x ^ n • f i := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers x) f
  choose g hg using hn
  exact ⟨n, g, hg⟩

theorem span_eq_top_of_semiBC {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) {ι : Type} [Fintype ι]
    (e : Module.Basis ι A M) : Submodule.span B (Set.range fun i => u (e i)) = ⊤ := by
  let S := Submodule.span B (Set.range fun i => u (e i))
  have hu : ∀ x, u x ∈ S := by
    intro x

    rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [u.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨w, -, huniq⟩ := h (N ⧸ S) 0
  have h1 : S.mkQ = w := huniq _ fun x => by
    simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]; exact hu x
  have h2 : (0 : N →ₗ[B] N ⧸ S) = w := huniq _ fun x => by simp
  rw [eq_top_iff]
  intro y _
  have := LinearMap.congr_fun (h1.trans h2.symm) y
  simpa using this

end GlobalTheory.BSP.FrobMat

namespace GlobalTheory.BSP.FrobMat

theorem frob_matrix_general {R Mo : Type} [CommRing R] [IsDomain R] [AddCommGroup Mo] [Module R Mo]
    (φ : R →+* R) (x : R) (hx : x ≠ 0)
    (u : Mo →ₛₗ[(algebraMap R (Localization.Away x)).comp φ] LocalizedModule (Submonoid.powers x) Mo)
    (hu : SemiBC u) {d : ℕ} (e : Module.Basis (Fin d) R Mo) :
    ∃ (a b : ℕ) (A A' : Matrix (Fin d) (Fin d) R), A * A' = x ^ b • (1 : Matrix (Fin d) (Fin d) R) ∧
      ∀ j, IsFrac x (u (e j)) (∑ i, A i j • e i) a := by
  haveI : Module.Free R Mo := Module.Free.of_basis e
  have h1 : ∀ j, ∃ m k, IsFrac x (u (e j)) m k := fun j => exists_isFrac _ _
  choose m k hmk using h1
  let a := ∑ j, k j
  have hk : ∀ j, k j ≤ a := fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let m' : Fin d → Mo := fun j => x ^ (a - k j) • m j
  have hm' : ∀ j, IsFrac x (u (e j)) (m' j) a := fun j => isFrac_le (hmk j) (hk j)
  let A : Matrix (Fin d) (Fin d) R := fun i j => e.repr (m' j) i
  have hA : ∀ j, ∑ i, A i j • e i = m' j := fun j => e.sum_repr (m' j)
  have hsp := span_eq_top_of_semiBC hu e
  have h2 : ∀ k' : Fin d, ∃ c : Fin d → Localization.Away x,
      ∑ j, c j • u (e j) = LocalizedModule.mk (e k') 1 := fun k' =>
    (Submodule.mem_span_range_iff_exists_fun _).1 (Submodule.eq_top_iff'.1 hsp _)
  choose c hc using h2
  obtain ⟨n, A', hA'⟩ := exists_common_den x (fun p : Fin d × Fin d => c p.2 p.1)
  let A'' : Matrix (Fin d) (Fin d) R := fun j k' => A' (j, k')
  refine ⟨a, a + n, A, A'', ?_, fun j => (hA j).symm ▸ hm' j⟩
  have key : ∀ k', LocalizedModule.mk (x ^ (a + n) • e k') (1 : Submonoid.powers x) =
      LocalizedModule.mk (∑ j, A' (j, k') • m' j) 1 := by
    intro k'
    have hr : LocalizedModule.mk (∑ j, A' (j, k') • m' j) (1 : Submonoid.powers x) =
        ∑ j, A' (j, k') • LocalizedModule.mk (m' j) (1 : Submonoid.powers x) := by

      rw [← LocalizedModule.mkLinearMap_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LocalizedModule.mkLinearMap_apply]
    rw [hr, ← LocalizedModule.smul'_mk, ← hc k', pow_add, mul_smul, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_assoc (x ^ n) (c k' j), ← hA' (j, k'), algebraMap_smul, smul_comm,
      isFrac_smul (hm' j)]
  have key2 : ∀ k', x ^ (a + n) • e k' = ∑ j, A' (j, k') • m' j := by
    intro k'
    obtain ⟨⟨_, r, rfl⟩, hr⟩ := LocalizedModule.mk_eq.1 (key k')
    simp only [Submonoid.smul_def, one_smul] at hr
    exact smul_right_injective _ (pow_ne_zero r hx) hr
  ext i k'
  have h3 := congrArg (fun y => e.repr y i) (key2 k')

  simp only [map_smul, e.repr_self, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum,
  Finset.sum_apply, Finsupp.single_apply, smul_eq_mul] at h3
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [eq_comm] at h3
  simp only [eq_comm (a := k') (b := i)] at h3
  rw [← h3]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.BSP.FrobMat

theorem GlobalTheory.BSP.frob_matrix_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), ∃ (a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) ∧ ∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a := by
  intro l _ K bk d M e
  haveI : IsDomain bk.prism.A := inferInstanceAs (IsDomain bk.S)
  exact GlobalTheory.BSP.FrobMat.frob_matrix_general (R := bk.prism.A) bk.prism.D.φ (bk.toP bk.E) bk.E_ne_zero
    (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩)
    (M.Φ_bc bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩) e
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

theorem ainf_exists_l_mul_of_coeff_zero (a : Ainf l) (h : a.coeff 0 = 0) :
    ∃ b : Ainf l, a = (l : Ainf l) * b := by
  have hv := WittVector.eq_iterate_verschiebung (n := 1) (x := a) (fun i hi => by
    rw [Nat.lt_one_iff.1 hi]; exact h)
  have hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l) := by
    rw [WittVector.frobenius_eq_map_frobenius]
    exact WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective
  obtain ⟨c, hc⟩ := hsurj (a.shift 1)
  refine ⟨c, ?_⟩
  rw [hv, Function.iterate_one, ← hc, WittVector.verschiebung_frobenius, mul_comm]

theorem coeff_zero_l_mul {R : Type} [CommRing R] [CharP R l] (x : WittVector l R) :
    ((l : WittVector l R) * x).coeff 0 = 0 := by
  change WittVector.constantCoeff ((l : WittVector l R) * x) = 0
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem isUnit_inclW_per_and_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → IsUnit (inclW l τ) ∧ (∀ g : GQ l, IsUnit (inclW l (Per.σA g τ))) ∧
      ∀ (k : ℕ) (a : Ainf l), ((l : ℕ) : WCb l) ^ k ∣ inclW l a → ((l : ℕ) : Ainf l) ^ k ∣ a := by
  intro l _ K bk τ hτ
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  have hε1 : ε ≠ 1 := by
    rintro rfl
    obtain ⟨-, hu⟩ := hε
    exact hu (by rw [map_one]; simp)
  have hc0 : τ.coeff 0 ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x => WittVector.constantCoeff x) hφ
    change (WittVector.frobenius τ).coeff 0 = _ at h1
    rw [WittVector.coeff_frobenius_charP, h0, zero_pow (Fact.out : l.Prime).ne_zero, map_mul, map_sub, map_one] at h1
    change 0 = WittVector.constantCoeff (η : Ainf l) * ((WittVector.teichmuller l ε).coeff 0 - 1) at h1
    rw [WittVector.teichmuller_coeff_zero] at h1
    have hη : IsUnit (WittVector.constantCoeff (η : Ainf l)) := η.isUnit.map _
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact hη.ne_zero h
    · exact hε1 (sub_eq_zero.1 h)
  have hU : IsUnit (inclW l τ) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change algebraMap (OCb l) (Cb l) (τ.coeff 0) ≠ 0
    exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hc0
  refine ⟨hU, fun g => ?_, ?_⟩
  · rw [← galW_inclW]
    exact hU.map (galW l g)
  · intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ⟨c, hc⟩
      have h0 : a.coeff 0 = 0 := by
        have h1 : (inclW l a).coeff 0 = 0 := by
          rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
        change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
        exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
      obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
      have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
        have h1 := congrArg (fun x : WCb l => x.coeff 1) h
        simp [WittVector.coeff_p] at h1
      have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
        refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
        rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
      exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem norm_E_le_radius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ ((l : ℝ)⁻¹ ≤ bk.ρ₀) ∧ ‖toDisc l (s X) bk.ρ₀ (s bk.E)‖ ≤ (l : ℝ)⁻¹ := by
  intro l hl K bk A _ s
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  have hρ : ((bk.ρ₀ : ℝ≥0) : ℝ) = (l : ℝ) ^ (-(1 / (bk.Ep.natDegree : ℝ))) := by
    simp [BK.ρ₀, NNReal.coe_rpow]
  have hρpos : 0 < bk.ρ₀ := by
    rw [← NNReal.coe_pos, hρ]; exact Real.rpow_pos_of_pos hl0 _
  have hρe : ((bk.ρ₀ : ℝ)) ^ bk.Ep.natDegree = (l : ℝ)⁻¹ := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
    have : -(1 / (bk.Ep.natDegree : ℝ)) * (bk.Ep.natDegree : ℝ) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]
  refine ⟨hρpos, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, hρ, NNReal.coe_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos (one_div_pos.2 he))
  · rw [hρ, ← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le hl1.le ?_
    have : 1 / (bk.Ep.natDegree : ℝ) ≤ 1 := by
      rw [div_le_one he]; exact_mod_cast bk.deg_pos
    linarith
  · have hE : bk.E = X ^ bk.Ep.natDegree + ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * X ^ i := by
      show (bk.Ep : (Wq l bk.a)⟦X⟧) = _
      conv_lhs => rw [bk.monic.as_sum]
      simp only [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]
      congr 1

      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
      simp
    have hmem : algebraMap A (PreDisc l (s X) bk.ρ₀) (s bk.E) ∈ ball l (s X) bk.ρ₀ (l : ℝ)⁻¹ := by

      rw [hE, map_add (f := _), map_add (f := _), map_sum, map_sum]
      refine add_mem ?_ (Submodule.sum_mem _ fun i hi => ?_)
      · refine Submodule.subset_span ⟨0, bk.Ep.natDegree, 0, ?_, ?_⟩
        · simp [hρe]
        · simp [map_pow]
      · obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
        have h2 : algebraMap A (PreDisc l (s X) bk.ρ₀) (s (C (bk.Ep.coeff i) * X ^ i)) =
            s (C c * X ^ i) • (algebraMap A (PreDisc l (s X) bk.ρ₀) ((l : A) ^ 1 * (s X) ^ 0) *
              IsLocalization.Away.invSelf (l : A) ^ 0) := by
          rw [hc, Algebra.smul_def]
          simp only [map_mul, map_natCast, map_pow, pow_one, pow_zero, mul_one]
          ring
        rw [h2]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, 0, 0, by simp [hl0.ne'], rfl⟩)
    exact (norm_ofPre l (s X) bk.ρ₀ _).trans_le (gauge_le l (s X) bk.ρ₀ (by positivity) hmem)
end GlobalTheory.BSP
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.PairW

theorem eq_zero_of_mem_pow {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] {x : A}
    (h : ∀ n : ℕ, x ∈ J ^ n) : x = 0 :=
  IsHausdorff.haus' (I := J) x fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact h n

theorem pow_sub_pow_mem_succ {A : Type} [CommRing A] {J : Ideal A} (p : ℕ) (hp : (p : A) ∈ J) {y z : A}
    {k : ℕ} (h : y - z ∈ J ^ (k + 1)) : y ^ p - z ^ p ∈ J ^ (k + 1 + 1) := by
  have h1 : y - z ∈ J := Ideal.pow_le_self (Nat.succ_ne_zero k) h
  have hs : (∑ i ∈ Finset.range p, y ^ i * z ^ (p - 1 - i)) ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hyz : Ideal.Quotient.mk J y = Ideal.Quotient.mk J z := Ideal.Quotient.eq.2 h1

    rw [map_sum]
    simp only [map_mul, map_pow, hyz]
    rw [geom_sum₂_self, ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]
  have e := geom_sum₂_mul y z p
  rw [← e, mul_comm, pow_succ]
  exact Ideal.mul_mem_mul h hs

theorem pow_pow_sub_mem {A : Type} [CommRing A] {J : Ideal A} (p : ℕ) (hp : (p : A) ∈ J) {y z : A}
    (h : y - z ∈ J) (n : ℕ) : y ^ p ^ n - z ^ p ^ n ∈ J ^ (n + 1) := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [pow_succ p n, pow_mul, pow_mul]; exact pow_sub_pow_mem_succ p hp ih

theorem eq_of_pow_eq_self {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] (p : ℕ) (hp : (p : A) ∈ J)
    {a : ℕ} (ha : 0 < a) {y z : A} (hy : y ^ p ^ a = y) (hz : z ^ p ^ a = z) (h : y - z ∈ J) : y = z := by
  have hy' : ∀ n, y ^ p ^ (a * n) = y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hy]
  have hz' : ∀ n, z ^ p ^ (a * n) = z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hz]
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_pow (J := J) fun n => ?_
  have h2 := pow_pow_sub_mem p hp h (a * n)
  rw [hy', hz'] at h2
  exact Ideal.pow_le_pow_right (Nat.le_succ_of_le (Nat.le_mul_of_pos_left n ha)) h2

theorem padicInt_ringHom_eq {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] (p : ℕ) [Fact p.Prime]
    (hp : (p : A) ∈ J) (φ ψ : ℤ_[p] →+* A) (u : ℤ_[p]) : φ u = ψ u := by
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_pow (J := J) fun n => ?_
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n u)
  have hu : u = ((u.appr n : ℕ) : ℤ_[p]) + v * (p : ℤ_[p]) ^ n := by linear_combination -hv
  have e : φ u - ψ u = (φ v - ψ v) * (p : A) ^ n := by
    rw [hu]; simp only [map_add (f := _), map_mul, map_pow, map_natCast]; ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hp n)

end GlobalTheory.BSP.PairW

namespace GlobalTheory.BSP

open GlobalTheory.BSP.PairW

theorem hf_C_eq_of_pair : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (f g : Hom bk.prism B) (w : Wq l bk.a), BK.hf f (C w) = BK.hf g (C w) := by
  intro l _ K bk B f g w
  haveI := B.complete
  have hlJ : (l : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hI : ∀ v : Wq l bk.a, BK.hf f (C v) - BK.hf g (C v) ∈ B.I := by
    intro v
    have hr : Ideal.Quotient.mk bk.prism.I (C v : bk.prism.A) =
        bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ (C v))) :=
      (bk.str.apply_symm_apply _).symm
    rw [← Ideal.Quotient.eq]
    exact (f.f_str _ _ hr).trans (g.f_str _ _ hr).symm
  have hT : ∀ x : Fq l bk.a, BK.hf f (C (WittVector.teichmuller l x)) = BK.hf g (C (WittVector.teichmuller l x)) := by
    intro x
    have ht : (WittVector.teichmuller l x) ^ l ^ bk.a = WittVector.teichmuller l x := by
      rw [← map_pow, Fq.pow_card]
    refine eq_of_pow_eq_self (J := Ideal.span {(l : B.A)} ⊔ B.I) l hlJ (Nat.pos_of_ne_zero (NeZero.ne bk.a))
      ?_ ?_ (Ideal.mem_sup_right (hI _))
    · rw [← map_pow, ← map_pow, ht]
    · rw [← map_pow, ← map_pow, ht]
  have hZ : ∀ u : ℤ_[l], BK.hf f (C (algebraMap ℤ_[l] (Wq l bk.a) u)) = BK.hf g (C (algebraMap ℤ_[l] (Wq l bk.a) u)) :=
    fun u => padicInt_ringHom_eq (J := Ideal.span {(l : B.A)} ⊔ B.I) l hlJ
      (((BK.hf f).comp C).comp (algebraMap ℤ_[l] (Wq l bk.a)))
      (((BK.hf g).comp C).comp (algebraMap ℤ_[l] (Wq l bk.a))) u
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l bk.a → Wq l bk.a)) := by
    rw [span_teich]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact hT y
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [Algebra.smul_def]; simp only [map_mul, hx, hZ]

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPrincipalIdealRing_away_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsPrincipalIdealRing (Localization.Away (l : bk.S)) := by
  intro l _ K bk
  have h : (l : bk.S) = C ((l : ℕ) : Wq l bk.a) := (map_natCast C l).symm
  rw [h]
  exact GlobalTheory.ChartRing.isPrincipalIdealRing_away_C (WittVector.irreducible l (k := Fq l bk.a)) _

end GlobalTheory.BSP
end
