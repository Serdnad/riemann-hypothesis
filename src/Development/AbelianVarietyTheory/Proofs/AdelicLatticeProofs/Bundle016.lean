module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle001
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
import Mathlib.Analysis.Matrix.Order

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem repr_algebraMap_of_basis_eq {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (a : F) (k : β) :
    b.repr (algebraMap F A a) k = algebraMap ℚ R (ω.repr a k) := by
  have hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q) :=
    fun q => DFunLike.congr_fun (RingHom.ext_rat ((algebraMap F A).comp (algebraMap ℚ F))
      ((algebraMap R A).comp (algebraMap ℚ R))) q
  have hsum : algebraMap F A a = ∑ i, algebraMap ℚ R (ω.repr a i) • b i := by
    conv_lhs => rw [← ω.sum_repr a]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def (ω.repr a i) (ω i), map_mul, hq, hb,
      Algebra.smul_def (algebraMap ℚ R (ω.repr a i))]
  rw [hsum, b.repr_sum_self]

private theorem basis_repr_mul_of_basis_eq_algebraMap {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (u v : A)
    (k : β) : b.repr (u * v) k =
      ∑ i, ∑ j, b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
  have e : ∀ i j, b.repr ((b.repr u i • b i) * (b.repr v j • b j)) k
      = b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
    intro i j
    rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, hb i, hb j, ← map_mul,
      repr_algebraMap_of_basis_eq ω b hb]
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]

  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, e]
  exact Finset.sum_comm

theorem exists_coord_polynomial : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (τ : Type) (P : MvPolynomial τ F), ∃ Q : β → MvPolynomial (τ × β) ℚ, ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ (x : τ → A) (k : β), b.repr (MvPolynomial.aeval x P) k = MvPolynomial.aeval (fun p : τ × β => b.repr (x p.1) p.2) (Q k) := by
  intro F β _ _ _ _ ω τ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨fun k => MvPolynomial.C (ω.repr a k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, repr_algebraMap_of_basis_eq ω b hb]
  | add p q hp hq =>
    obtain ⟨Q1, h1⟩ := hp
    obtain ⟨Q2, h2⟩ := hq
    refine ⟨fun k => Q1 k + Q2 k, ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, map_add (f := _), h1 R A b hb x k, h2 R A b hb x k]
  | mul_X p n hp =>
    obtain ⟨Q1, h1⟩ := hp
    refine ⟨fun k => ∑ i, ∑ j, Q1 i * MvPolynomial.X (n, j) *
      MvPolynomial.C (ω.repr (ω i * ω j) k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_mul, MvPolynomial.aeval_X, basis_repr_mul_of_basis_eq_algebraMap ω b hb]

    simp only [map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, h1 R A b hb x]

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory
namespace UnitPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

theorem hasSum_quot {G : Type} [Group G] (T : Subgroup G) [Finite T] (f : G ⧸ T → ℝ) (s : ℝ)
    (hf : HasSum f s) : HasSum (fun g : G => f (g : G ⧸ T) / Nat.card T) s := by
  classical
  have : Fintype T := Fintype.ofFinite T
  have hT : (Nat.card T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  let e : G ≃ (G ⧸ T) × T := Subgroup.groupEquivQuotientProdSubgroup
  have he : ∀ g : G, (e g).1 = (g : G ⧸ T) := fun g => rfl
  have hp : ∀ p : (G ⧸ T) × T, ((e.symm p : G) : G ⧸ T) = p.1 := fun p => by
    rw [← he, e.apply_symm_apply]
  have hfun : (fun g : G => f (g : G ⧸ T) / Nat.card T) ∘ e.symm =
      fun p : (G ⧸ T) × T => f p.1 * (Nat.card T : ℝ)⁻¹ := by
    funext p
    simp only [Function.comp_apply, hp p, div_eq_mul_inv]
  have hg : HasSum (fun _ : T => (Nat.card T : ℝ)⁻¹) 1 := by
    have h0 := hasSum_fintype (fun _ : T => (Nat.card T : ℝ)⁻¹)
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      mul_inv_cancel₀ hT] at h0
  have hprod : HasSum (fun p : (G ⧸ T) × T => f p.1 * (Nat.card T : ℝ)⁻¹) s := by
    have hs1 : Summable fun q : G ⧸ T => ‖f q‖ := by
      simpa only [Real.norm_eq_abs] using hf.summable.abs
    have hs2 : Summable fun _ : T => ‖(Nat.card T : ℝ)⁻¹‖ := Summable.of_finite
    have hs : Summable fun p : (G ⧸ T) × T => f p.1 * (fun _ : T => (Nat.card T : ℝ)⁻¹) p.2 :=
      summable_mul_of_summable_norm (R := ℝ) (f := f) (g := fun _ : T => (Nat.card T : ℝ)⁻¹) hs1 hs2
    have h0 := HasSum.mul (f := f) (g := fun _ : T => (Nat.card T : ℝ)⁻¹) hf hg hs
    rwa [mul_one] at h0
  rw [← e.symm.hasSum_iff, hfun]
  exact hprod

variable {K : Type} [Field K] [NumberField K]

theorem contDiffAt_normAtPlace (w : InfinitePlace K) (x : mixedSpace K)
    (hx : normAtPlace w x ≠ 0) : ContDiffAt ℝ ∞ (fun y : mixedSpace K => normAtPlace w y) x := by
  rcases w.isReal_or_isComplex with hw | hw
  · have e : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.1 ⟨w, hw⟩‖ :=
      funext fun y => normAtPlace_apply_of_isReal hw y
    rw [normAtPlace_apply_of_isReal hw] at hx
    rw [e]
    exact ContDiffAt.norm ℝ (by fun_prop) (norm_ne_zero_iff.1 hx)
  · have e : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.2 ⟨w, hw⟩‖ :=
      funext fun y => normAtPlace_apply_of_isComplex hw y
    rw [normAtPlace_apply_of_isComplex hw] at hx
    rw [e]
    exact ContDiffAt.norm ℝ (by fun_prop) (norm_ne_zero_iff.1 hx)

theorem contDiffAt_logMap (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    ContDiffAt ℝ ∞ (logMap (K := K)) x := by
  have hN : ∀ w, normAtPlace w x ≠ 0 := mixedEmbedding.norm_ne_zero_iff.1 hx
  have hnorm : ContDiffAt ℝ ∞ (fun y : mixedSpace K => mixedEmbedding.norm y) x := by
    have e : (fun y : mixedSpace K => mixedEmbedding.norm y) =
        fun y => ∏ w, normAtPlace w y ^ mult w := funext fun y => mixedEmbedding.norm_apply y
    rw [e]
    exact contDiffAt_prod fun w _ => (contDiffAt_normAtPlace w x (hN w)).pow _
  refine contDiffAt_pi.2 fun w => ?_
  simp only [logMap_apply]
  exact contDiffAt_const.mul (((contDiffAt_normAtPlace w.1 x (hN w.1)).log (hN w.1)).sub
    ((hnorm.log hx).mul contDiffAt_const))

private lemma le_of_mul_le_of_one_le' {m t B : ℝ} (hm : 1 ≤ m) (hB : 0 ≤ B) (h : m * t ≤ B) :
    t ≤ B := by
  rcases le_or_gt t 0 with ht | ht
  · exact ht.trans hB
  · nlinarith

theorem log_le (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) (w : InfinitePlace K) :
    Real.log (normAtPlace w x) ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ +
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹ := by
  classical
  have hN : ∀ w, normAtPlace w x ≠ 0 := mixedEmbedding.norm_ne_zero_iff.1 hx
  have hd0 : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
  have hL : Real.log (mixedEmbedding.norm x) =
      ∑ v, (mult v : ℝ) * Real.log (normAtPlace v x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod (fun v _ => pow_ne_zero _ (hN v))]
    simp only [Real.log_pow]
  have hm : ∑ v : InfinitePlace K, (mult v : ℝ) = Module.finrank ℚ K := by
    rw [← sum_mult_eq, Nat.cast_sum]
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_pos
  have hpos : 0 ≤ ‖logMap x‖ := norm_nonneg _
  have hB : 0 ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ := by positivity
  have hle : ‖logMap x‖ ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ :=
    le_mul_of_one_le_left hpos hcard
  rw [← sub_le_iff_le_add]
  by_cases hw : w = w₀
  · subst hw
    set L := Real.log (mixedEmbedding.norm x)
    set d : ℝ := (Module.finrank ℚ K : ℝ)
    have h1 := Fintype.sum_eq_add_sum_subtype_ne
      (fun v => (mult v : ℝ) * Real.log (normAtPlace v x)) w₀
    have h2 := Fintype.sum_eq_add_sum_subtype_ne (fun v : InfinitePlace K => (mult v : ℝ)) w₀
    rw [← hL] at h1
    rw [hm] at h2
    have hS : ∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v =
        ∑ v : {v : InfinitePlace K // v ≠ w₀}, (mult v.1 : ℝ) * Real.log (normAtPlace v.1 x) -
          (∑ v : {v : InfinitePlace K // v ≠ w₀}, (mult v.1 : ℝ)) * (L * d⁻¹) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [logMap_apply]
      ring
    have hdd : d * d⁻¹ = 1 := mul_inv_cancel₀ hd0.ne'
    have hkey : (mult (w₀ : InfinitePlace K) : ℝ) * (Real.log (normAtPlace w₀ x) - L * d⁻¹) =
        -∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v := by
      rw [hS]
      linear_combination (-1 : ℝ) * h1 + (L * d⁻¹) * h2 - L * hdd
    have hSle : -∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v ≤
        Fintype.card (InfinitePlace K) * ‖logMap x‖ := by
      refine (neg_le_abs _).trans ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
      refine (Finset.sum_le_sum fun v _ => (show |logMap x v| ≤ ‖logMap x‖ from
        (Real.norm_eq_abs (logMap x v)).symm.trans_le (norm_le_pi_norm (logMap x) v))).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Fintype.card_subtype_le _) hpos
    exact le_of_mul_le_of_one_le' one_le_mult hB (hkey.trans_le hSle)
  · have hv : logMap x ⟨w, hw⟩ = (mult w : ℝ) * (Real.log (normAtPlace w x) -
        Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹) := logMap_apply x ⟨w, hw⟩
    refine le_of_mul_le_of_one_le' (one_le_mult (w := w)) hB ?_
    rw [← hv]
    exact (le_abs_self _).trans (((Real.norm_eq_abs _).symm.trans_le
      (norm_le_pi_norm (logMap x) ⟨w, hw⟩)).trans hle)

end UnitPartition


open UnitPartition NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem exists_smooth_homogeneous_hasSum_unit_smul : ∀ (K : Type) [Field K] [NumberField K], ∃ h : mixedSpace K → ℝ, ContDiffOn ℝ ∞ h {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ (t : ℝ) x, 0 < t → h (t • x) = h x) ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → HasSum (fun u : (𝓞 K)ˣ => h (u • x)) 1) ∧ (∀ a b : ℝ, 0 < a → ∃ C : Set (mixedSpace K), IsCompact C ∧ (∀ x ∈ C, mixedEmbedding.norm x ≠ 0) ∧ ∀ x, h x ≠ 0 → a ≤ mixedEmbedding.norm x → mixedEmbedding.norm x ≤ b → x ∈ C) := by
  intro K _ _
  obtain ⟨η, hη, hηc, hηs⟩ := exists_smooth_compactSupport_hasSum_lattice_translates
    ({w : InfinitePlace K // w ≠ w₀} → ℝ) (unitLattice K)
  refine ⟨fun x => if mixedEmbedding.norm x = 0 then 0 else
    η (logMap x) / (Nat.card (torsion K) : ℝ), ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : mixedEmbedding.norm x ≠ 0 := hx
    have hopen : IsOpen {y : mixedSpace K | mixedEmbedding.norm y ≠ 0} :=
      isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
    refine ContDiffAt.contDiffWithinAt ?_
    have hev : (fun y : mixedSpace K => if mixedEmbedding.norm y = 0 then 0 else
        η (logMap y) / (Nat.card (torsion K) : ℝ)) =ᶠ[nhds x]
        fun y => η (logMap y) / (Nat.card (torsion K) : ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      rw [if_neg hy]
    exact ((hη.contDiffAt.comp x (contDiffAt_logMap x hx')).div_const _).congr_of_eventuallyEq hev
  · intro t x ht
    have ht0 : t ≠ 0 := ht.ne'
    simp only [mixedEmbedding.norm_smul]
    by_cases hx : mixedEmbedding.norm x = 0
    · simp [hx]
    · have hne : |t| ^ Module.finrank ℚ K * mixedEmbedding.norm x ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (abs_ne_zero.2 ht0)) hx
      rw [if_neg hne, if_neg hx, logMap_real_smul hx ht0]
  · intro x hx
    let e : ((𝓞 K)ˣ ⧸ torsion K) ≃ unitLattice K :=
      Additive.ofMul.trans (logEmbeddingEquiv K).toEquiv
    have hq : HasSum ((fun l : unitLattice K => η (logMap x + l)) ∘ e) 1 :=
      e.hasSum_iff.2 (hηs (logMap x))
    have hu := hasSum_quot (torsion K) _ 1 hq
    convert hu using 2 with u
    have hux : mixedEmbedding.norm (u • x) ≠ 0 := by rwa [norm_unit_smul]
    dsimp only
    rw [if_neg hux, logMap_unit_smul u hx, add_comm]
    simp only [Function.comp_apply, e, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
      logEmbeddingEquiv_apply]
  · intro a b ha
    obtain ⟨R, hR⟩ := hηc.isCompact.isBounded.exists_norm_le
    refine ⟨Metric.closedBall 0 (Real.exp (Fintype.card (InfinitePlace K) * R +
        Real.log b * (Module.finrank ℚ K : ℝ)⁻¹)) ∩ {x | a ≤ mixedEmbedding.norm x},
      (isCompact_closedBall _ _).inter_right
        (isClosed_le continuous_const (mixedEmbedding.continuous_norm K)),
      fun x hx => (ha.trans_le hx.2).ne', fun x hx hax hxb => ⟨?_, hax⟩⟩
    have hx0 : mixedEmbedding.norm x ≠ 0 := (ha.trans_le hax).ne'
    dsimp only at hx
    rw [if_neg hx0] at hx
    have hηx : η (logMap x) ≠ 0 := fun h0 => hx (by rw [h0, zero_div])
    have hlog : ‖logMap x‖ ≤ R := hR _ (subset_tsupport _ hηx)
    rw [mem_closedBall_zero_iff, norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ => ?_
    have hNw : 0 < normAtPlace w x :=
      lt_of_le_of_ne (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.1 hx0 w).symm
    rw [← Real.exp_log hNw]
    refine Real.exp_le_exp.2 ((log_le x hx0 w).trans (add_le_add
      (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)) ?_))
    exact mul_le_mul_of_nonneg_right (Real.log_le_log (ha.trans_le hax) hxb) (by positivity)

end GlobalTheory
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem gramLB_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    ∃ U : Matrix n n ℝ, U * Uᴴ = 1 ∧
      A + t • (1 : Matrix n n ℝ) = U * diagonal (fun i => hA.eigenvalues i + t) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℝ), Unitary.coe_mul_star_self _, ?_⟩
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ) * star (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self _
  have hD : diagonal (fun i => hA.eigenvalues i + t) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) + t • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, ← star_eq_conjTranspose, hU]

theorem gramLB_one_le_det {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℝ}
    (hR : R.PosSemidef) : 1 ≤ (R + 1).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hR.1 1
  rw [one_smul] at hEq
  have hdet : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
  rw [hEq, det_mul, det_mul, det_diagonal]
  have e : U.det * (∏ i, (hR.1.eigenvalues i + 1)) * Uᴴ.det = ∏ i, (hR.1.eigenvalues i + 1) := by
    linear_combination (∏ i, (hR.1.eigenvalues i + 1)) * hdet
  rw [e]
  calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
    _ ≤ ∏ i, (hR.1.eigenvalues i + 1) :=
      Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => by linarith [hR.eigenvalues_nonneg i]

theorem gramLB_exists_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosDef) : ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ (A - k • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with hn | hn
    · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min hA.1.eigenvalues
      exact ⟨_, hA.eigenvalues_pos i0, hi0⟩
  refine ⟨min 1 m, lt_min one_pos hm0, min_le_left _ _, ?_⟩
  obtain ⟨U, -, hEq⟩ := gramLB_shift hA.1 (-(min 1 m))
  rw [sub_eq_add_neg, ← neg_smul, hEq]
  exact (posSemidef_diagonal_iff.2 fun i => by linarith [hm i, min_le_right 1 m]).mul_mul_conjTranspose_same U

open scoped MatrixOrder in
theorem gramLB_det_mono {n : Type} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℝ}
    (hP : P.PosDef) (hQ : Q.PosSemidef) : P.det ≤ (P + Q).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hP.1 0
  simp only [zero_smul, add_zero] at hEq
  have hd : ∀ i, 0 < hP.1.eigenvalues i := hP.eigenvalues_pos
  have hUU : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  let s : n → ℝ := fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹
  let B : Matrix n n ℝ := U * diagonal s
  have hBt : Bᴴ = diagonal s * Uᴴ := by
    simp [B]
  have hBPB : Bᴴ * P * B = 1 := by
    rw [hBt, hEq]
    simp only [B, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
      diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hs : Real.sqrt (hP.1.eigenvalues i) * Real.sqrt (hP.1.eigenvalues i) = hP.1.eigenvalues i :=
      Real.mul_self_sqrt (hd i).le
    have hs0 : Real.sqrt (hP.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s]
    field_simp
    try nlinarith [hs, Real.sq_sqrt (hd i).le]
  have hsum : Bᴴ * (P + Q) * B = 1 + Bᴴ * Q * B := by
    rw [Matrix.mul_add, Matrix.add_mul, hBPB]
  have h1 : Bᴴ.det * B.det * P.det = 1 := by
    have e := congrArg det hBPB
    rw [det_mul, det_mul, det_one] at e
    linear_combination e
  have h2 : Bᴴ.det * B.det * (P + Q).det = (1 + Bᴴ * Q * B).det := by
    rw [← hsum, det_mul (Bᴴ * (P + Q)) B, det_mul Bᴴ (P + Q)]
    ring
  have h3 : 1 ≤ (1 + Bᴴ * Q * B).det := by
    rw [add_comm]
    exact gramLB_one_le_det (hQ.conjTranspose_mul_mul_same B)
  have hc : 0 < Bᴴ.det * B.det := by
    have := hP.det_pos
    by_contra hneg
    nlinarith [not_lt.mp hneg]
  exact le_of_mul_le_mul_left (by linarith) hc

theorem gramLB_posDef {n : Type} [Fintype n] [DecidableEq n] {g : Matrix n n ℝ}
    (hg : g.det ≠ 0) : (gᵀ * g).PosDef := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact PosDef.conjTranspose_mul_self g
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (Ne.isUnit hg)))

theorem gram_leading_minor_lower_bound :
    ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ γ : Matrix (Fin N) (Fin N) ℤ, γ.det ≠ 0 → ∀ (j : ℕ) (h : j ≤ N), c ≤ (((g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ))).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  intro N g hg
  obtain ⟨k, hk0, hk1, hkQ⟩ := gramLB_exists_shift (gramLB_posDef hg)
  refine ⟨k ^ N, pow_pos hk0 N, fun γ hγ j hj => ?_⟩
  set Γ : Matrix (Fin N) (Fin N) ℝ := γ.map (Int.cast : ℤ → ℝ) with hΓ
  set E : Fin j → Fin N := Fin.castLE hj with hE
  let C : Matrix (Fin N) (Fin j) ℝ := Γ.submatrix id E
  let Cz : Matrix (Fin N) (Fin j) ℤ := γ.submatrix id E
  have hGram : ((g * Γ)ᵀ * (g * Γ)).submatrix E E = Cᵀ * (gᵀ * g) * C := by
    have e1 : (g * Γ)ᵀ * (g * Γ) = Γᵀ * (gᵀ * g) * Γ := by
      rw [transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.submatrix_mul _ _ E id E Function.bijective_id,
      Matrix.submatrix_mul _ _ E id id Function.bijective_id, submatrix_id_id, transpose_submatrix]
  have hsplit : Cᵀ * (gᵀ * g) * C = k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    abel
  have hΓdet : Γ.det ≠ 0 := by
    have e := (Int.castRingHom ℝ).map_det γ
    rw [show Γ = (Int.castRingHom ℝ).mapMatrix γ from rfl, ← e]
    simpa using hγ
  have hCinj : Function.Injective C.mulVec := by
    have hC : C = Γ * (1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E := by
      rw [← Matrix.submatrix_id_id Γ, ← Matrix.submatrix_mul _ _ id id E Function.bijective_id,
        Matrix.mul_one]
    have hI : Function.Injective ((1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E).mulVec := by
      intro x y hxy
      funext a
      have hEinj : Function.Injective E := Fin.castLE_injective hj
      have e := congrFun hxy (E a)
      simpa [mulVec, dotProduct, Matrix.one_apply, hEinj.eq_iff] using e
    rw [hC]
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact hI (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det Γ).2 (Ne.isUnit hΓdet)) hxy)
  have hCC : (Cᵀ * C).PosDef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact PosDef.conjTranspose_mul_self C hCinj
  have hQ' : (Cᵀ * (gᵀ * g - k • 1) * C).PosSemidef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hkQ.conjTranspose_mul_mul_same C
  have hCz : Cᵀ * C = (Int.castRingHom ℝ).mapMatrix (Czᵀ * Cz) := by
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
    rfl
  have hdet1 : 1 ≤ (Cᵀ * C).det := by
    have hpos := hCC.det_pos
    rw [hCz, ← RingHom.map_det, eq_intCast] at hpos
    rw [hCz, ← RingHom.map_det, eq_intCast]
    have hz : 0 < (Czᵀ * Cz).det := by exact_mod_cast hpos
    have hz1 : (1 : ℤ) ≤ (Czᵀ * Cz).det := hz
    exact_mod_cast hz1
  calc k ^ N ≤ k ^ j := pow_le_pow_of_le_one hk0.le hk1 hj
    _ ≤ k ^ j * (Cᵀ * C).det := le_mul_of_one_le_right (pow_nonneg hk0.le _) hdet1
    _ = (k • (Cᵀ * C)).det := by rw [det_smul, Fintype.card_fin]
    _ ≤ (k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C).det := gramLB_det_mono (hCC.smul hk0) hQ'
    _ = _ := by rw [← hsplit, ← hGram]

end GlobalTheory.ClassFin
end
