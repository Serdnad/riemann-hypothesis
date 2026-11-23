module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RationalLowerBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Group.Completion

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen

open Finset

section Supp

variable {R σ Pl : Type} [CommRing R]

def SuppOn (π : σ → Pl) (v : Pl) : Subring (MvPowerSeries σ R) where
  carrier := {f | ∀ m, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, π x = v}
  mul_mem' := by
    classical
    intro f g hf hg m hm x hx
    rw [MvPowerSeries.coeff_mul] at hm
    obtain ⟨ab, hab, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [← hab] at hx
    rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
    · exact hf _ (left_ne_zero_of_mul hne) x h
    · exact hg _ (right_ne_zero_of_mul hne) x h
  one_mem' := by
    classical
    intro m hm x hx
    rw [MvPowerSeries.coeff_one] at hm
    split_ifs at hm with h
    · subst h; simp at hx
    · exact absurd rfl hm
  add_mem' := by
    intro f g hf hg m hm x hx
    rw [map_add (f := _)] at hm
    by_cases h : MvPowerSeries.coeff m f = 0
    · rw [h, zero_add] at hm; exact hg m hm x hx
    · exact hf m h x hx
  zero_mem' := by
    intro m hm
    exact absurd (map_zero _) hm
  neg_mem' := by
    intro f hf m hm x hx
    rw [map_neg, neg_ne_zero] at hm
    exact hf m hm x hx

theorem mem_SuppOn {π : σ → Pl} {v : Pl} {f : MvPowerSeries σ R} :
    f ∈ SuppOn π v ↔ ∀ m, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, π x = v := Iff.rfl

theorem X_mem {π : σ → Pl} {v : Pl} {x : σ} (h : π x = v) : (MvPowerSeries.X x : MvPowerSeries σ R) ∈ SuppOn π v := by
  classical
  intro m hm y hy
  rw [MvPowerSeries.coeff_X] at hm
  split_ifs at hm with hmx
  · subst hmx
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hy
    rw [hy]
    exact h
  · exact absurd rfl hm

theorem C_mem {π : σ → Pl} {v : Pl} (c : R) : (MvPowerSeries.C c : MvPowerSeries σ R) ∈ SuppOn π v := by
  classical
  intro m hm y hy
  rw [MvPowerSeries.coeff_C] at hm
  split_ifs at hm with h0
  · subst h0
    simp at hy
  · exact absurd rfl hm

theorem subst_mem {τ : Type} {π : σ → Pl} {π' : τ → Pl} {v : Pl} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) {f : MvPowerSeries σ R} (hf : f ∈ SuppOn π v)
    (h : ∀ s, π s = v → a s ∈ SuppOn π' v) : MvPowerSeries.subst a f ∈ SuppOn π' v := by
  classical
  intro e he x hx
  rw [MvPowerSeries.coeff_subst ha] at he
  by_contra hxv
  apply he
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : MvPowerSeries.coeff d f = 0
  · rw [hd, zero_smul]
  · have hprod : (d.prod fun s n => a s ^ n) ∈ SuppOn π' v := by
      unfold Finsupp.prod
      exact Subring.prod_mem _ fun s hs => Subring.pow_mem _ (h s ((mem_SuppOn.mp hf) d hd s hs)) _
    have h0 : MvPowerSeries.coeff e (d.prod fun s n => a s ^ n) = 0 := by
      by_contra hne
      exact hxv ((mem_SuppOn.mp hprod) e hne x hx)
    rw [h0, smul_zero]

theorem map_mem {R' : Type} [CommRing R'] (φ : R →+* R') {π : σ → Pl} {v : Pl} {f : MvPowerSeries σ R}
    (hf : f ∈ SuppOn π v) : MvPowerSeries.map φ f ∈ SuppOn π v := by
  intro m hm x hx
  rw [MvPowerSeries.coeff_map] at hm
  exact (mem_SuppOn.mp hf) m (fun h0 => hm (by rw [h0, map_zero])) x hx

end Supp

def resP {R Pl : Type} [CommRing R] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (Σ v, ι v) R) : MvPowerSeries (ι v) R :=
  fun m => MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) f

theorem coeff_resP {R Pl : Type} [CommRing R] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (Σ v, ι v) R) (m : ι v →₀ ℕ) :
    MvPowerSeries.coeff m (resP v f) = MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) f := rfl

theorem eq_atP {R Pl : Type} [CommRing R] {ι : Pl → Type} [Fintype Pl] [DecidableEq Pl] (v : Pl)
    (f : MvPowerSeries (Σ v, ι v) R) (hf : f ∈ SuppOn (Sigma.fst : (Σ v, ι v) → Pl) v) :
    f = atP v (resP v f) := by
  classical
  ext n
  have h2 : ∀ m : ι v →₀ ℕ, (eqv (ι := ι)).symm (Pi.single v m) =
      Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
    intro m
    rw [AddEquiv.symm_apply_eq, eqv_embDomain]
  by_cases hn : MvPowerSeries.coeff n f = 0
  · rw [hn]
    by_cases h : ∃ m, n = eqv.symm (Pi.single v m)
    · obtain ⟨m, rfl⟩ := h
      rw [coeff_atP_single, coeff_resP, ← h2]
      exact hn.symm
    · push_neg at h
      exact (coeff_atP_eq_zero v _ n h).symm
  · have hsupp := (mem_SuppOn.mp hf) n hn
    have hn' : n = eqv.symm (Pi.single v (eqv n v)) := by
      rw [AddEquiv.eq_symm_apply]
      funext w
      ext i
      by_cases hw : w = v
      · subst hw
        rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hw, Finsupp.coe_zero, Pi.zero_apply,
          Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]
        by_contra hne
        exact hw (hsupp ⟨w, i⟩ (Finsupp.mem_support_iff.mpr hne))
    calc MvPowerSeries.coeff n f
        = MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) (eqv n v)) f := by
          rw [← h2, ← hn']
      _ = MvPowerSeries.coeff n (atP v (resP v f)) := by
          rw [← coeff_resP, ← coeff_atP_single v (resP v f) (eqv n v), ← hn']

theorem jp_subst_expand {K A σ τ : Type} [CommRing K] [CommRing A] [Algebra K A] (Q : MvPolynomial σ A)
    (F : MvPowerSeries σ K) (a : τ → MvPowerSeries σ K) (ha : MvPowerSeries.HasSubst a) (U : MvPowerSeries τ K) :
    ∃ B : Finset (τ →₀ ℕ), jp Q (F * MvPowerSeries.subst a U) =
      ∑ β ∈ B, MvPowerSeries.coeff β U • jp Q (F * β.prod fun s e => a s ^ e) := by
  classical
  refine ⟨Q.support.biUnion fun κ => (Finset.HasAntidiagonal.antidiagonal κ).biUnion fun pq =>
    (MvPowerSeries.coeff_subst_finite ha U pq.2).toFinset, ?_⟩
  set B := Q.support.biUnion fun κ => (Finset.HasAntidiagonal.antidiagonal κ).biUnion fun pq =>
    (MvPowerSeries.coeff_subst_finite ha U pq.2).toFinset with hB
  have hq : ∀ κ ∈ Q.support, ∀ pq ∈ Finset.HasAntidiagonal.antidiagonal κ,
      MvPowerSeries.coeff pq.2 (MvPowerSeries.subst a U) =
        ∑ β ∈ B, MvPowerSeries.coeff β U * MvPowerSeries.coeff pq.2 (β.prod fun s e => a s ^ e) := by
    intro κ hκ pq hpq
    rw [MvPowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset (s := B)]
    · simp only [smul_eq_mul]
    · intro β hβ
      rw [Finset.mem_coe, hB, Finset.mem_biUnion]
      exact ⟨κ, hκ, Finset.mem_biUnion.mpr ⟨pq, hpq,
        (MvPowerSeries.coeff_subst_finite ha U pq.2).mem_toFinset.mpr hβ⟩⟩
  have hκ : ∀ κ ∈ Q.support, MvPowerSeries.coeff κ (F * MvPowerSeries.subst a U) =
      ∑ β ∈ B, MvPowerSeries.coeff β U * MvPowerSeries.coeff κ (F * β.prod fun s e => a s ^ e) := by
    intro κ hκ
    rw [MvPowerSeries.coeff_mul]
    simp_rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun pq hpq => ?_
    rw [hq κ hκ pq hpq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  unfold jp
  have hL : ∑ κ ∈ Q.support, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ (F * MvPowerSeries.subst a U)) •
        AddMonoidAlgebra.coeff Q κ =
      ∑ κ ∈ Q.support, ∑ β ∈ B, (((fac κ : ℕ) : K) * (MvPowerSeries.coeff β U *
        MvPowerSeries.coeff κ (F * β.prod fun s e => a s ^ e))) • AddMonoidAlgebra.coeff Q κ := by
    refine Finset.sum_congr rfl fun κ hκ' => ?_
    rw [hκ κ hκ', Finset.mul_sum, Finset.sum_smul]
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [smul_smul]
  congr 1
  ring

end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open scoped Classical

variable {K : Type*} [Field K] {R : Subring K} {p : ℕ}


variable (R p) in
def nm_N (x : K) : ℝ := if x = 0 then 0 else (p : ℝ) ^ (-nm_v R p x)

theorem nm_N_zero : nm_N R p (0 : K) = 0 := by
  simp [nm_N]

theorem nm_N_of_ne {x : K} (hx : x ≠ 0) : nm_N R p x = (p : ℝ) ^ (-nm_v R p x) := by
  simp [nm_N, hx]

theorem nm_pR (h : nm_Hyp R p) : (1 : ℝ) < p := by
  exact_mod_cast h.one_lt

theorem nm_N_nonneg (h : nm_Hyp R p) (x : K) : 0 ≤ nm_N R p x := by
  unfold nm_N
  split_ifs
  · exact le_rfl
  · exact (Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).le

theorem nm_N_mul (h : nm_Hyp R p) (x y : K) : nm_N R p (x * y) = nm_N R p x * nm_N R p y := by
  by_cases hx : x = 0
  · simp [nm_N, hx]
  by_cases hy : y = 0
  · simp [nm_N, hy]
  rw [nm_N_of_ne (mul_ne_zero hx hy), nm_N_of_ne hx, nm_N_of_ne hy, nm_v_mul h hx hy, neg_add,
    Real.rpow_add (zero_lt_one.trans (nm_pR h))]

theorem nm_N_eq_zero (h : nm_Hyp R p) (x : K) : nm_N R p x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [nm_N, hx]
  · rw [nm_N_of_ne hx]
    simp only [hx, iff_false]
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).ne'

theorem nm_N_add (h : nm_Hyp R p) (x y : K) : nm_N R p (x + y) ≤ max (nm_N R p x) (nm_N R p y) := by
  by_cases hx : x = 0
  · simp only [hx, zero_add, nm_N_zero]
    exact le_max_right _ _
  by_cases hy : y = 0
  · simp only [hy, add_zero, nm_N_zero]
    exact le_max_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, nm_N_zero]
    exact le_max_of_le_left (nm_N_nonneg h x)
  rw [nm_N_of_ne hxy, nm_N_of_ne hx, nm_N_of_ne hy]
  have hp1 : (1 : ℝ) ≤ p := (nm_pR h).le
  have hm := nm_v_add h hx hy hxy
  rcases le_total (nm_v R p x) (nm_v R p y) with hle | hle
  · rw [min_eq_left hle] at hm
    exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))
  · rw [min_eq_right hle] at hm
    exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))

theorem nm_N_p (h : nm_Hyp R p) : nm_N R p (p : K) = (p : ℝ)⁻¹ := by
  rw [nm_N_of_ne (nm_p_ne h), nm_v_p h, Real.rpow_neg_one]

theorem nm_N_le_one (h : nm_Hyp R p) (x : K) : nm_N R p x ≤ 1 ↔ x ∈ R := by
  by_cases hx : x = 0
  · subst hx
    simp only [nm_N_zero, zero_le_one, true_iff]
    exact R.zero_mem
  rw [nm_N_of_ne hx, ← nm_v_nonneg_iff h hx]
  have e : (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
  rw [e, Real.rpow_le_rpow_left_iff (nm_pR h), neg_nonpos]

def nm_abs (h : nm_Hyp R p) : AbsoluteValue K ℝ where
  toFun := nm_N R p
  map_mul' := nm_N_mul h
  nonneg' := nm_N_nonneg h
  eq_zero' := nm_N_eq_zero h
  add_le' x y := le_trans (nm_N_add h x y) (max_le_add_of_nonneg (nm_N_nonneg h x) (nm_N_nonneg h y))

theorem nm_extG {K : Type} [Field K] (N : AbsoluteValue K ℝ) (hna : ∀ x y, N (x + y) ≤ max (N x) (N y)) (c : K)
    (hc : 1 < N c) :
    ∃ (K' : Type) (_ : NormedField K') (_ : Algebra K K'), IsUltrametricDist K' ∧ IsAlgClosed K' ∧
      ∀ x, ‖algebraMap K K' x‖ = N x := by
  let nK : NormedField K := N.toNormedField
  have hnorm : ∀ x : K, ‖x‖ = N x := fun _ => rfl
  have hnatK : ∀ n : ℕ, N (n : K) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact le_trans (hna _ _) (max_le ih (by simp))
  have hcast : ∀ n : ℕ, ((n : K) : UniformSpace.Completion K) = (n : UniformSpace.Completion K) := fun n =>
    map_natCast (UniformSpace.Completion.coeRingHom (α := K)) n
  have hnatC : ∀ n : ℕ, ‖(n : UniformSpace.Completion K)‖ ≤ 1 := by
    intro n
    rw [← hcast, UniformSpace.Completion.norm_coe]
    exact hnatK n
  have uC : IsUltrametricDist (UniformSpace.Completion K) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hnatC
  let nnC : NontriviallyNormedField (UniformSpace.Completion K) :=
    { (inferInstance : NormedField (UniformSpace.Completion K)) with
      non_trivial := ⟨(c : UniformSpace.Completion K), by rw [UniformSpace.Completion.norm_coe]; exact hc⟩ }
  let nL : NormedField (AlgebraicClosure (UniformSpace.Completion K)) :=
    spectralNorm.normedField (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))
  have hext : ∀ z : UniformSpace.Completion K,
      ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K)) z‖ = ‖z‖ :=
    fun z => spectralNorm_extends z
  let aL : Algebra K (AlgebraicClosure (UniformSpace.Completion K)) :=
    ((algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))).comp
      (UniformSpace.Completion.coeRingHom (α := K))).toAlgebra
  refine ⟨AlgebraicClosure (UniformSpace.Completion K), nL, aL, ?_, inferInstance, ?_⟩
  · apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
    intro n
    have := hext (n : UniformSpace.Completion K)
    rw [map_natCast] at this
    rw [this]
    exact hnatC n
  · intro x
    show ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))
      (x : UniformSpace.Completion K)‖ = N x
    rw [hext, UniformSpace.Completion.norm_coe]
    rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
