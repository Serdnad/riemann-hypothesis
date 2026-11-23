module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteLength
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Mathlib.Topology.LocallyConstant.Basic
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem mem_span_l_pow_S_iff (n : ℕ) (f : S O K e) :
    f ∈ Ideal.span {(l : S O K e)} ^ n ↔
      ∀ m, ‖coeff m (f : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ n := by
  have h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩ m
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow,
      mul_assoc]
    exact mul_le_of_le_one_right hl.le ((mem_S.1 g.2).1 m)
  · intro h
    have hc : ∀ m, ‖coeff m (C (((l : K) ^ n)⁻¹) * (f : K⟦X⟧))‖ * wS K e m =
        (‖(l : K)‖ ^ n)⁻¹ * (‖coeff m (f : K⟦X⟧)‖ * wS K e m) := fun m => by
      rw [coeff_C_mul, norm_mul, norm_inv, norm_pow, mul_assoc]
    refine ⟨⟨C (((l : K) ^ n)⁻¹) * (f : K⟦X⟧), mem_S.2 ⟨fun m => ?_, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [hc, inv_mul_le_iff₀ hl, mul_one]
      exact h m
    · simp only [hc]
      simpa using (mem_S.1 f.2).2.const_mul (‖(l : K)‖ ^ n)⁻¹
    · rw [Subalgebra.coe_mul, Subalgebra.coe_pow, h2, ← map_pow, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ (pow_ne_zero _ (l_ne_zero l)), map_one, one_mul]

theorem smodEq_l_pow_S_iff (n : ℕ) (f g : S O K e) :
    f ≡ g [SMOD (Ideal.span {(l : S O K e)} ^ n • ⊤ : Submodule (S O K e) (S O K e))] ↔
      ∀ m, ‖coeff m (f : K⟦X⟧) - coeff m (g : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_l_pow_S_iff]
  simp

omit [IsUltrametricDist K] in
include l in
theorem wS_pos_of_padic (m : ℕ) : 0 < wS K e m :=
  norm_pos_iff.2 (natCast_ne_zero' l (Nat.factorial_ne_zero _))

theorem isHausdorff_S : IsHausdorff (Ideal.span {(l : S O K e)}) (S O K e) := by
  refine ⟨fun f hf => Subtype.ext ?_⟩
  ext m
  have h := fun n => (smodEq_l_pow_S_iff l e n f 0).1 (hf n) m
  have h0 := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
    (norm_l_lt_one (K := K) l)) h
  have h1 := nonpos_of_mul_nonpos_left h0 (wS_pos_of_padic l e m)
  simpa using h1

theorem isPrecomplete_S [CompleteSpace K] :
    IsPrecomplete (Ideal.span {(l : S O K e)}) (S O K e) := by
  refine ⟨fun f hf => ?_⟩
  have hf' : ∀ {a b : ℕ}, a ≤ b → ∀ m, ‖coeff m (f a : K⟦X⟧) - coeff m (f b : K⟦X⟧)‖ * wS K e m ≤
      ‖(l : K)‖ ^ a := fun h => (smodEq_l_pow_S_iff l e _ _ _).1 (hf h)
  have hl0 := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one (K := K) l)
  have hcau : ∀ m, CauchySeq fun n => coeff m (f n : K⟦X⟧) := fun m => by
    refine cauchySeq_of_le_tendsto_0' (fun n => ‖(l : K)‖ ^ n / wS K e m) (fun a b h => ?_)
      (by simpa using hl0.div_const (wS K e m))
    rw [dist_eq_norm, le_div_iff₀ (wS_pos_of_padic l e m)]
    exact hf' h m
  choose c hc using fun m => cauchySeq_tendsto_of_complete (hcau m)
  have hb : ∀ n m, ‖coeff m (f n : K⟦X⟧) - c m‖ * wS K e m ≤ ‖(l : K)‖ ^ n := fun n m =>
    le_of_tendsto ((tendsto_const_nhds.sub (hc m)).norm.mul_const _)
      ((eventually_ge_atTop n).mono fun b h => hf' h m)
  have hu : ∀ n m, ‖c m‖ * wS K e m ≤
      max (‖coeff m (f n : K⟦X⟧)‖ * wS K e m) (‖(l : K)‖ ^ n) := fun n m => by
    refine le_trans ?_ (max_le_max le_rfl (hb n m))
    rw [← max_mul_of_nonneg _ _ (wS_nonneg e m)]
    refine mul_le_mul_of_nonneg_right ?_ (wS_nonneg e m)
    have := IsUltrametricDist.norm_add_le_max (coeff m (f n : K⟦X⟧))
      (-(coeff m (f n : K⟦X⟧) - c m))
    rw [norm_neg] at this
    simpa using this
  have hmem : PowerSeries.mk c ∈ S O K e := by
    refine mem_S.2 ⟨fun m => ?_, ?_⟩
    · rw [coeff_mk]
      exact (hu 0 m).trans (max_le ((mem_S.1 (f 0).2).1 m) (by simp))
    · simp only [coeff_mk]
      refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun m =>
        ha.trans_le (mul_nonneg (norm_nonneg _) (wS_nonneg e m)), fun a ha => ?_⟩
      obtain ⟨n, hn⟩ := (hl0.eventually (gt_mem_nhds ha)).exists
      filter_upwards [(mem_S.1 (f n).2).2.eventually (gt_mem_nhds ha)] with m hm
      exact (hu n m).trans_lt (max_lt hm hn)
  refine ⟨⟨_, hmem⟩, fun n => (smodEq_l_pow_S_iff l e _ _ _).2 fun m => ?_⟩
  simpa using hb n m

end GlobalTheory.BK

namespace GlobalTheory.BK

theorem isAdicComplete_S (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : IsAdicComplete (Ideal.span {(l : S O K e)}) (S O K e) :=
  { toIsHausdorff := isHausdorff_S l e, toIsPrecomplete := isPrecomplete_S l e }

end GlobalTheory.BK
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.PowKill

theorem exists_pow_smul_eq_zero {R : Type} [CommRing R] {x : R}
    (hx : ∀ I : Ideal R, I.IsMaximal → x ∈ I) {M : Type} [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) : ∃ m : ℕ, ∀ q : M, (x ^ m) • q = 0 := by
  induction h with
  | of_subsingleton => exact ⟨0, fun q => Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
    refine ⟨m + 1, fun q => ?_⟩
    have h1 : x • q ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      apply e.injective
      obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective I (e (Submodule.Quotient.mk q))
      rw [map_smul, ← hr, map_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul]
      exact I.mul_mem_right r (hx I hI)
    have h2 := hm ⟨x • q, h1⟩
    rw [pow_succ, mul_smul]
    exact congrArg Subtype.val h2

section

variable {O : Type} [CommRing O] (l : ℕ) [Fact l.Prime]

theorem isUnit_l_mul_add_one (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (c : O) : IsUnit ((l : O) * c + 1) := by
  set u := algebraMap O K ((l : O) * c + 1) with hu
  have hlc : ‖(l : K) * algebraMap O K c‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (norm_algebraMap_le c))
      (norm_l_lt_one (K := K) l)
  have hu1 : ‖u‖ = 1 := by
    have : u = (l : K) * algebraMap O K c + 1 := by simp [hu]
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlc.ne)]
    rw [norm_one]; exact max_eq_right hlc.le
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  obtain ⟨b, hb⟩ := (IsUnitBall.mem_range_iff (O := O) (u⁻¹)).2 (by rw [norm_inv, hu1, inv_one])
  refine isUnit_iff_exists_inv.2 ⟨b, IsUnitBall.inj (O := O) (K := K) ?_⟩
  rw [map_mul, hb, ← hu, mul_inv_cancel₀ hu0, map_one]

theorem l_mem_maximal {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (I : Ideal (A O K)) (hI : I.IsMaximal) : (l : A O K) ∈ I := by
  have hj : (l : A O K) ∈ Ideal.jacobson (⊥ : Ideal (A O K)) := by
    rw [Ideal.mem_jacobson_bot]
    intro y
    have key : IsUnit ((equivA O K).symm ((l : A O K) * y + 1)) := by
      rw [map_add (f := _), map_mul, map_natCast, map_one, PowerSeries.isUnit_iff_constantCoeff, map_add (f := _),
        map_mul, map_natCast, map_one]
      exact isUnit_l_mul_add_one l K _
    simpa using key.map (equivA O K).toRingEquiv.toRingHom
  have hle : Ideal.jacobson (⊥ : Ideal (A O K)) ≤ I := by
    rw [Ideal.jacobson]; exact sInf_le ⟨bot_le, hI⟩
  exact hle hj

end

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (Mo : Type) [AddCommGroup Mo]
    [Module (A O K) Mo], IsFiniteLength (A O K) Mo → ∃ m : ℕ, ∀ q : Mo, ((l : A O K) ^ m) • q = 0 :=
  fun O K _ _ _ _ _ l _ _ _ _ _ h => exists_pow_smul_eq_zero (l_mem_maximal (K := K) l) h

end GlobalTheory.PowKill
end

section

noncomputable section
namespace GlobalTheory.LatticeComap
open GlobalTheory.PhiGam

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module (LaurentSeries k) V]
  [Module (PowerSeries k) V] [IsScalarTower (PowerSeries k) (LaurentSeries k) V]

theorem exists_pow_smul_mem {N : Submodule (PowerSeries k) V}
    (hN : Submodule.span (LaurentSeries k) (N : Set V) = ⊤) (x : V) :
    ∃ m : ℕ, ((PowerSeries.X : PowerSeries k) ^ m) • x ∈ N := by
  have hx : x ∈ Submodule.span (LaurentSeries k) (N : Set V) := by rw [hN]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨0, by simpa using hy⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m1, h1⟩ := hy
    obtain ⟨m2, h2⟩ := hz
    refine ⟨m1 + m2, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact N.smul_mem _ h1
    · rw [pow_add, mul_smul]; exact N.smul_mem _ h2
  | smul a y _ hy =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨⟨p, s⟩, hps⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : PowerSeries k)) a
    obtain ⟨j, hj⟩ := s.2
    have hj' : (PowerSeries.X : PowerSeries k) ^ j = (s : PowerSeries k) := hj
    have hps' : a * algebraMap (PowerSeries k) (LaurentSeries k) (s : PowerSeries k) =
        algebraMap (PowerSeries k) (LaurentSeries k) p := hps
    have key : ((PowerSeries.X : PowerSeries k) ^ j) • a • y = p • y := by
      rw [← algebraMap_smul (LaurentSeries k) ((PowerSeries.X : PowerSeries k) ^ j) (a • y), smul_smul, hj',
        mul_comm, hps', algebraMap_smul]
    refine ⟨m + j, ?_⟩
    rw [pow_add, mul_smul, key, smul_comm]
    exact N.smul_mem _ hm

variable {W : Type} [AddCommGroup W] [Module (LaurentSeries k) W]
  [Module (PowerSeries k) W] [IsScalarTower (PowerSeries k) (LaurentSeries k) W]

theorem isLat_comap (f : W →ₗ[LaurentSeries k] V) (hf : Function.Injective f)
    {N : Submodule (PowerSeries k) V} (hN : IsLat N) :
    IsLat (N.comap (f.restrictScalars (PowerSeries k))) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (f.restrictScalars (PowerSeries k)) hf ?_
    haveI : IsNoetherian (PowerSeries k) N := isNoetherian_of_fg_of_noetherian N hN.1
    exact isNoetherian_submodule.1 this _ (Submodule.map_comap_le _ _)
  · refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨m, hm⟩ := exists_pow_smul_mem hN.2 (f w)
    have hmem : ((PowerSeries.X : PowerSeries k) ^ m) • w ∈ N.comap (f.restrictScalars (PowerSeries k)) := by
      rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.map_smul_of_tower]
      exact hm
    have hne : algebraMap (PowerSeries k) (LaurentSeries k) ((PowerSeries.X : PowerSeries k) ^ m) ≠ 0 := by
      rw [map_pow]
      refine pow_ne_zero _ ?_
      intro h
      have hX : (PowerSeries.X : PowerSeries k) ≠ 0 := PowerSeries.X_ne_zero
      exact hX (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k) (by rw [map_zero]; exact h))
    rw [← Submodule.smul_mem_iff _ hne, algebraMap_smul]
    exact Submodule.subset_span hmem

end

theorem main : ∀ {k : Type} [inst : Field k] {V : Type} [inst_1 : AddCommGroup V]
    [inst_2 : Module (LaurentSeries k) V] [inst_3 : Module (PowerSeries k) V]
    [inst_4 : IsScalarTower (PowerSeries k) (LaurentSeries k) V] {W : Type} [inst_5 : AddCommGroup W]
    [inst_6 : Module (LaurentSeries k) W] [inst_7 : Module (PowerSeries k) W]
    [inst_8 : IsScalarTower (PowerSeries k) (LaurentSeries k) W] (f : LinearMap (RingHom.id (LaurentSeries k)) W V),
    Function.Injective (DFunLike.coe f) → ∀ {N : Submodule (PowerSeries k) V}, GlobalTheory.PhiGam.IsLat N →
      GlobalTheory.PhiGam.IsLat (Submodule.comap (LinearMap.restrictScalars (PowerSeries k) f) N) :=
  fun f hf _ hN => isLat_comap f hf hN

end GlobalTheory.LatticeComap
end
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
noncomputable section
namespace GlobalTheory.PhiGam.GmultAdd

variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

def quotEquiv (A B S : Submodule k U) (hSB : S ≤ B) :
    (↥A ⧸ B.submoduleOf A) ≃ₗ[k] (↥(A.map S.mkQ) ⧸ (B.map S.mkQ).submoduleOf (A.map S.mkQ)) :=
  (Submodule.quotEquivOfEq _ _ (by
      ext a
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      change (a : U) ∈ B ↔ S.mkQ a ∈ B.map S.mkQ
      have h : (B.map S.mkQ).comap S.mkQ = B := by
        rw [Submodule.comap_map_mkQ]; exact sup_eq_right.2 hSB
      constructor
      · intro ha
        exact Submodule.mem_map_of_mem (f := S.mkQ) ha
      · intro ha
        rw [← h]
        exact ha)).trans
    (LinearMap.quotKerEquivOfSurjective
      (((B.map S.mkQ).submoduleOf (A.map S.mkQ)).mkQ ∘ₗ (S.mkQ.submoduleMap A))
      ((Submodule.mkQ_surjective _).comp (LinearMap.submoduleMap_surjective _ _)))

theorem map_self (S : Submodule k U) : S.map S.mkQ = ⊥ := by
  simp

theorem fin_map (A S : Submodule k U) (h : FiniteDimensional k (↥A ⧸ S.submoduleOf A)) :
    FiniteDimensional k (A.map S.mkQ) := by
  have e := quotEquiv A S S le_rfl
  have h2 : (S.map S.mkQ).submoduleOf (A.map S.mkQ) = ⊥ := by
    rw [map_self]; simp [Submodule.submoduleOf]
  have e2 := e.trans (Submodule.quotEquivOfEqBot _ h2)
  exact e2.finiteDimensional

theorem finrank_quot (A B S : Submodule k U) (hSB : S ≤ B) (hBA : B ≤ A)
    [FiniteDimensional k (A.map S.mkQ)] :
    Module.finrank k (↥A ⧸ B.submoduleOf A) + Module.finrank k (B.map S.mkQ)
      = Module.finrank k (A.map S.mkQ) := by
  rw [(quotEquiv A B S hSB).finrank_eq,
    ← Submodule.finrank_quotient_add_finrank ((B.map S.mkQ).submoduleOf (A.map S.mkQ)),
    (Submodule.submoduleOfEquivOfLe (Submodule.map_mono hBA)).finrank_eq]

theorem map_inf_mkQ (A B S : Submodule k U) (hA : S ≤ A) :
    (A ⊓ B).map S.mkQ = A.map S.mkQ ⊓ B.map S.mkQ := by
  apply le_antisymm (Submodule.map_inf_le _)
  rintro y ⟨⟨a, ha, rfl⟩, b, hb, hab⟩
  refine ⟨b, ⟨?_, hb⟩, hab⟩
  have : b - a ∈ S := by
    simpa [Submodule.Quotient.eq] using hab
  simpa using A.add_mem (hA this) ha

theorem pow_mem (N : Module.End k U) (Q : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q) (m : ℕ) :
    ∀ y ∈ Q, (N ^ m) y ∈ Q := by
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact hQ _ (ih y hy)

theorem mem_gen (N : Module.End k U) (Q : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q) (y : U) :
    y ∈ (⨆ m : ℕ, Q.comap (N ^ m)) ↔ ∃ m : ℕ, (N ^ m) y ∈ Q := by
  have hmono : Monotone (fun m : ℕ => Q.comap (N ^ m)) := by
    apply monotone_nat_of_le_succ
    intro m z hz
    simp only [Submodule.mem_comap] at hz ⊢
    rw [pow_succ', Module.End.mul_apply]; exact hQ _ hz
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  rfl

theorem stab (N : Module.End k U) (Q S : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q)
    [FiniteDimensional k (Q.map S.mkQ)] :
    ∃ M : ℕ, ∀ m : ℕ, (Q.map (N ^ M)).map S.mkQ ≤ (Q.map (N ^ (M + m))).map S.mkQ := by
  have hle : ∀ j : ℕ, (Q.map (N ^ j)).map S.mkQ ≤ Q.map S.mkQ := fun j =>
    Submodule.map_mono (by rintro _ ⟨y, hy, rfl⟩; exact pow_mem N Q hQ j y hy)
  have hfin : ∀ j : ℕ, FiniteDimensional k ((Q.map (N ^ j)).map S.mkQ) := fun j =>
    Submodule.finiteDimensional_of_le (hle j)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ j : ℕ, Module.finrank k ((Q.map (N ^ M)).map S.mkQ)
      ≤ Module.finrank k ((Q.map (N ^ j)).map S.mkQ) :=
    ⟨Function.argmin (fun j : ℕ => Module.finrank k ((Q.map (N ^ j)).map S.mkQ)),
      fun j => Function.argmin_le (fun j : ℕ => Module.finrank k ((Q.map (N ^ j)).map S.mkQ)) j⟩
  refine ⟨M, fun m => ?_⟩
  have h1 : (Q.map (N ^ (M + m))).map S.mkQ ≤ (Q.map (N ^ M)).map S.mkQ := by
    apply Submodule.map_mono
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(N ^ m) y, pow_mem N Q hQ m y hy, by rw [pow_add, Module.End.mul_apply]⟩
  haveI := hfin M
  exact (Submodule.eq_of_le_of_finrank_le h1 (hM _)).ge

theorem gen_sup (N : Module.End k U) (P Q S : Submodule k U) (hSQ : S ≤ Q) (hQP : Q ≤ P)
    (hQ : ∀ y ∈ Q, N y ∈ Q) (hS : ∀ y ∈ S, N y ∈ S) [FiniteDimensional k (Q.map S.mkQ)] :
    P ⊓ (⨆ m : ℕ, Q.comap (N ^ m)) = (P ⊓ ⨆ m : ℕ, S.comap (N ^ m)) ⊔ Q := by
  apply le_antisymm
  · rintro u ⟨huP, hu⟩
    obtain ⟨m, hm⟩ := (mem_gen N Q hQ u).1 hu
    obtain ⟨M, hM⟩ := stab N Q S hQ
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := hM m
      (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (f := N ^ M) hm))
    have h' : (N ^ M) ((N ^ m) u) - (N ^ (M + m)) q ∈ S := by
      simpa [Submodule.Quotient.eq] using h.symm
    have hu' : u = (u - q) + q := by abel
    rw [hu']
    refine Submodule.add_mem_sup ⟨P.sub_mem huP (hQP hq), (mem_gen N S hS _).2 ⟨M + m, ?_⟩⟩ hq
    rw [map_sub]
    convert h' using 2
    rw [pow_add, Module.End.mul_apply]
  · refine sup_le (inf_le_inf_left _ (iSup_mono fun m => Submodule.comap_mono hSQ)) (le_inf hQP ?_)
    intro y hy
    exact (mem_gen N Q hQ y).2 ⟨0, by simpa using hy⟩

theorem main : ∀ {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (P Q S : Submodule k U), S ≤ Q → Q ≤ P → (∀ x ∈ P, T x ∈ P) → (∀ x ∈ Q, T x ∈ Q) → (∀ x ∈ S, T x ∈ S) → FiniteDimensional k (↥P ⧸ S.submoduleOf P) → ∀ x : k, gmult T P S x = gmult T P Q x + gmult T Q S x := by
  intro k U _ _ _ T P Q S hSQ hQP _ hQ hS hfin x
  unfold gmult
  set N := T - algebraMap k (Module.End k U) x with hN
  have hst : ∀ A : Submodule k U, (∀ y ∈ A, T y ∈ A) → ∀ y ∈ A, N y ∈ A := by
    intro A hA y hy
    have : N y = T y - x • y := by simp [hN, Module.algebraMap_end_apply]
    rw [this]
    exact A.sub_mem (hA y hy) (A.smul_mem x hy)
  haveI hP := fin_map P S hfin
  have hf : ∀ A : Submodule k U, A ≤ P → FiniteDimensional k (A.map S.mkQ) := fun A hA =>
    Submodule.finiteDimensional_of_le (Submodule.map_mono hA)
  haveI := hf Q hQP
  have hSG : S ≤ ⨆ m : ℕ, S.comap (N ^ m) := fun y hy =>
    (mem_gen N S (hst S hS) y).2 ⟨0, by simpa using hy⟩
  have h1 := gen_sup N P Q S hSQ hQP (hst Q hQ) (hst S hS)
  set G := ⨆ m : ℕ, S.comap (N ^ m) with hG
  have h2 : Q ⊓ G = (P ⊓ G) ⊓ Q := by
    rw [inf_right_comm, inf_eq_right.2 hQP]
  rw [h1, h2]
  set A := P ⊓ G with hA
  have hSA : S ≤ A := le_inf (hSQ.trans hQP) hSG
  haveI := hf A inf_le_left
  haveI := hf (A ⊔ Q) (sup_le inf_le_left hQP)
  haveI := hf (A ⊓ Q) (inf_le_right.trans hQP)
  have e1 := finrank_quot A S S le_rfl hSA
  have e2 := finrank_quot (A ⊔ Q) Q S hSQ le_sup_right
  have e3 := finrank_quot (A ⊓ Q) S S le_rfl (le_inf hSA hSQ)
  have e4 := Submodule.finrank_sup_add_finrank_inf_eq (A.map S.mkQ) (Q.map S.mkQ)
  rw [← Submodule.map_sup, ← map_inf_mkQ A Q S hSA] at e4
  rw [map_self, finrank_bot] at e1 e3
  omega

end GlobalTheory.PhiGam.GmultAdd
end
end

section

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem contAction_levRepZ_of_isLocallyConstant
    {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O)
    (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (hloc : ∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) :
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
  unfold ReciprocityTheory.Gal.ContAction
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨g₀, x₀⟩
  have hx := hloc x₀.val (Lev.smul_val x₀)
  refine ⟨{g | ρ g x₀.val = ρ g₀ x₀.val} ×ˢ {x₀},
    (hx.isOpen_fiber _).prod (isOpen_discrete _), ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨g, x⟩ ⟨hg, hx'⟩
  simp only [Set.mem_singleton_iff] at hx'
  subst hx'
  apply Lev.ext
  show (levRep ρ c g x).val = (levRep ρ c g₀ x).val
  rw [levRep_val, levRep_val]
  exact hg

end GlobalTheory.ShapeNeg
end
