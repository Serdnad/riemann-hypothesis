module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

section

noncomputable section

open IsDedekindDomain NumberField TensorProduct ValuativeRel

namespace PI.ProdFormulaE.Tr

structure LocFam (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) where
  P : ι → HeightOneSpectrum (𝓞 F)
  K : ι → Type
  [fld : ∀ i, Field (K i)]
  [vr : ∀ i, ValuativeRel (K i)]
  [top : ∀ i, TopologicalSpace (K i)]
  [lf : ∀ i, IsNonarchimedeanLocalField (K i)]
  [cz : ∀ i, CharZero (K i)]
  [alg : ∀ i, Algebra ℚ_[ℓ] (K i)]
  cont : ∀ i, Continuous (algebraMap ℚ_[ℓ] (K i))
  [fin : ∀ i, FiniteDimensional ℚ_[ℓ] (K i)]
  ιF : ∀ i, F →+* K i
  dense : ∀ i, DenseRange (ιF i)
  val : ∀ i (x y : F), (ιF i x ≤ᵥ ιF i y) ↔ (P i).valuation F x ≤ (P i).valuation F y

attribute [instance] LocFam.fld LocFam.vr LocFam.top LocFam.lf LocFam.cz LocFam.alg LocFam.fin

variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}

def LocFam.Over (D : LocFam F ℓ ι) : Prop :=
  Function.Injective D.P ∧ ∀ p, p ∈ Set.range D.P ↔ ((ℓ : 𝓞 F) ∈ p.asIdeal)

def LocFam.Φ (D : LocFam F ℓ ι) : ℚ_[ℓ] ⊗[ℚ] F →ₐ[ℚ_[ℓ]] (∀ i, D.K i) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[ℓ] _) (AlgHom.pi fun i => (D.ιF i).toRatAlgHom)
    (fun _ _ => Commute.all _ _)

theorem LocFam.Φ_tmul (D : LocFam F ℓ ι) (c : ℚ_[ℓ]) (x : F) (i : ι) :
    D.Φ (c ⊗ₜ x) i = algebraMap ℚ_[ℓ] (D.K i) c * D.ιF i x := by
  simp [LocFam.Φ, Algebra.ofId_apply]

def TrSurj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) [Fintype ι]
    (D : LocFam F ℓ ι), D.Over → Function.Surjective D.Φ

def TrInj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) [Fintype ι]
    (D : LocFam F ℓ ι), D.Over → Function.Injective D.Φ

def TrSum : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (ι : Type) [Fintype ι]
    (D : LocFam F ℓ ι), D.Over → ∀ y : F,
      ∑ i, Algebra.trace ℚ_[ℓ] (D.K i) (D.ιF i y) = algebraMap ℚ ℚ_[ℓ] (Algebra.trace ℚ F y)

end PI.ProdFormulaE.Tr
end
end

section

noncomputable section

open Finset

namespace PI.ProdFormulaE.Frac

private theorem padicNorm_le_one_iff_not_dvd_den {q : ℕ} [Fact q.Prime] (r : ℚ) :
    padicNorm q r ≤ 1 ↔ ¬ q ∣ r.den := by
  have hmul : padicNorm q r * padicNorm q (r.den : ℚ) = padicNorm q (r.num : ℚ) := by
    rw [← padicNorm.mul, Rat.mul_den_eq_num]
  constructor
  · intro h hd
    have h1 : padicNorm q (r.den : ℚ) < 1 := (padicNorm.nat_lt_one_iff _).2 hd
    have h2 : padicNorm q (r.num : ℚ) < 1 := by
      rw [← hmul]
      calc padicNorm q r * padicNorm q (r.den : ℚ) ≤ 1 * padicNorm q (r.den : ℚ) :=
            mul_le_mul_of_nonneg_right h (padicNorm.nonneg _)
        _ < 1 := by rw [one_mul]; exact h1
    have h4 : q ∣ r.num.natAbs := Int.natCast_dvd.1 ((padicNorm.int_lt_one_iff _).1 h2)
    have h5 := Nat.dvd_gcd h4 hd
    rw [r.reduced.gcd_eq_one] at h5
    exact (Nat.Prime.not_dvd_one Fact.out) h5
  · intro hd
    have h1 : padicNorm q (r.den : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).2 hd
    rw [h1, mul_one] at hmul
    rw [hmul]
    exact padicNorm.of_int _

theorem padicNorm_le_one_of_den_pow {q l : ℕ} [hq : Fact q.Prime] (hl : l.Prime) (hne : l ≠ q)
    {a : ℚ} {n : ℕ} (ha : a.den = l ^ n) : padicNorm q a ≤ 1 := by
  rw [padicNorm_le_one_iff_not_dvd_den, ha]
  intro h
  exact hne ((Nat.prime_dvd_prime_iff_eq hq.out hl).1 (hq.out.dvd_of_dvd_pow h)).symm

theorem den_eq_one_of_forall_padicNorm_le_one {r : ℚ}
    (h : ∀ q : ℕ, q.Prime → padicNorm q r ≤ 1) : r.den = 1 := by
  by_contra hd
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd
  haveI : Fact q.Prime := ⟨hq⟩
  exact (padicNorm_le_one_iff_not_dvd_den r).1 (h q hq) hqd

theorem padicNorm_le_one_of_den_eq_one {q : ℕ} [Fact q.Prime] {a : ℚ} (ha : a.den = 1) :
    padicNorm q a ≤ 1 := by
  rw [padicNorm_le_one_iff_not_dvd_den, ha]
  exact Nat.Prime.not_dvd_one Fact.out

theorem padicNorm_add_le_one {q : ℕ} [Fact q.Prime] {a b : ℚ} (ha : padicNorm q a ≤ 1)
    (hb : padicNorm q b ≤ 1) : padicNorm q (a + b) ≤ 1 := le_trans padicNorm.nonarchimedean (max_le ha hb)

theorem padicNorm_sub_le_one {q : ℕ} [Fact q.Prime] {a b : ℚ} (ha : padicNorm q a ≤ 1)
    (hb : padicNorm q b ≤ 1) : padicNorm q (a - b) ≤ 1 := by
  exact le_trans padicNorm.sub (max_le ha hb)

theorem den_sub_sum_eq_one {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (a : ι → ℚ)
    (ha : ∀ i, ∃ n : ℕ, (a i).den = ℓ i ^ n) (fib : ℕ → Finset ι)
    (hfib : ∀ i q, i ∈ fib q ↔ ℓ i = q) (I : Finset ι) (hI : ∀ i, i ∉ I → (a i).den = 1)
    (t : ℚ) (ht : ∀ q : ℕ, q.Prime → padicNorm q (t - ∑ i ∈ fib q, a i) ≤ 1) :
    (t - ∑ i ∈ I, a i).den = 1 := by
  classical
  apply den_eq_one_of_forall_padicNorm_le_one
  intro q hq
  haveI : Fact q.Prime := ⟨hq⟩
  have hsum : ∀ s : Finset ι, (∀ i ∈ s, padicNorm q (a i) ≤ 1) →
      padicNorm q (∑ i ∈ s, a i) ≤ 1 :=
    fun s hs => Finset.sum_induction _ (fun x => padicNorm q x ≤ 1)
      (fun x y hx hy => padicNorm_add_le_one hx hy) (by simp) hs
  have h1 : padicNorm q (∑ i ∈ fib q \ I, a i) ≤ 1 :=
    hsum _ (fun i hi => padicNorm_le_one_of_den_eq_one (hI i (Finset.mem_sdiff.1 hi).2))
  have h2 : padicNorm q (∑ i ∈ I \ fib q, a i) ≤ 1 := hsum _ (fun i hi => by
    obtain ⟨n, hn⟩ := ha i
    have hne : ℓ i ≠ q := fun h => (Finset.mem_sdiff.1 hi).2 ((hfib i q).2 h)
    exact padicNorm_le_one_of_den_pow (hℓ i) hne hn)
  have e : t - ∑ i ∈ I, a i =
      (t - ∑ i ∈ fib q, a i) + (∑ i ∈ fib q \ I, a i - ∑ i ∈ I \ fib q, a i) := by
    rw [Finset.sum_sdiff_sub_sum_sdiff]
    ring
  rw [e]
  exact padicNorm_add_le_one (ht q hq) (padicNorm_sub_le_one h1 h2)

theorem exp_two_pi_int (n : ℤ) : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem exp_two_pi_of_den_eq_one {a : ℚ} (ha : a.den = 1) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 := by
  have h : (a : ℂ) = ((a.num : ℤ) : ℂ) := by
    calc (a : ℂ) = (((a.num : ℤ) : ℚ) : ℂ) :=
          congrArg (fun x : ℚ => (x : ℂ)) (Rat.coe_int_num_of_den_eq_one ha).symm
      _ = ((a.num : ℤ) : ℂ) := Rat.cast_intCast _
  rw [h]
  exact exp_two_pi_int _

theorem finprod_exp_of_padicNorm {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (a : ι → ℚ)
    (ha : ∀ i, ∃ n : ℕ, (a i).den = ℓ i ^ n) (fib : ℕ → Finset ι)
    (hfib : ∀ i q, i ∈ fib q ↔ ℓ i = q) (hfin : {i | (a i).den ≠ 1}.Finite)
    (t : ℚ) (ht : ∀ q : ℕ, q.Prime → padicNorm q (t - ∑ i ∈ fib q, a i) ≤ 1) :
    (Function.mulSupport fun i => Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ))).Finite ∧
    ∏ᶠ i, Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  classical
  set I := hfin.toFinset with hIdef
  have hI : ∀ i, i ∉ I → (a i).den = 1 := by
    intro i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have hsub : (Function.mulSupport fun i => Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ))) ⊆
      (I : Set ι) := by
    intro i hi
    by_contra h
    exact hi (exp_two_pi_of_den_eq_one (hI i h))
  refine ⟨I.finite_toSet.subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← Complex.exp_sum]
  have h1 := exp_two_pi_of_den_eq_one (den_sub_sum_eq_one ℓ hℓ a ha fib hfib I hI t ht)
  have key : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      2 * Real.pi * Complex.I * (((t - ∑ i ∈ I, a i : ℚ)) : ℂ) +
        ∑ i ∈ I, 2 * Real.pi * Complex.I * (a i : ℂ) := by
    push_cast
    rw [← Finset.mul_sum]
    ring
  rw [key, Complex.exp_add, h1, one_mul]

theorem finprod_exp {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, (ℓ i).Prime) (a : ι → ℚ)
    (ha : ∀ i, ∃ n : ℕ, (a i).den = ℓ i ^ n) (fib : ℕ → Finset ι)
    (hfib : ∀ i q, i ∈ fib q ↔ ℓ i = q) (hfin : {i | (a i).den ≠ 1}.Finite) (t : ℚ)
    (ht : ∀ (q : ℕ) [Fact q.Prime], ‖(t : ℚ_[q]) - ∑ i ∈ fib q, (a i : ℚ_[q])‖ ≤ 1) :
    (Function.mulSupport fun i => Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ))).Finite ∧
    ∏ᶠ i, Complex.exp (2 * Real.pi * Complex.I * (a i : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  refine finprod_exp_of_padicNorm ℓ hℓ a ha fib hfib hfin t ?_
  intro q hq
  haveI : Fact q.Prime := ⟨hq⟩
  have h := ht q
  have e : ‖((t - ∑ i ∈ fib q, a i : ℚ) : ℚ_[q])‖ = _ := Padic.eq_padicNorm (t - ∑ i ∈ fib q, a i)
  have h' : ((padicNorm q (t - ∑ i ∈ fib q, a i) : ℚ) : ℝ) ≤ 1 := by
    rw [← e]
    push_cast
    exact h
  exact_mod_cast h'

theorem den_eq_one_of_norm_le_one {l : ℕ} [hl : Fact l.Prime] {a : ℚ} {n : ℕ}
    (ha : a.den = l ^ n) {T : ℚ_[l]} (hT : ‖T‖ ≤ 1) (hTa : ‖T - (a : ℚ_[l])‖ ≤ 1) :
    a.den = 1 := by
  have h1 : ‖(a : ℚ_[l])‖ ≤ 1 := by
    have e : (a : ℚ_[l]) = T + -(T - (a : ℚ_[l])) := by ring
    rw [e]
    refine le_trans (Padic.nonarchimedean _ _) (max_le hT ?_)
    rw [norm_neg]
    exact hTa
  have h2 : padicNorm l a ≤ 1 := by
    have e : ‖((a : ℚ) : ℚ_[l])‖ = _ := Padic.eq_padicNorm a
    have h' : ((padicNorm l a : ℚ) : ℝ) ≤ 1 := by
      rw [← e]
      exact h1
    exact_mod_cast h'
  have h3 := (padicNorm_le_one_iff_not_dvd_den a).1 h2
  rw [ha] at h3 ⊢
  rcases n with _ | n
  · simp
  · exact absurd (dvd_pow_self l (Nat.succ_ne_zero n)) h3

theorem norm_sum_sub_sum_le_one {q : ℕ} [Fact q.Prime] {ι : Type*} (s : Finset ι)
    (T b : ι → ℚ_[q]) (h : ∀ i ∈ s, ‖T i - b i‖ ≤ 1) :
    ‖∑ i ∈ s, T i - ∑ i ∈ s, b i‖ ≤ 1 := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_induction _ (fun x : ℚ_[q] => ‖x‖ ≤ 1)
    (fun x y hx hy => le_trans (Padic.nonarchimedean x y) (max_le hx hy)) (by simp) h

end PI.ProdFormulaE.Frac
end
end

section

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise

namespace PI.ProdFormulaE.HaarBox

section Field

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem secondCountable : SecondCountableTopology K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  open scoped Valued in
  exact secondCountable_of_proper

variable {K}

theorem isOpen_ball (γ : ValueGroupWithZero K) (hγ : γ ≠ 0) :
    IsOpen {x : K | valuation K x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation K).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hy.le hx)

theorem isCompact_ball (γ : ValueGroupWithZero K) : IsCompact {x : K | valuation K x ≤ γ} :=
  IsNonarchimedeanLocalField.isCompact_closedBall K γ

end Field

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : Set E :=
  {x | ∀ i, valuation K (b.repr x i) ≤ γ i}

theorem continuous_coord (b : Basis ι K E) (i : ι) : Continuous fun x : E => b.repr x i := by
  have h := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap
  exact (continuous_apply i).comp h

theorem continuous_equivFun_symm (b : Basis ι K E) : Continuous b.equivFun.symm := by
  haveI := IsModuleTopology.toContinuousAdd K E
  exact IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.symm.toLinearMap

theorem isOpen_box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) (hγ : ∀ i, γ i ≠ 0) :
    IsOpen (box b γ) := by
  have e : box b γ = ⋂ i, (fun x : E => b.repr x i) ⁻¹' {a : K | valuation K a ≤ γ i} := by
    ext x
    simp [box]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_ball (γ i) (hγ i)).preimage (continuous_coord b i)

theorem box_eq_image (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) :
    box b γ = b.equivFun.symm '' Set.univ.pi (fun i => {a : K | valuation K a ≤ γ i}) := by
  have hr : ∀ y : ι → K, b.repr (b.equivFun.symm y) = y := fun y => by
    have h1 := b.equivFun.apply_symm_apply y
    rw [Basis.equivFun_apply] at h1
    exact h1
  ext x
  simp only [box, Set.mem_setOf_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h
    exact ⟨b.equivFun x, fun i => by simpa [Basis.equivFun_apply] using h i, by simp⟩
  · rintro ⟨y, hy, rfl⟩ i
    rw [hr]
    exact hy i

theorem isCompact_box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : IsCompact (box b γ) := by
  rw [box_eq_image]
  exact (isCompact_univ_pi fun i => isCompact_ball (γ i)).image (continuous_equivFun_symm b)

theorem zero_mem_box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : (0 : E) ∈ box b γ := by
  intro i
  simp

theorem locallyCompact (b : Basis ι K E) : LocallyCompactSpace E := by
  let e : E ≃ₜ (ι → K) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap
      continuous_invFun := continuous_equivFun_symm b }
  exact e.isOpenEmbedding.locallyCompactSpace

def homeo (b : Basis ι K E) : E ≃ₜ (ι → K) where
  toEquiv := b.equivFun.toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap
  continuous_invFun := continuous_equivFun_symm b

theorem secondCountableE (b : Basis ι K E) : SecondCountableTopology E := by
  haveI := secondCountable K
  exact (homeo b).isEmbedding.secondCountableTopology

def toCLE (T : E ≃ₗ[K] E) : E ≃L[K] E :=
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd K E
  { T with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) T.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (R := K) T.symm.toLinearMap }

variable [MeasurableSpace E] [BorelSpace E]

theorem image_eq_smul (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[K] E) :
    ∃ c : ℝ≥0, ∀ S : Set E, μ (T '' S) = c * μ S := by
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup K E
  haveI := locallyCompact b
  haveI := secondCountableE b
  let L := toCLE T
  haveI : (μ.map L.symm).IsAddHaarMeasure := L.symm.isAddHaarMeasure_map μ
  refine ⟨addHaarScalarFactor (μ.map L.symm) μ, fun S => ?_⟩
  have h := isAddLeftInvariant_eq_smul (μ.map L.symm) μ
  have h2 : (μ.map L.symm) S = μ (T '' S) := by
    have hm : (μ.map L.symm) = μ.map (L.symm.toHomeomorph.toMeasurableEquiv) := rfl
    rw [hm, MeasurableEquiv.map_apply]
    have hL : ∀ x, L.symm x = T.symm x := fun x => rfl
    congr 1
    ext x
    simp only [Set.mem_preimage, Homeomorph.toMeasurableEquiv_coe,
      ContinuousLinearEquiv.coe_toHomeomorph, hL, Set.mem_image]
    constructor
    · intro hx; exact ⟨T.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have h' : (μ.map L.symm) S = _ := DFunLike.congr_fun h S
  rw [← h2, h']
  first | rfl | exact (nnreal_smul_coe_apply _ _ _) | simp

theorem image_eq_of_box (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[K] E)
    (γ : ι → ValueGroupWithZero K) (hγ : ∀ i, γ i ≠ 0) (c : ℝ≥0∞)
    (hc : μ (T '' box b γ) = c * μ (box b γ)) (S : Set E) : μ (T '' S) = c * μ S := by
  obtain ⟨c', hc'⟩ := image_eq_smul b μ T
  have hpos : μ (box b γ) ≠ 0 := (isOpen_box b γ hγ).measure_ne_zero μ ⟨0, zero_mem_box b γ⟩
  have hfin : μ (box b γ) ≠ ⊤ := (isCompact_box b γ).measure_lt_top.ne
  rw [hc' (box b γ)] at hc
  have hcc : ((c' : ℝ≥0∞)) = c := (ENNReal.mul_left_inj hpos hfin).mp hc
  rw [hc' S, hcc]

end PI.ProdFormulaE.HaarBox
end
end

section

noncomputable section

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE.Tr

theorem exists_eq_ell_mul {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (X : 𝓞 F)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal →
      v.valuation F (X : F) ≤ v.valuation F (ℓ : F)) :
    ∃ Z : 𝓞 F, X = ℓ * Z := by
  have hℓ : (ℓ : F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  have hval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v.valuation F ((X : F) / ℓ) ≤ 1 := by
    intro v
    rw [map_div₀]
    have hℓv : v.valuation F (ℓ : F) = v.intValuation (ℓ : 𝓞 F) := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]
      simp
    by_cases hv : (ℓ : 𝓞 F) ∈ v.asIdeal
    · have hpos : v.valuation F (ℓ : F) ≠ 0 := (Valuation.ne_zero_iff _).2 hℓ
      exact (div_le_one₀ (zero_lt_iff.2 hpos)).2 (h v hv)
    · rw [hℓv, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hv, div_one]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v X
  obtain ⟨Z, hZ⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F
    ((X : F) / ℓ) hval
  refine ⟨Z, ?_⟩
  apply IsFractionRing.injective (𝓞 F) F
  have hZ' : algebraMap (𝓞 F) F Z = (X : F) / ℓ := hZ
  have hc : (ℓ : F) * ((X : F) / ℓ) = X := by field_simp
  rw [map_mul, hZ', map_natCast, hc]
  try rfl

theorem exists_int_approx (ℓ : ℕ) [Fact ℓ.Prime] (c : ℚ_[ℓ]) (hc : ‖c‖ ≤ 1) :
    ∃ m : ℤ, ‖(c - m) / ℓ‖ ≤ 1 := by
  obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (⟨c, hc⟩ : ℤ_[ℓ])
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_lt_one_iff_dvd] at hn
  obtain ⟨y, hy⟩ := hn
  refine ⟨n, ?_⟩
  have hy' : c - (n : ℚ_[ℓ]) = ℓ * (y : ℚ_[ℓ]) := by
    have := congrArg (fun w : ℤ_[ℓ] => (w : ℚ_[ℓ])) hy
    push_cast at this
    exact this
  have hℓ : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  rw [show ((n : ℤ) : ℚ_[ℓ]) = (n : ℚ_[ℓ]) by push_cast; rfl, hy', mul_div_cancel_left₀ _ hℓ]
  exact y.norm_le_one

end PI.ProdFormulaE.Tr
end
end
