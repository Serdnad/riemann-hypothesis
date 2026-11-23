module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle213
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle265
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle274
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle243
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import GroundTheory.AutomorphicForms.AffineBruhat
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LbSpreads
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem exists_natCast_mul_eq_l_pow {n k : ℕ} (hn : n ≠ 0) (hk : n.factorization l ≤ k) :
    ∃ w : A.Acr0, (n : A.Acr0) * w = (l : A.Acr0) ^ k := by
  obtain ⟨w, hw⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l) hn hk
  refine ⟨algebraMap A.W A.Acr0 (A.sW w), ?_⟩
  have h := congrArg (fun t => algebraMap A.W A.Acr0 (A.sW t)) hw
  simpa using h

theorem exists_divided_power_of_dividedXi {j k : ℕ} (hj : j ≠ 0) (hk : k ≠ 0) :
    ∃ y ∈ A.Fil0 1, (k.factorial : A.Acr0) * y = A.dxi0 j ^ k := by
  obtain ⟨-, -, hf, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  refine ⟨(Nat.uniformBell k j : A.Acr0) * A.dxi0 (k * j),
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k * j, Nat.mul_pos (Nat.pos_of_ne_zero hk)
      (Nat.pos_of_ne_zero hj), rfl⟩), ?_⟩
  have hnz := A.acris_torsion_free (j.factorial ^ k) (pow_ne_zero k j.factorial_ne_zero)
  refine (mul_cancel_left_mem_nonZeroDivisors hnz).1 ?_
  have h1 : ((j.factorial ^ k : ℕ) : A.Acr0) *
      ((k.factorial : A.Acr0) * ((Nat.uniformBell k j : A.Acr0) * A.dxi0 (k * j))) =
      ((k * j).factorial : A.Acr0) * A.dxi0 (k * j) := by
    rw [← Nat.uniformBell_mul_eq k hj]
    push_cast
    ring
  rw [h1, hf, pow_mul', ← hf j]
  push_cast
  ring

theorem exists_l_pow {k : ℕ} (hk : k ≠ 0) :
    ∃ y ∈ Ideal.span {(l : A.Acr0)}, (k.factorial : A.Acr0) * y = (l : A.Acr0) ^ k := by
  have hv : k.factorial.factorization l ≤ k - 1 := by
    rw [Nat.factorization_def _ Fact.out]
    have h := sub_one_mul_multiplicity_factorial_lt_of_ne_zero (p := l) hk
    have h2 : 1 ≤ l - 1 := Nat.le_sub_of_add_le (Fact.out : l.Prime).two_le
    have h3 : multiplicity l k.factorial ≤ (l - 1) * multiplicity l k.factorial :=
      Nat.le_mul_of_pos_left _ h2
    omega
  obtain ⟨w, hw⟩ := exists_natCast_mul_eq_l_pow A k.factorial_ne_zero hv
  refine ⟨(l : A.Acr0) * w, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [mul_left_comm, hw]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  ring

theorem filtration_one_eq_span_dividedXi : A.Fil0 1 = Ideal.span {z | ∃ k, 1 ≤ k ∧ z = A.dxi0 k} := rfl

theorem pFil0_eq : A.PFil0 = Ideal.span ({(l : A.Acr0)} ∪ {z | ∃ k, 1 ≤ k ∧ z = A.dxi0 k}) := by
  rw [Ideal.span_union]
  rfl

theorem filtration_one_has_divided_powers : R.PdI (A.Fil0 1) := by
  rw [filtration_one_eq_span_dividedXi]
  refine GlobalTheory.CompanionTheory.DivPow.pdI_span A.acris_torsion_free _ ?_
  rintro _ ⟨j, hj, rfl⟩ k hk
  exact exists_divided_power_of_dividedXi A (by omega) hk

theorem pdI_pFil0 : R.PdI A.PFil0 := by
  rw [pFil0_eq]
  refine GlobalTheory.CompanionTheory.DivPow.pdI_span A.acris_torsion_free _ ?_
  rw [← pFil0_eq]
  rintro x (rfl | ⟨j, hj, rfl⟩) k hk
  · obtain ⟨y, hy, e⟩ := exists_l_pow A hk
    exact ⟨y, (le_sup_left : _ ≤ A.PFil0) hy, e⟩
  · obtain ⟨y, hy, e⟩ := exists_divided_power_of_dividedXi A (by omega : j ≠ 0) hk
    exact ⟨y, (le_sup_right : _ ≤ A.PFil0) hy, e⟩

theorem pow_mem_filtration_of_mem_one {x : A.Acr0} (hx : x ∈ A.Fil0 1) (k : ℕ) : x ^ k ∈ A.Fil0 k := by
  obtain ⟨h0, -, -, hm, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  induction k with
  | zero => rw [h0]; exact Submodule.mem_top
  | succ k ih => rw [pow_succ]; exact hm k 1 (Ideal.mul_mem_mul ih hx)

theorem mem_filtration_of_prime_pow_mul_mem (r N : ℕ) (z : A.Acr0) (h : (l : A.Acr0) ^ N * z ∈ A.Fil0 r) :
    z ∈ A.Fil0 r := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih (GlobalTheory.T.crystalline_filtration_saturated A r _ ?_)
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem mem_filtration_of_factorial_mul_eq_pow {x : A.Acr0} (hx : x ∈ A.Fil0 1) (k : ℕ) (y : A.Acr0)
    (e : (k.factorial : A.Acr0) * y = x ^ k) : y ∈ A.Fil0 k := by
  obtain ⟨w, hw⟩ := exists_natCast_mul_eq_l_pow A k.factorial_ne_zero le_rfl
  refine mem_filtration_of_prime_pow_mul_mem A k (k.factorial.factorization l) y ?_
  rw [← hw, mul_right_comm, e, mul_comm]
  exact Ideal.mul_mem_left _ _ (pow_mem_filtration_of_mem_one A hx k)

theorem pdI_main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.PdI (A.Fil0 1) ∧ R.PdI A.PFil0 ∧
    ∀ x ∈ A.Fil0 1, ∀ (k : ℕ) (y : A.Acr0), (k.factorial : A.Acr0) * y = x ^ k → y ∈ A.Fil0 k :=
  fun A => ⟨filtration_one_has_divided_powers A, pdI_pFil0 A, fun _ hx k y e => mem_filtration_of_factorial_mul_eq_pow A hx k y e⟩

end GlobalTheory.CompanionTheory.PerfFil
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

namespace GradedFiltration

theorem Fil0_succ_le {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.Fil0 (r + 1) ≤ A.Fil0 r :=
  Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩

theorem dividedXi_mem_filtration {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.dxi0 r ∈ A.Fil0 r :=
  Ideal.subset_span ⟨r, le_rfl, rfl⟩

theorem mem_filtration_of_prime_pow_mul {l : ℕ} [Fact l.Prime] (A : PAlg l) (r n : ℕ) (z : A.Acr0)
    (h : (l : A.Acr0) ^ n * z ∈ A.Fil0 r) : z ∈ A.Fil0 r := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply GlobalTheory.T.crystalline_filtration_saturated A r
    rwa [pow_succ', mul_assoc, mul_comm, mul_assoc, mul_comm z, ← mul_assoc, mul_comm _ (l : A.Acr0), mul_assoc] at h

theorem mkAcr_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.mkAcr n) := Ideal.Quotient.mk_surjective

end GradedFiltration


open GradedFiltration in
theorem graded_mod_pow : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n r : ℕ),
    (∀ z ∈ A.Fil n r, ∃ w : A.W, z - A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1)) ∧
    ∀ w : A.W, A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1) ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  intro l _ A n r
  have hF : ∀ s, A.Fil n s = (A.Fil0 s).map (A.mkAcr n) := (GlobalTheory.T.crystalline_filtration_multiplicative A).2.2.2.2.1 n
  have hsurj := mkAcr_surjective A n
  have hto : ∀ w, A.toAcr n w = A.mkAcr n (algebraMap A.W A.Acr0 w) := fun _ => rfl
  have hdx : A.dxi n r = A.mkAcr n (A.dxi0 r) := rfl
  refine ⟨fun z hz => ?_, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hF, Ideal.mem_map_iff_of_surjective _ hsurj] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    obtain ⟨w, hw⟩ := (GlobalTheory.T.crystalline_graded_pieces_description A r).1 z0 hz0
    refine ⟨w, ?_⟩
    set_option synthInstance.maxHeartbeats 200000 in
      rw [hF, hto, hdx, ← map_mul (A.mkAcr n), ← map_sub (A.mkAcr n)]
    exact Ideal.mem_map_of_mem _ hw
  · rw [hF, Ideal.mem_map_iff_of_surjective _ hsurj, hto, hdx, ← map_mul] at h
    obtain ⟨z', hz', e⟩ := h
    have hd : algebraMap A.W A.Acr0 w * A.dxi0 r - z' ∈ Ideal.span {(l : A.Acr0) ^ n} := by
      apply Ideal.Quotient.eq.1
      exact e.symm
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 hd
    have hzr : z ∈ A.Fil0 r := by
      apply mem_filtration_of_prime_pow_mul A r n
      rw [← hz]
      exact sub_mem (Ideal.mul_mem_left _ _ (dividedXi_mem_filtration A r)) (Fil0_succ_le A r hz')
    obtain ⟨w', hw'⟩ := (GlobalTheory.T.crystalline_graded_pieces_description A r).1 z hzr
    have hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi} := by
      rw [← (GlobalTheory.T.crystalline_graded_pieces_description A r).2.1]
      have : algebraMap A.W A.Acr0 (w - (l : A.W) ^ n * w') * A.dxi0 r =
          z' + (l : A.Acr0) ^ n * (z - algebraMap A.W A.Acr0 w' * A.dxi0 r) := by
        rw [map_sub, map_mul, map_pow, map_natCast]
        linear_combination hz
      rw [this]
      exact add_mem hz' (Ideal.mul_mem_left _ _ hw')
    have : A.th w = (l : A.U) ^ n * A.th w' := by
      have h0 : A.th (w - (l : A.W) ^ n * w') = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hxi
      rw [map_sub, map_mul, map_pow, map_natCast, sub_eq_zero] at h0
      exact h0
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h
    obtain ⟨w', rfl⟩ : ∃ w', A.th w' = u := Ideal.Quotient.mk_surjective u
    have hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi} := by
      apply Ideal.Quotient.eq_zero_iff_mem.1
      change A.th (w - (l : A.W) ^ n * w') = 0
      rw [map_sub, map_mul, map_pow, map_natCast, hu, sub_self]
    have h1 := (GlobalTheory.T.crystalline_graded_pieces_description A r).2.1 _ |>.2 hxi
    have h2 : A.toAcr n (w - (l : A.W) ^ n * w') * A.dxi n r ∈ A.Fil n (r + 1) := by
      rw [hF, hto, hdx, ← map_mul]
      exact Ideal.mem_map_of_mem _ h1
    have h3 : A.toAcr n (w - (l : A.W) ^ n * w') = A.toAcr n w := by
      rw [map_sub, map_mul, map_pow, map_natCast, pow_l_acr, zero_mul, sub_zero]
    rwa [h3] at h2

end GlobalTheory.CompanionTheory.PerfFil
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology PositivityTheory.JacquetShalikaLocal GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
  GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

theorem col_add {F : Type} [Field F] (n k : ℕ) (x y : Fin (k + 1) → F) :
    col n k (x + y) = col n k x * col n k y := by
  apply Units.ext
  show 1 + cM n k (x + y) = (1 + cM n k x) * (1 + cM n k y)
  have h : cM n k (x + y) = cM n k x + cM n k y := by
    ext i j
    simp only [cM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [h, mul_add, add_mul, add_mul, cM_mul]
  simp [add_assoc]

theorem exists_weak_integral {X V : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup V] [Module ℂ V] (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (Λ : Set X) (hc : IsCompact Λ) (hΛ : MeasurableSet Λ) (φ : X → ℂ) (hφ : Continuous φ)
    (f : X → V) (hf : IsLocallyConstant f) :
    ∃ w : V, ∀ l : V →ₗ[ℂ] ℂ, l w = ∫ x in Λ, φ x * l (f x) ∂ν := by
  classical
  have hS : (f '' Λ).Finite := by
    haveI : CompactSpace Λ := isCompact_iff_compactSpace.mp hc
    have h := (hf.comp_continuous (continuous_subtype_val (p := (· ∈ Λ)))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at h
  have hmeas : ∀ v, MeasurableSet (Λ ∩ f ⁻¹' {v}) := fun v =>
    hΛ.inter (hf.isOpen_fiber v).measurableSet
  have hcont : ∀ l : V →ₗ[ℂ] ℂ, Continuous fun x => φ x * l (f x) := fun l =>
    hφ.mul (hf.comp l).continuous
  refine ⟨∑ v ∈ hS.toFinset, (∫ x in Λ ∩ f ⁻¹' {v}, φ x ∂ν) • v, fun l => ?_⟩
  have hU : Λ = ⋃ v ∈ hS.toFinset, Λ ∩ f ⁻¹' {v} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.Finite.mem_toFinset, exists_prop]
    exact ⟨fun hx => ⟨f x, ⟨x, hx, rfl⟩, hx, rfl⟩, fun ⟨_, _, hx, _⟩ => hx⟩
  have hdisj : Set.PairwiseDisjoint (↑hS.toFinset) fun v => Λ ∩ f ⁻¹' {v} := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun x hxa hxb => hab ?_
    exact hxa.2.symm.trans hxb.2
  have hint : ∀ s, s ⊆ Λ → ∀ g : X → ℂ, Continuous g → IntegrableOn g s ν := fun s hs g hg =>
    (hg.continuousOn.integrableOn_compact hc).mono_set hs
  conv_rhs => rw [hU]

  rw [integral_biUnion_finset _ (fun v _ => hmeas v) hdisj
  (fun v _ => hint _ Set.inter_subset_left _ (hcont l)), map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, smul_eq_mul, ← integral_mul_const]
  refine setIntegral_congr_fun (hmeas v) fun x hx => ?_
  have hx2 : f x = v := hx.2
  simp only [hx2]

theorem twisted_column_average_exists : L0 → L3 := by
  intro h0
  unfold L3 ForR ForF
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ k M ξ u
  obtain ⟨hψc, hL⟩ := h0 F μ ψ hψ
  obtain ⟨hcomp, -, hmeas, -⟩ := (hL (k + 1)).1 M
  have hopen0 : IsOpen (lat F (k + 1) 0) := ((hL (k + 1)).1 0).2.1
  have hϖ : (uniformizer F : F) ≠ 0 := uniformizer_ne_zero F
  obtain ⟨c, hc⟩ := hρ u
  have hfix : ∀ y : Fin (k + 1) → F, (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ (c + 1) * t) →
      ρ (col n k y) u = u := by
    intro y hy
    apply hc
    intro i j
    show ∃ t ∈ 𝒪[F], ((1 + cM n k y) - 1) i j = (uniformizer F : F) ^ (c + 1) * t
    rw [add_sub_cancel_left]
    simp only [cM, Matrix.of_apply]
    split_ifs with h
    · exact hy _
    · exact ⟨0, zero_mem _, by simp⟩
  have hcol : ∀ x y : Fin (k + 1) → F, ∀ v, ρ (col n k (x + y)) v = ρ (col n k x) (ρ (col n k y) v) := by
    intro x y v
    rw [col_add, map_mul]
    rfl
  have hf : IsLocallyConstant fun x : Fin (k + 1) → F => ρ (col n k x) u := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hcont : Continuous fun y : Fin (k + 1) → F =>
        ((uniformizer F : F) ^ (c + 1))⁻¹ • (y - x) := by fun_prop
    have h0mem : ((uniformizer F : F) ^ (c + 1))⁻¹ • (x - x) ∈ lat F (k + 1) 0 := by
      intro i
      simp
    have hev := hcont.continuousAt.eventually_mem (hopen0.mem_nhds h0mem)
    filter_upwards [hev] with y hy
    have hy' : ρ (col n k (y - x)) u = u := by
      refine hfix _ fun i => ⟨((uniformizer F : F) ^ (c + 1))⁻¹ * (y - x) i, ?_, ?_⟩
      · simpa using hy i
      · field_simp
    show ρ (col n k y) u = ρ (col n k x) u
    rw [show ρ (col n k y) u = ρ (col n k (x + (y - x))) u by rw [add_sub_cancel], hcol, hy']
  have hdot : Continuous fun x : Fin (k + 1) → F => ξ ⬝ᵥ x := by
    simp only [dotProduct]
    fun_prop
  have hφ : Continuous fun x : Fin (k + 1) → F => ψ (-(ξ ⬝ᵥ x)) := hψc.comp hdot.neg
  obtain ⟨w, hw⟩ := exists_weak_integral (Measure.pi fun _ : Fin (k + 1) => μ) (lat F (k + 1) M)
    hcomp hmeas _ hφ _ hf
  refine ⟨w, hw, fun y hy => ?_⟩
  have hpre : (fun x => y + x) ⁻¹' lat F (k + 1) M = lat F (k + 1) M := by
    ext x
    constructor
    · intro hx i
      have h1 := hx i
      have h2 := hy i
      have h3 := sub_mem h1 h2
      simpa [mul_add] using h3
    · intro hx i
      have h1 := hx i
      have h2 := hy i
      have h3 := add_mem h2 h1
      simpa [mul_add] using h3
  refine sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun l => ?_)
  have hl := hw (l ∘ₗ ρ (col n k y))
  have htr := (measurePreserving_add_left (Measure.pi fun _ : Fin (k + 1) => μ) y).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft y).measurableEmbedding
    (fun x => ψ (-(ξ ⬝ᵥ x)) * l (ρ (col n k x) u)) (lat F (k + 1) M)
  rw [hpre] at htr
  have hψy : ∀ x, ψ (-(ξ ⬝ᵥ x)) = ψ (ξ ⬝ᵥ y) * ψ (-(ξ ⬝ᵥ (y + x))) := by
    intro x
    rw [← AddChar.map_add_eq_mul, dotProduct_add]
    congr 1
    ring
  have hmain : l (ρ (col n k y) w) = ψ (ξ ⬝ᵥ y) * l w := by
    have e1 : l (ρ (col n k y) w) = (l ∘ₗ ρ (col n k y)) w := rfl
    rw [e1, hl, hw l, ← htr, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [LinearMap.comp_apply]
    rw [hcol, hψy x, mul_assoc]
  rw [map_sub, map_smul, smul_eq_mul, hmain, sub_self]

end GlobalTheory.CompanionTheory.SatakeBound

end
end

section

open PositivityTheory.JacquetShalikaLocal

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel NNReal Pointwise

namespace GlobalTheory.CompanionTheory.JSBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_of_trivial_integer {ψ : AddChar F ℂ} (h : ∀ x ∈ 𝒪[F], ψ x = 1) : Continuous ψ := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' (𝒪[F] : Set F),
    (Valuation.isOpen_integer).preimage (by fun_prop), ?_, ?_⟩
  · simpa using (𝒪[F]).zero_mem
  · intro y hy
    have hxy : y = x + (y - x) := by ring
    rw [hxy, AddChar.map_add_eq_mul, h _ hy, mul_one]

theorem uniformizer_pow_ne_zero (M : ℕ) : (uniformizer F : F) ^ M ≠ 0 :=
  pow_ne_zero _ ((Valuation.ne_zero_iff _).mp (valuation_uniformizer_ne_zero F))

theorem lat_eq_preimage (m M : ℕ) : lat F m M =
    (Homeomorph.smulOfNeZero ((uniformizer F : F) ^ M) (uniformizer_pow_ne_zero M)) ⁻¹'
      Measures.box (F := F) (ι := Fin m) := by
  ext x
  simp [lat, Measures.mem_box]

theorem isOpen_lat (m M : ℕ) : IsOpen (lat F m M) := by
  rw [lat_eq_preimage]
  exact Measures.isOpen_box.preimage (Homeomorph.continuous _)

theorem isCompact_lat (m M : ℕ) : IsCompact (lat F m M) := by
  rw [lat_eq_preimage]
  exact (Homeomorph.isCompact_preimage _).2 Measures.isCompact_box

theorem zero_mem_lat (m M : ℕ) : (0 : Fin m → F) ∈ lat F m M := by
  intro i
  simpa using (𝒪[F]).zero_mem

variable [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

theorem lat_measure_pos (m M : ℕ) :
    0 < (Measure.pi fun _ : Fin m => μ).real (lat F m M) := by
  haveI := Measures.sigmaCompactSpace F
  have h0 := (isOpen_lat (F := F) m M).measure_ne_zero (Measure.pi fun _ : Fin m => μ)
    ⟨0, zero_mem_lat m M⟩
  have h1 := (isCompact_lat (F := F) m M).measure_lt_top (μ := Measure.pi fun _ : Fin m => μ)
  exact ENNReal.toReal_pos h0 h1.ne

theorem setIntegral_image_mulVec {m : ℕ} (g : GL (Fin m) F) (A : Set (Fin m → F))
    (f : (Fin m → F) → ℂ) :
    ∫ x in (fun x => (g : Matrix (Fin m) (Fin m) F) *ᵥ x) '' A, f x ∂(Measure.pi fun _ => μ) =
      ((Measures.modulus (g : Matrix (Fin m) (Fin m) F).det : ℝ) : ℂ) *
        ∫ x in A, f ((g : Matrix (Fin m) (Fin m) F) *ᵥ x) ∂(Measure.pi fun _ => μ) := by
  haveI := Measures.sigmaCompactSpace F
  haveI := Measures.metrizableSpace F
  set ν : Measure (Fin m → F) := Measure.pi fun _ => μ with hν
  set L := Measures.glEquiv g with hL
  let e : (Fin m → F) ≃ᵐ (Fin m → F) := (Homeomorph.smul L).toMeasurableEquiv
  have he : ∀ x, e x = (g : Matrix (Fin m) (Fin m) F) *ᵥ x := fun x => Measures.glEquiv_apply g x
  have hc : distribHaarChar (Fin m → F) L =
      Measures.modulus (g : Matrix (Fin m) (Fin m) F).det := by
    rw [hL, Measures.distribHaarChar_glEquiv, ← Measures.modulus_units]
    rfl
  have hmap : ν.map e.symm = (Measures.modulus (g : Matrix (Fin m) (Fin m) F).det) • ν := by
    refine Measure.ext fun s _ => ?_
    have hs : e.symm ⁻¹' s = L • s := (e.image_eq_preimage_symm s).symm
    rw [e.symm.map_apply, hs, ← distribHaarChar_mul ν L s, hc, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul]
  have himg : (fun x => (g : Matrix (Fin m) (Fin m) F) *ᵥ x) '' A = e.symm ⁻¹' A := by
    rw [← e.image_eq_preimage_symm]
    exact Set.image_congr fun x _ => (he x).symm
  have key := setIntegral_map_equiv (μ := ν) e.symm (fun x => f (e x)) A
  simp only [MeasurableEquiv.apply_symm_apply] at key
  rw [himg, ← key, hmap, Measure.restrict_smul, integral_smul_nnreal_measure]
  simp only [he, NNReal.smul_def, Complex.real_smul]

theorem l0 : L0 := by
  intro F _ _ _ _ _ _ μ _ ψ hψ
  refine ⟨continuous_of_trivial_integer hψ.1, fun m => ⟨fun M => ?_, fun g A f _ => ?_⟩⟩
  · exact ⟨isCompact_lat m M, isOpen_lat m M, (isOpen_lat m M).measurableSet, lat_measure_pos μ m M⟩
  · exact setIntegral_image_mulVec μ g A f

end GlobalTheory.CompanionTheory.JSBound

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

theorem _root_.GlobalTheory.T.line_bundle_spreads_out' : GlobalTheory.SpreadingModels.LBSpreads := by
  first | exact @GlobalTheory.CompanionTheory.LBLimit.lbSpreads | exact GlobalTheory.CompanionTheory.LBLimit.lbSpreads | (intros; apply GlobalTheory.CompanionTheory.LBLimit.lbSpreads <;> assumption)
end
