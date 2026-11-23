module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import GroundTheory.PAdicHodge.ACrisBdRGalois
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

private theorem exists_factorial_mul_eq_pow' (k : ℕ) :
    ∃ (N : ℕ) (c : A.W), (k.factorial : A.W) * c = (l : A.W) ^ N := by
  have hp : l.Prime := Fact.out
  obtain ⟨e, m, hm, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero k) l hp.one_lt.ne'
  have hcop : IsCoprime (((l : ℤ)) : A.W) (((m : ℤ)) : A.W) :=
    (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).intCast
  obtain ⟨u, v, huv⟩ := hcop
  push_cast at huv
  have := A.completeW
  have hj : (l : A.W) ∈ (⊥ : Ideal A.W).jacobson :=
    IsAdicComplete.le_jacobson_bot (I := Ideal.span {(l : A.W)}) (Ideal.subset_span (Set.mem_singleton _))
  have hu : IsUnit ((m : A.W) * v) := by
    have h := Ideal.mem_jacobson_bot.1 hj (-u)
    convert h using 1
    linear_combination huv
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  refine ⟨e, v * t, ?_⟩
  rw [hk]
  push_cast
  linear_combination (l : A.W) ^ e * ht

theorem factorial_mul_divided_power_xi (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k := by
  obtain ⟨N, c, hc⟩ := exists_factorial_mul_eq_pow' A k
  have hu : IsUnit (algebraMap A.W (Localization.Away (l : A.W)) (k.factorial : A.W)) := by
    have h1 : IsUnit (algebraMap A.W (Localization.Away (l : A.W)) ((l : A.W) ^ N)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit _).pow N
    rw [← hc, map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  rw [map_natCast] at hu
  unfold CrystallineSemistableComparison.PAlg.dxi0
  apply Subtype.ext
  push_cast
  unfold CrystallineSemistableComparison.dpw
  rw [← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]

theorem xi_mul_divided_power (r : ℕ) :
    algebraMap A.W A.Acr0 A.xi * A.dxi0 r = ((r + 1 : ℕ) : A.Acr0) * A.dxi0 (r + 1) := by
  have h1 := factorial_mul_divided_power_xi A 1
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h1
  rw [← h1, divided_power_xi_mul, add_comm 1 r, Nat.choose_one_right]

theorem exists_factorial_mul_eq_pow (k : ℕ) :
    ∃ (N : ℕ) (c : A.W), (k.factorial : A.W) * c = (l : A.W) ^ N := by
  obtain ⟨c, hc⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l)
    (Nat.factorial_ne_zero k) (le_refl _)
  refine ⟨k.factorial.factorization l, A.sW c, ?_⟩
  have := congrArg A.sW hc
  simpa using this

theorem filtration_element_power_multiple_xi (r : ℕ) {z : A.Acr0} (hz : z ∈ A.Fil0 r) :
    ∃ (N : ℕ) (w : A.W), (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  rw [mem_crystalline_filtration_iff_span] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨N, c, hc⟩ := exists_factorial_mul_eq_pow A k
    refine ⟨N, A.xi ^ (k - r) * c, ?_⟩
    have h := factorial_mul_divided_power_xi A k
    calc (l : A.Acr0) ^ N * A.dxi0 k = algebraMap A.W A.Acr0 ((l : A.W) ^ N) * A.dxi0 k := by simp
    _ = algebraMap A.W A.Acr0 c * ((k.factorial : A.Acr0) * A.dxi0 k) := by
        rw [← hc, map_mul, map_natCast]; ring
    _ = algebraMap A.W A.Acr0 (A.xi ^ r * (A.xi ^ (k - r) * c)) := by
        rw [h, ← map_pow, ← map_mul]
        congr 1
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk]
        ring
  | zero => exact ⟨0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N1, w1, h1⟩ := hx
    obtain ⟨N2, w2, h2⟩ := hy
    refine ⟨N1 + N2, (l : A.W) ^ N2 * w1 + (l : A.W) ^ N1 * w2, ?_⟩
    calc (l : A.Acr0) ^ (N1 + N2) * (x + y)
        = (l : A.Acr0) ^ N2 * ((l : A.Acr0) ^ N1 * x) + (l : A.Acr0) ^ N1 * ((l : A.Acr0) ^ N2 * y) := by ring
    _ = _ := by
        rw [h1, h2]
        simp only [map_mul, map_add (f := _), map_pow, map_natCast]
        ring
  | smul a x _ hx =>
    obtain ⟨N, w, h⟩ := hx
    refine ⟨N, a * w, ?_⟩
    rw [Algebra.smul_def]
    calc (l : A.Acr0) ^ N * (algebraMap A.W A.Acr0 a * x)
        = algebraMap A.W A.Acr0 a * ((l : A.Acr0) ^ N * x) := by ring
    _ = _ := by
        rw [h, ← map_mul]
        congr 1
        ring

theorem filtration_element_mod_next_level (r : ℕ) {z : A.Acr0} (hz : z ∈ A.Fil0 r) :
    ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) := by
  rw [mem_crystalline_filtration_iff_span] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    rcases hk.eq_or_lt with h | h
    · subst h
      exact ⟨1, by simp⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, zero_mul, sub_zero]
      exact (mem_crystalline_filtration_iff_span A (r + 1) _).2 (Submodule.subset_span ⟨k, Nat.succ_le_of_lt h, rfl⟩)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w1, h1⟩ := hx
    obtain ⟨w2, h2⟩ := hy
    refine ⟨w1 + w2, ?_⟩
    have e : x + y - algebraMap A.W A.Acr0 (w1 + w2) * A.dxi0 r =
        (x - algebraMap A.W A.Acr0 w1 * A.dxi0 r) + (y - algebraMap A.W A.Acr0 w2 * A.dxi0 r) := by
      rw [map_add (f := _)]; ring
    rw [e]
    exact Ideal.add_mem _ h1 h2
  | smul a x _ hx =>
    obtain ⟨w, h⟩ := hx
    refine ⟨a * w, ?_⟩
    have e : a • x - algebraMap A.W A.Acr0 (a * w) * A.dxi0 r =
        algebraMap A.W A.Acr0 a * (x - algebraMap A.W A.Acr0 w * A.dxi0 r) := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ h

theorem divided_power_multiple_next_level_iff (r : ℕ) (w : A.W) :
    algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi} := by
  have hinj : Function.Injective (algebraMap A.W A.Acr0) := by
    intro x y h
    apply A.algebraMap_WL_injective
    exact congrArg Subtype.val h
  constructor
  · intro h
    obtain ⟨N, v, hv⟩ := filtration_element_power_multiple_xi A (r + 1) h
    have hr := factorial_mul_divided_power_xi A r
    have e1 : algebraMap A.W A.Acr0 ((l : A.W) ^ N * w * A.xi ^ r) =
        algebraMap A.W A.Acr0 (A.xi * ((r.factorial : A.W) * v) * A.xi ^ r) := by
      have e2 := congrArg (fun t => (r.factorial : A.Acr0) * t) hv
      simp only [map_mul, map_pow, map_natCast] at e2 ⊢
      linear_combination e2 - (l : A.Acr0) ^ N * algebraMap A.W A.Acr0 w * hr
    have e3 : (l : A.W) ^ N * w = A.xi * ((r.factorial : A.W) * v) :=
      (mul_cancel_right_mem_nonZeroDivisors (pow_mem (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).2.1 r)).1 (hinj e1)
    have e4 : (r.factorial : A.W) * v ∈ Ideal.span {(l : A.W) ^ N} := by
      apply (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).2.2 N
      rw [← e3]
      exact Ideal.mem_span_singleton.2 ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 e4
    rw [hy] at e3
    have e5 : w = A.xi * y := by
      apply (mul_cancel_left_mem_nonZeroDivisors (pow_mem A.l_mem_nzd N)).1
      rw [e3]
      ring
    exact Ideal.mem_span_singleton.2 ⟨y, e5⟩
  · intro h
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 h
    have h2 := xi_mul_divided_power A r
    have e : algebraMap A.W A.Acr0 (A.xi * y) * A.dxi0 r =
        algebraMap A.W A.Acr0 y * (((r + 1 : ℕ) : A.Acr0) * A.dxi0 (r + 1)) := by
      rw [← h2, map_mul]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
      ((mem_crystalline_filtration_iff_span A (r + 1) _).2 (Submodule.subset_span ⟨r + 1, le_rfl, rfl⟩)))

theorem crystalline_filtration_graded_pieces : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ),
    (∀ z ∈ A.Fil0 r, ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1)) ∧
    (∀ w : A.W, algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi}) ∧
    ∀ z ∈ A.Fil0 r, ∃ (N : ℕ) (w : A.W),
      (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  intro l hl A r
  exact ⟨fun z hz => filtration_element_mod_next_level A r hz, fun w => divided_power_multiple_next_level_iff A r w,
    fun z hz => filtration_element_power_multiple_xi A r hz⟩

end GlobalTheory.CompanionTheory.PerfFil
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCSig

variable {p : ℕ} [Fact p.Prime] {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem galCp_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[p] →+* ℂ_[p]) = (galCp τ : ℂ_[p] →+* ℂ_[p]) := by
  refine RingHom.ext fun x => ?_
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_galCp σ) (continuous_galCp τ)) fun a => ?_
  show galCp σ (a : ℂ_[p]) = galCp τ (a : ℂ_[p])
  rw [galCp_coe, galCp_coe, h]

theorem galMap_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (galCp_congr σ τ h) _ _

theorem galAway_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : galAway σ = galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt (normInteger ℂ_[p]) p)))
    (RingHom.ext fun w => by
      simp only [RingHom.comp_apply, galAway_algebraMap]
      rw [AInf.gal_smul_def, AInf.gal_smul_def, galMap_congr σ τ h])

theorem galQuot_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) (n : ℕ) : galQuot σ n = galQuot τ n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
    simp only [RingHom.comp_apply, galQuot_mk]
    rw [galAway_congr σ τ h])

theorem galBdRHom_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : galBdRHom σ = galBdRHom τ :=
  RingHom.ext fun x => IsPerfectoidField.evalB_ext fun n => by
    rw [evalB_galBdRHom, evalB_galBdRHom, galQuot_congr σ τ h]

theorem gP_iota {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (g : K.fixingSubgroup) (c : Acris l) :
    gP l g (ACris.iota ℂ_[l] l c) =
      ACris.iota ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) c) := by
  have h := ACris.iota_gal_smul (IntermediateField.fixingSubgroupEquiv K g) c
  rw [ACris.gal_smul_def, gal_smul_bdR_def] at h
  rw [h]
  exact congrArg (fun f => f (ACris.iota ℂ_[l] l c))
    (galBdRHom_congr (toBot g.1) (IntermediateField.fixingSubgroupEquiv K g) fun y => rfl)

theorem sig_lam : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ), ∀ g c,
    (lev h k).σA g ((lev h k).lam c) = (lev h k).lam ((per l K).σA g c) := by
  intro l _ K M h k g c
  apply ι_injective (fk l k) (xi0 l) l M
  show gB h k g (pk l k (ACris.iota ℂ_[l] l c)) =
    pk l k (ACris.iota ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) c))
  rw [← gP_iota]
  exact Ideal.quotientMap_mk

end GlobalTheory.CompanionTheory.LatCSig
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCHyp

theorem isAdicComplete_of_equiv {Q R : Type*} [CommRing Q] [CommRing R] (e : Q ≃+* R) (a : Q)
    (h : IsAdicComplete (Ideal.span {e a}) R) : IsAdicComplete (Ideal.span {a}) Q := by
  have hmem : ∀ (n : ℕ) (x y : Q),
      x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule Q Q)] ↔
        e x ≡ e y [SMOD (Ideal.span {e a} ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, SModEq.sub_mem, smul_eq_mul, smul_eq_mul, Ideal.mul_top, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton, ← map_pow, ← map_sub]
    exact (map_dvd_iff e).symm
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h0 : e x = 0 := by
      refine h.toIsHausdorff.haus' (e x) fun n => ?_
      have := (hmem n x 0).1 (hx n)
      rwa [map_zero] at this
    exact (map_eq_zero_iff e e.injective).1 h0
  · intro f hf
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun n => e (f n))
      (fun {m n} hmn => (hmem m _ _).1 (hf hmn))
    refine ⟨e.symm L, fun n => (hmem n _ _).2 ?_⟩
    rw [RingEquiv.apply_symm_apply]
    exact hL n

variable (l : ℕ) [Fact l.Prime]

def eQ : (Ainf l ⧸ Ideal.span {xi0 l}) ≃+* OC l :=
  (Ideal.quotEquivOfEq (ker_theta0 (l := l)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l))

theorem eQ_natCast (n : ℕ) : eQ l (n : Ainf l ⧸ Ideal.span {xi0 l}) = (n : OC l) := map_natCast _ n

theorem norm_l_lt_one : ‖((l : OC l) : ℂ_[l])‖ < 1 :=
  IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) l

theorem l_ne_zero : (l : OC l) ≠ 0 := by
  intro h
  have h1 : ((l : OC l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [h] at h1
  exact (Nat.cast_ne_zero (R := ℂ_[l])).2 (Fact.out : l.Prime).ne_zero (by simpa using h1.symm)

theorem dvd_pow_l {x : OC l} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (l : OC l) ^ n := by
  have hx0 : (x : ℂ_[l]) ≠ 0 := fun h => hx (Subtype.ext h)
  have hxp : 0 < ‖(x : ℂ_[l])‖ := norm_pos_iff.2 hx0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hxp (norm_l_lt_one l)
  refine ⟨n, ⟨((l : OC l) : ℂ_[l]) ^ n / x, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ hn.le hxp.le
  · simp [mul_div_cancel₀ _ hx0]

theorem dvd_total_OC (x y : OC l) : x ∣ y ∨ y ∣ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inr (dvd_zero y)
  have hx0 : (x : ℂ_[l]) ≠ 0 := fun h => hx (Subtype.ext h)
  rcases le_total ‖(y : ℂ_[l])‖ ‖(x : ℂ_[l])‖ with h | h
  · refine Or.inl ⟨⟨(y : ℂ_[l]) / x, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · simp [mul_div_cancel₀ _ hx0]
  · have hy : y ≠ 0 := by
      rintro rfl
      exact hx0 (norm_eq_zero.1 (le_antisymm (by simpa using h) (norm_nonneg _)))
    have hy0 : (y : ℂ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
    refine Or.inr ⟨⟨(x : ℂ_[l]) / y, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · simp [mul_div_cancel₀ _ hy0]

theorem unit_ainf (n : ℕ) (hn : n ≠ 0) : ∃ (k : ℕ) (u : Ainf l), (n : Ainf l) * u = (l : Ainf l) ^ k := by
  have h0 : (n : ℤ_[l]) ≠ 0 := by exact_mod_cast hn
  refine ⟨(n : ℤ_[l]).valuation, IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l
    (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]), ?_⟩
  have h1 : (n : ℤ_[l]) * (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) =
      (l : ℤ_[l]) ^ (n : ℤ_[l]).valuation := by
    have e2 := congrArg (· * (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) (PadicInt.unitCoeff_spec h0)
    refine e2.trans ?_
    change ((PadicInt.unitCoeff h0 : ℤ_[l]ˣ) : ℤ_[l]) * _ * _ = _
    rw [mul_comm ((PadicInt.unitCoeff h0 : ℤ_[l]ˣ) : ℤ_[l]), mul_assoc, Units.mul_inv, mul_one]
  have h2 := congrArg (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l) h1
  simpa only [map_mul, map_pow, map_natCast] using h2

abbrev xiB : BdRp l := wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)

theorem span_xiB : Ideal.span {xiB l} = Ideal.span {tBdR l} := by
  rw [← IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))]
  exact maximalIdeal_eq_span_tBdR

theorem xi_dvd_fontaine_t : xiB l ∣ tBdR l :=
  Ideal.mem_span_singleton.1 ((span_xiB l).symm ▸ Ideal.mem_span_singleton_self _)

theorem t_dvd_xiB : tBdR l ∣ xiB l :=
  Ideal.mem_span_singleton.1 ((span_xiB l) ▸ Ideal.mem_span_singleton_self _)

theorem xiB_ne_zero : xiB l ≠ 0 :=
  (IsPerfectoidField.irreducible_wittToBDeRhamPlus (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))).ne_zero

theorem nil_k (k : ℕ) : fk l k (xi0 l) ^ k = 0 := by
  change Ideal.Quotient.mk _ (xiB l) ^ k = 0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.mem_span_singleton.2 (pow_dvd_pow_of_dvd (t_dvd_xiB l) k))

theorem dvd_of_witt_mem {a : Ainf l} (h : xiB l ∣ wittToBDeRhamPlus (normInteger ℂ_[l]) l a) : xi0 l ∣ a := by
  have h1 : wittToBDeRhamPlus (normInteger ℂ_[l]) l a ∈
      IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l) := by
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))]
    exact Ideal.mem_span_singleton.2 h
  rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l), RingHom.mem_ker,
    IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus] at h1
  have h2 : a ∈ RingHom.ker (theta0 l) := Subtype.ext h1
  rw [ker_theta0] at h2
  exact Ideal.mem_span_singleton.1 h2

theorem gr_k (k i : ℕ) (hi : i < k) (a : Ainf l) (b : Bk l k)
    (h : fk l k a * fk l k (xi0 l) ^ i = fk l k (xi0 l) ^ (i + 1) * b) : xi0 l ∣ a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply dvd_of_witt_mem
  set w := wittToBDeRhamPlus (normInteger ℂ_[l]) l a with hw
  have h1 : Ideal.Quotient.mk (Ideal.span {tBdR l ^ k}) (w * xiB l ^ i) =
      Ideal.Quotient.mk _ (xiB l ^ (i + 1) * b) := by
    rw [map_mul, map_mul, map_pow, map_pow]
    exact h
  have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
  have h3 : xiB l ^ (i + 1) ∣ tBdR l ^ k :=
    (pow_dvd_pow _ hi).trans (pow_dvd_pow_of_dvd (xi_dvd_fontaine_t l) k)
  have h4 : xiB l ^ (i + 1) ∣ w * xiB l ^ i := by
    obtain ⟨c, hc⟩ := h3.trans h2
    exact ⟨c + b, by linear_combination hc⟩
  rw [pow_succ', mul_comm w, mul_comm (xiB l)] at h4
  exact (mul_dvd_mul_iff_left (pow_ne_zero i (xiB_ne_zero l))).1 h4

theorem hyp_k (l : ℕ) [Fact l.Prime] (k : ℕ) (hk : 1 ≤ k) : Lat.Hyp (Lat.fk l k) (xi0 l) l k := by
  have hl : eQ l (l : Ainf l ⧸ Ideal.span {xi0 l}) = (l : OC l) := eQ_natCast l l
  refine
    { one_le := hk
      nil := nil_k l k
      gr := fun i hi a b h => gr_k l k i hi a b h
      dom := (eQ l).toMulEquiv.isDomain _
      val := fun x y => ?_
      dv := fun x hx => ?_
      l0 := fun h => ?_
      cpl := ?_
      unit := unit_ainf l }
  · rcases dvd_total_OC l (eQ l x) (eQ l y) with h | h
    · exact Or.inl ((map_dvd_iff (eQ l)).1 h)
    · exact Or.inr ((map_dvd_iff (eQ l)).1 h)
  · obtain ⟨n, hn⟩ := dvd_pow_l l (x := eQ l x) ((map_ne_zero_iff _ (eQ l).injective).2 hx)
    refine ⟨n, (map_dvd_iff (eQ l)).1 ?_⟩
    rwa [map_pow, hl]
  · apply l_ne_zero l
    rw [← hl, h, map_zero]
  · refine isAdicComplete_of_equiv (eQ l) _ ?_
    rw [hl]
    exact IsPerfectoidField.isAdicComplete (K := ℂ_[l]) l

end GlobalTheory.CompanionTheory.LatCHyp
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem lev_IB_eq_map {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : (lev h k).IB = (lev h k).I.map (lev h k).ι := by
  have key : IB (fk l k) (xi0 l) = (I (fk l k) (xi0 l) l M).map (ι (fk l k) (xi0 l) l M) := by
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨⟩
      have hm : ofW (fk l k) (xi0 l) l M (xi0 l) ∈ I (fk l k) (xi0 l) l M := by
        show ι (fk l k) (xi0 l) l M (ofW (fk l k) (xi0 l) l M (xi0 l)) ∈ IB (fk l k) (xi0 l)
        rw [ι_ofW]
        exact Ideal.subset_span rfl
      have := Ideal.mem_map_of_mem (ι (fk l k) (xi0 l) l M) hm
      rwa [ι_ofW] at this
    · exact Ideal.map_comap_le
  exact key

end GlobalTheory.CompanionTheory.LatC
end
