module

public import Formalism.DistinguishedUnitIdeals.Bundle002
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.CutPlace
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.Bundle001
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Subgroup.Finite

@[expose] public section

section

noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Helpers

variable {O : Type} [CommRing O] [IsDomain O]

theorem C_dvd_of_forall_dvd_coeff (a : O) (w : PowerSeries O) (h : ∀ n, a ∣ coeff n w) :
    C a ∣ w := by
  choose q hq using h
  refine ⟨PowerSeries.mk q, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  exact hq n

theorem C_dvd_of_C_dvd_mul (ϖ : O) [(Ideal.span {ϖ}).IsMaximal] (f w : PowerSeries O)
    (hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f ≠ 0)
    (h : C ϖ ∣ f * w) : C ϖ ∣ w := by
  obtain ⟨q, hq⟩ := h
  have hk : Ideal.Quotient.mk (Ideal.span {ϖ}) ϖ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ)
  have h0 : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (f * w) = 0 := by
    rw [hq, map_mul, PowerSeries.map_C, hk, map_zero, zero_mul]
  rw [map_mul] at h0
  have hw : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) w = 0 :=
    (mul_eq_zero.mp h0).resolve_left hf
  apply C_dvd_of_forall_dvd_coeff
  intro n
  have hn := congrArg (PowerSeries.coeff n) hw
  rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hn
  exact hn

theorem map_ne_zero_of_unitDist (ϖ : O) [(Ideal.span {ϖ}).IsMaximal] (d : ℕ)
    (p : PowerSeries O) (hp : UnitDist ϖ d p) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) p ≠ 0 := by
  obtain ⟨u, E, hu, hE, hdeg, rfl⟩ := hp
  subst hdeg
  rw [map_mul]
  refine mul_ne_zero (hu.map _).ne_zero ?_
  intro h0
  have hc := congrArg (PowerSeries.coeff E.natDegree) h0
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, hE.monic.coeff_natDegree, map_one, map_zero] at hc
  exact one_ne_zero hc

theorem constantCoeff_mem_of_unitDist (ϖ : O) (d : ℕ) (p : PowerSeries O) (hp : UnitDist ϖ d p)
    (hd : 1 ≤ d) : coeff 0 p ∈ Ideal.span {ϖ} := by
  obtain ⟨u, E, hu, hE, hdeg, rfl⟩ := hp
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  refine Ideal.mul_mem_left _ _ ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  exact hE.mem (by omega)

end Helpers

private theorem mem_span_of_C_pow_mul_mem_span {O : Type} [CommRing O] [IsDomain O] (ϖ : O)
    [(Ideal.span {ϖ}).IsMaximal] (hϖ0 : ϖ ≠ 0) (q : PowerSeries O)
    (hq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) q ≠ 0) :
    ∀ (N : ℕ) (z : PowerSeries O), C (ϖ ^ N) * z ∈ Ideal.span {q} → z ∈ Ideal.span {q} := by
  have hC : (C ϖ : PowerSeries O) ≠ 0 := fun h =>
    hϖ0 (by simpa using congrArg PowerSeries.constantCoeff h)
  intro N
  induction N with
  | zero =>
    intro z hz
    simpa using hz
  | succ N ih =>
    intro z hz
    apply ih
    rw [Ideal.mem_span_singleton] at hz ⊢
    obtain ⟨y, hy⟩ := hz
    have hdiv : C ϖ ∣ q * y := ⟨C (ϖ ^ N) * z, by rw [← hy, pow_succ, map_mul]; ring⟩
    obtain ⟨y', rfl⟩ := C_dvd_of_C_dvd_mul ϖ q y hq hdiv
    refine ⟨y', ?_⟩
    apply mul_left_cancel₀ hC
    rw [pow_succ, map_mul] at hy
    linear_combination hy

theorem mem_span_pow_of_uniformizer_mul : SatDist := by
  intro O _ _ _ ϖ hϖ d p hp k N z hz
  have := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have hq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (p ^ k) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero k (map_ne_zero_of_unitDist ϖ d p hp)
  exact mem_span_of_C_pow_mul_mem_span ϖ hϖ.ne_zero (p ^ k) hq N z hz

theorem pow_dvd_of_const_mem_span : ConstDist := by
  intro O _ _ _ ϖ hϖ d p hp hd c y N a h
  have key : ∀ (N : ℕ) (z : PowerSeries O), C (ϖ ^ N) * z ∈ Ideal.span {p} → z ∈ Ideal.span {p} :=
    fun N z hz => by simpa using mem_span_pow_of_uniformizer_mul O ϖ hϖ d p hp 1 N z (by simpa using hz)
  have hp0 := constantCoeff_mem_of_unitDist ϖ d p hp hd
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, Ideal.mem_span_singleton] at hp0
  have h1 := key N _ h
  clear h
  induction y generalizing c a with
  | zero => simp
  | succ y ih =>
    have e2 : C (ϖ ^ y) * (C ϖ * a) = C (ϖ ^ (y + 1)) * a := by
      rw [← mul_assoc, ← map_mul, pow_succ]
    have h2 : C c - C (ϖ ^ y) * (C ϖ * a) ∈ Ideal.span {p} := by
      rw [e2]
      exact h1
    obtain ⟨c', rfl⟩ := ih c (C ϖ * a) h2
    have e3 : C (ϖ ^ y) * (C c' - C ϖ * a) = C (ϖ ^ y * c') - C (ϖ ^ (y + 1)) * a := by
      rw [mul_sub, ← map_mul, ← mul_assoc, ← map_mul, ← pow_succ]
    have h3 : C c' - C ϖ * a ∈ Ideal.span {p} := by
      apply key y
      rw [e3]
      exact h1
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h3
    have h4 := congrArg PowerSeries.constantCoeff hg
    simp only [map_mul, map_sub, PowerSeries.constantCoeff_C] at h4
    have hc' : ϖ ∣ c' := by
      have e : c' = PowerSeries.constantCoeff g * PowerSeries.constantCoeff p +
          ϖ * PowerSeries.constantCoeff a := by
        linear_combination (-1 : O) * h4
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_right hp0 _) (dvd_mul_right _ _)
    obtain ⟨c'', rfl⟩ := hc'
    exact ⟨c'', by ring⟩

end Formalism.ExponentWindows
end
end

section

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

namespace PhiGammaCoboundaries

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

theorem base_phi_C (B : Base O) (m : O) : B.φ (C m) = C m := by
  rw [← PowerSeries.algebraMap_eq]
  exact B.φ.commutes m

theorem base_gam_C (B : Base O) (m : O) : B.γ (C m) = C m := by
  rw [← PowerSeries.algebraMap_eq]
  exact B.γ.commutes m

theorem cob_zero (L : Lat B n V) : L.IsCobound 0 0 := by
  exact ⟨0, by funext i; simp [Lat.dφ], by funext i; simp [Lat.dγ]⟩

theorem cob_add (L : Lat B n V) {y z y' z' : ZMod n → V} (h : L.IsCobound y z)
    (h' : L.IsCobound y' z') : L.IsCobound (y + y') (z + z') := by
  obtain ⟨m, rfl, rfl⟩ := h
  obtain ⟨m', rfl, rfl⟩ := h'
  refine ⟨m + m', ?_, ?_⟩ <;> funext i <;> simp only [Lat.dφ, Lat.dγ, Pi.add_apply, map_add (f := _)] <;> abel

theorem cob_neg (L : Lat B n V) {y z : ZMod n → V} (h : L.IsCobound y z) :
    L.IsCobound (-y) (-z) := by
  obtain ⟨m, rfl, rfl⟩ := h
  refine ⟨-m, ?_, ?_⟩ <;> funext i <;> simp only [Lat.dφ, Lat.dγ, Pi.neg_apply, map_neg] <;> abel

theorem cob_sub (L : Lat B n V) {y z y' z' : ZMod n → V} (h : L.IsCobound y z)
    (h' : L.IsCobound y' z') : L.IsCobound (y - y') (z - z') := by
  simpa [sub_eq_add_neg] using cob_add L h (cob_neg L h')

theorem cob_smul (L : Lat B n V) (a : O) {y z : ZMod n → V} (h : L.IsCobound y z) :
    L.IsCobound (C a • y) (C a • z) := by
  obtain ⟨m, rfl, rfl⟩ := h
  refine ⟨C a • m, ?_, ?_⟩ <;> funext i <;>
    simp only [Lat.dφ, Lat.dγ, Pi.smul_apply, L.φ_semi, L.γ_semi, base_phi_C, base_gam_C, smul_sub]

theorem cob_sum (L : Lat B n V) {ι : Type} (s : Finset ι) (y z : ι → ZMod n → V)
    (h : ∀ c ∈ s, L.IsCobound (y c) (z c)) :
    L.IsCobound (∑ c ∈ s, y c) (∑ c ∈ s, z c) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using cob_zero L) ?_
  intro c s hc ih h
  rw [Finset.sum_insert hc, Finset.sum_insert hc]
  exact cob_add L (h c (Finset.mem_insert_self c s))
    (ih fun c' hc' => h c' (Finset.mem_insert_of_mem hc'))

theorem lc_pow (B : Base O) (k : ℕ) : B.lc ^ k = C ((B.ℓ : O) ^ k) := by
  unfold Base.lc
  rw [map_pow]

end

theorem combine {O : Type} [CommRing O] {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
    [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
    (f : V₁ →ₗ[PowerSeries O] V₂) (s : Finset (ZMod n)) (l : O) (e e₁ e₂ : ℕ) (he : e = e₂ + e₁)
    (a m : ZMod n → O) (ham : ∀ c ∈ s, a c * m c = l ^ e₂)
    (y₀ : ZMod n → V₂) (yc : ZMod n → ZMod n → V₂) (y1 : ZMod n → ZMod n → V₁) :
    (C (l ^ e) • y₀ - fun i => f ((∑ c ∈ s, C (a c) • y1 c) i)) =
      C (l ^ e₂) • (C (l ^ e₁) • y₀ - ∑ c ∈ s, yc c) -
        ∑ c ∈ s, C (a c) • ((fun i => f (y1 c i)) - C (m c) • yc c) := by
  subst he
  funext i

  simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, map_sum, map_smul, smul_sub,
  Finset.smul_sum, Finset.sum_sub_distrib, smul_smul]
  have h1 : ∑ c ∈ s, (C (a c) * C (m c)) • yc c i = ∑ c ∈ s, C (l ^ e₂) • yc c i :=
    Finset.sum_congr rfl fun c hc => by rw [← map_mul, ham c hc]
  rw [h1, pow_add, map_mul]
  abel

end PhiGammaCoboundaries

open PhiGammaCoboundaries in
theorem thmE_of (h1 : RhoExists) (h2 : RhoLin) (h3 : RhoFun) (h4 : Step1) : ThmEAssembly := by
  intro O _ B n _ Cu abelian₂ j M g sig rr a₀ kap V₁ V₂ V₀ _ _ _ _ _ _ L₁ L₂ L₀ e₀ h Zf₁ Zf₂
    hM hB hG1 hG2 hell he1 he2 hZsmul hZrho hZext hW κ hκ
  obtain ⟨Y, hYrep, hYgood⟩ := hZext κ hκ
  obtain ⟨w, yc, zc, hwc, hcob⟩ := h4 O B n Cu abelian₂ j M g sig rr V₂ V₀ L₂ L₀ e₀ Y κ.1 κ.2 hM hB
    hG2 hell he1 he2 hYrep hYgood
  have H : ∀ c ∈ Cu.cuts, ∃ (w' : V₁) (k : ℕ) (ε : Oˣ), k ≤ 2 * kap ∧ L₁.Wc Cu abelian₂ c w' ∧
      h.f w' - C ((ε : O) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + k)) • w c ∈ sm X (L₂.N c) :=
    fun c hc => hW c hc (w c) (hwc c hc).1
  choose! W1 K E hK hW1 hD using H
  have H2 : ∀ c ∈ Cu.cuts, ∃ y z : ZMod n → V₁, L₁.IsRho c j M g sig (W1 c) y z :=
    fun c hc => h1 O B n Cu j M g sig V₁ L₁ hB hG1 c hc (W1 c) (hW1 c hc).1
  choose! Y1 Z1 hR using H2
  let mc : ZMod n → O := fun c => (E c : O) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + K c)
  let ac : ZMod n → O := fun c => (((E c)⁻¹ : Oˣ) : O) * (B.ℓ : O) ^ (2 * kap - K c)
  have ham : ∀ c ∈ Cu.cuts, ac c * mc c = (B.ℓ : O) ^ (rr + 2 * sig + 2 * a₀ + 2 * kap) := by
    intro c hc
    have hk := hK c hc
    calc ac c * mc c = ((((E c)⁻¹ : Oˣ) : O) * (E c : O)) *
          ((B.ℓ : O) ^ (2 * kap - K c) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + K c)) := by
          simp only [ac, mc]; ring
      _ = _ := by
          rw [Units.inv_mul, one_mul, ← pow_add]
          congr 1
          omega
  have hlin : ∀ c ∈ Cu.cuts, L₂.IsCobound ((fun i => h.f (Y1 c i)) - C (mc c) • yc c)
      ((fun i => h.f (Z1 c i)) - C (mc c) • zc c) := fun c hc =>
    h2 O B n Cu j M g sig V₂ L₂ hB hG2 c hc (mc c) (w c) (h.f (W1 c)) (yc c) (zc c) _ _
      (hwc c hc).2 (h3 O B n j M g sig V₁ V₂ L₁ L₂ h c (W1 c) (Y1 c) (Z1 c) (hR c hc)) (hD c hc)
  refine ⟨∑ c ∈ Cu.cuts, (C (ac c) • Y1 c, C (ac c) • Z1 c), ?_, ?_⟩
  · exact AddSubgroup.sum_mem _ fun c hc =>
      hZsmul (ac c) (Y1 c, Z1 c) (hZrho c hc (W1 c) (hW1 c hc) (Y1 c) (Z1 c) (hR c hc))
  · have e : 2 * rr + 4 * sig + 2 * a₀ + 2 * kap =
        (rr + 2 * sig + 2 * a₀ + 2 * kap) + (rr + 2 * sig) := by ring
    simp only [lc_pow] at hcob ⊢
    simp only [Prod.fst_sum, Prod.snd_sum]
    rw [e, combine h.f Cu.cuts (B.ℓ : O) _ (rr + 2 * sig) (rr + 2 * sig + 2 * a₀ + 2 * kap) rfl
        ac mc ham κ.1 yc Y1,
      combine h.f Cu.cuts (B.ℓ : O) _ (rr + 2 * sig) (rr + 2 * sig + 2 * a₀ + 2 * kap) rfl
        ac mc ham κ.2 zc Z1]
    exact cob_sub L₂ (cob_smul L₂ _ hcob)
      (cob_sum L₂ Cu.cuts _ _ fun c hc => cob_smul L₂ (ac c) (hlin c hc))

end Formalism.ExponentWindows.E
end
end

section

namespace Formalism.ExponentWindows

theorem exists_cuts_exponent_bounds : AprimeCuts := by
  obtain ⟨C, hC, hA⟩ := Formalism.TruncatedSeriesCounting.WachCoordinates.exists_constant_exponent_inequalities
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ n j _ size b w S η rr hj hjn _hsize hCb hsep hrr

  obtain ⟨cuts, ell, hne, hcuts⟩ :=
    exists_cuts_of_sparse_thick n j (fun a => b ≤ size a ∧ size a ≤ b + η) hj hjn hsep
  refine ⟨cuts, ell, hne, fun c hc => ?_⟩
  obtain ⟨h1, h2, h3, _h4, h5, h6, _h7, h8, _h9⟩ := hcuts c hc
  refine ⟨h1, h2, h3, h5, h6, h8, ?_, ?_⟩
  · intro k _ hk
    exact (hA ℓ hℓ b w S η j (3 * j + 1) _ _ rr hj hCb le_rfl hk.1 hk.2 hk.1 hk.2 hrr).1
  · intro k k' _ _ hk hk'
    obtain ⟨_, _, e1, e2, e3⟩ :=
      hA ℓ hℓ b w S η j (3 * j + 1) _ _ rr hj hCb le_rfl hk'.1 hk'.2 hk.1 hk.2 hrr
    exact ⟨e1, e2, e3⟩

end Formalism.ExponentWindows
end
