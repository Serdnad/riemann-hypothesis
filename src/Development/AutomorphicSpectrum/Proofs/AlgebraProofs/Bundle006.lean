module

import Development.AutomorphicArithmetic.FrobeniusLocalisation.LocStab
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.Conj

open UniformSpace Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem exists_padicAlgCl_factor {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ_[p]) :
    ∃ φ : K →+* PadicAlgCl p, ∀ a, ((φ a : PadicAlgCl p) : ℂ_[p]) = κ a := by
  let j : PadicAlgCl p →+* ℂ_[p] := UniformSpace.Completion.coeRingHom
  have hjinj : Function.Injective j := j.injective
  let _ : Algebra (PadicAlgCl p) ℂ_[p] := j.toAlgebra
  have hmem : ∀ a : K, ∃ y, j y = κ a := by
    intro a
    have ha : IsIntegral ℚ a := IsIntegral.of_finite ℚ a
    have hκ : aeval (κ a) (minpoly ℚ a) = κ (aeval a (minpoly ℚ a)) :=
      Polynomial.aeval_algHom_apply κ.toRatAlgHom a _
    have hint : IsIntegral (PadicAlgCl p) (κ a) := by
      refine ⟨(minpoly ℚ a).map (algebraMap ℚ (PadicAlgCl p)), (minpoly.monic ha).map _, ?_⟩
      rw [eval₂_map]
      have hc : (algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap ℚ (PadicAlgCl p)) =
          algebraMap ℚ ℂ_[p] := RingHom.ext_rat _ _
      rw [hc, ← aeval_def, hκ, minpoly.aeval, map_zero]
    exact RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one (PadicAlgCl p) (κ a)
      (IsAlgClosed.degree_eq_one_of_irreducible (PadicAlgCl p) (minpoly.irreducible hint)))
  choose f hf using hmem
  refine ⟨{ toFun := f
            map_one' := hjinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hjinj (by rw [hf, map_mul, map_mul, hf, hf])
            map_zero' := hjinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hjinj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }, fun a => hf a⟩

theorem norm_aeval_monomial_sub (x : PadicAlgCl p) (n : ℕ) (r : ℚ) (c : ℚ_[p]) :
    ‖aeval x (monomial n r) - aeval x (monomial n c)‖ = ‖(r : ℚ_[p]) - c‖ * ‖x‖ ^ n := by
  rw [aeval_monomial, aeval_monomial, ← sub_mul, norm_mul, norm_pow,
    eq_ratCast (algebraMap ℚ (PadicAlgCl p)) r,
    ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)) r, ← map_sub, PadicAlgCl.norm_extends]

theorem exists_rat_poly_approx (x y : PadicAlgCl p) (e : ℚ_[p][X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℚ[X], ‖aeval x u - aeval x e‖ < ε ∧ ‖aeval y u - aeval y e‖ < ε := by
  apply UpperTheory.HF.LocStab.approx <;> assumption

theorem norm_natCast_prime : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem minpoly_eq_of_unit_ball {K : Type} [Field K] [NumberField K] (φ ψ : K →+* PadicAlgCl p)
    (h : ∀ a, ‖φ a‖ ≤ 1 ↔ ‖ψ a‖ ≤ 1) (θ : K) :
    minpoly ℚ_[p] (φ θ) = minpoly ℚ_[p] (ψ θ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hnorm : ∀ (χ : K →+* PadicAlgCl p) (j : ℕ), ‖χ ((p : K) ^ j)⁻¹‖ = ((p : ℝ)⁻¹ ^ j)⁻¹ := by
    intro χ j
    rw [map_inv₀, map_pow, map_natCast, norm_inv, norm_pow, norm_natCast_prime]
  have core : ∀ φ₁ ψ₁ : K →+* PadicAlgCl p, (∀ a, ‖φ₁ a‖ ≤ 1 → ‖ψ₁ a‖ ≤ 1) →
      aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)) = 0 := by
    intro φ₁ ψ₁ h₁
    have hφ : ∀ v : ℚ[X], aeval (φ₁ θ) v = φ₁ (aeval θ v) := fun v =>
      Polynomial.aeval_algHom_apply φ₁.toRatAlgHom θ v
    have hψ : ∀ v : ℚ[X], aeval (ψ₁ θ) v = ψ₁ (aeval θ v) := fun v =>
      Polynomial.aeval_algHom_apply ψ₁.toRatAlgHom θ v
    by_contra hne
    have hz : 0 < ‖aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ))‖ := norm_pos_iff.mpr hne
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (half_pos hz) (inv_lt_one_of_one_lt₀ hp1)
    have ht : 0 < (p : ℝ)⁻¹ ^ j := pow_pos (inv_pos.mpr (by linarith)) j
    obtain ⟨u, hux, huy⟩ := exists_rat_poly_approx (φ₁ θ) (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)) ht
    rw [minpoly.aeval, sub_zero, hφ] at hux
    have h1 : ‖φ₁ (((p : K) ^ j)⁻¹ * aeval θ u)‖ ≤ 1 := by
      rw [map_mul, norm_mul, hnorm, inv_mul_le_iff₀ ht, mul_one]
      exact hux.le
    have h2 := h₁ _ h1
    rw [map_mul, norm_mul, hnorm, inv_mul_le_iff₀ ht, mul_one, ← hψ] at h2
    have h4 := norm_sub_le (aeval (ψ₁ θ) u) (aeval (ψ₁ θ) u - aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)))
    rw [sub_sub_cancel] at h4
    linarith
  have hx : IsIntegral ℚ_[p] (φ θ) := Algebra.IsIntegral.isIntegral _
  have hy : IsIntegral ℚ_[p] (ψ θ) := Algebra.IsIntegral.isIntegral _
  have hPQ : minpoly ℚ_[p] (φ θ) ∣ minpoly ℚ_[p] (ψ θ) :=
    minpoly.dvd _ _ (core ψ φ fun a => (h a).mpr)
  refine minpoly.unique' ℚ_[p] (ψ θ) (minpoly.monic hx) (core φ ψ fun a => (h a).mp) fun q hq => ?_
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  · refine Or.inr fun hqy => ?_
    have h3 := Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ hqy) hq0
    have h4 := Polynomial.natDegree_le_of_dvd hPQ (minpoly.ne_zero hy)
    have h5 := Polynomial.natDegree_lt_natDegree hq0 hq
    omega

theorem exists_extension (σ : PadicAlgCl p ≃+* PadicAlgCl p) (hσ : ∀ x, ‖σ x‖ = ‖x‖) :
    ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧
      ∀ x : PadicAlgCl p, g (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) := by
  have hσs : ∀ x, ‖σ.symm x‖ = ‖x‖ := fun x => by rw [← hσ, RingEquiv.apply_symm_apply]
  have hσi : Isometry σ := AddMonoidHomClass.isometry_of_norm σ hσ
  have hτi : Isometry σ.symm := AddMonoidHomClass.isometry_of_norm σ.symm hσs
  let F : ℂ_[p] →+* ℂ_[p] :=
    UniformSpace.Completion.mapRingHom (σ : PadicAlgCl p →+* PadicAlgCl p) hσi.continuous
  let G : ℂ_[p] →+* ℂ_[p] :=
    UniformSpace.Completion.mapRingHom (σ.symm : PadicAlgCl p →+* PadicAlgCl p) hτi.continuous
  have hF : ∀ x : PadicAlgCl p, F x = (σ x : ℂ_[p]) := fun x =>
    UniformSpace.Completion.mapRingHom_coe hσi.continuous x
  have hG : ∀ x : PadicAlgCl p, G x = (σ.symm x : ℂ_[p]) := fun x =>
    UniformSpace.Completion.mapRingHom_coe hτi.continuous x
  have hFc : Continuous F := UniformSpace.Completion.continuous_extension
  have hGc : Continuous G := UniformSpace.Completion.continuous_extension
  have hGF : ∀ z, G (F z) = z := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (hGc.comp hFc) continuous_id) fun x => ?_
    rw [hF, hG, RingEquiv.symm_apply_apply]
  have hFG : ∀ z, F (G z) = z := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (hFc.comp hGc) continuous_id) fun x => ?_
    rw [hG, hF, RingEquiv.apply_symm_apply]
  have hFn : ∀ z, ‖F z‖ = ‖z‖ := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (continuous_norm.comp hFc) continuous_norm) fun x => ?_
    rw [hF, PadicComplex.norm_extends, PadicComplex.norm_extends, hσ]
  refine ⟨{ toFun := fun z => F z
            invFun := fun z => G z
            left_inv := hGF
            right_inv := hFG
            map_mul' := map_mul F
            map_add' := map_add F }, hFn, hF⟩

theorem exists_isometry_conj_of_unit_ball (K : Type) [Field K] [NumberField K] (p : Nat.Primes)
    (κ κ' : K →+* ℂ_[p]) (h : ∀ a : K, ‖κ a‖ ≤ 1 ↔ ‖κ' a‖ ≤ 1) :
    ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧ ∀ a, g (κ a) = κ' a := by
  obtain ⟨φ, hφ⟩ := exists_padicAlgCl_factor κ
  obtain ⟨ψ, hψ⟩ := exists_padicAlgCl_factor κ'
  have hb : ∀ a, ‖φ a‖ ≤ 1 ↔ ‖ψ a‖ ≤ 1 := fun a => by
    rw [← PadicComplex.norm_extends, ← PadicComplex.norm_extends, hφ, hψ]
    exact h a
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ K
  have hm := minpoly_eq_of_unit_ball φ ψ hb θ
  have : Normal ℚ_[p] (PadicAlgCl p) := IsAlgClosure.normal _ _
  obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.mp
    ((Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).mp hm.symm)
  have hτ' : τ (φ θ) = ψ θ := by rw [← AlgEquiv.smul_def]; exact hτ
  have hτn : ∀ x, ‖τ.toRingEquiv x‖ = ‖x‖ := fun x => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    unfold spectralNorm
    rw [AlgEquiv.coe_ringEquiv, minpoly.algEquiv_eq]
  obtain ⟨g, hgn, hg⟩ := exists_extension τ.toRingEquiv hτn
  have hv : ∀ v : ℚ[X], τ (φ (aeval θ v)) = ψ (aeval θ v) := by
    intro v
    have e1 : φ (aeval θ v) = aeval (φ θ) v := (Polynomial.aeval_algHom_apply φ.toRatAlgHom θ v).symm
    have e2 : ψ (aeval θ v) = aeval (ψ θ) v := (Polynomial.aeval_algHom_apply ψ.toRatAlgHom θ v).symm
    have e3 : τ (aeval (φ θ) v) = aeval (τ (φ θ)) v :=
      (Polynomial.aeval_algHom_apply (τ.toRingEquiv : PadicAlgCl p →+* PadicAlgCl p).toRatAlgHom
        (φ θ) v).symm
    rw [e1, e2, e3, hτ']
  refine ⟨g, hgn, fun a => ?_⟩
  have ha : a ∈ IntermediateField.adjoin ℚ {θ} := by
    rw [hθ]
    exact IntermediateField.mem_top
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ a).mp ha
  have key : τ (φ a) = ψ a := by
    rw [hrs, map_div₀, map_div₀, map_div₀, hv, hv]
  rw [← hφ, ← hψ, hg]
  exact congrArg _ key

end GlobalTheory.CompanionTheory.Ar.Br.Conj
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω]

section One

variable {E : Type*} [AddCommGroup E] [Module Ω E]

def loc (R : Subalgebra o Ω) (f : Ω) (hf : f ∈ R) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) : AddSubgroup E where
  carrier := {e | ∃ n : ℕ, f ^ n • e ∈ L}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact hL _ (R.pow_mem hf _) _ hn
    · rw [pow_add, mul_smul]; exact hL _ (R.pow_mem hf _) _ hm
  neg_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, by rw [smul_neg]; exact L.neg_mem hn⟩

theorem mem_loc {R : Subalgebra o Ω} {f : Ω} {hf : f ∈ R} {L : AddSubgroup E}
    {hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L} {e : E} :
    e ∈ loc R f hf L hL ↔ ∃ n : ℕ, f ^ n • e ∈ L := Iff.rfl

theorem sum_mem_loc {R : Subalgebra o Ω} {f : Ω} (hf : f ∈ R) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (a : Fin r → Ω) (b : Fin r → E)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) (hb : ∀ q, ∃ n : ℕ, f ^ n • b q ∈ L) :
    ∃ n : ℕ, f ^ n • (∑ q, a q • b q) ∈ L := by
  rw [← mem_loc (hf := hf) (hL := hL)]
  refine AddSubgroup.sum_mem _ fun q _ => ?_
  obtain ⟨n, hn⟩ := ha q
  obtain ⟨m, hm⟩ := hb q
  refine ⟨n + m, ?_⟩
  have h := hL _ hn _ hm
  rw [smul_smul] at h
  rw [smul_smul]
  convert h using 2
  ring

def FreeOn (R : Subalgebra o Ω) (f : Ω) (L : AddSubgroup E) {r : ℕ} (b : Fin r → E) : Prop :=
  LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ e, (∃ n : ℕ, f ^ n • e ∈ L) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q

theorem FreeOn.basis_mem {R : Subalgebra o Ω} {f : Ω} {L : AddSubgroup E} {r : ℕ} {b : Fin r → E}
    (h : FreeOn R f L b) (q : Fin r) : ∃ n : ℕ, f ^ n • b q ∈ L := by
  classical
  refine (h.2.2 _).2 ⟨Pi.single q 1, fun p => ⟨0, ?_⟩, ?_⟩
  · by_cases hp : p = q
    · subst hp; simp
    · simp [Pi.single_eq_of_ne hp]
  · simp [Pi.single_apply, ite_smul]

theorem exists_coord {r : ℕ} {b : Fin r → E} (h : Submodule.span Ω (Set.range b) = ⊤) (e : E) :
    ∃ a : Fin r → Ω, e = ∑ q, a q • b q := by
  have he : e ∈ Submodule.span Ω (Set.range b) := h ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
  exact ⟨a, ha.symm⟩

theorem FreeOn.mul {R : Subalgebra o Ω} {f g : Ω} (hf : f ∈ R) (hg : g ∈ R) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} {b : Fin r → E}
    (h : FreeOn R f L b) : FreeOn R (f * g) L b := by
  refine ⟨h.1, h.2.1, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    by_cases hg0 : g = 0
    · obtain ⟨a, ha⟩ := exists_coord h.2.1 e
      exact ⟨a, fun q => ⟨1, by simp [hg0]⟩, ha⟩
    · rw [mul_pow, mul_smul] at hn
      obtain ⟨a, ha, he⟩ := (h.2.2 _).1 ⟨n, hn⟩
      refine ⟨fun q => (g ^ n)⁻¹ * a q, fun q => ?_, ?_⟩
      · obtain ⟨m, hm⟩ := ha q
        refine ⟨n + m, ?_⟩
        have h1 := R.mul_mem (R.mul_mem (R.pow_mem hf n) (R.pow_mem hg m)) hm
        convert h1 using 1
        have : g ^ n ≠ 0 := pow_ne_zero _ hg0
        field_simp
        ring
      · simp only [mul_smul]
        rw [← Finset.smul_sum, ← he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hg0), one_smul]
  · rintro ⟨a, ha, rfl⟩
    refine sum_mem_loc (R.mul_mem hf hg) hL a b ha fun q => ?_
    obtain ⟨n, hn⟩ := h.basis_mem q
    refine ⟨n, ?_⟩
    rw [mul_pow, mul_comm, mul_smul]
    exact hL _ (R.pow_mem hg _) _ hn

end One

variable {E E₁ E₂ : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁]
  [AddCommGroup E₂] [Module Ω E₂]

theorem freeOn_ext {R : Subalgebra o Ω} {f : Ω} (hf : f ∈ R) (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hiq : LinearMap.range i = LinearMap.ker q) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r₁ r₂ : ℕ} {b₁ : Fin r₁ → E₁} {b₂ : Fin r₂ → E₂}
    (h₁ : FreeOn R f (L.comap i.toAddMonoidHom) b₁) (h₂ : FreeOn R f (L.map q.toAddMonoidHom) b₂) :
    ∃ b : Fin (r₁ + r₂) → E, FreeOn R f L b := by
  have hlift : ∀ p, ∃ t : E, q t = b₂ p ∧ ∃ n : ℕ, f ^ n • t ∈ L := by
    intro p
    by_cases hf0 : f = 0
    · obtain ⟨t, ht⟩ := hq (b₂ p)
      exact ⟨t, ht, 1, by simp [hf0]⟩
    · obtain ⟨n, s, hs, hs'⟩ := h₂.basis_mem p
      have hs'' : q s = f ^ n • b₂ p := hs'
      refine ⟨(f ^ n)⁻¹ • s, ?_, n, ?_⟩
      · rw [map_smul, hs'', smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hf0), one_smul]
      · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hf0), one_smul]; exact hs
  choose t ht htL using hlift
  have hqi : ∀ x, q (i x) = 0 := fun x => by
    have : i x ∈ LinearMap.ker q := hiq ▸ LinearMap.mem_range_self i x
    exact this
  have hsum : ∀ (a₁ : Fin r₁ → Ω) (a₂ : Fin r₂ → Ω),
      ∑ p, Fin.append a₁ a₂ p • Fin.append (fun p => i (b₁ p)) t p
        = i (∑ p, a₁ p • b₁ p) + ∑ p, a₂ p • t p := by
    intro a₁ a₂
    rw [Fin.sum_univ_add]

    simp [map_sum]
  have hker : ∀ (e : E) (a₂ : Fin r₂ → Ω), q e = ∑ p, a₂ p • b₂ p →
      ∃ x, i x = e - ∑ p, a₂ p • t p := by
    intro e a₂ he
    have : e - ∑ p, a₂ p • t p ∈ LinearMap.range i := by
      rw [hiq, LinearMap.mem_ker, map_sub, he]

      simp [map_sum, ht]
    exact this
  refine ⟨Fin.append (fun p => i (b₁ p)) t, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [Fin.append_left, Fin.append_right] at hg
    have h2 : ∑ p, g (Fin.natAdd r₁ p) • b₂ p = 0 := by
      have := congrArg q hg

      simpa [map_sum, hqi, ht] using this
    have h2' := Fintype.linearIndependent_iff.1 h₂.1 _ h2
    have h1 : ∑ p, g (Fin.castAdd r₂ p) • b₁ p = 0 := by
      apply hi

      simpa [map_sum, h2'] using hg
    have h1' := Fintype.linearIndependent_iff.1 h₁.1 _ h1
    intro p
    refine Fin.addCases (fun p => h1' p) (fun p => h2' p) p
  · rw [eq_top_iff]
    intro e _
    obtain ⟨a₂, ha₂⟩ := exists_coord h₂.2.1 (q e)
    obtain ⟨x, hx⟩ := hker e a₂ ha₂
    obtain ⟨a₁, ha₁⟩ := exists_coord h₁.2.1 x
    refine (Submodule.mem_span_range_iff_exists_fun Ω).2 ⟨Fin.append a₁ a₂, ?_⟩
    rw [hsum, ← ha₁, hx, sub_add_cancel]
  · rintro ⟨n, hn⟩
    obtain ⟨a₂, ha₂R, ha₂⟩ := (h₂.2.2 (q e)).1 ⟨n, f ^ n • e, hn, by simp⟩
    obtain ⟨x, hx⟩ := hker e a₂ ha₂
    have hxL : i x ∈ loc R f hf L hL := by
      rw [hx]
      exact AddSubgroup.sub_mem _ ⟨n, hn⟩ (sum_mem_loc hf hL a₂ t ha₂R htL)
    obtain ⟨m, hm⟩ := hxL
    obtain ⟨a₁, ha₁R, ha₁⟩ := (h₁.2.2 x).1 ⟨m, by
      rw [AddSubgroup.mem_comap]; simpa using hm⟩
    refine ⟨Fin.append a₁ a₂, fun p => ?_, ?_⟩
    · refine Fin.addCases (fun p => ?_) (fun p => ?_) p
      · simpa using ha₁R p
      · simpa using ha₂R p
    · rw [hsum, ← ha₁, hx, sub_add_cancel]
  · rintro ⟨a, ha, rfl⟩
    refine sum_mem_loc hf hL a _ ha fun p => ?_
    refine Fin.addCases (fun p => ?_) (fun p => ?_) p
    · obtain ⟨n, hn⟩ := h₁.basis_mem p
      rw [AddSubgroup.mem_comap] at hn
      exact ⟨n, by simpa using hn⟩
    · simpa using htL p

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) → LocFree R r₁ (L.comap i.toAddMonoidHom) → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R (r₁ + r₂) L := by
  intro o Ω _ _ _ R E E₁ E₂ _ _ _ _ _ _ i q hi hq hiq L r₁ r₂ hL
  rintro ⟨hL₁, k₁, f₁, c₁, hf₁, hc₁, hs₁, hb₁⟩ ⟨hL₂, k₂, f₂, c₂, hf₂, hc₂, hs₂, hb₂⟩
  refine ⟨hL, k₁ * k₂,
    fun l => f₁ (finProdFinEquiv.symm l).1 * f₂ (finProdFinEquiv.symm l).2,
    fun l => c₁ (finProdFinEquiv.symm l).1 * c₂ (finProdFinEquiv.symm l).2,
    fun l => R.mul_mem (hf₁ _) (hf₂ _), fun l => R.mul_mem (hc₁ _) (hc₂ _), ?_, fun l => ?_⟩
  · rw [Equiv.sum_comp finProdFinEquiv.symm
      (fun p : Fin k₁ × Fin k₂ => c₁ p.1 * c₂ p.2 * (f₁ p.1 * f₂ p.2)), Fintype.sum_prod_type,
      ← mul_one (1 : Ω)]
    conv_rhs => rw [← hs₁]; enter [2]; rw [hs₁, ← hs₂]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · obtain ⟨b₁, h₁⟩ := hb₁ (finProdFinEquiv.symm l).1
    obtain ⟨b₂, h₂⟩ := hb₂ (finProdFinEquiv.symm l).2
    have h₁' := FreeOn.mul (hf₁ _) (hf₂ (finProdFinEquiv.symm l).2) hL₁ h₁
    have h₂' := FreeOn.mul (hf₂ _) (hf₁ (finProdFinEquiv.symm l).1) hL₂ h₂
    rw [mul_comm] at h₂'
    exact freeOn_ext (R.mul_mem (hf₁ _) (hf₂ _)) i q hi hq hiq hL h₁' h₂'

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt
end

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate

theorem translate_mem_of_isHopfOrder : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)),
    IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  intro R _ T _ A hA f hf t
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, -, b, hb, rfl⟩ := hg
      exact A.smul_mem hb (a t)
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

end GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegFormula

theorem finite_det {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
    {L : C.I → AddSubgroup V} (b₀ : Module.Basis (Fin (Module.finrank K V)) K V)
    (b : C.I → Module.Basis (Fin (Module.finrank K V)) K V) (hL : IsBun C L)
    (h : ∀ i, IsLatOf C i (b i) (L i)) : {i | C.v i (b₀.det (b i)) ≠ 1}.Finite := by
  obtain ⟨c, hc⟩ := hL.2
  refine (hc.union (C.fin _ (b₀.isUnit_det c).ne_zero)).subset fun i hi => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  refine hi ?_
  rw [← Module.Basis.det_mul_det _ c, map_mul, Inhab.v_det C hn.1 (h i), hn.2, mul_one]

theorem deg_formula : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (n : ℕ)
    (b₀ : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V), IsBun C L →
    (∀ i, IsLatOf C i (b i) (L i)) → {i | C.v i (b₀.det (b i)) ≠ 1}.Finite ∧
      deg C L = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
  intro K _ C V _ _ _ L n b₀ b hL h
  have hn : n = Module.finrank K V := by
    simpa using (Module.finrank_eq_card_basis b₀).symm
  subst hn
  have hf := finite_det C b₀ b hL h
  refine ⟨hf, ?_⟩
  rw [Inhab.deg_eq C b h]
  have hx : (Module.finBasis K V).det b₀ ≠ 0 := ((Module.finBasis K V).isUnit_det b₀).ne_zero
  have key : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) =
      (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det b₀)) +
        (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
    intro i
    rw [← Module.Basis.det_mul_det _ b₀, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx)
        ((Valuation.ne_zero_iff _).2 (b₀.isUnit_det (b i)).ne_zero), mul_add]
  simp only [key]
  rw [finsum_add_distrib ((C.fin _ hx).subset fun i hi h1 => hi (by simp [h1]))
    (hf.subset fun i hi h1 => hi (by simp [h1])), C.prod _ hx, zero_add]

end GlobalTheory.CompanionTheory.Ar.Crv.DegFormula
end
