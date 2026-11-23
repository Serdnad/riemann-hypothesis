module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import GroundTheory.AutomorphicForms.GLnLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import GroundTheory.AutomorphicForms.Bundle002
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open ValuativeRel Filter

private theorem val_natCast_lt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* k) (hi : Continuous i) :
    valuation k (g : k) < 1 := by
  have h1 : Tendsto (fun m : ℕ => (g : ℚ_[g]) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  have hT : Tendsto (fun m : ℕ => i ((g : ℚ_[g]) ^ m)) atTop (nhds 0) := by
    have := (hi.tendsto 0).comp h1
    rwa [map_zero] at this
  have hopen : IsOpen {x : k | valuation k x < 1} := by
    simpa [Valuation.restrict_lt_one_iff] using (valuation k).isOpen_ball 1
  have hO : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    hopen.mem_nhds (by simp)
  obtain ⟨m, hm, hm0⟩ := ((hT.eventually hO).and (eventually_gt_atTop 0)).exists
  have hm' : valuation k (g : k) ^ m < 1 := by
    have : valuation k (i ((g : ℚ_[g]) ^ m)) < 1 := hm
    rwa [map_pow, map_natCast, map_pow] at this
  by_contra hge
  exact absurd hm' (not_lt.2 (one_le_pow₀ (not_lt.1 hge)))

private theorem val_intCast_le_one {k : Type} [Field k] [ValuativeRel k] (a : ℤ) :
    valuation k (a : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (intCast_mem (valuation k).integer a)

theorem UpperTheory.Zero.LLC.isoUniq :
    UpperTheory.Zero.LLC.IsoUniq := by
  intro k _ _ _ _ _ g g' _ _ i i' hi hi'
  refine ⟨?_, fun i'' hi'' => ?_⟩
  · by_contra hne
    have hc : Nat.Coprime g g' := (Nat.coprime_primes Fact.out Fact.out).2 hne
    have hb : ((1 : ℤ) : k) = (g : k) * (Nat.gcdA g g' : k) + (g' : k) * (Nat.gcdB g g' : k) := by
      have h := Nat.gcd_eq_gcd_ab g g'
      rw [hc.gcd_eq_one] at h
      exact_mod_cast congrArg (Int.cast : ℤ → k) h
    have hv : valuation k (1 : k) < 1 := by
      have h1 : ((1 : ℤ) : k) = 1 := Int.cast_one
      rw [← h1, hb]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le (val_natCast_lt_one g i hi) (val_intCast_le_one _)
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le (val_natCast_lt_one g' i' hi') (val_intCast_le_one _)
    rw [map_one] at hv
    exact lt_irrefl _ hv
  · have h : (i'' : ℚ_[g] → k) = i :=
      (Padic.denseRange_ratCast g).equalizer hi'' hi (by
        funext q
        simp only [Function.comp_apply, map_ratCast])
    exact DFunLike.coe_injective h
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Zero.LLC

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem val_det_sub_one_lt {g : GL (Fin n) k} (hg : g ∈ KOne k (Fin n)) :
    valuation k ((GeneralLinearGroup.det g : kˣ) - 1 : k) < 1 := by
  classical
  rw [GlobalTheory.StepData.mem_KOne] at hg
  unfold GlobalTheory.StepData.MaxM at hg
  have hint : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    intro i j
    have h1 := hg i j
    rw [Matrix.sub_apply] at h1
    have h2 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [Valuation.mem_integer_iff]
    calc valuation k ((g : Matrix (Fin n) (Fin n) k) i j)
        = valuation k (((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j)
            + (1 : Matrix (Fin n) (Fin n) k) i j) := by rw [sub_add_cancel]
      _ ≤ max _ _ := Valuation.map_add _ _ _
      _ ≤ 1 := max_le h1.le h2
  let M : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨(g : Matrix (Fin n) (Fin n) k) i j, hint i j⟩
  have hdet : ((M.det : 𝒪[k]) : k) = ((GeneralLinearGroup.det g : kˣ) : k) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    have h3 := RingHom.map_det (𝒪[k].subtype) M
    rw [Subring.coe_subtype] at h3
    rw [h3]
    congr 1
  have hres : IsLocalRing.residue 𝒪[k] M.det = IsLocalRing.residue 𝒪[k] 1 := by
    rw [RingHom.map_det, map_one]
    have hM : (IsLocalRing.residue 𝒪[k]).mapMatrix M = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
      have h5 : IsLocalRing.residue 𝒪[k] (M i j)
          = IsLocalRing.residue 𝒪[k] (if i = j then 1 else 0) := by
        rw [GlobalTheory.StepData.residue_eq_iff_lt]
        have h6 := hg i j
        rw [Matrix.sub_apply, Matrix.one_apply] at h6
        split_ifs at h6 ⊢ <;> simpa [M] using h6
      rw [h5]
      split_ifs <;> simp
    rw [hM, Matrix.det_one]
  have h4 := (GlobalTheory.StepData.residue_eq_iff_lt _ _).mp hres
  rw [hdet] at h4
  simpa using h4

private theorem fixed_ne_bot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) {H : Subgroup G} {v : V}
    (hv : v ∈ fixed ρ H) (h0 : v ≠ 0) : fixed σ H ≠ ⊥ := by
  intro hbot
  have hm : e v ∈ fixed σ H := by
    rw [GlobalTheory.Parabolic.mem_fixed] at hv ⊢
    intro u hu
    have := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap u v
    simp only [Representation.Equiv.coe_toIntertwiningMap] at this
    rw [← this, hv u hu]
  rw [hbot, Submodule.mem_bot] at hm
  exact h0 ((map_eq_zero_iff e (EquivLike.injective e)).mp hm)

private def dOf (i₀ : Fin n) (u : kˣ) : GL (Fin n) k :=
  ⟨diagonal (Function.update (fun _ => (1 : k)) i₀ u), diagonal (Function.update (fun _ => (1 : k)) i₀ (u⁻¹ : kˣ)),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      by_cases h : i = i₀
      · subst h; simp
      · simp [Function.update_of_ne h],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      by_cases h : i = i₀
      · subst h; simp
      · simp [Function.update_of_ne h]⟩

private theorem det_dOf (i₀ : Fin n) (u : kˣ) : GeneralLinearGroup.det (dOf i₀ u) = u := by
  ext
  simp [dOf, Matrix.GeneralLinearGroup.val_det_apply, det_diagonal, Finset.prod_update_of_mem]

private theorem dOf_mem {i₀ : Fin n} {u : kˣ} (hu : valuation k ((u : k) - 1) < 1) : dOf i₀ u ∈ KOne k (Fin n) := by
  rw [GlobalTheory.StepData.mem_KOne]
  unfold GlobalTheory.StepData.MaxM
  intro i j
  simp only [dOf, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h : i = i₀
    · subst h
      simpa using hu
    · simp [Function.update_of_ne h]
  · simp [hij]

private theorem dOf_comm (i₀ : Fin n) (u : kˣ) (μ : Fin n → ℤ) :
    dOf i₀ u * GroundTheory.Automorphic.Cartan.diagPow k n μ = GroundTheory.Automorphic.Cartan.diagPow k n μ * dOf i₀ u := by
  apply Units.ext
  simp only [Units.val_mul, GroundTheory.Automorphic.Cartan.coe_diagPow, dOf, diagonal_mul_diagonal, mul_comm]

end SlopeTestRemainingChoices

private theorem tame_of_dz {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (y : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (h0 : 0 < y.1) (hy : DZ y) (ht : DZ (y.tw χ hχ)) : TameChar χ := by
  classical
  unfold DZ at hy ht
  unfold TameChar
  intro u hu
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hy
  have ht' : fixed (twist y.rep (detChar (Fin y.fst) χ)) (KOne k (Fin y.fst)) ≠ ⊥ := by
    obtain ⟨w', hw', hw0'⟩ := (Submodule.ne_bot_iff _).mp ht
    exact fixed_ne_bot (y.twEquiv χ hχ).symm hw' hw0'
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp ht'
  set σ := twist y.rep (detChar (Fin y.fst) χ) with hσ
  set K := KOne k (Fin y.fst) with hK
  let i₀ : Fin y.fst := ⟨0, h0⟩
  have hd : dOf i₀ u ∈ K := dOf_mem hu
  set c : ℂ := ((χ u : ℂˣ) : ℂ) with hc
  have hc0 : c ≠ 0 := Units.ne_zero _
  have hc1 : c⁻¹ - 1 ≠ 0 := by
    intro h
    apply hne
    apply Units.ext
    rw [Units.val_one]
    exact inv_eq_one.mp (sub_eq_zero.mp h)
  have key : ∀ x ∈ fixed σ K, ∀ μ : Fin y.fst → ℤ,
      y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x ∈ twKer y.rep K 1 := by
    intro x hx μ
    rw [GlobalTheory.Parabolic.mem_fixed] at hx
    have hdx : c • y.rep (dOf i₀ u) x = x := by
      have h1 := hx (dOf i₀ u) hd
      rwa [hσ, twist_apply, detChar_apply, det_dOf] at h1
    have hdx' : y.rep (dOf i₀ u) x = c⁻¹ • x := by
      calc y.rep (dOf i₀ u) x = c⁻¹ • (c • y.rep (dOf i₀ u) x) := by
            rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • x := by rw [hdx]
    have hz : y.rep (dOf i₀ u) (y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x)
        = c⁻¹ • y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x := by
      rw [← Module.End.mul_apply, ← map_mul, dOf_comm, map_mul, Module.End.mul_apply, hdx', map_smul]
    have hgen : y.rep (dOf i₀ u) (y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x)
        - (((1 : ↥K →* ℂˣ) ⟨dOf i₀ u, hd⟩ : ℂˣ) : ℂ) • y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x
        ∈ twKer y.rep K 1 := by
      unfold twKer
      exact Submodule.subset_span ⟨⟨dOf i₀ u, hd⟩, _, rfl⟩
    rw [hz, MonoidHom.one_apply, Units.val_one, one_smul] at hgen
    rw [show ∀ z : y.snd.rep.V, c⁻¹ • z - z = (c⁻¹ - 1) • z from
      fun z => by rw [sub_smul, one_smul]] at hgen
    have h2 := Submodule.smul_mem _ (c⁻¹ - 1)⁻¹ hgen
    rwa [smul_smul, inv_mul_cancel₀ hc1, one_smul] at h2
  have hall : ∀ g, y.rep g w ∈ twKer y.rep K 1 := by
    intro g
    obtain ⟨μ, -, k1, hk1, k2, hk2, rfl⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagPow_mul k y.fst g
    rw [← GlobalTheory.CompanionTheory.SphSupp.KO_eq_integralGL] at hk1 hk2
    have hx := GlobalTheory.DepthZeroJac.apply_mem_fixed (π := σ) hw hk2
    have h3 := key _ hx μ
    rw [hσ, twist_apply, map_smul] at h3
    have h4 := Submodule.smul_mem _ (((detChar (Fin y.fst) χ) k2 : ℂˣ) : ℂ)⁻¹ h3
    rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h4
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact GlobalTheory.DepthZeroJac.apply_mem_twKer_of_normalizer (GlobalTheory.DepthZeroJac.mem_normalizer_KOne hk1) h4
  haveI : y.rep.IsIrreducible := y.snd.rep.irr
  have htop := GroundTheory.Automorphic.SchurOrthogonality.span_orbit_eq_top (π := y.rep) hw0
  have hvk : v ∈ twKer y.rep K 1 := by
    have h5 : v ∈ Submodule.span ℂ (Set.range fun g => y.rep g w) := by
      rw [htop]
      exact Submodule.mem_top
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hall g) h5
  exact hv0 (GlobalTheory.IwahoriInj.eq_zero_of_fixed y.snd.rep.smooth GlobalTheory.DepthZeroJac.isCompact_KOne hv hvk)

private theorem dz_of_tame {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (y : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hy : DZ y) (ht : TameChar χ) : DZ (y.tw χ hχ) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hy
  refine fixed_ne_bot (y.twEquiv χ hχ) (v := v) (GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_) hv0
  have h1 : χ (GeneralLinearGroup.det g) = 1 := ht _ (val_det_sub_one_lt (n := y.1) hg)
  rw [twist_apply, detChar_apply, h1]
  simpa using GlobalTheory.Parabolic.mem_fixed.1 hv g hg

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.twTame :
    UpperTheory.Zero.LLC.TwTame := by
  unfold TwTame
  intro k _ _ _ _ _ y χ hχ h0 hy
  exact ⟨fun ht => tame_of_dz y χ hχ h0 hy ht, fun ht => dz_of_tame y χ hχ hy ht⟩
end

section

open Finset

namespace UpperTheory.Zero.LLC.CharacterSumPairs

private def Reg (g n N t : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, (t * g ^ i) % N = (t * g ^ j) % N → i = j

private def Cl (g n N e t : ℕ) : Prop :=
  ∀ i < n, ∃ j < n, (t * g ^ i + e) % N = (t * g ^ j) % N

private instance (g n N t : ℕ) : Decidable (Reg g n N t) := by
  unfold Reg
  infer_instance

private instance (g n N e t : ℕ) : Decidable (Cl g n N e t) := by
  unfold Cl
  infer_instance

private def Pair (g n N e t t' : ℕ) : Prop :=
  (Reg g n N t ∧ Cl g n N e t) → (Reg g n N t' ∧ Cl g n N e t') → ∃ j < n, t' % N = (t * g ^ j) % N

private instance (g n N e t t' : ℕ) : Decidable (Pair g n N e t t') := by
  unfold Pair
  infer_instance

private theorem pairCheck_two_two : ∀ t < 2 ^ 2 - 1, ∀ t' < 2 ^ 2 - 1, Pair 2 2 (2 ^ 2 - 1) 1 t t' := by
  decide

private theorem pairCheck_three_two : ∀ t < 3 ^ 2 - 1, ∀ t' < 3 ^ 2 - 1, Pair 3 2 (3 ^ 2 - 1) 2 t t' := by
  decide


private theorem pairCheck_two_four : ∀ t < 2 ^ 4 - 1, ∀ t' < 2 ^ 4 - 1, Pair 2 4 (2 ^ 4 - 1) 3 t t' := by
  decide


private theorem pairCheck_two_six : ∀ t < 2 ^ 6 - 1, ∀ t' < 2 ^ 6 - 1, Pair 2 6 (2 ^ 6 - 1) 21 t t' := by
  decide

section

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem card_unitsK [Fintype Kˣ] (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) :
    Fintype.card Kˣ = g ^ n - 1 := by
  rw [Fintype.card_eq_nat_card, Nat.card_units, natCard_K hn hr]

private theorem exc (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (e : ℕ)
    (he : ∀ p ∈ n.primeFactors, (g ^ (n / p) - 1) ∣ e)
    (hcheck : ∀ t < g ^ n - 1, ∀ t' < g ^ n - 1, Pair g n (g ^ n - 1) e t t')
    (θ θ' : Kˣ →* ℂˣ)
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j)
    (hθ' : ∀ i j, i < n → j < n → θ' ^ g ^ i = θ' ^ g ^ j → i = j)
    (hs : ∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) :
    ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  haveI := fin_of hn hr
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  by_contra hne
  have hdisj := disj_cj hn hr θ θ' hne
  obtain ⟨D, hD1, hD2, -⟩ := exists_D (K := K) (g := g) hn hr
  have hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0 := by
    intro z hz
    unfold dif
    rw [sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]
  obtain ⟨η₀, hgen, hpow⟩ := exists_gen_char (G := Kˣ)
  have hcard := card_unitsK (K := K) (g := g) hn hr
  rw [hcard] at hgen hpow
  have key : ∀ s : ℕ, (∀ i j, i < n → j < n → (η₀ ^ s) ^ g ^ i = (η₀ ^ s) ^ g ^ j → i = j) →
      (∀ ψ ∈ cj g n (η₀ ^ s), ψ * η₀ ^ e ∈ cj g n (η₀ ^ s)) →
      Reg g n (g ^ n - 1) s ∧ Cl g n (g ^ n - 1) e s := by
    intro s hreg hcl
    unfold Reg Cl
    refine ⟨fun i hi j hj hij => hreg i j hi hj ?_, fun i hi => ?_⟩
    · rw [← pow_mul, ← pow_mul, hpow]
      exact hij
    · have hm : (η₀ ^ s) ^ g ^ i ∈ cj g n (η₀ ^ s) := mem_cj.2 ⟨i, hi, rfl⟩
      obtain ⟨j, hj, hjeq⟩ := mem_cj.1 (hcl _ hm)
      refine ⟨j, hj, ?_⟩
      rw [← pow_mul, ← pow_mul, ← pow_add, hpow] at hjeq
      exact hjeq.symm
  have hηD : ∀ z ∈ D, (η₀ ^ e) z = 1 := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := hD2 z hz
    obtain ⟨c, hc⟩ := he p hp
    rw [MonoidHom.pow_apply, ← map_pow, hc, pow_mul, hzp, one_pow, map_one]
  have hmm := mul_mem _ _ hdisj D hdif (η₀ ^ e) hηD
  obtain ⟨t, ht, rfl⟩ := hgen θ
  obtain ⟨t', ht', rfl⟩ := hgen θ'
  have hP := hcheck t ht t' ht'
  unfold Pair at hP
  obtain ⟨j, hj, hjt⟩ := hP (key t hθ (fun ψ hψ => (hmm ψ).1 hψ))
    (key t' hθ' (fun ψ hψ => (hmm ψ).2 hψ))
  exact hne ⟨j, hj, by rw [← pow_mul, hpow]; exact hjt⟩

private theorem main (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ)
    (hθ : ∀ i j, i < n → j < n → θ ^ g ^ i = θ ^ g ^ j → i = j) :
    (∃ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n ∧
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) ≠ 0) ∧
    ∀ θ' : Kˣ →* ℂˣ, (∀ i j, i < n → j < n → θ' ^ g ^ i = θ' ^ g ^ j → i = j) →
      (∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
        ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) = ∑ j ∈ range n, ((θ' (z ^ g ^ j) : ℂˣ) : ℂ)) →
      ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  haveI := fin_of hn hr
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hcard := card_unitsK (K := K) (g := g) hn hr
  obtain ⟨D, hD1, hD2, hDb⟩ := exists_D (K := K) (g := g) hn hr
  have hA := card_cj hθ
  refine ⟨?_, ?_⟩
  · by_contra hno
    push_neg at hno
    have hdif : ∀ z ∉ D, dif (cj g n θ) ∅ z = 0 := by
      intro z hz
      unfold dif
      rw [sum_cj hθ, hno z (hD1 z hz)]
      simp
    have hle := card_le (cj g n θ) ∅ (Finset.disjoint_empty_right _) D hdif (by simp [hA, hn])
    rw [hA, hcard] at hle
    simp only [Finset.card_empty, add_zero] at hle
    have h1 := one_bd g n hg2 hn
    have h2 : D.card * n ≤ n * bd g n := by
      rw [mul_comm n]
      exact Nat.mul_le_mul_right n hDb
    omega
  · intro θ' hθ' hs
    by_cases hex : g = 2 ∧ n = 2 ∨ g = 3 ∧ n = 2 ∨ g = 2 ∧ n = 4 ∨ g = 2 ∧ n = 6
    · rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine exc hn hr 1 ?_ pairCheck_two_two θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 2 ?_ pairCheck_three_two θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 3 ?_ pairCheck_two_four θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
      · refine exc hn hr 21 ?_ pairCheck_two_six θ θ' hθ hθ' hs
        intro p hp
        have h1 := Nat.le_of_mem_primeFactors hp
        have h2 := Nat.dvd_of_mem_primeFactors hp
        have h3 := (Nat.prime_of_mem_primeFactors hp).two_le
        interval_cases p <;> revert h2 <;> decide
    · by_contra hne
      have hB := card_cj hθ'
      have hdisj := disj_cj hn hr θ θ' hne
      have hdif : ∀ z ∉ D, dif (cj g n θ) (cj g n θ') z = 0 := by
        intro z hz
        unfold dif
        rw [sum_cj hθ, sum_cj hθ', hs z (hD1 z hz), sub_self]
      have hle := card_le _ _ hdisj D hdif (by rw [hA, hB]; omega)
      rw [hA, hB, hcard] at hle
      have h1 := two_bd g n hg2 hn hex
      have h2 : D.card * (n + n) ≤ 2 * n * bd g n := by
        calc D.card * (n + n) ≤ bd g n * (n + n) := Nat.mul_le_mul_right _ hDb
          _ = 2 * n * bd g n := by ring
      omega

end

end UpperTheory.Zero.LLC.CharacterSumPairs

theorem UpperTheory.Zero.LLC.pin :
    UpperTheory.Zero.LLC.Pin := by
  unfold UpperTheory.Zero.LLC.Pin
  intro g _ n hn K _ _ hr θ hθ
  exact UpperTheory.Zero.LLC.CharacterSumPairs.main hn hr θ hθ
end
