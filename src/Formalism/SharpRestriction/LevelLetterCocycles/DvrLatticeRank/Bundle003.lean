module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfB
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfA
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem unit_comp (w : (LetA O n)ˣ) (i : ZMod n) :
    (w : LetA O n) i * ((w⁻¹ : (LetA O n)ˣ) : LetA O n) i = 1 := by
  exact congrFun (Units.mul_inv w) i

theorem π_at (s' : ℕ) (π' : LetA O n) (w₁ : (LetA O n)ˣ) (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (i : ZMod n) :
    π' i = (w₁ : LetA O n) i * PowerSeries.X ^ s' := by
  rw [hπ]
  rfl

theorem hlet_of [IsDomain O] (s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n) (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (hπΔ : π' ∈ W.AΔ) (hπu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (c : ZMod n) :
    ∀ a : O, a ≠ 0 → ∀ u : W.EE,
      (∃ g ∈ W.AΔ, algebraMap (LetA O n) W.EE π' * u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) →
      (∃ g ∈ W.AΔ, a • u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) →
      ∃ g ∈ W.AΔ, u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g) := by
  rintro a ha u ⟨g, hg, hgu⟩ ⟨h, hh, hhu⟩
  have hA : π' * ((letE c : LetA O n) * h) = algebraMap O (LetA O n) a * ((letE c : LetA O n) * g) := by
    apply W.EE_inj
    calc algebraMap (LetA O n) W.EE (π' * ((letE c : LetA O n) * h))
        = algebraMap (LetA O n) W.EE π' * algebraMap (LetA O n) W.EE ((letE c : LetA O n) * h) := map_mul _ _ _
      _ = algebraMap (LetA O n) W.EE π' * (a • u) := by rw [hhu]
      _ = a • (algebraMap (LetA O n) W.EE π' * u) := by rw [mul_smul_comm]
      _ = a • algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g) := by rw [hgu]
      _ = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) a * ((letE c : LetA O n) * g)) := by
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, ← map_mul]
  have hc : π' c * h c = a • g c := by
    have := congrFun hA c
    rw [Algebra.smul_def]
    simpa [letE] using this
  have hdvd : PowerSeries.X ^ s' ∣ g c := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    have h1 := congrArg (PowerSeries.coeff m) hc
    rw [π_at s' π' w₁ hπ c, mul_comm ((w₁ : LetA O n) c), mul_assoc, PowerSeries.coeff_X_pow_mul',
      if_neg (by omega), map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left ha
  obtain ⟨G', hG'⟩ := hdvd
  set g' : LetA O n := (letE c : LetA O n) * (fun _ => ((w₁⁻¹ : (LetA O n)ˣ) : LetA O n) c * G') with hg'
  have hπg' : π' * g' = (letE c : LetA O n) * g := by
    funext i
    by_cases hi : i = c
    · subst hi
      simp only [Pi.mul_apply, hg', letE, Pi.single_eq_same, one_mul]
      rw [π_at s' π' w₁ hπ i, hG']
      linear_combination (PowerSeries.X ^ s' * G') * unit_comp w₁ i
    · simp [hg', letE, Pi.single_apply, hi]
  have hcancel : ∀ x y : LetA O n, π' * x = π' * y → x = y := by
    intro x y hxy
    funext i
    have hxi := congrFun hxy i
    simp only [Pi.mul_apply] at hxi
    rw [π_at s' π' w₁ hπ i] at hxi
    have hne : (w₁ : LetA O n) i * PowerSeries.X ^ s' ≠ 0 := by
      have hw : (w₁ : LetA O n) i ≠ 0 := by
        intro h0
        have := unit_comp w₁ i
        rw [h0, zero_mul] at this
        exact zero_ne_one this
      exact mul_ne_zero hw (pow_ne_zero _ PowerSeries.X_ne_zero)
    exact mul_left_cancel₀ hne hxi
  have hπΔ' : ∀ δ ∈ W.DelF, W.γA δ π' = π' := hπΔ
  have hm : (letE c : LetA O n) * g ∈ W.AΔ := mul_mem (letE_mem W c) hg
  have hm' : ∀ δ ∈ W.DelF, W.γA δ ((letE c : LetA O n) * g) = (letE c : LetA O n) * g := hm
  have hg'Δ : g' ∈ W.AΔ := by
    show ∀ δ ∈ W.DelF, W.γA δ g' = g'
    intro δ hδ
    apply hcancel
    calc π' * W.γA δ g' = W.γA δ π' * W.γA δ g' := by rw [hπΔ' δ hδ]
      _ = W.γA δ (π' * g') := (map_mul _ _ _).symm
      _ = W.γA δ ((letE c : LetA O n) * g) := by rw [hπg']
      _ = (letE c : LetA O n) * g := hm' δ hδ
      _ = π' * g' := hπg'.symm
  refine ⟨g', hg'Δ, ?_⟩
  have hle : (letE c : LetA O n) * g' = g' := by rw [hg', ← mul_assoc, letE_mul_self']
  rw [hle]
  exact hπu.mul_left_cancel (by rw [hgu, ← hπg', map_mul])

theorem q_unit (hp : PD.p.Prime) : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
  exact Formalism.MainNotions.LiftingTheory.liftb_q_unit W

end Formalism.MainNotions.N.Ln34.MQ
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.FrobeniusSpanLemma

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.LiftingTheory

section PhiB

variable {O : Type} [CommRing O]

end PhiB

section PhiBW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end PhiBW

section PhiBC

theorem phib_smodeq {M : Type} [CommRing M] (c x y : M) (k : ℕ) :
    x ≡ y [SMOD ((Ideal.span {c}) ^ k • ⊤ : Submodule M M)] ↔ c ^ k ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem phib_complete {R M : Type} [CommRing R] [CommRing M] [Algebra R M] (ϖ : R)
    [IsAdicComplete (Ideal.span {ϖ}) R] {ι : Type} [Fintype ι] (b : Module.Basis ι R M) :
    IsAdicComplete (Ideal.span {algebraMap R M ϖ}) M := by
  apply (config := { allowSynthFailures := true }) Formalism.MainNotions.LiftingTheory.phib_complete <;> assumption

theorem phib_OL_complete {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsAdicComplete (Ideal.span {((l : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
  have h1 : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h2 : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 :=
    inferInstanceAs (IsIntegralClosure ↥(integralClosure ℤ_[l] ↥LL.1) ℤ_[l] ↥LL.1)
  have h3 : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  have h4 : Module.IsTorsionFree ℤ_[l] ↥(OL LL) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (zl_inj_O LL)
  have h5 : Module.Free ℤ_[l] ↥(OL LL) := Module.free_of_finite_type_torsion_free'
  have h6 : IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have h7 := phib_complete ((l : ℕ) : ℤ_[l]) (Module.finBasis ℤ_[l] ↥(OL LL))
  rwa [map_natCast] at h7

end PhiBC

section PhiI1

variable {O : Type} [CommRing O]

end PhiI1

section PhiI2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end PhiI2

section PhiI3

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end PhiI3

end Formalism.MainNotions.N.Ln34.FrobeniusSpanLemma

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CyclotomicLifting

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem fix_of_mem_GK {K : FinExt l} {σ : GQ l} (hσ : σ ∈ GK K) {x : Om l} (hx : x ∈ K.1) :
    σ x = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx

theorem Ks_stable (K : FinExt l) {σ : GQ l} (hσ : σ ∈ GK K) {x : Om l} (hx : x ∈ Ks K 1) :
    σ x ∈ Ks K 1 := by
  have hle : Ks K 1 ≤ (Ks K 1).map (σ.symm : Om l ≃ₐ[ℚ_[l]] Om l).toAlgHom := by
    unfold Ks
    refine sup_le ?_ ?_
    · intro y hy
      refine (IntermediateField.mem_map _).2 ⟨y, (le_sup_left : K0 K ≤ _) hy, ?_⟩
      have h1 : σ y = y := fix_of_mem_GK hσ (inf_le_left (a := K.1) (b := MaximalUnramifiedExtension l) hy)
      show σ.symm y = y
      rw [AlgEquiv.symm_apply_eq]
      exact h1.symm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      refine (IntermediateField.mem_map _).2 ⟨σ y, ?_, by simp⟩
      apply (le_sup_right : _ ≤ K0 K ⊔ _)
      apply IntermediateField.subset_adjoin
      show (σ y) ^ (l ^ 1) = 1
      rw [← map_pow, show y ^ (l ^ 1) = 1 from hy, map_one]
  obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).1 (hle hx)
  have hyx' : σ.symm y = x := hyx
  rw [← hyx', AlgEquiv.apply_symm_apply]
  exact hy

theorem GKin_normal (K : FinExt l) (hKK : K.1 ≤ (cycL K).1) : (GKin hKK).Normal := by
  constructor
  intro n hn g
  rw [GKin, Subgroup.mem_subgroupOf] at hn ⊢
  rw [GK, IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  have h1 : ((g : GQ l)⁻¹) x ∈ Ks K 1 := Ks_stable K (inv_mem g.2) hx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply]
  rw [hn _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem range_inclusion_eq (K : FinExt l) (hKK : K.1 ≤ (cycL K).1) (hle : GK (cycL K) ≤ GK K) :
    (Subgroup.inclusion hle).range = GKin hKK := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Subgroup.mem_subgroupOf.2 y.2
  · intro hx
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩

theorem chi_cong (P : LocPrime l) (K : FinExt l) (g : GQ l) (hg : g ∈ GK (cycL K)) :
    ‖(P.χQ g : ℚ_[l]) - 1‖ ≤ (l : ℝ)⁻¹ := by
  have hp : l.Prime := Fact.out
  have hζl : P.ζQ 1 ^ (l ^ 1) = 1 := by
    have := P.ζQ_succ 0
    rw [P.ζQ_zero] at this
    simpa using this
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g 1 (P.ζQ 1) hζl
  have hζK : P.ζQ 1 ∈ (cycL K).1 :=
    (le_sup_right : _ ≤ K0 K ⊔ _) (IntermediateField.subset_adjoin _ _ hζl)
  have hfix : g (P.ζQ 1) = P.ζQ 1 := fix_of_mem_GK hg hζK
  have hord : orderOf (P.ζQ 1) = l := orderOf_eq_prime (by simpa using hζl) P.ζQ_one
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      apply P.ζQ_one
      have h2 : P.ζQ 1 ^ 0 = P.ζQ 1 ^ 1 := by rw [pow_one, ← hga, hfix]
      rw [pow_zero, pow_one] at h2
      exact h2.symm
    · exact h
  have hζ0 : P.ζQ 1 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_pos hp.pos 1).ne'] at hζl
    exact zero_ne_one hζl
  have h3 : P.ζQ 1 ^ (a - 1) = 1 := by
    have h4 : P.ζQ 1 ^ (a - 1) * P.ζQ 1 = 1 * P.ζQ 1 := by
      rw [← pow_succ, Nat.sub_add_cancel ha1, one_mul, ← hga, hfix]
    exact mul_right_cancel₀ hζ0 h4
  have hdvdN : l ∣ a - 1 := hord ▸ orderOf_dvd_of_pow_eq_one h3
  have hdvdN1 : l ^ 1 ∣ a - 1 := by rw [pow_one]; exact hdvdN
  have hcast : (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) := by omega
  have h1 := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - 1) 1).2
    (by rw [hcast]; exact_mod_cast hdvdN1)
  have e : (P.χQ g : ℚ_[l]) - 1 = ((P.χQ g : ℚ_[l]) - (a : ℚ_[l])) + (((a : ℤ) - 1 : ℤ) : ℚ_[l]) := by
    push_cast; ring
  rw [e]
  refine ((Padic.nonarchimedean _ _).trans (max_le ha h1)).trans (le_of_eq ?_)
  simp

theorem v_ge_one (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (hx : ‖x‖ ≤ (l : ℝ)⁻¹) :
    (1 : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hy : ‖x / l‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p, div_le_one (inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos))]
    exact hx
  have hxy : x = (l : ℚ_[l]) * (x / l) := by field_simp
  have hyO : algebraMap ℚ_[l] ↥LL.1 (x / l) ∈ OL LL := by
    obtain ⟨y, hy'⟩ : ∃ y : ℤ_[l], (y : ℚ_[l]) = x / l := ⟨⟨x / l, hy⟩, rfl⟩
    rw [← hy', show (y : ℚ_[l]) = algebraMap ℤ_[l] ℚ_[l] y from rfl,
      ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  rw [hxy, map_mul, map_natCast, AddValuation.map_mul, P.v_l LL]
  exact le_add_of_nonneg_right ((P.v_O LL _).2 hyO)

theorem FildR_succ_le (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) :
    FildR (P.PD K) T.ρ τ (a + 1) ≤ FildR (P.PD K) T.ρ τ a := by
  unfold FildR FilV
  refine inf_le_inf_left _ ?_
  have hle : ((P.PD K).Fil (a + 1)).restrictScalars ℚ_[l] ≤ ((P.PD K).Fil a).restrictScalars ℚ_[l] :=
    fun x hx => (P.PD K).Fil_anti a hx
  rintro x ⟨y, rfl⟩
  exact ⟨TensorProduct.AlgebraTensorModule.map LinearMap.id (Submodule.inclusion hle) y, by
    rw [← LinearMap.comp_apply, ← TensorProduct.AlgebraTensorModule.map_comp]
    rfl⟩

theorem multV_ne_zero (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ)
    (hfd : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) T.ρ τ)) (hj : IsJumpV (P.PD K) T.ρ τ a) :
    multV (P.PD K) T.ρ τ a ≠ 0 := by
  unfold multV
  have hle := FildR_succ_le P K LL T τ a
  have hlt : FildR (P.PD K) T.ρ τ (a + 1) < FildR (P.PD K) T.ρ τ a := lt_of_le_of_ne hle hj
  haveI := hfd
  haveI : FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) T.ρ τ a) := Submodule.finiteDimensional_of_le inf_le_left
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

theorem isJump_of_multV (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ)
    (h : multV (P.PD K) T.ρ τ a ≠ 0) : IsJumpV (P.PD K) T.ρ τ a := by
  intro he
  apply h
  unfold multV
  rw [he]
  simp

end Formalism.MainNotions.N.Ln34.CyclotomicLifting

end
end
