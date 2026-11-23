module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.card_dvd_of_partition_equal_size :
    ∀ (ι Q : Type) [Finite ι] (T : Q → Set ι) (d : ℕ), (∀ q, (T q).ncard = d) → (∀ i, ∃! q, i ∈ T q) →
      Nat.card Q ∣ Nat.card ι := by
  intro ι Q _ T d hT hu
  classical
  choose f hf hf' using hu
  have hfib : ∀ q, T q = {i | f i = q} := by
    intro q
    ext i
    constructor
    · intro h
      exact (hf' i q h).symm
    · intro h
      rw [Set.mem_setOf_eq] at h
      rw [← h]
      exact hf i
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : IsEmpty ι := ⟨fun i => by
      have h := hT (f i)
      rw [Set.ncard_eq_zero (Set.toFinite _)] at h
      have hi : i ∈ T (f i) := hf i
      rw [h] at hi
      simp at hi⟩
    rw [Nat.card_of_isEmpty (α := ι)]
    exact dvd_zero _
  · have hne : ∀ q, (T q).Nonempty := fun q =>
      Set.nonempty_of_ncard_ne_zero (by rw [hT q]; omega)
    choose g hg using hne
    have ginj : Function.Injective g := by
      intro q q' h
      calc q = f (g q) := hf' _ _ (hg q)
        _ = f (g q') := by rw [h]
        _ = q' := (hf' _ _ (hg q')).symm
    haveI : Finite Q := Finite.of_injective g ginj
    letI : Fintype Q := Fintype.ofFinite Q
    have hc : ∀ q, Nat.card {x // f x = q} = d := fun q => by
      rw [← hT q, hfib q, ← Nat.card_coe_set_eq]
      rfl
    have key : Nat.card ι = Nat.card Q * d := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
      simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    rw [key]
    exact dvd_mul_right _ _
end

section

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
      (Z : Subgroup G) (P : G → Prop), (∀ V : Subgroup Z, V.FiniteIndex → ∀ σ : Z, ∃ g ∈ V, P (σ * g : Z)) →
      ∀ U : Set G, IsOpen U → (U ∩ (Z : Set G)).Nonempty → ∃ σ ∈ U ∩ (Z : Set G), P σ := by
  intro G _ _ _ _ _ Z P h U hU hne
  obtain ⟨σ, hσU, hσZ⟩ := hne
  have hW : IsOpen ((fun x : G => σ * x) ⁻¹' U) := hU.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : G) ∈ ((fun x : G => σ * x) ⁻¹' U) := by simpa using hσU
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1
  have hfi : (N.toSubgroup).FiniteIndex := by
    have := Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨g, hg, hP⟩ := h (N.toSubgroup.subgroupOf Z) inferInstance ⟨σ, hσZ⟩
  refine ⟨_, ⟨?_, ((⟨σ, hσZ⟩ : Z) * g).2⟩, hP⟩
  exact hN (show (g : G) ∈ N.toSubgroup from hg)
end

section

open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem UpperTheory.V.Ws.tendsto_pow_prime_pow_one (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) (hx : ¬ IsUnit (x - 1)) :
    Filter.Tendsto (fun n : ℕ => x ^ l ^ n) Filter.atTop (nhds 1) := by
  have hd : (l : ℤ_[l]) ∣ x - 1 :=
    (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.mem_nonunits.mp (mem_nonunits_iff.mpr hx))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n : ℕ, ‖x ^ l ^ n - 1‖ ≤ ((l : ℝ)⁻¹) ^ (n + 1) := by
    intro n
    obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub hd n
    rw [one_pow] at hc
    rw [hc, norm_mul, norm_pow, PadicInt.norm_p]
    calc _ ≤ (l : ℝ)⁻¹ ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) (by positivity)
      _ = _ := mul_one _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ (n + 1)) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    exact this.comp (Filter.tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun n => norm_nonneg _) hb h0

theorem UpperTheory.V.Ws.sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
      (ε : G →* ℤ_[l]ˣ), Continuous ε → ∀ η : G →* ℤˣ, IsOpen (η.ker : Set G) → ε.ker ≤ η.ker →
      ∀ g, ¬ IsUnit ((ε g : ℤ_[l]) - 1) → η g = 1 := by
  intro l _ hl2 G _ _ _ _ ε hε η hopen hker g hg
  rcases Int.units_eq_one_or (η g) with h | h
  · exact h
  exfalso
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two hl2
  let C : Set G := ((η.ker : Set G))ᶜ
  have hCc : IsCompact C := (isClosed_compl_iff.mpr hopen).isCompact
  let f : G → ℤ_[l] := fun h => (ε h : ℤ_[l])
  have hf : Continuous f := Units.continuous_val.comp hε
  have hK : IsClosed (f '' C) := (hCc.image hf).isClosed
  have hmem : ∀ n : ℕ, f (g ^ l ^ n) ∈ f '' C := by
    intro n
    refine ⟨g ^ l ^ n, ?_, rfl⟩
    show g ^ l ^ n ∉ η.ker
    rw [MonoidHom.mem_ker, map_pow, h, (hodd.pow).neg_one_pow]
    decide
  have hlim : Filter.Tendsto (fun n : ℕ => f (g ^ l ^ n)) Filter.atTop (nhds 1) := by
    have := tendsto_pow_prime_pow_one l (ε g : ℤ_[l]) hg
    refine this.congr fun n => ?_
    simp [f, map_pow]
  have h1 : (1 : ℤ_[l]) ∈ f '' C := hK.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  obtain ⟨k, hkC, hk1⟩ := h1
  apply hkC
  apply hker
  rw [MonoidHom.mem_ker]
  exact Units.ext hk1
end
