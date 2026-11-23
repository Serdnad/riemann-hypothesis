module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.GroupTheory.PGroup
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem inf_pow_bot (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (h : maximalIdeal R * I = ⊥) : ∃ N : ℕ, ∀ x ∈ I, x ∈ maximalIdeal R ^ N → x = 0 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (I : Submodule R R)
  refine ⟨k + 1, fun x hxI hxm => ?_⟩
  have hx : x ∈ maximalIdeal R ^ (k + 1) • (⊤ : Submodule R R) ⊓ (I : Submodule R R) := by
    refine ⟨?_, hxI⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hxm
  rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
  have hle : maximalIdeal R • (maximalIdeal R ^ k • (⊤ : Submodule R R) ⊓ (I : Submodule R R))
      ≤ maximalIdeal R • (I : Submodule R R) :=
    Submodule.smul_mono le_rfl inf_le_right
  have hx' := hle hx
  rw [Ideal.smul_eq_mul, h] at hx'
  exact (Submodule.mem_bot R).1 hx'

theorem UpperTheory.V.Fr.pr_sec :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C), Function.Surjective p → maximalIdeal C' * RingHom.ker p = ⊥ → ∀ (Γ : Type) [TopologicalSpace Γ] (x : Γ → C), AdicCont (maximalIdeal C) x → ∃ y : Γ → C', AdicCont (maximalIdeal C') y ∧ ∀ g, p (y g) = x g := by
  intro O _ _ C' _ _ _ C _ _ _ p hp hker Γ _ x hx
  have hmem : ∀ z : C', p z ∈ maximalIdeal C ↔ z ∈ maximalIdeal C' := by
    intro z
    rw [← res_eq_zero_iff O C, ← res_eq_zero_iff O C', res_map]
  have hmap : Ideal.map p (maximalIdeal C') = maximalIdeal C := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      exact (hmem z).2 hz
    · intro c hc
      obtain ⟨z, rfl⟩ := hp c
      exact Ideal.mem_map_of_mem p ((hmem z).1 hc)
  have hpow : ∀ n : ℕ, ∀ c ∈ maximalIdeal C ^ n, ∃ z ∈ maximalIdeal C' ^ n, p z = c := by
    intro n c hc
    rw [← hmap, ← Ideal.map_pow] at hc
    exact (Ideal.mem_map_iff_of_surjective p hp).1 hc
  haveI : IsNoetherianRing C' := IsCO.toIsNoetherian O
  obtain ⟨N₀, hN₀⟩ := inf_pow_bot C' (RingHom.ker p) hker
  have hq : Function.Surjective (fun z : C' => Ideal.Quotient.mk (maximalIdeal C ^ N₀) (p z)) :=
    Ideal.Quotient.mk_surjective.comp hp
  let σ := Function.surjInv hq
  have hσ : ∀ c : C, c - p (σ (Ideal.Quotient.mk _ c)) ∈ maximalIdeal C ^ N₀ := by
    intro c
    apply Ideal.Quotient.eq.1
    exact (Function.surjInv_eq hq (Ideal.Quotient.mk _ c)).symm
  have hw : ∀ c : C, ∃ w ∈ maximalIdeal C' ^ N₀, p w = c - p (σ (Ideal.Quotient.mk _ c)) :=
    fun c => hpow N₀ _ (hσ c)
  choose w hwm hwp using hw
  let s : C → C' := fun c => σ (Ideal.Quotient.mk (maximalIdeal C ^ N₀) c) + w c
  have hs : ∀ c, p (s c) = c := by
    intro c
    simp only [s, map_add (f := _), hwp]
    ring
  have hsd : ∀ n ≥ N₀, ∀ c₁ c₂ : C, c₁ - c₂ ∈ maximalIdeal C ^ n →
      s c₁ - s c₂ ∈ maximalIdeal C' ^ n := by
    intro n hn c₁ c₂ h
    have hcl : Ideal.Quotient.mk (maximalIdeal C ^ N₀) c₁ = Ideal.Quotient.mk _ c₂ :=
      Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right hn h)
    obtain ⟨z, hz, hpz⟩ := hpow n _ h
    have hdiff : s c₁ - s c₂ = w c₁ - w c₂ := by
      simp only [s, hcl]
      ring
    have hz0 : (s c₁ - s c₂) - z = 0 := by
      apply hN₀
      · rw [RingHom.mem_ker]
        simp [map_sub, hs, hpz]
      · rw [hdiff]
        exact sub_mem (sub_mem (hwm c₁) (hwm c₂)) (Ideal.pow_le_pow_right hn hz)
    rw [sub_eq_zero.1 hz0]
    exact hz
  refine ⟨fun g => s (x g), ?_, fun g => hs (x g)⟩
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hxl := (IsLocallyConstant.iff_eventually_eq _).1 (hx (max n N₀)) g
  filter_upwards [hxl] with g' hg'
  apply Ideal.Quotient.eq.2
  exact Ideal.pow_le_pow_right (le_max_left n N₀)
    (hsd _ (le_max_right _ _) _ _ (Ideal.Quotient.eq.1 hg'))
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_dualb :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Ideal C) (κ : Type) [Fintype κ] (ε : κ → C), maximalIdeal C * K = ⊥ → K = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) → ∃ co : κ → K →ₗ[O] ResidueField O, ∀ y : K, ∃ a : κ → O, (∀ u, residue O (a u) = co u y) ∧ (y : C) = ∑ u, a u • ε u := by
  intro O _ _ C _ _ _ K κ _ ε hK hspan hind
  have hε : ∀ u, ε u ∈ K := fun u => by
    rw [hspan]; exact Ideal.subset_span ⟨u, rfl⟩
  have hex : ∀ y : K, ∃ a : κ → O, (y : C) = ∑ u, a u • ε u := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Ideal.span (Set.range ε) := hspan ▸ hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy'
    choose a ha using fun u => IsCO.res_surj (O := O) (c u)
    refine ⟨a, ?_⟩
    show y = _
    rw [← hc]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h0 : (c u - algebraMap O C (a u)) * ε u ∈ maximalIdeal C * K :=
      Ideal.mul_mem_mul (ha u) (hε u)
    rw [hK, Ideal.mem_bot, sub_mul, sub_eq_zero] at h0
    rw [h0, Algebra.smul_def]
  have huniq : ∀ a b : κ → O, ∑ u, a u • ε u = ∑ u, b u • ε u →
      ∀ u, residue O (a u) = residue O (b u) := by
    intro a b hab u
    have h := hind (fun u => a u - b u) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hab, sub_self]) u
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact h
  choose a ha using hex
  refine ⟨fun u =>
    { toFun := fun y => residue O (a y u)
      map_add' := fun x y => ?_
      map_smul' := fun c x => ?_ }, fun y => ⟨a y, fun u => rfl, ha y⟩⟩
  · rw [← map_add (f := _)]
    refine huniq (a (x + y)) (fun u => a x u + a y u) ?_ u
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← ha, ← ha, ← ha]
    rfl
  · have h := huniq (a (c • x)) (fun u => c * a x u) (by
      simp only [mul_smul, ← Finset.smul_sum]
      rw [← ha, ← ha]
      rfl) u
    rw [h, RingHom.id_apply, map_mul, Algebra.smul_def]
    rfl
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.adic_char_unipotent_pgroup_quotient :
    ∀ {l : ℕ} [Fact l.Prime] {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] [IsNoetherianRing Q] [CharP Q l] [Finite (ResidueField Q)] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* Q) (h : ℕ), h ≠ 0 → AdicCont (maximalIdeal Q) χ → (∀ g, χ g - 1 ∈ maximalIdeal Q) → (∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ ψ : G →* A, IsOpen (ψ.ker : Set G) → (∀ g g', χ g = χ g' → ψ g = ψ g') → ∀ g, ψ g ^ h = 1) → ∀ g, χ g = 1 := by
  intro l hl Q _ _ _ _ _ hfin G _ _ χ h hh hc hm H g
  have hp : l.Prime := hl.out
  have krull : ∀ x : Q, (∀ N : ℕ, Ideal.Quotient.mk (maximalIdeal Q ^ N) x = 1) → x = 1 := by
    intro x hx
    have h0 : x - 1 ∈ (⨅ N : ℕ, maximalIdeal Q ^ N) := by
      rw [Ideal.mem_iInf]
      intro N
      rw [← Ideal.Quotient.eq, hx N, map_one]
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal Q).ne_top, Ideal.mem_bot] at h0
    exact sub_eq_zero.mp h0
  have unip : ∀ (N : ℕ) (g : G), Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g) ^ (l ^ N) = 1 := by
    intro N g
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (maximalIdeal Q ^ N)), Ideal.Quotient.eq]
    have : χ g ^ l ^ N - 1 = (χ g - 1) ^ l ^ N := by rw [sub_pow_char_pow, one_pow]
    rw [this]
    exact Ideal.pow_le_pow_right (Nat.lt_pow_self hp.one_lt).le (Ideal.pow_mem_pow (hm g) _)
  have hpow : χ g ^ h = 1 := by
    apply krull
    intro N
    haveI : Finite (Q ⧸ maximalIdeal Q) := hfin
    haveI : Finite (Q ⧸ maximalIdeal Q ^ N) :=
      Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
    let φ : G →* (Q ⧸ maximalIdeal Q ^ N)ˣ :=
      ((Ideal.Quotient.mk (maximalIdeal Q ^ N)).toMonoidHom.comp χ).toHomUnits
    have hφ : ∀ g, (φ g : Q ⧸ maximalIdeal Q ^ N) = Ideal.Quotient.mk _ (χ g) := fun g => rfl
    have hP : IsPGroup l φ.range := by
      rintro ⟨_, g, rfl⟩
      refine ⟨N, Subtype.ext (Units.ext ?_)⟩
      simpa [hφ] using unip N g
    have hO : IsOpen (φ.rangeRestrict.ker : Set G) := by
      have := (hc N).isOpen_fiber 1
      convert this using 1
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq]
      rw [← hφ, Units.val_eq_one, Subtype.ext_iff]
      rfl
    have := H φ.range hP φ.rangeRestrict hO
      (fun g g' e => Subtype.ext (Units.ext (by
        change (φ g : Q ⧸ maximalIdeal Q ^ N) = φ g'
        rw [hφ, hφ, e]))) g
    have h2 : φ g ^ h = 1 := congrArg Subtype.val this
    rw [map_pow, ← hφ, ← Units.val_pow_eq_pow_val, h2, Units.val_one]
  obtain ⟨a, h', hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hh l hp.ne_one
  have h3 : χ g ^ h' = 1 := by
    have : (χ g ^ h' - 1) ^ l ^ a = 0 := by
      rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, hpow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ hp.ne_zero) |>.mp this)
  apply krull
  intro N
  have h4 : Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g) ^ h' = 1 := by
    rw [← map_pow, h3, map_one]
  have hcop : Nat.Coprime (l ^ N) h' := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have h5 : orderOf (Ideal.Quotient.mk (maximalIdeal Q ^ N) (χ g)) ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (unip N g)) (orderOf_dvd_of_pow_eq_one h4)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
end
