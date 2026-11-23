module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.CardOfIsFiniteLength
public import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)

private noncomputable def monoL (m : Fin k →₀ ℕ) : lat N m →ₗ[B] rees N where
  toFun f := mono N m f.1 f.2
  map_add' f g := Subtype.ext (by
    show MvPolynomial.monomial m (f.1 + g.1) = MvPolynomial.monomial m f.1 + MvPolynomial.monomial m g.1
    rw [map_add (f := _)])
  map_smul' c f := Subtype.ext (by
    show MvPolynomial.monomial m (c • f.1) = c • MvPolynomial.monomial m f.1
    rw [MvPolynomial.smul_monomial])

private theorem eq_mono {m : Fin k →₀ ℕ} {p : rees N} (hp : p ∈ reesGr N (toDeg m)) :
    p = mono N m (AddMonoidAlgebra.coeff p.1 m) (p.2 m) := by
  classical
  apply Subtype.ext
  ext n
  show _ = AddMonoidAlgebra.coeff (MvPolynomial.monomial m _) n
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · rw [h]
  · exact hp n fun h' => h (toDeg_injective h').symm

private theorem gr_eq_range (m : Fin k →₀ ℕ) : reesGr N (toDeg m) = LinearMap.range (monoL N m) := by
  apply le_antisymm
  · intro p hp
    exact ⟨⟨_, p.2 m⟩, (eq_mono N hp).symm⟩
  · rintro _ ⟨f, rfl⟩
    exact mono_mem N m f.1 f.2

private theorem e_eq (i : Fin k) : e i = toDeg (Finsupp.single i 1) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [e, toDeg]
  · simp [e, toDeg, Pi.single_apply, h, Finsupp.single_apply, Ne.symm h]

private theorem gr_add (m m' : Fin k →₀ ℕ) :
    reesGr N (toDeg (m + m')) = reesGr N (toDeg m) * reesGr N (toDeg m') := by
  apply le_antisymm
  · intro p hp
    have hf : AddMonoidAlgebra.coeff p.1 (m + m') ∈ lat N m * lat N m' := by
      rw [← lat_add]
      exact p.2 (m + m')
    obtain ⟨q, hq, hqv⟩ : ∃ q ∈ reesGr N (toDeg m) * reesGr N (toDeg m'),
        q.1 = MvPolynomial.monomial (m + m') (AddMonoidAlgebra.coeff p.1 (m + m')) := by
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb
        refine ⟨mono N m a ha * mono N m' b hb,
          Submodule.mul_mem_mul (mono_mem N m a ha) (mono_mem N m' b hb), ?_⟩
        show MvPolynomial.monomial m a * MvPolynomial.monomial m' b = _
        rw [MvPolynomial.monomial_mul]
      · rintro x y ⟨q₁, h₁, e₁⟩ ⟨q₂, h₂, e₂⟩
        refine ⟨q₁ + q₂, add_mem h₁ h₂, ?_⟩
        rw [map_add (f := _), ← e₁, ← e₂]
        rfl
    have hpq : p = q := by
      apply Subtype.ext
      rw [hqv]
      exact congrArg Subtype.val (eq_mono N hp)
    rw [hpq]
    exact hq
  · rw [Submodule.mul_le]
    intro a ha b hb
    have hab : AddMonoidAlgebra.coeff a.1 m * AddMonoidAlgebra.coeff b.1 m' ∈ lat N (m + m') := by
      rw [lat_add]
      exact Submodule.mul_mem_mul (a.2 m) (b.2 m')
    have h : a * b = mono N (m + m') _ hab := by
      apply Subtype.ext
      show a.1 * b.1 = MvPolynomial.monomial (m + m') _
      rw [← MvPolynomial.monomial_mul]
      exact congrArg₂ (· * ·) (congrArg Subtype.val (eq_mono N ha)) (congrArg Subtype.val (eq_mono N hb))
    rw [h]
    exact mono_mem N (m + m') _ hab

end

theorem UpperTheory.V.Alg.M.std_holds :
    ∀ (B A : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing A] [Algebra B A] (k : ℕ)
      (N : Fin k → Submodule B A), (∀ i, (N i).FG) → Std (reesGr N) := by
  intro B A _ _ hB _ _ k N hN
  have hdeg : ∀ d : Deg k, 0 ≤ d → ∃ m : Fin k →₀ ℕ, toDeg m = d := by
    intro d hd
    refine ⟨Finsupp.equivFunOnFinite.symm (fun j => (d j).toNat), ?_⟩
    funext j
    simp [toDeg, Int.toNat_of_nonneg (hd j)]
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · intro d hd
    refine (Submodule.eq_bot_iff _).2 fun p hp => ?_
    apply Subtype.ext
    ext m
    have hnn : 0 ≤ toDeg m := fun j => by simp [toDeg]
    have hm : toDeg m ≠ d := fun h => hd (h ▸ hnn)
    simpa using hp m hm
  · have h0 : (0 : Deg k) = toDeg 0 := by
      funext j
      simp [toDeg]
    rw [h0, gr_eq_range]
    ext p
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨⟨f, hf⟩, rfl⟩
      have hf' := hf
      rw [lat_zero, Submodule.mem_one] at hf'
      obtain ⟨b, hb⟩ := hf'
      refine ⟨b, Subtype.ext ?_⟩
      show algebraMap B (MvPolynomial (Fin k) A) b = MvPolynomial.monomial 0 f
      rw [MvPolynomial.algebraMap_apply, MvPolynomial.C_apply, hb]
    · rintro ⟨b, rfl⟩
      have hb : algebraMap B A b ∈ lat N 0 := by
        rw [lat_zero]
        exact Submodule.algebraMap_mem b
      refine ⟨⟨algebraMap B A b, hb⟩, Subtype.ext ?_⟩
      show MvPolynomial.monomial 0 (algebraMap B A b) = algebraMap B (MvPolynomial (Fin k) A) b
      rw [MvPolynomial.algebraMap_apply, MvPolynomial.C_apply]
  · intro i
    rw [e_eq, gr_eq_range, LinearMap.range_eq_map]
    refine Submodule.FG.map _ ((Submodule.fg_top _).2 ?_)
    rw [lat_single]
    exact hN i
  · intro d i hd
    obtain ⟨m, rfl⟩ := hdeg d hd
    rw [e_eq, ← toDeg_add, gr_add]
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.neg_weight_le {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    -Finsupp.weight wt ν ≤ ((Finsupp.weight (negW wt) ν : ℕ) : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : -wt i ≤ ((negW wt i : ℕ) : ℤ) := by
    simp only [negW]
    exact Int.self_le_toNat _
  have hc : (0 : ℤ) ≤ (ν i : ℤ) := Int.natCast_nonneg _
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  nlinarith

theorem UpperTheory.V.Alg.M.fil_holds :
    ∀ (E τ : Type) [CommRing E] (wt : τ → ℤ) (a b : ℕ) (g h : MvPowerSeries τ E), g ∈ fil E wt a → h ∈ fil E wt b →
      g * h ∈ fil E wt (a + b) ∧ ∀ j : ℤ, g ∈ wtPart E wt j → g ∈ fil E wt (-j).toNat := by
  intro E τ _ wt a b g h hg hh
  classical
  refine ⟨?_, ?_⟩
  · intro ν hν
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hw : Finsupp.weight (negW wt) p.1 + Finsupp.weight (negW wt) p.2 =
        Finsupp.weight (negW wt) ν := by
      rw [← hp, map_add (f := _)]
    by_cases h1 : Finsupp.weight (negW wt) p.1 < a
    · rw [hg p.1 h1, zero_mul]
    · rw [hh p.2 (by omega), mul_zero]
  · intro j hj ν hν
    by_contra hne
    have hwj : Finsupp.weight wt ν = j := by
      by_contra h'
      exact hne (hj ν h')
    have key := neg_weight_le wt ν
    rw [hwj] at key
    omega
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem satfil_wt {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    Finsupp.weight wt ν = (Finsupp.weight (posW wt) ν : ℤ) - (Finsupp.weight (negW wt) ν : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [posW, negW, nsmul_eq_mul, smul_eq_mul]
  push_cast
  rw [← mul_sub, Int.toNat_sub_toNat_neg]

private theorem satfil_deg {τ : Type} (wt : τ → ℤ) (h : ∀ i, wt i ≠ 0) (ν : τ →₀ ℕ) :
    Finsupp.degree ν ≤ Finsupp.weight (posW wt) ν + Finsupp.weight (negW wt) ν := by
  change (∑ i ∈ ν.support, ν i) ≤ _
  simp only [Finsupp.weight_apply, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : 1 ≤ posW wt i + negW wt i := by
    simp only [posW, negW]
    have := h i
    omega
  simp only [smul_eq_mul]
  nlinarith

theorem UpperTheory.V.Alg.M.satfil_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
      (∀ f ∈ 𝒜 (-1), f ∈ satSq x → φ f ∈ fil (FractionRing O) wt 2) ∧ ∀ b ∈ 𝒜 0, x b = 0 → φ b ∈ fil (FractionRing O) wt 1 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx τ _ wt φ hφ
  have hnz : ∀ i, wt i ≠ 0 := by
    intro i
    rcases hφ.wts i with h | h | h | h <;> omega
  have hlow : ∀ y ∈ RingHom.ker x ^ 2, ∀ ν : τ →₀ ℕ, Finsupp.degree ν ≤ 1 →
      MvPowerSeries.coeff ν (φ y) = 0 := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm n hn ν hν
      classical
      rw [map_mul, MvPowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hd : Finsupp.degree p.1 + Finsupp.degree p.2 ≤ 1 := by
        rw [← map_add (f := _), hp]
        exact hν
      have hm0 : MvPowerSeries.coeff 0 (φ m) = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, RingHom.mem_ker.mp hm, map_zero]
      have hn0 : MvPowerSeries.coeff 0 (φ n) = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, RingHom.mem_ker.mp hn, map_zero]
      by_cases h1 : Finsupp.degree p.1 = 0
      · rw [(Finsupp.degree_eq_zero_iff _).mp h1, hm0, zero_mul]
      · have h2 : Finsupp.degree p.2 = 0 := by omega
        rw [(Finsupp.degree_eq_zero_iff _).mp h2, hn0, mul_zero]
    · intro a b ha hb ν hν
      rw [map_add (f := _), map_add (f := _), ha ν hν, hb ν hν, add_zero]
  refine ⟨?_, ?_⟩
  · intro f hf hsat ν hν
    obtain ⟨c, hc, hcf⟩ := hsat
    by_contra hne
    have hw : Finsupp.weight wt ν = -1 := by
      by_contra h'
      exact hne (hφ.graded (-1) f hf ν h')
    have e := satfil_wt wt ν
    have hdeg := satfil_deg wt hnz ν
    have hd1 : Finsupp.degree ν ≤ 1 := by omega
    have h0 := hlow _ hcf ν hd1
    rw [map_smul, ← algebraMap_smul (FractionRing O) c (φ f), map_smul, smul_eq_mul] at h0
    have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
      intro hz
      exact hc (IsFractionRing.injective O (FractionRing O) (by rw [hz, map_zero]))
    exact hne ((mul_eq_zero.mp h0).resolve_left hc')
  · intro b hb hxb ν hν
    by_contra hne
    have hw : Finsupp.weight wt ν = 0 := by
      by_contra h'
      exact hne (hφ.graded 0 b hb ν h')
    have e := satfil_wt wt ν
    have hdeg := satfil_deg wt hnz ν
    have hd : Finsupp.degree ν = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).mp hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const, hxb,
      map_zero] at hne
    exact hne rfl
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem nz_coeff_mul {τ E : Type} [CommRing E] (i : τ) (f g : MvPowerSeries τ E)
    (hf : MvPowerSeries.constantCoeff f = 0) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd := congrArg Finsupp.degree h
  rw [map_add (f := _), Finsupp.degree_single] at hd
  by_cases h1 : Finsupp.degree p.1 = 0
  · rw [(Finsupp.degree_eq_zero_iff _).1 h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
  · have h2 : Finsupp.degree p.2 = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).1 h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, mul_zero]

private theorem nz_comp {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (wt : τ → ℤ)
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (h : IsChart0 𝒜 x wt φ) (i : τ) :
    ∃ f ∈ 𝒜 (wt i), MvPowerSeries.coeff (Finsupp.single i 1) (φ f) ≠ 0 := by
  classical
  obtain ⟨f, hf, -⟩ := h.onto i

  rw [← DirectSum.sum_support_decompose 𝒜 f, map_sum, map_sum] at hf
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hf
  have hm := (DirectSum.decompose 𝒜 f j).2
  have hw : wt i = j := by
    by_contra hne
    exact hj (h.graded j _ hm _ (by simpa [Finsupp.weight_single] using hne))
  exact ⟨_, hw ▸ hm, hj⟩

theorem UpperTheory.V.Alg.M.nz_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    1 ≤ Nat.card {i // wt i = -1} → 1 ≤ Nat.card {i // wt i = 1} → SpansCot x 𝒜 (-1) Q.F →
    ∀ a ∈ 𝒜 0, ∃ a' ∈ 𝒜 0, a' - a ∈ Q.ideal ∧ x a' = x a ∧ φ a' ≠ 0 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hn hp hS a ha
  by_cases h0 : φ a = 0
  swap
  · exact ⟨a, ha, by simp, rfl, h0⟩
  obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.1 hn).1
  obtain ⟨⟨i', hi'⟩⟩ := (Nat.card_pos_iff.1 hp).1
  obtain ⟨f, hf, hf0⟩ := nz_comp 𝒜 x wt φ hφ i
  obtain ⟨g, hg, hg0⟩ := nz_comp 𝒜 x wt φ hφ i'
  rw [hi] at hf
  rw [hi'] at hg
  have hg1 : φ g ≠ 0 := fun h => hg0 (by rw [h, map_zero])
  have hinj : ∀ c : O, c ≠ 0 → ∀ y : FractionRing O, c • y = 0 → y = 0 := fun c hc y hy => by
    rw [Algebra.smul_def] at hy
    exact (mul_eq_zero.1 hy).resolve_left fun h => hc (IsFractionRing.injective O _ (h.trans (map_zero _).symm))
  have hF : ∃ k, φ (Q.F k) ≠ 0 := by
    by_contra hall
    push Not at hall
    let L : A →ₗ[O] FractionRing O :=
      ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap
    have hL : ∀ y, L y = MvPowerSeries.coeff (Finsupp.single i 1) (φ y) := fun _ => rfl
    have hsq : ∀ y ∈ RingHom.ker x ^ 2, L y = 0 := by
      intro y hy
      rw [sq] at hy
      refine Submodule.mul_induction_on hy (fun u hu v hv => ?_) (fun u v hu hv => by rw [map_add (f := _), hu, hv, add_zero])
      have hu' : x u = 0 := hu
      have hv' : x v = 0 := hv
      rw [hL, map_mul]
      exact nz_coeff_mul _ _ _ (by rw [hφ.const, hu', map_zero]) (by rw [hφ.const, hv', map_zero])
    have hk : satSq x ≤ LinearMap.ker L := by
      rintro y ⟨c, hc, hy⟩
      have := hsq _ hy
      rw [map_smul] at this
      exact hinj c hc _ this
    have hsp : cotSpan x Q.F ≤ LinearMap.ker ((satSq x).liftQ L hk) := by
      rw [cotSpan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show L (Q.F k) = 0
      rw [hL, hall k, map_zero]
    obtain ⟨c, hc, hcf⟩ := hS ((satSq x).mkQ f) ⟨f, ⟨hf, hW.fixed (-1) (by norm_num) f hf⟩, rfl⟩
    have := hsp hcf
    rw [LinearMap.mem_ker, map_smul] at this
    exact hf0 (hinj c hc _ this)
  obtain ⟨k, hk⟩ := hF
  have hm : g * Q.F k ∈ 𝒜 0 := by simpa using SetLike.GradedMul.mul_mem hg (Q.hF k)
  refine ⟨a + g * Q.F k, add_mem ha hm, ?_, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [map_add (f := _), map_mul, hW.fixed 1 one_ne_zero g hg, zero_mul, add_zero]
  · rw [map_add (f := _), h0, zero_add, map_mul]
    exact mul_ne_zero hg1 hk
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem locLen_le_of_exact {O B K : Type} [CommRing O] [CommRing B] [Algebra O B] [Field K] [Algebra O K]
    (σ : B →ₐ[O] K) {M N P : Type} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (f : M →ₗ[B] N) (g : N →ₗ[B] P) (h : Function.Exact f g) :
    locLen σ N ≤ locLen σ M + locLen σ P := by
  haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
  exact Formalism.MainNotions.V.Pf.V2.length_le_of_exact (LocalizedModule.map (RingHom.ker σ).primeCompl f)
    (LocalizedModule.map (RingHom.ker σ).primeCompl g) (LocalizedModule.map_exact _ f g h)

theorem UpperTheory.V.Alg.M.locLen_aPiece_sup_span_sq_le_add :
    ∀ (O K A : Type) [CommRing O] [Field K] [Algebra O K] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
      (σ : 𝒜 0 →ₐ[O] K) (J : Ideal A), J.IsHomogeneous 𝒜 → ∀ (d : ℤ) (t : A), t ∈ 𝒜 d → ∀ w : ℤ,
      locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w) ≤
        locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t}) (w - d)) + locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t}) w) := by
  intro O K A _ _ _ _ _ 𝒜 _ σ J hJ d t ht w
  have h1 : J ⊔ Ideal.span {t} ≤ Submodule.comap (LinearMap.mulLeft A t) (J ⊔ Ideal.span {t ^ 2}) := by
    intro a ha
    obtain ⟨j, hj, b, hb, rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    show t * (j + c * t) ∈ J ⊔ Ideal.span {t ^ 2}
    rw [show t * (j + c * t) = t * j + c * t ^ 2 by ring]
    exact Submodule.add_mem_sup (J.mul_mem_left _ hj) (Ideal.mem_span_singleton'.2 ⟨c, rfl⟩)
  have h2 : J ⊔ Ideal.span {t ^ 2} ≤ Submodule.comap (LinearMap.id : A →ₗ[A] A) (J ⊔ Ideal.span {t}) :=
    sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self t two_ne_zero)) J
  let F : (A ⧸ (J ⊔ Ideal.span {t})) →ₗ[𝒜 0] A ⧸ (J ⊔ Ideal.span {t ^ 2}) :=
    (Submodule.mapQ _ _ (LinearMap.mulLeft A t) h1).restrictScalars (𝒜 0)
  let G : (A ⧸ (J ⊔ Ideal.span {t ^ 2})) →ₗ[𝒜 0] A ⧸ (J ⊔ Ideal.span {t}) :=
    (Submodule.mapQ _ _ (LinearMap.id : A →ₗ[A] A) h2).restrictScalars (𝒜 0)
  have hF : ∀ a : A, F (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (t * a) := fun a => rfl
  have hG : ∀ a : A, G (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := fun a => rfl
  have hF' : ∀ x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t}) (w - d), F x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨t * a, ?_, (hF a).symm⟩
    have := SetLike.GradedMul.mul_mem ht (show a ∈ 𝒜 (w - d) from ha)
    rwa [add_sub_cancel] at this
  have hG' : ∀ x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w, G x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t}) w := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (hG a).symm⟩
  refine locLen_le_of_exact σ (F.restrict hF') (G.restrict hG') ?_
  rintro ⟨_, a, ha, rfl⟩
  constructor
  · intro h
    have h0 : Ideal.Quotient.mk (J ⊔ Ideal.span {t}) a = 0 := congrArg Subtype.val h
    obtain ⟨j, hj, b, hb, hab⟩ := Submodule.mem_sup.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    have ha' : a ∈ 𝒜 w := ha
    have e1 : ((DirectSum.decompose 𝒜 (t * c)) (d + (w - d)) : A) = t * DirectSum.decompose 𝒜 c (w - d) :=
      DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 ht
    rw [add_sub_cancel] at e1
    have e2 : a = (DirectSum.decompose 𝒜 j w : A) + t * DirectSum.decompose 𝒜 c (w - d) := by
      rw [← e1, ← DirectSum.decompose_of_mem_same 𝒜 ha', ← hab, DirectSum.decompose_add, mul_comm c t]
      rfl
    refine ⟨⟨Ideal.Quotient.mk _ (DirectSum.decompose 𝒜 c (w - d) : A),
      ⟨_, (DirectSum.decompose 𝒜 c (w - d)).2, rfl⟩⟩, Subtype.ext ?_⟩
    show Ideal.Quotient.mk _ (t * (DirectSum.decompose 𝒜 c (w - d) : A)) = Ideal.Quotient.mk _ a
    rw [eq_comm, Ideal.Quotient.eq, e2, add_sub_cancel_right]
    exact Submodule.mem_sup_left (hJ w hj)
  · rintro ⟨⟨_, c, hc, rfl⟩, h⟩
    rw [← h]
    apply Subtype.ext
    show Ideal.Quotient.mk (J ⊔ Ideal.span {t}) (t * c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Submodule.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩))
end
