module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.SemistableReduction.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsLocalRing

theorem Op_isDVR {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (Op D N la) := by
  classical
  set P := laT D N la with hP
  have hp0 : la.asIdeal ≠ ⊥ := la.ne_bot
  have hp1 : la.asIdeal ≠ ⊤ := la.isPrime.ne_top

  obtain ⟨π, hπp, hπ2⟩ : ∃ π ∈ la.asIdeal, π ∉ la.asIdeal ^ 2 := by
    have hlt : la.asIdeal ^ 2 < la.asIdeal ^ 1 :=
      Ideal.pow_right_strictAnti la.asIdeal hp0 hp1 (by norm_num : 1 < 2)
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx2⟩
  have hmemP : ∀ t : 𝓞 K, MvPolynomial.C t ∈ P ↔ t ∈ la.asIdeal := by
    intro t
    rw [hP, laT, MvPolynomial.mem_map_C_iff]
    constructor
    · intro h
      simpa using h 0
    · intro h m
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact h
      · exact zero_mem _

  have hdiv : ∀ a ∈ la.asIdeal, ∃ t c : 𝓞 K, t ∉ la.asIdeal ∧ t * a = π * c := by
    intro a ha
    have hle : Ideal.span {π} ≤ la.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hπp
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    have hJp : ¬ J ≤ la.asIdeal := by
      intro hJle
      apply hπ2
      have hsq : Ideal.span {π} ≤ la.asIdeal ^ 2 := by
        rw [hJ, pow_two]
        exact Ideal.mul_mono_right hJle
      exact hsq (Ideal.mem_span_singleton_self π)
    obtain ⟨t, htJ, htp⟩ := SetLike.not_le_iff_exists.mp hJp
    have hta : t * a ∈ Ideal.span {π} := by
      rw [hJ, mul_comm t a]
      exact Ideal.mul_mem_mul ha htJ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hta
    exact ⟨t, c, htp, by rw [← hc, mul_comm]⟩
  haveI : IsNoetherianRing (Op D N la) :=
    IsLocalization.isNoetherianRing P.primeCompl (Op D N la) inferInstance
  let f : 𝓞 K →+* Op D N la := (algebraMap (OT K D N) (Op D N la)).comp MvPolynomial.C
  have hmax : IsLocalRing.maximalIdeal (Op D N la) = Ideal.map f la.asIdeal := by
    have e : Ideal.map f la.asIdeal =
        Ideal.map (algebraMap (OT K D N) (Op D N la)) (laT D N la) :=
      (Ideal.map_map (MvPolynomial.C : 𝓞 K →+* OT K D N) (algebraMap (OT K D N) (Op D N la))).symm
    rw [e]
    exact (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hπm : IsLocalRing.maximalIdeal (Op D N la) = Ideal.span {f π} := by
    apply le_antisymm
    · rw [hmax, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      obtain ⟨t, c, htp, htc⟩ := hdiv a ha
      have hu : IsUnit (f t) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (Op D N la) P (MvPolynomial.C t)).mpr
          (fun h => htp ((hmemP t).mp h))
      obtain ⟨u, hu'⟩ := hu
      rw [Ideal.mem_span_singleton']
      refine ⟨↑u⁻¹ * f c, ?_⟩
      have hfm : f t * f a = f π * f c := by rw [← map_mul, ← map_mul, htc]
      calc ↑u⁻¹ * f c * f π = ↑u⁻¹ * (f π * f c) := by ring
        _ = ↑u⁻¹ * (f t * f a) := by rw [hfm]
        _ = f a := by rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff, hmax]
      exact Ideal.mem_map_of_mem f hπp
  have hnf : ¬ IsField (Op D N la) := by
    intro hF
    have hb := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
    rw [hπm, Ideal.span_singleton_eq_bot] at hb
    have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ zero_mem _)
    have hinj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
      IsLocalization.injective (Op D N la) (Ideal.primeCompl_le_nonZeroDivisors P)
    exact hπ0 (MvPolynomial.C_injective _ _ ((hinj (hb.trans (map_zero _).symm)).trans
      (map_zero _).symm))
  have hprin : (IsLocalRing.maximalIdeal (Op D N la)).IsPrincipal := ⟨⟨f π, hπm⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Op D N la) hnf).out 1 5).mpr hprin

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

noncomputable def hTX5 {κ : Type} [Fintype κ] (f : MvPolynomial κ K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w f)) +
      ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ f)) / (Module.finrank ℚ K : ℝ)

noncomputable def bilinearSubstitution {D N : ℕ} (f : KTp K D N) :
    MvPolynomial ((Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) K :=
  MvPolynomial.aeval (fun t : TVar D N =>
    MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
      MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2))) f

section Gen

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] {P I : Type*} [Fintype P]
  [Fintype I]

theorem aeval_elim_mul_of_xhom (f : P → S) (g : I → S) (t : S) (n : ℕ) (Q : MvPolynomial (P ⊕ I) R)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = n) :
    MvPolynomial.aeval (Sum.elim f (fun i => t * g i)) Q =
      t ^ n * MvPolynomial.aeval (Sum.elim f g) Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]

  simp only [map_sum, MvPolynomial.aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hQ s hs]
  ring

end Gen

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def affineCoord (c : ι) (j : Fin (d.N + 1)) : Ω c :=
  ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)

noncomputable def linearSubstitution (c : ι) :
    MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K]
      MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X p
    | Sum.inr i => ∑ j, MvPolynomial.X (i, j) * MvPolynomial.C (d.affineCoord c j)

noncomputable def scaledSubstitution (c : ι) :
    MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K]
      MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X (some p)
    | Sum.inr i => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j)

theorem scaledSubstitution_eq (c : ι) : d.scaledSubstitution c = MvPolynomial.aeval (Sum.elim (fun p => MvPolynomial.X (some p))
    (fun i => MvPolynomial.X none *
      ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) := by
  unfold scaledSubstitution
  congr 1
  funext v
  cases v <;> rfl

theorem aeval_elim_eq_rename_linearSubstitution (c : ι)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) :
    MvPolynomial.aeval (Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun i => ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) Q =
      MvPolynomial.rename some (d.linearSubstitution c Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [linearSubstitution, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    cases v <;> simp [linearSubstitution, map_mul, hp, map_sum]

theorem scaledSubstitution_of_homogeneous (c : ι) (n : ℕ)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = n) :
    d.scaledSubstitution c Q = MvPolynomial.X none ^ n * MvPolynomial.rename some (d.linearSubstitution c Q) := by
  rw [scaledSubstitution_eq, aeval_elim_mul_of_xhom _ _ _ n Q hQ, aeval_elim_eq_rename_linearSubstitution]

theorem eq_zero_of_xhom_zero (c : ι)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = 0) (h : d.linearSubstitution c Q = 0) : Q = 0 := by
  have hvars : (↑Q.vars : Set ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2))) ⊆ Set.range Sum.inl := by
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    cases x with
    | inl p => exact ⟨p, rfl⟩
    | inr i =>
      exfalso
      have h0 := (Finset.sum_eq_zero_iff.mp (hQ s hs)) i (Finset.mem_univ _)
      exact (Finsupp.mem_support_iff.mp hxs) h0
  obtain ⟨Q0, rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q Sum.inl Sum.inl_injective hvars
  have hmap : ∀ q : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) K,
      MvPolynomial.aeval (fun p => (MvPolynomial.X p : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c))) q =
        MvPolynomial.map (algebraMap K (Ω c)) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [MvPolynomial.algebraMap_eq]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p v hp => simp [map_mul, hp]
  have e : d.linearSubstitution c (MvPolynomial.rename Sum.inl Q0) = MvPolynomial.map (algebraMap K (Ω c)) Q0 := by
    rw [← hmap, linearSubstitution, MvPolynomial.aeval_rename]
    rfl
  rw [e] at h
  have hQ0 : Q0 = 0 := MvPolynomial.map_injective _ (algebraMap K (Ω c)).injective (by rw [h, map_zero])
  rw [hQ0, map_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
