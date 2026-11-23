module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem exists_norm {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (hρ : ContAction ρ)
    (h2 : Function.Surjective fun m : M => m + m) (c : Γ) (hc : ∀ m, ρ c m = -m) (x : H1 ρ) :
    ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 c = 0 := by
  obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := h2 (-(z0.1 c))
  have hB : d0 ρ m ∈ Z1 ρ := coboundaries_le_cocycles ρ hρ (LinearMap.mem_range_self _ m)
  refine ⟨z0 - ⟨d0 ρ m, hB⟩, ?_, ?_⟩
  · rw [Submodule.Quotient.eq, Submodule.mem_comap, sub_sub_cancel_left, map_neg]
    exact Submodule.neg_mem _ ⟨m, rfl⟩
  · show z0.1 c - d0 ρ m c = 0
    rw [amitsur_d0_apply, hc]
    have hm' : m + m = -(z0.1 c) := hm
    calc z0.1 c - (-m - m) = z0.1 c + (m + m) := by abel
      _ = 0 := by rw [hm']; abel

theorem UpperTheory.V.Ws.Bl.selToZc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → (Function.Bijective fun m : M => m + m) →
          ∀ c : G ℚ Ω, (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ v0 : S, ((l : ℕ) : 𝓞 ℚ) ∈ v0.1.asIdeal → ∀ (P : Set M) (K : Subgroup (G ℚ Ω)), (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → L v ≤ H1ur (ρ.comp (locFam S Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) →
          (∀ z : Z1 (ρ.comp (locFam S Av v0)), (Submodule.Quotient.mk z : H1 (ρ.comp (locFam S Av v0))) ∈ L v0 → ∃ y, ∀ h, z.1 h - (ρ (locFam S Av v0 h) y - y) ∈ P) →
          ∃ f : Sel ρ (locFam S Av) (continuous_locFam S Av) L → Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P, Function.Injective f := by
  intro Ω _ _ _ l _ R M _ _ _ _ _ S ρ hρ hbij c hcneg Av hAv v0 hlv0 P K hK L hL hP
  have val_top {Ω : Type} [Field Ω] {x : Ω} (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
    by_contra hx
    have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
      (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
    have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
    rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
    exact lt_irrefl _ h2

  have int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
      A.valuation b ≤ 1 := by
    have h : IsIntegral A b := hb.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [A.valuation_le_one_iff, ← hy]
    exact y.2

  have exists_place (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
      (A : ValuationSubring Ω) (hA : A ≠ ⊤) : ∃ v : HeightOneSpectrum (𝓞 K),
        ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ v.asIdeal := by
    have hm : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x =>
      (A.valuation_le_one_iff _).1 (int_le A (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom))
    let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hm
    let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
    have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
      (A.valuation_lt_one_iff (f x)).symm
    refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
    rw [eq_top_iff]
    intro x _
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
    have h1 : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).2 inferInstance
    have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ K Ω
    obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
    have h3 : ¬ A.valuation (algebraMap K Ω ((n : 𝓞 K) : K)) < 1 := by
      rw [hP, h0, Ideal.mem_bot]
      exact Int.cast_ne_zero.2 hn
    have h4 : A.valuation (n : Ω) = 1 :=
      le_antisymm (int_le A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
    have h5 := int_le A hi
    rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
    exact (A.valuation_le_one_iff x).1 h5

  have placeDict : Ine (F := ℚ) (⊤ : ValuationSubring Ω) = ⊥ ∧
      (∀ A : ValuationSubring Ω, A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v) := by
    refine ⟨?_, fun A hA => exists_place ℚ Ω A hA⟩
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    have h := hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _))
    exact sub_eq_zero.1 (val_top h)
  have hex : ∀ x : H1 ρ, ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 (toGS Ω _ c) = 0 :=
    fun x => exists_norm ρ hρ hbij.2 (toGS Ω _ c) hcneg x
  have hA : ∀ x : H1 ρ, x ∈ Sel ρ (locFam S Av) (continuous_locFam S Av) L → ∀ z : Z1 ρ,
      (Submodule.Quotient.mk z : H1 ρ) = x → z.1 (toGS Ω _ c) = 0 →
      (fun g => z.1 (toGS Ω _ g)) ∈ Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P := by
    intro x hx z hzx hzc
    subst hzx
    have hcoc : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h) := ((mem_Z1_iff_cocycle _ _).mp z.2).2
    have hz1 : z.1 1 = 0 := by
      have h := hcoc 1 1
      rw [one_mul, map_one, Module.End.one_apply] at h
      simpa using h
    have hmemv : ∀ v, (Submodule.Quotient.mk (restrictCocycles1 ρ (locFam S Av v) (continuous_locFam S Av v) z) :
        H1 (ρ.comp (locFam S Av v))) ∈ L v := fun v => (mem_Sel _ _ _ _ _).mp hx v
    obtain ⟨y, hy⟩ := hP _ (hmemv v0)
    refine ⟨y, ⟨?_, ?_, hzc, ?_, ?_⟩⟩
    · exact ((IsLocallyConstant.iff_continuous _).mpr ((mem_Z1_iff_cocycle _ _).mp z.2).1).comp_continuous
        continuous_quot_mk
    · intro g h
      show z.1 (toGS Ω _ (g * h)) = z.1 (toGS Ω _ g) + ρ (toGS Ω _ g) (z.1 (toGS Ω _ h))
      rw [map_mul]
      exact hcoc _ _
    · rintro g ⟨hgK, A, hAl, hgA⟩
      show z.1 (toGS Ω _ g) = 0
      by_cases hAtop : A = ⊤
      · subst hAtop
        rw [(placeDict).1, Subgroup.mem_bot] at hgA
        rw [hgA, map_one, hz1]
      obtain ⟨v, hAv'⟩ := (placeDict).2 A hAtop
      by_cases hvS : v ∈ S
      · set w : S := ⟨v, hvS⟩
        have hne : w ≠ v0 := by
          intro hw
          apply hAl
          have h := (hAv' (l : 𝓞 ℚ)).mpr (by rw [show v = v0.1 from congrArg Subtype.val hw]; exact hlv0)
          simpa using h
        obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hAv w) hAv'
        rw [← hσ] at hgA
        have hgA' : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (Av w) := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hgA
        have hur := hL w hne (hmemv w)
        rw [H1ur, LinearMap.mem_ker] at hur
        have hur' := (Submodule.Quotient.mk_eq_zero _).mp hur
        rw [Submodule.mem_comap] at hur'
        obtain ⟨m, hm⟩ := hur'
        have hj := congrFun hm ⟨⟨σ⁻¹ * g * σ, Ine_le_Dec _ hgA'⟩, hgA'⟩
        rw [amitsur_d0_apply] at hj
        have hconj : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = 0 := by
          have hj' : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = ρ (toGS Ω _ (σ⁻¹ * g * σ)) m - m := hj.symm
          rw [hj']
          rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
            show ρ (toGS Ω _ g) (ρ (toGS Ω _ σ) m) = ρ (toGS Ω _ σ) m from hK g hgK _,
            ← Module.End.mul_apply, ← map_mul, map_inv, inv_mul_cancel, map_one, Module.End.one_apply, sub_self]
        set a := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) σ
        set b := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g
        have hb : ∀ m, ρ b m = m := hK g hgK
        rw [map_mul, map_mul, map_inv] at hconj
        have e1 := hcoc (a⁻¹ * b) a
        have e2 := hcoc a⁻¹ b
        have e3 := hcoc a⁻¹ a
        rw [inv_mul_cancel, hz1] at e3
        rw [map_mul, Module.End.mul_apply, hb, e2, hconj] at e1
        have hinv0 : ρ a⁻¹ (z.1 b) = 0 := by
          have : (0 : M) = ρ a⁻¹ (z.1 b) + (z.1 a⁻¹ + ρ a⁻¹ (z.1 a)) := by rw [e1]; abel
          rw [← e3, add_zero] at this
          exact this.symm
        have : z.1 b = ρ a (ρ a⁻¹ (z.1 b)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [this, hinv0, map_zero]
      · have hgN : g ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) :=
          Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
            (Set.mem_iUnion₂.mpr ⟨v, hvS, Set.mem_iUnion₂.mpr ⟨A, hAv', hgA⟩⟩))
        rw [show toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g = 1 from (QuotientGroup.eq_one_iff g).mpr hgN, hz1]
    · intro h hh
      exact hy ⟨h, hh⟩
  choose zc hzc using hex
  refine ⟨fun x => ⟨fun g => (zc x.1).1 (toGS Ω _ g), hA x.1 x.2 (zc x.1) (hzc x.1).1 (hzc x.1).2⟩, ?_⟩
  intro x x' hxx
  have hfun : (fun g => (zc x.1).1 (toGS Ω _ g)) = (fun g => (zc x'.1).1 (toGS Ω _ g)) :=
    congrArg Subtype.val hxx
  have hz : zc x.1 = zc x'.1 := by
    apply Subtype.ext
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) q
    exact congrFun hfun g
  apply Subtype.ext
  rw [← (hzc x.1).1, ← (hzc x'.1).1, hz]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem res_entry {R : Type} [CommRing R] [IsLocalRing R] {X X' : M4 R} (hX : Sep X) (h : X' * X = 1) (Y : M4 R)
    (i j : Fin 4) : residue R (X' j j) * residue R (X j j) = 1 ∧
      residue R ((X * Y * X' - Y) i j) = residue R ((X i i - X j j) * X' j j) * residue R (Y i j) := by
  have hoff : ∀ a b, a ≠ b → residue R (X a b) = 0 :=
    fun a b hab => (residue_eq_zero_iff _).2 (hX.off a b hab)
  have kr : ∀ (A B : M4 R), (∀ a b, a ≠ b → residue R (B a b) = 0) →
      ∀ a b, residue R ((A * B) a b) = residue R (A a b) * residue R (B b b) := by
    intro A B hB a b

    rw [Matrix.mul_apply, map_sum, Finset.sum_eq_single b]
    · rw [map_mul]
    · intro c _ hc
      rw [map_mul, hB c b hc, mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  have kl : ∀ (A B : M4 R), (∀ a b, a ≠ b → residue R (A a b) = 0) →
      ∀ a b, residue R ((A * B) a b) = residue R (A a a) * residue R (B a b) := by
    intro A B hA a b

    rw [Matrix.mul_apply, map_sum, Finset.sum_eq_single a]
    · rw [map_mul]
    · intro c _ hc
      rw [map_mul, hA a c (Ne.symm hc), zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  have hdiag : ∀ j, residue R (X' j j) * residue R (X j j) = 1 := by
    intro j
    rw [← kr X' X hoff j j, h, Matrix.one_apply_eq, map_one]
  have hoff' : ∀ a b, a ≠ b → residue R (X' a b) = 0 := by
    intro a b hab
    have h0 : residue R (X' a b) * residue R (X b b) = 0 := by
      rw [← kr X' X hoff a b, h, Matrix.one_apply_ne hab, map_zero]
    linear_combination residue R (X' b b) * h0 - residue R (X' a b) * hdiag b
  refine ⟨hdiag j, ?_⟩
  rw [Matrix.sub_apply, map_sub, kr _ _ hoff' i j, kl _ _ hoff i j, map_mul, map_sub]
  linear_combination residue R (Y i j) * hdiag j

theorem UpperTheory.V.Ws.Bl.adBij :
    ∀ (R Γ : Type) [CommRing R] [IsLocalRing R] [Group Γ] (r : Γ →* M4 R) (h : BG r) (s : Γ), Sep (r s) → Function.Bijective fun Y => adU h s Y - Y := by
  intro R Γ _ _ _ r h s hs
  obtain ⟨hfin, -, hmem⟩ := uMFacts R
  haveI := hfin
  let φ : uM R →ₗ[R] uM R := adU h s - LinearMap.id
  have hinv : r s⁻¹ * r s = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hkey : ∀ Y : uM R, φ Y ∈ (maximalIdeal R • ⊤ : Submodule R (uM R)) →
      Y ∈ (maximalIdeal R • ⊤ : Submodule R (uM R)) := by
    intro Y hY
    rw [hmem] at hY ⊢
    intro i j
    by_cases hij : lamW i < lamW j
    · have h1 := hY i j
      have e := res_entry hs hinv (Y : M4 R) i j
      have hu : IsUnit (r s i i - r s j j) := hs.unit i j (ne_of_lt hij)
      have hc : (↑(φ Y) : M4 R) i j = (r s * ↑Y * r s⁻¹ - ↑Y) i j := rfl
      rw [hc, ← residue_eq_zero_iff, e.2, map_mul] at h1
      rw [← residue_eq_zero_iff]
      have hu' : residue R (r s i i - r s j j) ≠ 0 := (hu.map (residue R)).ne_zero
      have hv : residue R (r s⁻¹ j j) ≠ 0 := left_ne_zero_of_mul_eq_one e.1
      exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero hu' hv)
    · have hY2 := (Submodule.mem_inf.1 Y.2).1
      rw [hY2 i j hij]
      exact zero_mem _
  have hS : (maximalIdeal R • ⊤ : Submodule R (uM R)) ≤
      (maximalIdeal R • ⊤ : Submodule R (uM R)).comap φ := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  let ψ := Submodule.mapQ _ _ φ hS
  have hψinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨Y, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hkey Y hq
  letI : Module (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    inferInstanceAs (Module (R ⧸ maximalIdeal R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))))
  letI : IsScalarTower R (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))))
  haveI : Module.Finite (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hsurjA : Function.Surjective (algebraMap R (ResidueField R)) := Ideal.Quotient.mk_surjective
  let ψk := LinearMap.extendScalarsOfSurjective hsurjA ψ
  have hψsurj : Function.Surjective ψ := (LinearMap.injective_iff_surjective (f := ψk)).1 hψinj
  have hrange : LinearMap.range φ = ⊤ := by
    rw [← IsLocalRing.map_mkQ_eq_top, ← LinearMap.range_comp, eq_top_iff]
    intro q _
    obtain ⟨q', rfl⟩ := hψsurj q
    obtain ⟨Y, rfl⟩ := Submodule.mkQ_surjective _ q'
    exact ⟨Y, rfl⟩
  have hsurj : Function.Surjective φ := LinearMap.range_eq_top.1 hrange
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism φ hsurj, hsurj⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

open CategoryTheory in
private theorem seq_ex (S : ℕ → Type) (hf : ∀ n, Finite (S n)) (hn : ∀ n, Nonempty (S n)) (t : ∀ n, S (n + 1) → S n) :
    ∃ u : ∀ n, S n, ∀ n, t n (u (n + 1)) = u n :=
  _root_.UpperTheory.Reformulated.B.Qj7.seq_ex S hf hn t

theorem UpperTheory.V.Ws.Bl.compat :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), (∀ n, Finite (T ⧸ lev A T n)) → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z) →
          ∃ (z : ∀ n, Γ → T ⧸ lev A T n) (y : ∀ n, T ⧸ lev A T n), (∀ n, IsZn ρ c N H P n (z n) (y n)) ∧ (∀ n g, redn A T n (z (n + 1) g) = z n g) ∧ (∀ n, redn A T n (y (n + 1)) = y n) ∧ Prim (z 1) := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hT hZ hP
  let S : ℕ → Type := fun n =>
    {p : (Γ → T ⧸ lev A T n) × (T ⧸ lev A T n) // IsZn ρ c N H P n p.1 p.2 ∧ (0 < n → Prim p.1)}
  let t : ∀ n, S (n + 1) → S n := fun n p =>
    ⟨(fun g => redn A T n (p.1.1 g), redn A T n p.1.2),
      (redMem A T Γ ρ c N H P n _ _ p.2.1).1,
      (redMem A T Γ ρ c N H P n _ _ p.2.1).2.1 (p.2.2 n.succ_pos)⟩
  have hf : ∀ n, Finite (S n) := fun n => by
    have := hT n
    have h : ((Zn ρ c N H P n) ×ˢ (Set.univ : Set (T ⧸ lev A T n))).Finite := (hZ n).prod Set.finite_univ
    have h' : {p : (Γ → T ⧸ lev A T n) × (T ⧸ lev A T n) |
        IsZn ρ c N H P n p.1 p.2 ∧ (0 < n → Prim p.1)}.Finite :=
      h.subset (by
        intro p hp
        exact ⟨⟨p.2, hp.1⟩, trivial⟩)
    exact h'.to_subtype
  have hn : ∀ n, Nonempty (S n) := fun n => by
    obtain ⟨z, ⟨y, hz⟩, hp⟩ := hP (n + 1) n.succ_pos
    exact ⟨t n ⟨(z, y), hz, fun _ => hp⟩⟩
  obtain ⟨u, hu⟩ := seq_ex S hf hn t
  exact ⟨fun n => (u n).1.1, fun n => (u n).1.2, fun n => (u n).2.1,
    fun n g => congrArg (fun p : S n => p.1.1 g) (hu n),
    fun n => congrArg (fun p : S n => p.1.2) (hu n), (u 1).2.2 Nat.one_pos⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.primEx :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, n ≤ Nat.card (Zn ρ c N H P n)) → ∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL hfin hcard n hn
  by_contra hne
  push_neg at hne
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hA : ∀ k, ∀ z ∈ Zn ρ c N H P (n + k), ¬Prim z := by
    intro k
    induction k with
    | zero => exact hne
    | succ k ih =>
      intro z hz hpz
      obtain ⟨y, hy⟩ := hz
      have hr := redMem A T Γ ρ c N H P (n + k) z y hy
      exact ih _ ⟨_, hr.1⟩ (hr.2.1 hpz (by omega))
  have hB : ∀ k, Nat.card (Zn ρ c N H P (n + k + 1)) ≤ Nat.card (Zn ρ c N H P (n + k)) := by
    intro k
    haveI := (hfin (n + k)).to_subtype
    have key : ∀ z : Zn ρ c N H P (n + k + 1), ∃ z' : Zn ρ c N H P (n + k),
        ∀ g x, (lev A T (n + k)).mkQ x = z'.1 g → (lev A T (n + k + 1)).mkQ (t • x) = z.1 g := by
      intro z
      obtain ⟨z', hz', h⟩ := divStep A T Γ ρ c N H P hL t ht (n + k) z.1 z.2 (hA (k + 1) z.1 z.2)
      exact ⟨⟨z', hz'⟩, h⟩
    choose f hf using key
    refine Nat.card_le_card_of_injective f ?_
    intro z1 z2 h12
    apply Subtype.ext
    funext g
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (lev A T (n + k)) ((f z1).1 g)
    rw [← hf z1 g x hx, hf z2 g x (by rw [hx, h12])]
  have hC : ∀ k, Nat.card (Zn ρ c N H P (n + k)) ≤ Nat.card (Zn ρ c N H P n) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hB k).trans ih
  have h1 := hcard (n + (Nat.card (Zn ρ c N H P n) + 1))
  have h2 := hC (Nat.card (Zn ρ c N H P n) + 1)
  omega
end
