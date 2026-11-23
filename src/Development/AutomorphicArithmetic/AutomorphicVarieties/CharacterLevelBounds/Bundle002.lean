module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle002
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem sumBack_one {ι : Type} (S : Finset ι) (f : ι → ℕ∞) (a : ℕ∞) (b E : ℕ) (hE : E ≠ 0)
    (hf : ∀ i ∈ S, f i ≠ ⊤) (h : a * (E : ℕ∞) ≤ ∑ i ∈ S, (f i + (b : ℕ∞) * (E : ℕ∞))) :
    a ≠ ⊤ ∧ (a.toNat : ℝ) ≤ ∑ i ∈ S, ((f i).toNat : ℝ) / (E : ℝ) + S.card * (b : ℝ) := by
  have hsum : ∑ i ∈ S, (f i + (b : ℕ∞) * (E : ℕ∞)) = ((∑ i ∈ S, ((f i).toNat + b * E) : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    push_cast
    rw [ENat.coe_toNat (hf i hi)]
  rw [hsum] at h
  have ha : a ≠ ⊤ := by
    rintro rfl
    rw [ENat.top_mul (by exact_mod_cast hE)] at h
    exact absurd h (not_le.2 (ENat.coe_lt_top _))
  refine ⟨ha, ?_⟩
  have h2 : a.toNat * E ≤ ∑ i ∈ S, ((f i).toNat + b * E) := by
    rw [← ENat.coe_toNat ha] at h
    exact_mod_cast h
  have hE' : (0 : ℝ) < E := by exact_mod_cast Nat.pos_of_ne_zero hE
  have h3 : (a.toNat : ℝ) * E ≤ ∑ i ∈ S, (((f i).toNat : ℝ) + b * E) := by exact_mod_cast h2
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h3
  rw [← Finset.sum_div]
  have h4 : (∑ i ∈ S, ((f i).toNat : ℝ)) / E + S.card * (b : ℝ) = ((∑ i ∈ S, ((f i).toNat : ℝ)) + S.card * ((b : ℝ) * E)) / E := by
    field_simp
  rw [h4, le_div_iff₀ hE']
  exact h3

theorem UpperTheory.V.Chr.sumBack :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) (T : ℕ → Finset ι) (T₀ : Finset ι) (f : ι → ℕ → ℕ∞) (a : ℕ → ℕ∞) (b : ℕ → ℕ) (t : ℕ),
          (∀ e, T e ⊆ T₀) → (∀ e, 0 < e → e < t → (∀ i ∈ T e, f i e ≠ ⊤) ∧ a e * eO l O ≤ ∑ i ∈ T e, (f i e + (b e : ℕ∞) * eO l O)) →
          (∀ e, 0 < e → e < t → a e ≠ ⊤) ∧
            ∑ e ∈ Finset.Ico 1 t, ((a e).toNat : ℝ) ≤ ∑ e ∈ Finset.Ico 1 t, ∑ i ∈ T e, nrm l O (f i e) + T₀.card * ∑ e ∈ Finset.Ico 1 t, (b e : ℝ) := by
  intro l _ O _ _ _ _ _ ι T T₀ f a b t hT h
  obtain ⟨-, -, -, -, -, hne, hle, -, -⟩ := dvrFacts l O
  have htop : eO l O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  have hEO : eO l O = (((eO l O).toNat : ℕ) : ℕ∞) := (ENat.coe_toNat htop).symm
  have hE : (eO l O).toNat ≠ 0 := by
    intro h0
    apply hne
    rw [hEO, h0]
    rfl
  have key : ∀ e ∈ Finset.Ico 1 t, a e ≠ ⊤ ∧ ((a e).toNat : ℝ) ≤ ∑ i ∈ T e, ((f i e).toNat : ℝ) / ((eO l O).toNat : ℝ) + (T e).card * (b e : ℝ) := by
    intro e he
    rw [Finset.mem_Ico] at he
    obtain ⟨h1, h2⟩ := h e (by omega) he.2
    rw [hEO] at h2
    exact sumBack_one (T e) (fun i => f i e) (a e) (b e) _ hE h1 h2
  refine ⟨fun e he0 het => (key e (Finset.mem_Ico.2 ⟨he0, het⟩)).1, ?_⟩
  have hn : ∀ x, nrm l O x = (x.toNat : ℝ) / ((eO l O).toNat : ℝ) := fun x => rfl
  simp only [hn]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e he => (key e he).2.trans ?_
  gcongr
  exact hT e
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.h0Nu :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G k Ω →* Oˣ) (U : Subgroup (G k Ω)),
          (∀ U' : Subgroup (G k Ω), U' ≤ U → h0 l e ψ U ≤ h0 l e ψ U') ∧
          (U ≤ ψ.ker → h0 l e ψ U ≤ KStar.TotallyRealRoots.nu l (U.map (cycZ k Ω l)) e * eO l O) := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ e ψ U
  refine ⟨fun U' h => ?_, fun h => ?_⟩
  · have hle : H0U (rho l e ψ) U ≤ H0U (rho l e ψ) U' := fun m hm =>
      (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm ⟨g.1, h g.2⟩
    exact Module.length_le_of_injective _ (Submodule.inclusion_injective hle)
  · obtain ⟨-, -, -, -, -, h0', -, hval, -⟩ := dvrFacts l O
    by_cases ht : KStar.TotallyRealRoots.nu l (U.map (cycZ k Ω l)) e = ⊤
    · rw [ht, ENat.top_mul h0']
      exact le_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ht
    have hle : H0U (rho l e ψ) U ≤
        LinearMap.ker (((l : O) ^ n) • (LinearMap.id : QO l O →ₗ[O] QO l O)) := by
      intro m hm
      have h1 : m ∈ KStar.TotallyRealRoots.twistInvOver l O (QO l O) (U.map (cycZ k Ω l)) e := by
        rw [KStar.TotallyRealRoots.mem_twistInvOver]
        rintro u ⟨g, hg, rfl⟩
        have h2 : rho l e ψ g⁻¹ m = m := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm ⟨g⁻¹, U.inv_mem hg⟩
        have h3 : ψ g = 1 := h hg
        rw [rho_eq, scalRep_apply, MonoidHom.inv_apply, map_inv, inv_inv, Psi, MonoidHom.mul_apply, h3, mul_one,
          zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at h2
        exact h2
      rw [KStar.TotallyRealRoots.twistInvOver_eq_torsionBy _ hn.symm, Submodule.mem_torsionBy_iff] at h1
      exact h1
    refine (Module.length_le_of_injective _ (Submodule.inclusion_injective hle)).trans ?_
    rw [(qoFacts l O).2.2.2, IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, ← hn, hval]
end
