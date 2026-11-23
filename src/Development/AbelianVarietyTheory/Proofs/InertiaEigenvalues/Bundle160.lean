module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Length
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
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

noncomputable section

namespace GlobalTheory.WeilRes

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
  [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω] {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
  {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')

theorem continuous_res : Continuous (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) := by
  refine continuous_of_continuousAt_one (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp hU
  let b := Module.finBasis E L
  let S : Set Ω := Set.range fun i => (b i : Ω)
  have : Finite S := (Set.finite_range _).to_subtype
  have : Algebra.IsAlgebraic E' Ω := IsAlgClosure.isAlgebraic
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff E' Ω _).mpr ⟨IntermediateField.adjoin E' S,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun σ hσ => hLU ?_⟩
  have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_
  have hlin : (AlgEquiv.restrictScalarsHom E σ).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => hσ' _ (IntermediateField.subset_adjoin E' S ⟨i, rfl⟩)
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

end GlobalTheory.WeilRes

end
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal TensorProduct

noncomputable section
namespace GlobalTheory.ConsCompare

theorem autCongr_continuous_cyc_inertia : ∀ (E Ω Ω₁ : Type) [Field E] [NumberField E] [Field Ω] [Field Ω₁] [Algebra E Ω] [Algebra E Ω₁] [IsAlgClosure E Ω] [IsAlgClosure E Ω₁] (σ : Ω ≃ₐ[E] Ω₁), Continuous (fun g : G E Ω => (AlgEquiv.autCongr σ g : G E Ω₁)) ∧ (∀ (p : ℕ) [Fact p.Prime] (g : G E Ω), cycZ E Ω₁ p (AlgEquiv.autCongr σ g) = cycZ E Ω p g) ∧ ∀ (A : ValuationSubring Ω) (A₁ : ValuationSubring Ω₁), (∀ y, σ y ∈ A₁ ↔ y ∈ A) → ∀ g : G E Ω, g ∈ Ine (F := E) A → (AlgEquiv.autCongr σ g : G E Ω₁) ∈ Ine (F := E) A₁ := by
  intro E Ω Ω₁ _ _ _ _ _ _ _ _ σ
  refine ⟨?_, fun p _ g => ?_, fun A A₁ hA g hg => ?_⟩
  · apply continuous_of_continuousAt_one (AlgEquiv.autCongr σ).toMonoidHom
    intro s hs
    rw [map_one, krullTopology_mem_nhds_one_iff] at hs
    obtain ⟨F, hF, hs⟩ := hs
    rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
    refine ⟨F.map σ.symm.toAlgHom,
      (IntermediateField.equivMap F σ.symm.toAlgHom).toLinearEquiv.finiteDimensional, fun g hg => hs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
    intro x hx
    have := hg (σ.symm x) ⟨x, hx, rfl⟩
    show σ (g (σ.symm x)) = x
    rw [this, σ.apply_symm_apply]
  · have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    have : IsAlgClosed Ω₁ := IsAlgClosure.isAlgClosed E
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    have : CharZero Ω₁ := charZero_of_injective_algebraMap (algebraMap E Ω₁).injective
    have : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
    have : NeZero ((p : ℕ) : Ω₁) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
    apply Units.ext
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ n)
    have hζ' : IsPrimitiveRoot (σ ζ) (p ^ n) := hζ.map_of_injective σ.injective
    have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((cycZ E Ω p g : ℤ_[p]ˣ) : ℤ_[p])).val :=
      cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (G E Ω) Ω g) ζ hζ.pow_eq_one
    have h2 : σ (g (σ.symm (σ ζ))) = σ ζ ^ (PadicInt.toZModPow n
        ((cycZ E Ω₁ p (AlgEquiv.autCongr σ g) : ℤ_[p]ˣ) : ℤ_[p])).val :=
      cyclotomicCharacter.spec (L := Ω₁) p
        (MulSemiringAction.toRingAut (G E Ω₁) Ω₁ (AlgEquiv.autCongr σ g)) (σ ζ) hζ'.pow_eq_one
    rw [σ.symm_apply_apply, h1, map_pow] at h2
    apply ZMod.val_injective
    exact (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2).symm
  · have hv : ∀ y, A₁.valuation (σ y) < 1 ↔ A.valuation y < 1 := fun y => by
      rw [valuation_lt_one_iff', valuation_lt_one_iff', hA, ← map_inv₀, hA, map_eq_zero_iff _ σ.injective]
    refine ⟨?_, fun x hx => ?_⟩
    · show AlgEquiv.autCongr σ g ∈ Dec (F := E) A₁
      rw [mem_Dec]
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      obtain ⟨z, rfl⟩ := σ.surjective y
      have : (AlgEquiv.autCongr σ g)⁻¹ • σ z = σ ((g⁻¹ : G E Ω) z) := by
        rw [← map_inv]
        show σ ((g⁻¹ : G E Ω) (σ.symm (σ z))) = _
        rw [σ.symm_apply_apply]
      rw [this, hA, hA]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hg.1) z
    · obtain ⟨z, rfl⟩ := σ.surjective x
      have : (AlgEquiv.autCongr σ g) (σ z) - σ z = σ (g z - z) := by
        rw [map_sub]
        show σ (g (σ.symm (σ z))) - _ = _
        rw [σ.symm_apply_apply]
      rw [this, hv]
      apply hg.2
      rwa [ValuationSubring.valuation_le_one_iff, hA, ← ValuationSubring.valuation_le_one_iff] at hx

section CharpolySeries
variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def cpOn (k : Type) [Field k] [Algebra k A] (a : A) (M : Type) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M] : Polynomial k :=
  LinearMap.charpoly (Algebra.lsmul k k M a)

variable (a : A) {M M' : Type} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [FiniteDimensional k M] [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M']
  [FiniteDimensional k M']

theorem cpOn_congr (e : M ≃ₗ[A] M') : cpOn k a M = cpOn k a M' := by
  unfold cpOn
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k)]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply]

instance finiteDimensional_sub (N : Submodule A M) : FiniteDimensional k N :=
  inferInstanceAs (FiniteDimensional k (N.restrictScalars k))

theorem cpOn_sub_quot (N : Submodule A M) : cpOn k a M = cpOn k a N * cpOn k a (M ⧸ N) :=
  GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (N.restrictScalars k) (Algebra.lsmul k k M a)
    fun _ hx => N.smul_mem a hx

theorem last_eq_mul_prod {P : Type} [CommMonoid P] : ∀ (n : ℕ) (u : Fin (n + 1) → P) (c : Fin n → P),
    (∀ j, u j.succ = u j.castSucc * c j) → u (Fin.last n) = u 0 * ∏ j, c j
  | 0, u, c, _ => by simp
  | n + 1, u, c, h => by
    have := last_eq_mul_prod n (fun j => u j.castSucc) (fun j => c j.castSucc) fun j => h j.castSucc
    rw [Fin.prod_univ_castSucc, ← Fin.succ_last, h, this, mul_assoc]
    rfl

theorem cpOn_series (s : CompositionSeries (Submodule A M)) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    cpOn k a M = ∏ j : Fin s.length,
      cpOn k a (↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) := by
  have := last_eq_mul_prod s.length (fun j => cpOn k a (s j)) _ fun j =>
    (cpOn_sub_quot a ((s j.castSucc).submoduleOf (s j.succ))).trans (congrArg (· * _)
      (cpOn_congr a (Submodule.submoduleOfEquivOfLe (s.step j).le)))
  have e1 : cpOn k a (s (Fin.last _)) = cpOn k a M :=
    cpOn_congr a (LinearEquiv.ofTop _ h1)
  have e0 : cpOn k a (s 0) = 1 := by
    have : Subsingleton (s 0) := by
      have h0' : s 0 = ⊥ := h0
      rw [h0']
      infer_instance
    unfold cpOn
    rw [← (LinearMap.charpoly_monic _).natDegree_eq_zero, LinearMap.charpoly_natDegree]
    exact Module.finrank_zero_of_subsingleton
  rw [← e1, this, e0, one_mul]

end CharpolySeries

end GlobalTheory.ConsCompare
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Cyc

theorem geom_sum_one_add_expand {R : Type*} [CommRing R] (y : R) (n : ℕ) :
    ∃ z : R, (1 + y) ^ n - 1 = y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z + (n.choose 2 : ℕ) + y * z, ?_⟩
    have h : (1 + y) ^ n = 1 + y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by
      rw [← hz]; ring
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    rw [pow_succ, h, hc]
    push_cast
    ring

variable {l : ℕ} [hl : Fact l.Prime]

theorem padicInt_norm_add_eq_of_lt {a b : ℤ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [PadicInt.norm_add_eq_max_of_ne h.ne', max_eq_left h.le]

theorem norm_pow_sub_one_of_not_dvd (x : ℤ_[l]) (hx : ‖x - 1‖ < 1) (n : ℕ) (hn : ¬ l ∣ n) :
    ‖x ^ n - 1‖ = ‖x - 1‖ := by
  obtain ⟨z, hz⟩ := geom_sum_one_add_expand (x - 1) n
  rw [add_sub_cancel] at hz
  have hn1 : ‖(n : ℤ_[l])‖ = 1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    by_contra h
    push_neg at h
    have h' : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    exact hn (Int.natCast_dvd_natCast.mp h')
  have e : (n : ℤ_[l]) + (n.choose 2 : ℕ) * (x - 1) + (x - 1) ^ 2 * z
      = n + (x - 1) * ((n.choose 2 : ℕ) + (x - 1) * z) := by ring
  rw [hz, norm_mul, e, padicInt_norm_add_eq_of_lt, hn1, mul_one]
  rw [hn1, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)) hx

theorem norm_pow_prime_sub_one (x : ℤ_[l]) (hx : ‖x - 1‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) :
    ‖x ^ l - 1‖ = ‖x - 1‖ * ‖(l : ℤ_[l])‖ := by
  obtain ⟨z, hz⟩ := geom_sum_one_add_expand (x - 1) l
  rw [add_sub_cancel] at hz
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hi0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hsq : (l : ℝ)⁻¹ * (l : ℝ)⁻¹ < (l : ℝ)⁻¹ := mul_lt_of_lt_one_right hi0 hi1
  have hA : ‖((l.choose 2 : ℕ) : ℤ_[l]) * (x - 1)‖ < (l : ℝ)⁻¹ := by
    rw [norm_mul]
    by_cases h : l = 2
    · exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)) (h2 h)
    · have hlt : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h)
      obtain ⟨c, hc⟩ := hl.out.dvd_choose_self (k := 2) (by norm_num) hlt
      have : ‖((l.choose 2 : ℕ) : ℤ_[l])‖ ≤ (l : ℝ)⁻¹ := by
        rw [hc, Nat.cast_mul, norm_mul, PadicInt.norm_p]
        exact mul_le_of_le_one_right hi0.le (PadicInt.norm_le_one _)
      exact lt_of_le_of_lt (mul_le_mul this hx (norm_nonneg _) hi0.le) hsq
  have hB : ‖(x - 1) ^ 2 * z‖ < (l : ℝ)⁻¹ := by
    rw [norm_mul, sq, norm_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)) ?_
    exact lt_of_le_of_lt (mul_le_mul hx hx (norm_nonneg _) hi0.le) hsq
  rw [hz, norm_mul, add_assoc, padicInt_norm_add_eq_of_lt]
  rw [PadicInt.norm_p]
  exact lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt hA hB)

theorem norm_pow_nat_sub_one (n : ℕ) (hn : n ≠ 0) : ∀ (x : ℤ_[l]), ‖x - 1‖ ≤ (l : ℝ)⁻¹ →
    (l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) → ‖x ^ n - 1‖ = ‖x - 1‖ * ‖(n : ℤ_[l])‖ := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx h2
    by_cases hd : l ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hlt : m < l * m := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hl.out.one_lt
      have key := norm_pow_prime_sub_one x hx h2
      have hle : ‖x ^ l - 1‖ ≤ ‖x - 1‖ := by
        rw [key]; exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
      rw [pow_mul, ih m hlt hm (x ^ l) (hle.trans hx) (fun h => hle.trans_lt (h2 h)), key,
        Nat.cast_mul, norm_mul, mul_assoc]
    · have hn1 : ‖(n : ℤ_[l])‖ = 1 := by
        apply le_antisymm (PadicInt.norm_le_one _)
        by_contra h
        push_neg at h
        have h' : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
        rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
        exact hd (Int.natCast_dvd_natCast.mp h')
      rw [norm_pow_sub_one_of_not_dvd x (hx.trans_lt hi1) n hd, hn1, mul_one]

theorem norm_unit_zpow_sub_one :
    ∀ (l : ℕ) [Fact l.Prime], ∀ (s : ℕ) (u : ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) →
      ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) → ∀ n : ℤ, n ≠ 0 →
      ‖((u ^ n : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) * ‖(n : ℤ_[l])‖ := by
  intro l hl s u hs h2 hu n hn
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hx : ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ)⁻¹ := by
    rw [hu, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  have hx2 : l = 2 → ‖(u : ℤ_[l]) - 1‖ < (l : ℝ)⁻¹ := fun h => by
    have := h2 h
    rw [hu, ← zpow_neg_one]
    exact zpow_lt_zpow_right₀ hl1 (by omega)
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · have hm : m ≠ 0 := by rintro rfl; simp at hn
    rw [zpow_natCast, Units.val_pow_eq_pow_val, norm_pow_nat_sub_one m hm _ hx hx2, hu,
      Int.cast_natCast]
  · have hm : m ≠ 0 := by rintro rfl; simp at hn
    have e : (((u ^ m)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1
        = -((((u ^ m)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (((u ^ m : ℤ_[l]ˣ) : ℤ_[l]) - 1)) := by
      rw [mul_sub, Units.inv_mul]; ring
    rw [zpow_neg, zpow_natCast, e, norm_neg, norm_mul, PadicInt.norm_units, one_mul,
      Units.val_pow_eq_pow_val, norm_pow_nat_sub_one m hm _ hx hx2, hu, Int.cast_neg, norm_neg,
      Int.cast_natCast]

end GlobalTheory.Cyc
end

section

open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory.CongruenceLengthSum

variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]

private theorem sep_lemma' {P₁ P₂ : Submodule O V} (hd : Disjoint P₁ P₂) {x₁ y₁ x₂ y₂ : V}
    (h₁ : x₁ ∈ P₁) (h₁' : y₁ ∈ P₁) (h₂ : x₂ ∈ P₂) (h₂' : y₂ ∈ P₂) (h : x₁ + x₂ = y₁ + y₂) :
    x₁ = y₁ ∧ x₂ = y₂ := by
  have e : x₁ - y₁ = y₂ - x₂ := by
    rw [sub_eq_sub_iff_add_eq_add, h, add_comm y₁ y₂]
  have hz : x₁ - y₁ = 0 :=
    Submodule.disjoint_def.mp hd _ (sub_mem h₁ h₁') (e ▸ sub_mem h₂' h₂)
  have e1 : x₁ = y₁ := sub_eq_zero.mp hz
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact add_left_cancel h

theorem length_quot_sup (T₁ T₂ S₁ S₂ : Submodule O V) (h₁ : S₁ ≤ T₁) (h₂ : S₂ ≤ T₂)
    (hd : Disjoint T₁ T₂) :
    Module.length O (↥(T₁ ⊔ T₂) ⧸ (S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype) =
      Module.length O (↥T₁ ⧸ S₁.comap T₁.subtype) + Module.length O (↥T₂ ⧸ S₂.comap T₂.subtype) := by
  have key : ∀ a ∈ T₁, ∀ b ∈ T₂, a + b ∈ S₁ ⊔ S₂ ↔ a ∈ S₁ ∧ b ∈ S₂ := by
    intro a ha b hb
    constructor
    · intro h
      obtain ⟨s₁, hs₁, s₂, hs₂, hs⟩ := Submodule.mem_sup.mp h
      obtain ⟨e1, e2⟩ := sep_lemma' hd ha (h₁ hs₁) hb (h₂ hs₂) hs.symm
      rw [e1, e2]
      exact ⟨hs₁, hs₂⟩
    · rintro ⟨h1, h2⟩
      exact add_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  let f : (↥T₁ × ↥T₂) →ₗ[O] ↥(T₁ ⊔ T₂) :=
    LinearMap.codRestrict (T₁ ⊔ T₂) (T₁.subtype.coprod T₂.subtype)
      (fun p => add_mem (Submodule.mem_sup_left p.1.2) (Submodule.mem_sup_right p.2.2))
  let Φ := ((S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype).mkQ ∘ₗ f
  let Ψ : (↥T₁ × ↥T₂) →ₗ[O] (↥T₁ ⧸ S₁.comap T₁.subtype) × (↥T₂ ⧸ S₂.comap T₂.subtype) :=
    LinearMap.prodMap (S₁.comap T₁.subtype).mkQ (S₂.comap T₂.subtype).mkQ
  have hΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hΨ : Function.Surjective Ψ := by
    rintro ⟨y₁, y₂⟩
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y₁
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y₂
    exact ⟨(a, b), rfl⟩
  have hker : LinearMap.ker Φ = LinearMap.ker Ψ := by
    ext ⟨a, b⟩
    simp only [LinearMap.mem_ker, Φ, Ψ, f, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.prodMap_apply, Prod.mk_eq_zero]
    exact key a a.2 b b.2
  calc Module.length O (↥(T₁ ⊔ T₂) ⧸ (S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype)
      = Module.length O ((↥T₁ × ↥T₂) ⧸ LinearMap.ker Φ) :=
        (Φ.quotKerEquivOfSurjective hΦ).length_eq.symm
    _ = Module.length O ((↥T₁ × ↥T₂) ⧸ LinearMap.ker Ψ) := (Submodule.quotEquivOfEq _ _ hker).length_eq
    _ = Module.length O ((↥T₁ ⧸ S₁.comap T₁.subtype) × (↥T₂ ⧸ S₂.comap T₂.subtype)) :=
        (Ψ.quotKerEquivOfSurjective hΨ).length_eq
    _ = _ := Module.length_prod _ _ _

theorem sup_inf_split (G₁ B₁ L₁ G₂ B₂ L₂ : Submodule O V) (hd : Disjoint (G₁ ⊔ B₁) (G₂ ⊔ B₂))
    (hL₁ : L₁ ≤ G₁ ⊔ B₁) (hL₂ : L₂ ≤ G₂ ⊔ B₂) :
    (G₁ ⊔ G₂) ⊓ ((L₁ ⊔ L₂) ⊔ (B₁ ⊔ B₂)) = G₁ ⊓ (L₁ ⊔ B₁) ⊔ G₂ ⊓ (L₂ ⊔ B₂) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.mp hx2
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hc
    have e : g₁ + g₂ = (l₁ + b₁) + (l₂ + b₂) := by rw [← hyc]; abel
    obtain ⟨e1, e2⟩ := sep_lemma' hd (Submodule.mem_sup_left hg₁)
      (add_mem (hL₁ hl₁) (Submodule.mem_sup_right hb₁)) (Submodule.mem_sup_left hg₂)
      (add_mem (hL₂ hl₂) (Submodule.mem_sup_right hb₂)) e
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hg₁, ?_⟩))
      (Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨hg₂, ?_⟩))
    · rw [e1]
      exact add_mem (Submodule.mem_sup_left hl₁) (Submodule.mem_sup_right hb₁)
    · rw [e2]
      exact add_mem (Submodule.mem_sup_left hl₂) (Submodule.mem_sup_right hb₂)
  · refine sup_le (le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans ?_))
      (le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans ?_))
    · exact sup_le_sup le_sup_left le_sup_left
    · exact sup_le_sup le_sup_right le_sup_right

theorem inf_split (G₁ B₁ L₁ G₂ B₂ L₂ : Submodule O V) (hd : Disjoint (G₁ ⊔ B₁) (G₂ ⊔ B₂))
    (hL₁ : L₁ ≤ G₁ ⊔ B₁) (hL₂ : L₂ ≤ G₂ ⊔ B₂) :
    (L₁ ⊔ L₂) ⊓ (G₁ ⊔ G₂) = L₁ ⊓ G₁ ⊔ L₂ ⊓ G₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨g₁, hg₁, g₂, hg₂, hg⟩ := Submodule.mem_sup.mp hx2
    obtain ⟨e1, e2⟩ := sep_lemma' hd (hL₁ hl₁) (Submodule.mem_sup_left hg₁) (hL₂ hl₂)
      (Submodule.mem_sup_left hg₂) hg.symm
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hl₁, ?_⟩))
      (Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨hl₂, ?_⟩))
    · rw [e1]
      exact hg₁
    · rw [e2]
      exact hg₂
  · exact sup_le (inf_le_inf le_sup_left le_sup_left) (inf_le_inf le_sup_right le_sup_right)

end GlobalTheory.CongruenceLengthSum


open GlobalTheory.CongruenceLengthSum in
theorem GlobalTheory.congruence_length_finset_sup : ∀ (O V ι : Type) [CommRing O] [AddCommGroup V] [Module O V] (F : Finset ι) (L G B : ι → Submodule O V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → (∀ i ∈ F, L i ≤ G i ⊔ B i) → Module.length O (↥(F.sup G ⊓ (F.sup L ⊔ F.sup B)) ⧸ (F.sup L ⊓ F.sup G).comap (F.sup G ⊓ (F.sup L ⊔ F.sup B)).subtype) = ∑ i ∈ F, Module.length O (↥(G i ⊓ (L i ⊔ B i)) ⧸ (L i ⊓ G i).comap (G i ⊓ (L i ⊔ B i)).subtype) := by
  classical
  intro O V ι _ _ _ F L G B
  induction F using Finset.induction_on with
  | empty =>
    intro _ _ _
    rw [Finset.sum_empty, Module.length_eq_zero_iff]
    have : Subsingleton ↥((∅ : Finset ι).sup G ⊓ ((∅ : Finset ι).sup L ⊔ (∅ : Finset ι).sup B)) :=
      ⟨fun a b => Subtype.ext (by
        have ha := a.2
        have hb := b.2
        simp only [Finset.sup_empty, bot_sup_eq, inf_bot_eq, Submodule.mem_bot] at ha hb
        rw [ha, hb])⟩
    exact (Submodule.mkQ_surjective _).subsingleton
  | insert j F hj ih =>
    intro hSI hdis hL
    have hdj : Disjoint (G j ⊔ B j) (F.sup (fun i => G i ⊔ B i)) :=
      hSI (Finset.subset_insert j F) (Finset.mem_insert_self j F) hj
    replace hSI : F.SupIndep (fun i => G i ⊔ B i) := fun t ht i hi hit =>
      hSI (ht.trans (Finset.subset_insert j F)) (Finset.mem_insert_of_mem hi) hit
    have hGB : F.sup (fun i => G i ⊔ B i) = F.sup G ⊔ F.sup B := Finset.sup_sup (s := F) (f := G) (g := B)
    rw [hGB] at hdj
    have hLF : F.sup L ≤ F.sup G ⊔ F.sup B := Finset.sup_le fun i hi =>
      (hL i (Finset.mem_insert_of_mem hi)).trans (sup_le_sup (Finset.le_sup hi) (Finset.le_sup hi))
    have hLj : L j ≤ G j ⊔ B j := hL j (Finset.mem_insert_self j F)
    rw [Finset.sum_insert hj, Finset.sup_insert, Finset.sup_insert, Finset.sup_insert]
    rw [sup_inf_split _ _ _ _ _ _ hdj hLj hLF, inf_split _ _ _ _ _ _ hdj hLj hLF]
    have hS₁ : L j ⊓ G j ≤ G j ⊓ (L j ⊔ B j) := le_inf inf_le_right (inf_le_left.trans le_sup_left)
    have hS₂ : F.sup L ⊓ F.sup G ≤ F.sup G ⊓ (F.sup L ⊔ F.sup B) :=
      le_inf inf_le_right (inf_le_left.trans le_sup_left)
    have hT : Disjoint (G j ⊓ (L j ⊔ B j)) (F.sup G ⊓ (F.sup L ⊔ F.sup B)) :=
      hdj.mono (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_left)
    rw [length_quot_sup _ _ _ _ hS₁ hS₂ hT, ih hSI (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
      (fun i hi => hL i (Finset.mem_insert_of_mem hi))]
end
