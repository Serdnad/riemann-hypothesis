module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDiamondCommuteModCoboundariesGamma1Gamma0
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle241
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle276
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle279
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle126
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle196
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0 : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → Odd k →
  ∀ (q q' : ℕ) (σ σ' τ τ' : SL(2, ℤ)) (d d' : ZMod N), q.Prime → ¬ q ∣ N * l → q'.Prime → ¬ q' ∣ N * l →
   IsDiam N l (q : ZMod N) σ → IsDiam N l (q' : ZMod N) σ' → IsDiam N l d τ → IsDiam N l d' τ' →
   ∀ z ∈ Z1 (Lev N l) (k - 2),
    TqZ (Lev N l) (k - 2) q σ (TqZ (Lev N l) (k - 2) q' σ' z) - TqZ (Lev N l) (k - 2) q' σ' (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (UlZ (Lev N l) (k - 2) l z) - UlZ (Lev N l) (k - 2) l (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    UlZ (Lev N l) (k - 2) l (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (UlZ (Lev N l) (k - 2) l z) ∈ B1 (Lev N l) (k - 2) ∧
    DdZ (Lev N l) (k - 2) τ (DdZ (Lev N l) (k - 2) τ' z) - DdZ (Lev N l) (k - 2) τ' (DdZ (Lev N l) (k - 2) τ z) ∈ B1 (Lev N l) (k - 2) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt | exact GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt | (intros; apply GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

theorem cup_eq_coboundary_vanishing_on_inertia : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) ∧
        ∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hC1 : IsFirstChernClassOfLineBundle K := GlobalTheory.T.tsen_theorem k K
  have hnorm : ∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 →
      ∃ x : L, Algebra.norm K x = c := fun L _ c hc => GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass K L hC1 c hc
  obtain ⟨η₀, hη₀c, hη₀⟩ := GlobalTheory.T.exists_locallyConstant_kum_cup_coboundary_of_norm_surj K Ω N ζ hN hζ hfix hnorm a b α β ha0 hb0 hα hβ
  obtain ⟨θ, hθ0, hθE, hθη, hθs⟩ :=
    GlobalTheory.T.kummer_cochain_character_galoisInvariant_class K Ω N ζ hN hζ hfix a b α β ha0 hb0 hα hβ η₀ hη₀c hη₀
  obtain ⟨f, hf0, hfB⟩ := GlobalTheory.T.kummer_divisor_descends_functionField k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ hθ0 hθE hθs
  obtain ⟨θ₀, hθ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω f) hN
  have hθ₀0 : θ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hθ₀
    exact hf0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hθ₀.symm)
  obtain ⟨hk0c, -, hk0add, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ θ₀ hN hζ hfix hθ₀0 ⟨f, hθ₀.symm⟩
  refine ⟨fun g => η₀ g - kum ζ θ₀ g, hη₀c.sub hk0c, ?_, ?_⟩
  · intro g h
    simp only
    rw [hη₀ g h, hk0add g h]
    ring
  · intro B hB g hg
    obtain ⟨c, hcE, hc0, hcv⟩ := hfB B hB
    rw [← hθ₀] at hcv
    obtain ⟨hgE, hk⟩ := GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ θ₀ hθ0 hθ₀0 hθE
      ⟨f, hθ₀.symm⟩ B hB g hg c hcE hc0 hcv
    show η₀ g - kum ζ θ₀ g = 0
    rw [hθη g hgE, hk, sub_self]

theorem thmA : GlobalTheory.NeedB.ThmA := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha0 hb0 haA hai hbA hbi hα hβ
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hβ.symm)
  obtain ⟨hαc, -, hαadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hβc, -, hβadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  exact ⟨hαadd, hαc, hβadd, hβc,
    cup_eq_coboundary_vanishing_on_inertia k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ⟩

end GlobalTheory.KummerCob
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_ringEquiv_coeff_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω),
    ∃ σ : GlobalTheory.FN.ring ε.range ≃+* GlobalTheory.FN.ring ε.range, ∀ (a : GlobalTheory.FN.ring ε.range) (h h' : HahnSeries ℚ Ω),
      IsExp ε a h → IsExp ε (σ a : GlobalTheory.FN.ring ε.range) h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s
  obtain ⟨e, he_inj, he⟩ := GlobalTheory.T.exists_injective_cuspExpansion_ringHom Ω ε
  have hmem := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1
  have key : ∀ t : Ω ≃+* Ω, ∃ c : ring ε.range → ring ε.range, ∀ a,
      (∀ r, (e (c a)).coeff r = t ((e a).coeff r)) ∧
      ∀ h h' : HahnSeries ℚ Ω, IsExp ε a h → IsExp ε (c a : ℍ → ℂ) h' → ∀ r, h'.coeff r = t (h.coeff r) := by
    intro t
    have hex : ∀ a : ring ε.range, ∃ b : ring ε.range, ∀ h h' : HahnSeries ℚ Ω,
        IsExp ε a h → IsExp ε (b : ℍ → ℂ) h' → ∀ r, h'.coeff r = t (h.coeff r) := by
      intro a
      obtain ⟨f', hf', hp⟩ := GlobalTheory.T.exists_galoisConjugate_modularFunction_someLevel Ω ε t a ((hmem a).1 a.2)
      exact ⟨⟨f', (hmem f').2 hf'⟩, hp⟩
    choose c hc using hex
    exact ⟨c, fun a => ⟨hc a (e a) (e (c a)) (he a) (he (c a)), hc a⟩⟩
  have mapc : ∀ t : Ω ≃+* Ω, ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω, ∀ h r, (Φ h).coeff r = t (h.coeff r) := by
    intro t
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω t.toRingHom 1 (fun _ => 1) one_pos rfl (by simp)
    exact ⟨Φ, fun h r => by simpa using hΦ h r⟩
  obtain ⟨c, hc⟩ := key s
  obtain ⟨d, hd⟩ := key s.symm
  obtain ⟨Φ, hΦ⟩ := mapc s
  have ec : ∀ a, e (c a) = Φ (e a) := fun a => by
    ext r
    rw [(hc a).1, hΦ]
  refine ⟨{ toFun := c, invFun := d, left_inv := ?_, right_inv := ?_, map_add' := ?_, map_mul' := ?_ },
    fun a h h' => (hc a).2 h h'⟩
  · intro a
    apply he_inj
    ext r
    rw [(hd _).1, (hc a).1]
    simp
  · intro a
    apply he_inj
    ext r
    rw [(hc _).1, (hd a).1]
    simp
  · intro a b
    apply he_inj
    simp only [map_mul, ec]
  · intro a b
    apply he_inj
    simp only [map_add (f := _), ec]

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem reciprocity_large_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hbK : T.io b ≠ 0 := by
    intro h
    exact hb (T.io_inj (by rw [h, map_zero]))
  have hf : f = T.io a / T.io b := by
    rw [eq_div_iff hbK, hab]
  obtain ⟨Na, wa, hNa, hLa⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 a).1 a.2
  obtain ⟨Nb, wb, hNb, hLb⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 b).1 b.2
  refine ⟨Na * Nb, Nat.mul_pos hNa hNb, ?_⟩
  intro N hN hdiv s d hs γ γ' hc
  have hLa' : Lv ε.range N wa a :=
    GlobalTheory.T.lv_mono_of_dvd_of_le ε.range Na N wa wa a hN (dvd_trans (dvd_mul_right Na Nb) hdiv) le_rfl hLa
  have hLb' : Lv ε.range N wb b :=
    GlobalTheory.T.lv_mono_of_dvd_of_le ε.range Nb N wb wb b hN (dvd_trans (dvd_mul_left Nb Na) hdiv) le_rfl hLb
  have ra := GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr Ω ε T a N wa hN hLa' s d hs γ γ' hc
  have rb := GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr Ω ε T b N wb hN hLb' s d hs γ γ' hc
  rw [hf, map_div₀, map_div₀, map_div₀, map_div₀, ra, rb]

end GlobalTheory.FN
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_mem_twKer_unipB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  intro k _ _ _ _ n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ψ V _ _ π hπ hψ hord v hv heig
  rcases GlobalTheory.T.orderedCharacterFamily_splits_or_constant_on_units k n ψ hord with ⟨r, hr0, hrn, hcut⟩ | ⟨χ, hχ, hag⟩
  swap
  · obtain ⟨hg, hth, -, -⟩ := GlobalTheory.T.principalSeriesType_data_depend_only_on_units k n ψ _ hag
    rw [hg, hth] at heig
    exact GlobalTheory.T.jacquetKernel_eigenvector_eq_zero_of_const_character k n χ V π hπ (hχ hψ) v hv heig
  obtain ⟨t, rfl⟩ : ∃ t, n = r + t := ⟨n - r, by omega⟩
  have ht : 0 < t := by omega
  set e := stdSum (rfl : r + t = r + t) with he
  set ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i) with hψ₁
  set ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i) with hψ₂
  obtain ⟨ho₁, ho₂, hmem⟩ := GlobalTheory.T.blockDiagonal_principalSeriesCongruenceSubgroup_split k r t ψ hord hcut
  have hs₁ : ∀ i, IsSmoothChar (ψ₁ i) := fun i => hψ _
  have hs₂ : ∀ i, IsSmoothChar (ψ₂ i) := fun i => hψ _
  have one_grp : ∀ (m : ℕ) (φ : Fin m → kˣ →* ℂˣ), (1 : GL (Fin m) k) ∈ grp φ := by
    intro m φ
    refine ⟨(KO k (Fin m)).one_mem, fun i j hij => ?_⟩
    have h0 : ((1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
  let Q := twKer π (unipRad k (two e)) 1
  let ρ := jacU₂ e π
  have hρ : IsSmooth ρ := isSmooth_comp (isSmooth_jacU _ hπ) _ (continuous_leviTwo k)
  have hact : ∀ g w, ρ g (Q.mkQ w) = Q.mkQ (π (emb₂ k e g) w) := fun g w => rfl
  let P : Submodule ℂ V := (twKer (ρ.comp (MonoidHom.inl _ _)) (unipB k (Fin r)) 1 ⊔
      twKer (ρ.comp (MonoidHom.inr _ _)) (unipB k (Fin t)) 1).comap Q.mkQ
  have hP : twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
    refine GlobalTheory.T.twistedJacquetKernel_twoBlock_unipotent_le_stages k r t V π P ?_ ?_ ?_
    · intro w hw
      refine Submodule.mem_comap.2 ?_
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero Q).2 hw]
      exact zero_mem _
    · intro u hu w
      refine Submodule.mem_comap.2 ?_
      refine Submodule.mem_sup_left (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rfl
    · intro u hu w
      refine Submodule.mem_comap.2 ?_
      refine Submodule.mem_sup_right (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rfl
  have hx := hP hv
  have hzero : Q.mkQ v = 0 := by
    refine GlobalTheory.T.twistedJacquet_survival_product_of_two_groups (GL (Fin r) k) (GL (Fin t) k) _ ρ hρ (unipB k (Fin r)) (unipB k (Fin t))
      (grp ψ₁) (grp ψ₂) (theta ψ₁) (theta ψ₂)
      (fun W _ _ σ hσ w hw hwe => ih r (by omega) ψ₁ W σ hσ hs₁ ho₁ w hw hwe)
      (fun W _ _ σ hσ w hw hwe => ih t (by omega) ψ₂ W σ hσ hs₂ ho₂ w hw hwe)
      (Q.mkQ v) hx ?_ ?_
    · intro a ha
      have hm : emb₂ k e (a, 1) ∈ grp ψ := (hmem a 1).2 ⟨ha, one_grp _ _⟩
      have hth := GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord a ha 1 (one_grp _ _)
      rw [(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k t ψ₂ hs₂).1, mul_one] at hth
      show ρ (a, 1) (Q.mkQ v) = _
      rw [hact, heig _ hm, map_smul]
      exact congrArg (· • Q.mkQ v) hth
    · intro b hb
      have hm : emb₂ k e (1, b) ∈ grp ψ := (hmem 1 b).2 ⟨one_grp _ _, hb⟩
      have hth := GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord 1 (one_grp _ _) b hb
      rw [(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k r ψ₁ hs₁).1, one_mul] at hth
      show ρ (1, b) (Q.mkQ v) = _
      rw [hact, heig _ hm, map_smul]
      exact congrArg (· • Q.mkQ v) hth
  have hvQ : v ∈ Q := (Submodule.Quotient.mk_eq_zero Q).1 hzero
  exact GlobalTheory.T.jacquetModule_maximalParabolic_principalSeriesTypeEigen k r t ψ V π hπ hψ hord hcut v hvQ heig

end GlobalTheory.PsType
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.depletedCuspEigenform_eigenvalue_eq_char_mul_conj : ∀ (k N q : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g → q.Prime → ¬ q ∣ N → g q = ch χ q * conj (g q) := by
  first | exact @GlobalTheory.EisMReal.eig_conj | exact GlobalTheory.EisMReal.eig_conj | (intros; apply GlobalTheory.EisMReal.eig_conj <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_heckeEigenfunctional_of_depletedEigenform : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (α β : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → Prim k N χ g → Wt (N * l) ρ → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (k - 1) → ∃ (B : ℕ) (c : ℕ → ℂ), EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = pet k ρ (qs (Vo l fun n => conj (g n))) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs fun n => conj (g n)) (qs a) := by
  first | exact @GlobalTheory.EisM.eigF_of_prim | exact GlobalTheory.EisM.eigF_of_prim | (intros; apply GlobalTheory.EisM.eigF_of_prim <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.siegelUnitAtScaledArgument_twoVariableExpansion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L N c : ℕ) (A₁ a₂ g : ℤ), 1 ≤ L → a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∃ θ : ℤ → ℤ → ℤ,
    (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) ∧
    (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) ∧
    (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) ∧
    (∀ r : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = ∑ᶠ k : ℤ, (θ k r : Ω) * zt ε p L ^ (g * k)) ∧
    (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ω) * zt ε p L ^ (g * k) =
      -∑ᶠ i : ℤ, (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L)) ∧
    (∀ n : ℕ, smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ n ∈ Subring.closure {zt ε p L}) ∧
    (∃ r m : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = zt ε p L ^ m ∨
      (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = -(zt ε p L ^ m)) := by
  first | exact @GlobalTheory.SiegTwo.sgN_two_variable | exact GlobalTheory.SiegTwo.sgN_two_variable | (intros; apply GlobalTheory.SiegTwo.sgN_two_variable ; all_goals assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (c : ℤ_[l]) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n (c • x) (fun δ => PadicInt.toZModPow n c * χ δ) := by
  first | exact @GlobalTheory.KZ.H3.kum_smul | exact GlobalTheory.KZ.H3.kum_smul | (intros; apply GlobalTheory.KZ.H3.kum_smul <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockForm

theorem act_of_mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {x : V} (h : x ∈ wtSub act μ)
    (a : Ix p q) : act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  have := (Submodule.mem_iInf _).1 h a
  simpa [LinearMap.mem_ker, sub_eq_zero] using this

theorem form_eq_zero {p q : ℕ} (M : GKMod p q) (D : M.V → M.V → ℂ)
    (hadd₁ : ∀ x x' y, D (x + x') y = D x y + D x' y)
    (hsmul₁ : ∀ (c : ℂ) x y, D (c • x) y = star c * D x y)
    (hadd₂ : ∀ x y y', D x (y + y') = D x y + D x y')
    (hsmul₂ : ∀ (c : ℂ) x y, D x (c • y) = c * D x y)
    (hinv : ∀ Z x y, D (M.act Z x) y = D x (M.act (adjZ Z) y))
    (μ : Ix p q → ℚ) (v : M.V) (hv : v ∈ wtSub M.act μ)
    (hline : ∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) (hgen : genSub M.act {v} = ⊤)
    (hvv : D v v = 0) : ∀ x y, D x y = 0 := by
  have hv0 : ∀ y, D v y = 0 := by
    intro y
    refine Submodule.iSup_induction (motive := fun y => D v y = 0) _ (M.wts y) ?_ ?_ ?_
    · intro ν y hy
      by_cases hν : ν = μ
      · subst hν
        obtain ⟨c, rfl⟩ := hline y hy
        rw [hsmul₂, hvv, mul_zero]
      · obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
        have h := hinv (Eab a a) v y
        rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul,
          act_of_mem_wtSub hv, act_of_mem_wtSub hy, hsmul₁, hsmul₂] at h
        have hs : star ((μ a : ℚ) : ℂ) = ((μ a : ℚ) : ℂ) := by simp
        rw [hs] at h
        have hne : ((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast ha.symm
        have : (((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ)) * D v y = 0 := by linear_combination h
        exact (mul_eq_zero.1 this).resolve_left hne
    · have := hsmul₂ 0 v 0
      simpa using this
    · intro y y' h h'
      rw [hadd₂, h, h', add_zero]
  let N : Submodule ℂ M.V :=
    { carrier := {x | ∀ y, D x y = 0}
      add_mem' := fun {x x'} h h' y => by rw [hadd₁, h y, h' y, add_zero]
      zero_mem' := fun y => by simpa using hsmul₁ 0 0 y
      smul_mem' := fun c x h y => by rw [hsmul₁, h y, mul_zero] }
  have hN : genSub M.act {v} ≤ N := by
    apply sInf_le
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact hv0
    · intro Z x hx y
      rw [hinv]
      exact hx _
  intro x y
  exact hN (hgen ▸ Submodule.mem_top) y

theorem inner_eq_mul : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j : M.V →ₗ[ℂ] H₁) (E₁ E₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (M.act (adjZ Z) y))) → ∀ (μ : Ix p q → ℚ) (v : M.V), v ∈ wtSub M.act μ → (∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) → genSub M.act {v} = ⊤ → ‖j v‖ = 1 → ∀ x y, inner ℂ (E₁ x) (E₂ y) = inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y) := by
  intro p q M H₁ _ _ H₂ _ _ j E₁ E₂ hj hE μ v hv hline hgen hnorm x y
  have := form_eq_zero M
    (fun x y => inner ℂ (E₁ x) (E₂ y) - inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y))
    (fun x x' y => by simp only [map_add (f := _), inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, inner_smul_left, starRingEnd_apply]; ring)
    (fun x y y' => by simp only [map_add (f := _), inner_add_right]; ring)
    (fun c x y => by simp only [map_smul, inner_smul_right]; ring)
    (fun Z x y => by simp only [hj, hE])
    μ v hv hline hgen (by simp [inner_self_eq_norm_sq_to_K, hnorm]) x y
  exact sub_eq_zero.1 this

end GlobalTheory.FockForm
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.derivationDenominators_and_hostField_sizes : ∀ (D : D7), admG1 D → (∃ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl) ∧ Real.log D.host.d ≤ 2 * Real.log D.host.rdE ∧ 1 ≤ D.host.rdE ∧ 1 ≤ fF D ∧ Fintype.card D.what₂.Tau = fF D ∧ Module.finrank ℚ D.host.E = 2 * fF D := by
  first | exact @GlobalTheory.NormSum.letters_and_sizes | exact GlobalTheory.NormSum.letters_and_sizes | (intros; apply GlobalTheory.NormSum.letters_and_sizes <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N'), idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 ∧ (∀ q : ℕ, q.Prime → TrivAt D q (g : GL (Fin N) (AE D)) → TrivAt D q (g' : GL (Fin N') (AE D)) → ¬ q ∣ idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g')))) ∧ (IntG D (g : GL (Fin N) (AE D)) → IntG D (g' : GL (Fin N') (AE D)) → (latA D cc N N').map (actA D N N' (g, g')) ≤ latA D cc N N') := by
  first | exact @GlobalTheory.FinWeil.idx_map_actA | exact GlobalTheory.FinWeil.idx_map_actA | (intros; apply GlobalTheory.FinWeil.idx_map_actA <;> assumption)
end
