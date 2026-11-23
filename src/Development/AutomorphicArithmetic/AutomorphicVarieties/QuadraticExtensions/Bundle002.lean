module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
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
import Mathlib.GroupTheory.Nilpotent
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.extTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (h : U ≤ V) (σ : Γ) (hσ : σ ∈ V) (h2 : σ * σ ∈ U), IsOpen (U.subgroupOf V : Set V) → U.relIndex V = 2 → σ ∉ U → (∀ s ∈ S, s ∈ V → s ∈ U) →
      ∀ φ ∈ CharOff U S 2, (∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ u' = φ u) → φ ⟨σ * σ, h2⟩ = 0 →
      ∃ ψ ∈ CharOff V S 2, ψ ⟨σ, hσ⟩ = 0 ∧ ∀ u : U, ψ ⟨u.1, h u.2⟩ = φ u := by
  intro Γ _ _ _ U V S h σ hσ h2 hopen hidx hσU hS φ hφ hinv hσσ
  classical
  obtain ⟨hlc, hadd, hoff⟩ := hφ
  have key : ∀ a b : Γ, a ∈ V → b ∈ V → (a * b ∈ U ↔ (a ∈ U ↔ b ∈ U)) := by
    intro a b ha hb
    have := Subgroup.mul_mem_iff_of_index_two (H := U.subgroupOf V) hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using this
  have hσi : σ⁻¹ ∉ U := fun hh => hσU (by simpa using U.inv_mem hh)
  let Φ : Γ → ZMod 2 := fun g => if hg : g ∈ U then φ ⟨g, hg⟩ else 0
  have hΦ : ∀ g (hg : g ∈ U), Φ g = φ ⟨g, hg⟩ := fun g hg => dif_pos hg
  have hΦadd : ∀ a b, a ∈ U → b ∈ U → Φ (a * b) = Φ a + Φ b := by
    intro a b ha hb
    rw [hΦ a ha, hΦ b hb, hΦ _ (U.mul_mem ha hb), ← hadd]
    rfl
  have hR : ∀ a, a ∈ V → a ∉ U → a * σ ∈ U := fun a ha haU =>
    (key a σ ha hσ).2 (by simp [haU, hσU])
  have hL : ∀ a, a ∈ V → a ∉ U → σ⁻¹ * a ∈ U := fun a ha haU =>
    (key σ⁻¹ a (V.inv_mem hσ) ha).2 (by simp [haU, hσi])
  have hconj : ∀ a, a ∈ U → σ⁻¹ * a * σ ∈ U := by
    intro a ha
    refine hR _ (V.mul_mem (V.inv_mem hσ) (h ha)) ?_
    rw [key _ _ (V.inv_mem hσ) (h ha)]
    simp [ha, hσi]
  have hΦconj : ∀ a, a ∈ U → Φ (σ⁻¹ * a * σ) = Φ a := by
    intro a ha
    rw [hΦ a ha, hΦ _ (hconj a ha)]
    exact hinv _ _ rfl
  have hΦσ : Φ (σ * σ) = 0 := by rw [hΦ _ h2, hσσ]
  let ψ : V → ZMod 2 := fun v => if v.1 ∈ U then Φ v.1 else Φ (v.1 * σ)
  have hψU : ∀ v : V, v.1 ∈ U → ψ v = Φ v.1 := fun v hv => if_pos hv
  have hψN : ∀ v : V, v.1 ∉ U → ψ v = Φ (v.1 * σ) := fun v hv => if_neg hv
  have hψadd : ∀ a b : V, ψ (a * b) = ψ a + ψ b := by
    intro a b
    have hk := key a.1 b.1 a.2 b.2
    by_cases ha : a.1 ∈ U <;> by_cases hb : b.1 ∈ U
    · rw [hψU a ha, hψU b hb, hψU (a * b) (U.mul_mem ha hb)]
      exact hΦadd _ _ ha hb
    · have hab : (a * b).1 ∉ U := fun hh => hb ((hk.1 hh).1 ha)
      rw [hψU a ha, hψN b hb, hψN _ hab, ← hΦadd _ _ ha (hR _ b.2 hb), Subgroup.coe_mul, mul_assoc]
    · have hab : (a * b).1 ∉ U := fun hh => ha ((hk.1 hh).2 hb)
      rw [hψN a ha, hψU b hb, hψN _ hab, ← hΦconj _ hb, ← hΦadd _ _ (hR _ a.2 ha) (hconj _ hb), Subgroup.coe_mul]
      congr 1
      group
    · have hab : (a * b).1 ∈ U := hk.2 (by simp [ha, hb])
      have e1 : Φ (b.1 * σ) = Φ (σ⁻¹ * b.1) := by
        rw [← hΦconj _ (hR _ b.2 hb), show σ⁻¹ * (b.1 * σ) * σ = (σ⁻¹ * b.1) * (σ * σ) by group,
          hΦadd _ _ (hL _ b.2 hb) h2, hΦσ, add_zero]
      rw [hψN a ha, hψN b hb, hψU _ hab, e1, ← hΦadd _ _ (hR _ a.2 ha) (hL _ b.2 hb), Subgroup.coe_mul]
      congr 1
      group
  have hφ1 : φ 1 = 0 := by
    have := hadd 1 1
    rw [mul_one] at this
    exact left_eq_add.1 this
  refine ⟨ψ, ⟨?_, hψadd, ?_⟩, ?_, ?_⟩
  · obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (hlc {0})
    have hW : IsOpen ((U.subgroupOf V : Set V) ∩ Subtype.val ⁻¹' O) :=
      hopen.inter (hO.preimage continuous_subtype_val)
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' ((U.subgroupOf V : Set V) ∩ Subtype.val ⁻¹' O),
      hW.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · have h1 : (1 : U) ∈ Subtype.val ⁻¹' O := by rw [hOe]; exact hφ1
      simp only [Set.mem_preimage, inv_mul_cancel]
      exact ⟨(U.subgroupOf V).one_mem, h1⟩
    · rintro y ⟨hy1, hy2⟩
      have hy1' : (x⁻¹ * y).1 ∈ U := hy1
      have h0 : (⟨_, hy1'⟩ : U) ∈ Subtype.val ⁻¹' O := hy2
      rw [hOe] at h0
      have h0' : ψ (x⁻¹ * y) = 0 := by
        rw [hψU _ hy1', hΦ _ hy1']
        exact h0
      have := hψadd x (x⁻¹ * y)
      rwa [mul_inv_cancel_left, h0', add_zero] at this
  · intro v hv
    have hvU := hS _ hv v.2
    rw [hψU v hvU, hΦ _ hvU]
    exact hoff _ hv
  · rw [hψN _ hσU]
    exact hΦσ
  · intro u
    rw [hψU _ u.2]
    exact hΦ _ u.2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have hv := congrArg A.valuation h
  rw [map_pow, map_one] at hv
  exact (pow_eq_one_iff.mp hv).resolve_right hm

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  have hS : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff]
    refine Subring.sum_mem A.toSubring (fun j _ => ?_)
    have hj : η ^ j ∈ A := by
      rw [← ValuationSubring.valuation_le_one_iff, map_pow, h1, one_pow]
    exact hj
  rw [← mul_neg_geom_sum, map_mul, Valuation.map_sub_swap]
  exact mul_lt_one_of_lt_of_le h hS

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  have hS : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have hg := mul_neg_geom_sum η m
    rw [hη, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  have h1 : A.valuation η = 1 := aux_one A hm hη
  have hlt : A.valuation ((m : Ω) - ∑ i ∈ Finset.range m, η ^ i) < 1 := by
    have he : (m : Ω) - ∑ i ∈ Finset.range m, η ^ i = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
      simp [Finset.sum_sub_distrib]
    rw [he]
    exact Valuation.map_sum_lt _ one_ne_zero (fun i _ => power_bounds_of_between A h1 h i)
  rw [hS, sub_zero] at hlt
  exact hv hlt

private theorem inertia_fixes_prime_to_roots {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hA : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) {ζ : Ω} (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have hI : g ∈ Inertia (F := ℚ) A := hg
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hζ
    exact zero_ne_one hζ
  have hv1 := aux_one A hm hζ
  have key := hI.2 ζ hv1.le
  have hη : (g ζ * ζ⁻¹) ^ m = 1 := by
    rw [mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : A.valuation (g ζ * ζ⁻¹ - 1) < 1 := by
    have he : g ζ * ζ⁻¹ - 1 = (g ζ - ζ) * ζ⁻¹ := by rw [sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, map_mul, map_inv₀, hv1, inv_one, mul_one]
    exact key
  have hfin := root_of_unity_eq_one_of_close_residue A hm hA hη hlt
  rwa [mul_inv_eq_one₀ hζ0] at hfin

theorem UpperTheory.V.Two.ineChar :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] (A : ValuationSubring Ω), ¬ A.valuation (m : Ω) < 1 → Ine (F := ℚ) A ≤ (galChar Ω m).ker := by
  intro Ω _ _ _ m _ A hA g hg
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hfix := inertia_fixes_prime_to_roots A (NeZero.ne m) hA hg hz.pow_eq_one
  rw [galChar_spec m g z hz.pow_eq_one] at hfix
  obtain ⟨u, rfl⟩ := hz.isUnit (NeZero.ne m)
  have hu : IsPrimitiveRoot u m := IsPrimitiveRoot.coe_units_iff.mp hz
  have heq : u ^ ((galChar Ω m g : ZMod m).val) = u ^ 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_one]
    exact hfix
  have hmod := pow_eq_pow_iff_modEq.mp heq
  rw [← hu.eq_orderOf] at hmod
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [Units.val_one, ← ZMod.natCast_zmod_val ((galChar Ω m g : ZMod m)), ← Nat.cast_one]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem mem_princ_iff (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (g : G ℚ Ω) : cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔ g ∈ (galChar Ω (l ^ n)).ker := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have e : cycZ ℚ Ω l g = cyclotomicCharacter Ω l g.toRingEquiv := rfl
  have h1 : cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔
      (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow n = 1 := by
    rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, Units.ext_iff, e]
    rfl
  rw [h1, cyclotomicCharacter.toZModPow, MonoidHom.mem_ker, Units.ext_iff]
  rfl

theorem UpperTheory.V.Two.levChar :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (U : Subgroup (G ℚ Ω)), levU l U n = U ⊓ (galChar Ω (l ^ n)).ker ∧ (cycZ ℚ Ω l).ker ≤ (galChar Ω (l ^ n)).ker := by
  intro Ω _ _ _ l _ n U
  refine ⟨?_, fun g hg => ?_⟩
  · ext g
    rw [levU, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_comap, mem_princ_iff]
  · rw [← mem_princ_iff, MonoidHom.mem_ker.1 hg]
    exact one_mem _
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.muIff :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω] (n : ℕ) [NeZero n], (∃ ζ : L, IsPrimitiveRoot ζ n) ↔ galOf ℚ L Ω ≤ (galChar Ω n).ker := by
  intro Ω _ _ _ L _ _ _ n _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  have key : ∀ g : G ℚ Ω, ∀ z : Ω, IsPrimitiveRoot z n → (g z = z ↔ galChar Ω n g = 1) := by
    intro g z hz
    rw [galChar_spec n g z hz.pow_eq_one]
    have hiff : z ^ ((galChar Ω n g : ZMod n).val) = z ↔
        (((galChar Ω n g : ZMod n).val : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      obtain ⟨u, rfl⟩ := hz.isUnit (NeZero.ne n)
      have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.mp hz
      nth_rewrite 2 [← pow_one (u : Ω)]
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_inj,
        pow_eq_pow_iff_modEq, ← hu.eq_orderOf, ZMod.natCast_eq_natCast_iff]
    rw [hiff, ZMod.natCast_zmod_val, Nat.cast_one, ← Units.val_one, Units.val_inj]
  constructor
  · rintro ⟨ζ, hζ⟩ g hg
    rw [MonoidHom.mem_ker, ← key g _ (hζ.map_of_injective (algebraMap L Ω).injective)]
    exact hg ζ
  · intro hle
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) L
    haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
    obtain ⟨ζ, hζ⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) z).mpr (fun f => by
      have hf := hle (galEmb_mem ℚ L Ω f)
      rw [MonoidHom.mem_ker, ← key _ z hz, galEmb_apply] at hf
      exact hf)
    refine ⟨ζ, ?_⟩
    rw [← hζ] at hz
    exact (IsPrimitiveRoot.map_iff_of_injective (algebraMap L Ω).injective).mp hz
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem root_of_hasMu (l : ℕ) (A : AbF) (L : Type) [Field L] [NumberField L] (hA : A.HasMu l)
    (hL : IsAbField A L) : ∃ ζ : L, IsPrimitiveRoot ζ l := by
  obtain ⟨N, hN, j, ζ, h1, h2, h3⟩ := hL
  obtain ⟨hl, hker⟩ := hA
  obtain ⟨k, hk⟩ := hl.trans h1
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne⟩
  haveI : IsGalois ℚ (CyclotomicField N ℚ) :=
    @IsCyclotomicExtension.isGalois {N} ℚ _ _ _ _ (CyclotomicField.isCyclotomicExtension N ℚ)
  have hη : IsPrimitiveRoot (ζ ^ k) l := h2.pow (NeZero.pos N) (by rw [hk, mul_comm])
  have key : ∀ b : ℕ, (ζ ^ k) ^ b = (ζ ^ k) ^ (b % l) := fun b => by
    conv_lhs => rw [← Nat.mod_add_div b l]
    rw [pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]
  have hmem : ζ ^ k ∈ j.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hfix : ∀ x : L, τ (j x) = j x := fun x => hτ _ ⟨x, rfl⟩
    have hτN : (τ ζ) ^ N = 1 := by rw [← map_pow, h2.pow_eq_one, map_one]
    obtain ⟨a, -, ha⟩ := h2.eq_pow_of_pow_eq_one hτN
    have hmod : a ≡ 1 [MOD l] := hker a ((h3 τ a ha.symm).1 hfix)
    have hpow : (ζ ^ k) ^ a = (ζ ^ k) ^ 1 := by
      rw [key a, key 1, show a % l = 1 % l from hmod]
    rw [map_pow, ← ha, ← pow_mul, mul_comm, pow_mul, hpow, pow_one]
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, IsPrimitiveRoot.of_map_of_injective (f := (j : L →+* CyclotomicField N ℚ)) ?_ j.toRingHom.injective⟩
  rw [show (j : L →+* CyclotomicField N ℚ) x = ζ ^ k from hx]
  exact hη

private theorem unitsMap_nat {m n a : ℕ} (h : m ∣ n) (u : (ZMod n)ˣ) (e : (u : ZMod n) = (a : ZMod n)) :
    ((ZMod.unitsMap h u : (ZMod m)ˣ) : ZMod m) = (a : ZMod m) := by
  rw [ZMod.unitsMap_def]
  simp [Units.coe_map, ZMod.castHom_apply, e, ZMod.cast_natCast h]

private theorem ker_sup {A B : AbF} {a : ℕ} (h : (A.sup B).ker a) : A.ker a ∧ B.ker a := by
  obtain ⟨u, ⟨hu1, hu2⟩, e⟩ := h
  exact ⟨⟨_, hu1, unitsMap_nat _ _ e⟩, ⟨_, hu2, unitsMap_nat _ _ e⟩⟩

private theorem hasMu_sup_left {A : AbF} (B : AbF) {l : ℕ} (h : A.HasMu l) : (A.sup B).HasMu l := by
  exact ⟨dvd_mul_of_dvd_left h.1 _, fun a ha => h.2 a (ker_sup ha).1⟩

private theorem hasMu_sup_right (A : AbF) {B : AbF} {l : ℕ} (h : B.HasMu l) : (A.sup B).HasMu l := by
  exact ⟨dvd_mul_of_dvd_right h.1 _, fun a ha => h.2 a (ker_sup ha).2⟩

private theorem hasMu_withI (M : AbF) : (withI M).HasMu 4 :=
  hasMu_sup_right M (AbF.hasMu_cyc (l := 4) (q := 1) (by norm_num) (by norm_num))

theorem UpperTheory.V.Two.hasMuQ :
    (∀ (l : ℕ) (A : AbF) (L : Type) [Field L] [NumberField L], A.HasMu l → IsAbField A L → ∃ ζ : L, IsPrimitiveRoot ζ l) ∧
      (∀ (M : AbF) (L : Type) [Field L] [NumberField L], IsAbField (withI M) L → ∃ ζ : L, IsPrimitiveRoot ζ 4) ∧
      ∀ (M : AbF) (q d : ℕ) (L : Type) [Field L] [NumberField L], IsAbField (base2 M q d) L → ∃ ζ : L, IsPrimitiveRoot ζ 4 := by
  refine ⟨fun l A L _ _ hA hL => root_of_hasMu l A L hA hL,
    fun M L _ _ hL => root_of_hasMu 4 _ L (hasMu_withI M) hL,
    fun M q d L _ _ hL => root_of_hasMu 4 _ L ?_ hL⟩
  exact hasMu_sup_left _ (hasMu_sup_left _ (hasMu_withI M))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.ineConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : G F Ω), (∀ (B : ValuationSubring Ω) (g : G F Ω), g ∈ Ine (F := F) (v • B) → v⁻¹ * g * v ∈ Ine (F := F) B) ∧
      (∀ (B : ValuationSubring Ω) (N : ℕ), (v • B).valuation (N : Ω) < 1 ↔ B.valuation (N : Ω) < 1) ∧ ∀ (N : ℕ), ∀ s ∈ ineOff F Ω N, v⁻¹ * s * v ∈ ineOff F Ω N := by
  intro F Ω _ _ _ _ _ v
  have hlt : ∀ (A : ValuationSubring Ω) (y : Ω), y ≠ 0 → (A.valuation y < 1 ↔ y⁻¹ ∉ A) := by
    intro A y hy
    rw [← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hy), inv_inv]
  have hL : ∀ (w : G F Ω) (B : ValuationSubring Ω) (x : Ω), (w • B).valuation x < 1 ↔ B.valuation (w⁻¹ • x) < 1 := by
    intro w B x
    by_cases hx : x = 0
    · subst hx
      simp
    have hx' : w⁻¹ • x ≠ 0 := by simpa using hx
    rw [hlt _ _ hx, hlt _ _ hx', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'']
  have p1 : ∀ (B : ValuationSubring Ω) (g : G F Ω), g ∈ Ine (F := F) (v • B) → v⁻¹ * g * v ∈ Ine (F := F) B := by
    intro B g hg
    obtain ⟨hd, hi⟩ := hg
    refine ⟨?_, ?_⟩
    · have hd' : g • (v • B) = v • B := hd
      show (v⁻¹ * g * v) • B = B
      rw [mul_smul, mul_smul, hd', inv_smul_smul]
    · intro x hx
      have hvx : (v • B).valuation (v x) ≤ 1 := by
        rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
          ← ValuationSubring.valuation_le_one_iff]
        simpa [AlgEquiv.smul_def] using hx
      have h2 := hi (v x) hvx
      rw [hL] at h2
      convert h2 using 2
      simp [AlgEquiv.smul_def, map_sub, AlgEquiv.mul_apply]
  have p2 : ∀ (B : ValuationSubring Ω) (N : ℕ), (v • B).valuation (N : Ω) < 1 ↔ B.valuation (N : Ω) < 1 := by
    intro B N
    rw [hL]
    simp [AlgEquiv.smul_def]
  refine ⟨p1, p2, ?_⟩
  rintro N s ⟨A, hA, hs⟩
  have hA' : v • (v⁻¹ • A) = A := smul_inv_smul v A
  refine ⟨v⁻¹ • A, ?_, ?_⟩
  · rw [← p2, hA']
    exact hA
  · apply p1
    rw [hA']
    exact hs
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.abField :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : AbF) (L : Type) [Field L] [NumberField L] [Algebra L Ω], IsAbField A L → galOf ℚ L Ω = abU Ω A := by
  intro Ω _ _ _ A L _ _ _ hL
  obtain ⟨N, hN, j, ζ, hm, hζ, hj⟩ := hL
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Normal ℚ (CyclotomicField N ℚ) := by
    haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
    have h := CyclotomicField.isCyclotomicExtension (n := N) (K := ℚ)
    have h2 := (@IsCyclotomicExtension.isGalois _ _ _ _ _ _ h).to_normal
    convert h2
    exact Subsingleton.elim _ _
  let k : CyclotomicField N ℚ →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra (CyclotomicField N ℚ) Ω := k.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField N ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsScalarTower ℚ L Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have key : ∀ σ : G ℚ Ω, (∀ x : L, σ (k (j x)) = k (j x)) ↔ galChar Ω A.m σ ∈ A.H := by
    intro σ
    let τ := σ.restrictNormal (CyclotomicField N ℚ)
    have hτ : ∀ y, k (τ y) = σ (k y) := fun y => σ.restrictNormal_commutes (CyclotomicField N ℚ) y
    have hkζ : IsPrimitiveRoot (k ζ) N := hζ.map_of_injective k.injective
    have hσζ : σ (k ζ) = k ζ ^ (galChar Ω N σ : ZMod N).val :=
      galChar_spec N σ (k ζ) hkζ.pow_eq_one
    have hτζ : τ ζ = ζ ^ (galChar Ω N σ : ZMod N).val := by
      apply k.injective
      show k (τ ζ) = k (ζ ^ _)
      rw [hτ, hσζ, map_pow]
    have h1 := hj τ _ hτζ
    have hfix : (∀ x : L, τ (j x) = j x) ↔ (∀ x : L, σ (k (j x)) = k (j x)) :=
      forall_congr' fun x => by rw [← hτ]; exact k.injective.eq_iff.symm
    rw [← hfix, h1]
    obtain ⟨d, hd⟩ := hm
    have hprim : IsPrimitiveRoot (k ζ ^ d) A.m :=
      hkζ.pow (Nat.pos_of_ne_zero (NeZero.ne N)) (hd.trans (mul_comm _ _))
    have e1 := galChar_spec A.m σ (k ζ ^ d) hprim.pow_eq_one
    rw [map_pow, hσζ, ← pow_mul, mul_comm _ d, pow_mul] at e1
    have hfin : IsOfFinOrder (k ζ ^ d) := isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hprim.pow_eq_one⟩
    have hmod : (galChar Ω N σ : ZMod N).val ≡ (galChar Ω A.m σ : ZMod A.m).val [MOD A.m] := by
      have h2 := hfin.pow_eq_pow_iff_modEq.1 e1
      rwa [← hprim.eq_orderOf] at h2
    have hcast : (((galChar Ω N σ : ZMod N).val : ℕ) : ZMod A.m) = (galChar Ω A.m σ : ZMod A.m) := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hmod, ZMod.natCast_zmod_val]
    constructor
    · rintro ⟨u, hu, hua⟩
      have hu' : u = galChar Ω A.m σ := Units.ext (hua.trans hcast)
      exact hu' ▸ hu
    · intro h
      exact ⟨_, h, hcast.symm⟩
  let σ₀ : Ω →ₐ[ℚ] Ω := j.liftNormal Ω
  have hσ₀ : ∀ x : L, σ₀ (algebraMap L Ω x) = k (j x) := fun x => j.liftNormal_commutes Ω x
  let e : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  have he : ∀ x : L, e (algebraMap L Ω x) = k (j x) := hσ₀
  have hconj : ∀ σ : G ℚ Ω, galChar Ω A.m (e * σ * e⁻¹) = galChar Ω A.m σ := by
    intro σ
    rw [map_mul, map_mul, map_inv, mul_comm (galChar Ω A.m e), mul_assoc, mul_inv_cancel, mul_one]
  ext σ
  change (∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) ↔ galChar Ω A.m σ ∈ A.H
  rw [← hconj σ, ← key]
  refine forall_congr' fun x => ?_
  rw [← he, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply,
    e.injective.eq_iff]
end
