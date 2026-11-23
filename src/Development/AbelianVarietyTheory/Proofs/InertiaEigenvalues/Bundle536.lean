module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle153
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachInclusionPowerSeriesIntoOneTmulAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle519
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle520
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.TowerPlace

theorem placeIn_unique : ∀ (Λ : Subring ℂ) [IsDiscreteValuationRing Λ] (l : ℕ), l.Prime → ¬ IsUnit ((l : ℕ) : Λ) → ∃ e : ℕ, ∀ (L : Type) [Field L] [NumberField L] (ι : L →+* ℂ), (∀ x, ι x ∈ Λ ∨ (ι x)⁻¹ ∈ Λ) → ∃ la : HeightOneSpectrum (𝓞 L), placesIn ι Λ = {la} ∧ (∀ x, ι x ∈ Λ ↔ la.valuation L x ≤ 1) ∧ ((l : ℕ) : 𝓞 L) ∈ la.asIdeal ∧ ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) := by
  intro Λ _ l hl hlu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Λ
  have hl0 : ((l : ℕ) : Λ) ≠ 0 := by
    intro h
    have h' : ((((l : ℕ) : Λ)) : ℂ) = 0 := by rw [h]; rfl
    push_cast at h'
    exact hl.ne_zero (by exact_mod_cast h')
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  refine ⟨e, fun L _ _ ι hval => ?_⟩
  let B : ValuationSubring L :=
    { toSubring := Λ.comap ι
      mem_or_inv_mem' := fun x => by
        rcases hval x with h | h
        · exact Or.inl h
        · right
          show ι x⁻¹ ∈ Λ
          rw [map_inv₀]; exact h }
  have hint : ∀ x : 𝓞 L, (ι.comp (algebraMap (𝓞 L) L)) x ∈ Λ := fun x => by
    have : IsIntegral B (algebraMap (𝓞 L) L x) := (x.isIntegral_coe).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    show ι (algebraMap (𝓞 L) L x) ∈ Λ
    rw [← hy]; exact y.2
  let g : 𝓞 L →+* Λ := (ι.comp (algebraMap (𝓞 L) L)).codRestrict Λ hint
  have hg : ∀ x : 𝓞 L, ((g x : Λ) : ℂ) = ι (algebraMap (𝓞 L) L x) := fun x => rfl
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal Λ).comap g
  have hlP : ((l : ℕ) : 𝓞 L) ∈ P := by
    show g l ∈ IsLocalRing.maximalIdeal Λ
    rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hlu
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlP
    exact hl.ne_zero (by exact_mod_cast hlP)
  let la : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime _ _, hPne⟩
  have hunit : ∀ s : 𝓞 L, s ∉ la.asIdeal → IsUnit (g s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hsup : ∀ x : L, la.valuation L x ≤ 1 → ι x ∈ Λ := by
    intro x hx
    obtain ⟨a, s, h⟩ := la.exists_primeCompl_mul_eq_of_integer (K := L) x hx
    obtain ⟨w, hw⟩ := hunit s s.2
    have h3 : (((w⁻¹ : Λˣ) : Λ) : ℂ) * ι (algebraMap (𝓞 L) L s) = 1 := by
      rw [← hg, ← hw]
      have := congrArg Subtype.val w.inv_mul
      exact this
    have hs0 : ι (algebraMap (𝓞 L) L s) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h3; exact zero_ne_one h3
    have hw' : (ι (algebraMap (𝓞 L) L s))⁻¹ ∈ Λ := by
      rw [← eq_inv_of_mul_eq_one_left h3]; exact ((w⁻¹ : Λˣ) : Λ).2
    have hx' : ι x = ι (algebraMap (𝓞 L) L a) * (ι (algebraMap (𝓞 L) L s))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, h]
    rw [hx']
    exact Λ.mul_mem (hint a) hw'
  have hsub : ∀ x : L, ι x ∈ Λ → la.valuation L x ≤ 1 := by
    intro x hx
    by_contra hv
    push_neg at hv
    have hx0 : x ≠ 0 := by rintro rfl; simp at hv
    have hy : la.valuation L x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hv
    obtain ⟨a, s, h⟩ := la.exists_primeCompl_mul_eq_of_integer (K := L) x⁻¹ hy.le
    have hs1 : la.valuation L (algebraMap (𝓞 L) L s) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) (v := la)).2 s.2
    have ha : a ∈ la.asIdeal := by
      refine (la.valuation_lt_one_iff_mem (K := L) a).1 ?_
      show la.valuation L (algebraMap (𝓞 L) L a) < 1
      rw [← h, map_mul, hs1, mul_one]; exact hy
    have h4 : (⟨ι x, hx⟩ : Λ) * g a = g s := Subtype.ext (show ι x * ι (algebraMap (𝓞 L) L a) = ι (algebraMap (𝓞 L) L s) by
      rw [← map_mul, ← h, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul])
    have hga : g a ∈ IsLocalRing.maximalIdeal Λ := ha
    have := hunit s s.2
    rw [← h4] at this
    exact ((IsLocalRing.mem_maximalIdeal _).1 (Ideal.mul_mem_left _ _ hga)) this
  refine ⟨la, ?_, fun x => ⟨hsub x, hsup x⟩, hlP, ?_⟩
  · ext la'
    constructor
    · intro h'
      rw [Set.mem_singleton_iff]
      have hle : la.asIdeal ≤ la'.asIdeal := by
        intro r hr
        by_contra hr'
        have h1 : la'.valuation L (algebraMap (𝓞 L) L r) = 1 :=
          (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) (v := la')).2 hr'
        have h2 : la'.valuation L (algebraMap (𝓞 L) L r)⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
        have h3 := hsub _ (h' _ h2)
        have h5 : la.valuation L (algebraMap (𝓞 L) L r) < 1 := (la.valuation_lt_one_iff_mem (K := L) r).2 hr
        have hr0' : r ≠ 0 := by rintro rfl; exact hr' la'.asIdeal.zero_mem
        have hr0 : la.valuation L (algebraMap (𝓞 L) L r) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 hr0')
        rw [map_inv₀] at h3
        have := one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 hr0, h5⟩
        exact absurd h3 (not_le.2 this)
      have hEq : la.asIdeal = la'.asIdeal := la.isMaximal.eq_of_le la'.isPrime.ne_top hle
      exact HeightOneSpectrum.ext hEq.symm
    · intro h
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hsup
  · intro hmem
    have hmap : Ideal.map g (la.asIdeal ^ (e + 1)) ≤ (IsLocalRing.maximalIdeal Λ) ^ (e + 1) := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono Ideal.map_comap_le (e + 1)
    have h5 := hmap (Ideal.mem_map_of_mem g hmem)
    rw [map_natCast, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, hu] at h5
    obtain ⟨c, hc⟩ := h5
    have hpe : ϖ ^ e ≠ 0 := pow_ne_zero _ hϖ.ne_zero
    have hu' : (u : Λ) = ϖ * c := by
      apply mul_right_cancel₀ hpe
      rw [hc]; ring
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (hu' ▸ u.isUnit))

end GlobalTheory.TowerPlace
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_injective_of_injective : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B),
    Function.Injective f → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N),
    SemiBC u → Function.Injective u := by
  intro A B _ _ f hf M _ _ _ _ N _ _ u h
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let v : M →ₛₗ[f] (Fin n → B) :=
    { toFun := fun x i => f (s x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  rw [← LinearMap.ker_eq_bot (τ₁₂ := f), LinearMap.ker_eq_bot']
  intro x hx
  have h1 : v x = 0 := by rw [← hS, hx, map_zero]
  have h2 : s x = 0 := by
    funext i
    apply hf
    rw [Pi.zero_apply, map_zero]
    exact congrFun h1 i
  have h3 : x = p (s x) := by
    rw [← LinearMap.comp_apply, hps, LinearMap.id_apply]
  rw [h3, h2, map_zero]

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EmbTwo

theorem range_eq_of_normal {F E L : Type} [Field F] [Field E] [Algebra F E] [Normal F E] [Field L]
    [Algebra F L] (φ ψ : E →ₐ[F] L) : φ.fieldRange = ψ.fieldRange := by
  let e : E ≃ₐ[F] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal F ψ.fieldRange := Normal.of_algEquiv e
  have h := AlgHom.fieldRange_of_normal (E := ψ.fieldRange) (φ.comp e.symm.toAlgHom)
  rw [← h]
  ext x
  simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨e y, by simp⟩
  · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩

variable {l : ℕ} [Fact l.Prime]

theorem exists_approx (y : OC l) : ∃ (z : OC l) (w : OC l), (∃ z' : Om l, (z : ℂ_[l]) = (z' : ℂ_[l])) ∧
    y = z + (l : OC l) * w := by
  have hl : 0 < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  obtain ⟨z', hz'⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt (y : ℂ_[l]) hl
  set w : ℂ_[l] := (y : ℂ_[l]) - (z' : ℂ_[l]) with hw
  have hw1 : ‖w‖ < ‖((l : ℕ) : ℂ_[l])‖ := by rw [hw, ← dist_eq_norm]; exact hz'
  have hwO : w ∈ 𝓞_ℂ_[l] := (GlobalTheory.RingBasics.mem_OC _).2 (hw1.le.trans GlobalTheory.RingBasics.norm_p_lt.le)
  have hzO : (z' : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
    have : (z' : ℂ_[l]) = (y : ℂ_[l]) - w := by rw [hw]; ring
    rw [this]; exact Subring.sub_mem _ y.2 hwO
  have hq : w / ((l : ℕ) : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC, norm_div, div_le_one hl]; exact hw1.le
  refine ⟨⟨_, hzO⟩, ⟨_, hq⟩, ⟨z', rfl⟩, Subtype.ext ?_⟩
  push_cast
  rw [mul_div_cancel₀ _ GlobalTheory.RingBasics.p_ne_zero, hw]; ring

end GlobalTheory.EmbTwo


open GlobalTheory.EmbTwo in
theorem GlobalTheory.EmbTwo.exists_gal_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (D : Type) [CommRing D] [IsDomain D] (θ₁ θ₂ : OC l →+* D), Function.Injective θ₁ → Function.Injective θ₂ → (∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r)) → ∃ g : ↥(GK K), (∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO (g : GQ l) y)) ∧ ∀ y : OC l, ((l : ℕ) : D) ∣ θ₂ y - θ₁ (Per.σO (g : GQ l) y) := by
  intro l _ K D _ _ θ₁ θ₂ h1 h2 hK
  let F := FractionRing D
  have i1 : Function.Injective ((algebraMap D F).comp θ₁) := (IsFractionRing.injective D F).comp h1
  have i2 : Function.Injective ((algebraMap D F).comp θ₂) := (IsFractionRing.injective D F).comp h2
  let τ₁ : ℂ_[l] →+* F := IsFractionRing.lift i1
  let τ₂ : ℂ_[l] →+* F := IsFractionRing.lift i2
  let σ₁ : Om l →+* F := τ₁.comp (algebraMap (Om l) ℂ_[l])
  let σ₂ : Om l →+* F := τ₂.comp (algebraMap (Om l) ℂ_[l])
  have hτ₁ : ∀ y : OC l, τ₁ (y : ℂ_[l]) = algebraMap D F (θ₁ y) := fun y =>
    IsFractionRing.lift_algebraMap (K := ℂ_[l]) i1 y
  have hτ₂ : ∀ y : OC l, τ₂ (y : ℂ_[l]) = algebraMap D F (θ₂ y) := fun y =>
    IsFractionRing.lift_algebraMap (K := ℂ_[l]) i2 y

  have hO : ∀ r : ↥(OL K), σ₁ ((r : ↥K.1) : Om l) = σ₂ ((r : ↥K.1) : Om l) := fun r => by
    change τ₁ ((intToOC K r : OC l) : ℂ_[l]) = τ₂ ((intToOC K r : OC l) : ℂ_[l])
    rw [hτ₁, hτ₂, hK]

  have hKK : ∀ x : ↥K.1, σ₁ (x : Om l) = σ₂ (x : Om l) := fun x => by
    have ha : IsAlgebraic ℤ_[l] x :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥K.1).2 (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨y, hy0, hy⟩ := ha.exists_integral_multiple
    let r : ↥(OL K) := ⟨y • x, hy⟩
    let s : ↥(OL K) := algebraMap ℤ_[l] ↥(OL K) y
    have hrs : ((r : ↥K.1) : Om l) = ((s : ↥K.1) : Om l) * (x : Om l) := by
      change ((y • x : ↥K.1) : Om l) = _
      rw [Algebra.smul_def]; rfl
    have hs0 : ((s : ↥K.1) : Om l) ≠ 0 := by
      intro h0
      apply hy0
      have : (s : ↥K.1) = 0 := Subtype.ext h0
      have h3 : algebraMap ℤ_[l] ↥K.1 y = 0 := this
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1, _root_.map_eq_zero] at h3
      exact (IsFractionRing.injective ℤ_[l] ℚ_[l]) (h3.trans (map_zero _).symm)
    have e1 := hO r
    rw [hrs, map_mul, map_mul, hO s] at e1
    exact mul_left_cancel₀ ((map_ne_zero σ₂).2 hs0) e1
  letI : Algebra ↥K.1 F := (σ₁.comp (algebraMap ↥K.1 (Om l))).toAlgebra
  let φ₁ : Om l →ₐ[↥K.1] F := { σ₁ with commutes' := fun _ => rfl }
  let φ₂ : Om l →ₐ[↥K.1] F := { σ₂ with commutes' := fun x => (hKK x).symm }
  have hR := range_eq_of_normal φ₁ φ₂
  let e₁ : Om l ≃ₐ[↥K.1] φ₁.fieldRange := AlgEquiv.ofInjectiveField φ₁
  have hmem : ∀ z, φ₂ z ∈ φ₁.fieldRange := fun z => hR ▸ ⟨z, rfl⟩
  let g₀ : Om l →ₐ[↥K.1] Om l := e₁.symm.toAlgHom.comp (φ₂.codRestrict φ₁.fieldRange.toSubalgebra hmem)
  have hg₀ : ∀ z, σ₁ (g₀ z) = σ₂ z := fun z => by
    have := congrArg Subtype.val (e₁.apply_symm_apply ⟨φ₂ z, hmem z⟩)
    exact this
  let g₁ : Om l ≃ₐ[↥K.1] Om l := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  let g : GQ l := g₁.restrictScalars ℚ_[l]
  have hgK : g ∈ GK K := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact g₀.commutes ⟨x, hx⟩
  have hg : ∀ z : Om l, σ₁ (g z) = σ₂ z := hg₀
  have c1 : ∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO g y) := by
    rintro y ⟨z, hz⟩
    apply IsFractionRing.injective D F
    rw [← hτ₁, ← hτ₂]
    have e2 : ((Per.σO g y : OC l) : ℂ_[l]) = ((g z : Om l) : ℂ_[l]) := by
      refine (GlobalTheory.RingIface.sigO_coe l g y).trans ?_
      rw [hz, GlobalTheory.RingBasics.σC_coe]
    rw [e2, hz]
    exact (hg z).symm
  refine ⟨⟨g, hgK⟩, c1, fun y => ?_⟩
  obtain ⟨z, w, hz, rfl⟩ := exists_approx y
  refine ⟨θ₂ w - θ₁ (Per.σO g w), ?_⟩
  have := c1 z hz
  simp only [map_add (f := _), map_mul, map_natCast]
  rw [this]; ring
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.IntDvr

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), IsDiscreteValuationRing ↥(OL K) ∧
    Module.Finite ℤ_[l] ↥(OL K) ∧ ∀ x : ↥(OL K), IsUnit x ↔ IsUnit (intToOC K x) := by
  intro l _ K
  refine ⟨Formalism.BasicNotions.Examples₂.LB.OL_dvr K, Formalism.BasicNotions.Examples₂.LB.OL_finite K,
    fun x => ⟨fun h => h.map _, fun h => ?_⟩⟩
  rw [Formalism.BasicNotions.Examples₂.LB.isUnit_iff]
  obtain ⟨u, hu⟩ := h
  have h1 := (GlobalTheory.RingBasics.mem_OC _).1 (u : OC l).2
  have h2 := (GlobalTheory.RingBasics.mem_OC _).1 ((u⁻¹ : (OC l)ˣ) : OC l).2
  have h3 : ((u : OC l) : ℂ_[l]) * (((u⁻¹ : (OC l)ˣ) : OC l) : ℂ_[l]) = 1 := by
    have := congrArg (fun z : OC l => (z : ℂ_[l])) u.mul_inv
    exact this
  have h4 : ‖((u : OC l) : ℂ_[l])‖ = 1 := by
    have h5 := congrArg norm h3
    rw [norm_mul, norm_one] at h5
    nlinarith [norm_nonneg ((u : OC l) : ℂ_[l]), norm_nonneg (((u⁻¹ : (OC l)ˣ) : OC l) : ℂ_[l])]
  have h6 : ((u : OC l) : ℂ_[l]) = (((x : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [hu, coe_intToOC]
  rw [h6, PadicComplex.norm_extends] at h4
  exact h4

end GlobalTheory.IntDvr
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem span_eq_ker_theta_of_distinguished : ∀ (l : ℕ) [Fact l.Prime] (x : Ainf l), Per.θ l x = 0 →
    IsUnit ((ainfDelta l).δ x) → Ideal.span {x} = RingHom.ker (Per.θ l) := by
  intro l hl x hx hu
  obtain ⟨ξ, h, -, h1⟩ := GlobalTheory.Prism.exists_generator l
  have h0 : Per.θ l ξ = 0 := by rw [← RingHom.mem_ker, h]; exact Ideal.mem_span_singleton_self ξ
  obtain ⟨c, hc⟩ : ξ ∣ x := by
    rw [← Ideal.mem_span_singleton, ← h]; exact hx
  have hφ := (ainfDelta l).φ_eq x
  have hφ' : (ainfDelta l).φ x = WittVector.frobenius x := rfl
  have hfx : WittVector.frobenius x = WittVector.frobenius ξ * WittVector.frobenius c := by
    rw [hc, map_mul]
  rw [hφ', hfx] at hφ
  have h3 := congrArg (Per.θ l) hφ
  rw [map_mul, h1, map_add (f := _), map_pow, map_mul, map_natCast, hx,
    zero_pow hl.out.ne_zero, zero_add] at h3
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h4 : v * WittVector.frobenius c - 1 ∈ Ideal.span {ξ} := by
    rw [← h, RingHom.mem_ker, map_sub, map_mul, map_one, sub_eq_zero]
    have h5 : Per.θ l (WittVector.frobenius c) = Per.θ l ((ainfDelta l).δ x) :=
      mul_left_cancel₀ (Nat.cast_ne_zero.2 hl.out.ne_zero : (l : OC l) ≠ 0) h3
    rw [h5, ← map_mul, hv, map_one]
  have := (GlobalTheory.Per.AinfComplete.main l ξ fun hu =>  (hu.map (Per.θ l)).ne_zero h0).2
  have h5 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h4) 1
  rw [mul_one, sub_add_cancel] at h5
  have h6 : IsUnit c := by
    rw [← (WittVector.frobeniusEquiv l (OCb l)).symm_apply_apply c]
    exact (isUnit_of_mul_isUnit_right h5).map (WittVector.frobeniusEquiv l (OCb l)).symm
  rw [h, hc, Ideal.span_singleton_mul_right_unit h6]

end GlobalTheory.BSP
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift


theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_iterated_rationalSplitting : ∀ (D : D7) (r m s t : ℕ) (J : Matrix (Fin r) (Fin s) D.host.E) (K : Matrix (Fin r) (Fin t) D.host.E) (L : Matrix (Fin s) (Fin r) D.host.E) (M : Matrix (Fin t) (Fin r) D.host.E), L * J = 1 → L * K = 0 → M * J = 0 → M * K = 1 → J * L + K * M = 1 → ∀ (μ : Measure (Mx D r m)) (𝓕 : Set (Mx D r m)), IsCovolOne (GlobalTheory.MixModel.ratMx D r m) μ 𝓕 → ∀ (ν : Measure (Mx D s m)) (𝓨 : Set (Mx D s m)), IsCovolOne (GlobalTheory.MixModel.ratMx D s m) ν 𝓨 → ∀ (η : Measure (Mx D t m)) (𝓥 : Set (Mx D t m)), IsCovolOne (GlobalTheory.MixModel.ratMx D t m) η 𝓥 → ∃ κ : ℝ, ∀ T : Mx D r m → ℂ, Continuous T → (∀ γ ∈ GlobalTheory.MixModel.ratMx D r m, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂μ = κ * ∫ v in 𝓥, (∫ y in 𝓨, T (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) ∂ν) ∂η := by
  first | exact @GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split | exact GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split | (intros; apply GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS

theorem _root_.GlobalTheory.T.exists_wachInclusion_powerSeries_into_one_tmul_ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∃ io : PowerSeries (WK K) →+* Ainf l, (∀ x, I.io (letEmb Γ.emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x) ∧ io PowerSeries.X = WittVector.teichmuller l (AI.εroot s) - 1 ∧ ∀ w : WK K, Formalism.Per.θ l (io (PowerSeries.C w)) = intToOC (unr K) w := by
  first | exact @GlobalTheory.PrismS.IoDescent.main | exact GlobalTheory.PrismS.IoDescent.main | (intros; apply GlobalTheory.PrismS.IoDescent.main <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.kernelOperator_integrable_continuous_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, Continuous φ.1 →
    (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
      (∀ g, Integrable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν) ∧ Continuous (kerOp ν k γ φ.1) := by
  first | exact @GlobalTheory.JSW.kerOp_integrable_continuous | exact GlobalTheory.JSW.kerOp_integrable_continuous | (intros; apply GlobalTheory.JSW.kerOp_integrable_continuous <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.isCuspidal_archimedeanKernelConvolutionOperator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, IsBCC φ.1 →
      IsCuspidal (kerOp ν k γ φ.1) := by
  first | exact @GlobalTheory.JSW.isCuspidal_kerOp | exact GlobalTheory.JSW.isCuspidal_kerOp | (intros; apply GlobalTheory.JSW.isCuspidal_kerOp <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.norm_fderiv_chart_le_of_bounded_lieDerivatives : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  first | exact @GlobalTheory.JSW.norm_fderiv_chart_le | exact GlobalTheory.JSW.norm_fderiv_chart_le | (intros; apply GlobalTheory.JSW.norm_fderiv_chart_le <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), IsBCC (0 : GA E a → ℂ) ∧
    ∀ (c : ℂ) (F G : GA E a → ℂ), IsBCC F → IsBCC G → IsBCC (c • F + G) := by
  first | exact @GlobalTheory.JSW.isBCC_zero_and_add | exact GlobalTheory.JSW.isBCC_zero_and_add | (intros; apply GlobalTheory.JSW.isBCC_zero_and_add <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

theorem _root_.GlobalTheory.T.hodgeTateSymbolMatrix_equivariant : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K LL : FinExt l} {m : ℕ} (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → ∀ g : ↥(GK K), (∀ i, ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec (fun j => P.actQdR (g : GQ l) (u i j)) = u i) → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (colHT J u k).map (Per.σC (g : GQ l)) = colHT J u k * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  first | (exact @GlobalTheory.HTBasis.colHT_equivariant) | (exact GlobalTheory.HTBasis.colHT_equivariant) | (intros; apply GlobalTheory.HTBasis.colHT_equivariant <;> assumption)
end
