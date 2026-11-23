module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle037
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem selfDual_comp_selfAdjoint : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ) (T : V ≃ₜ V) (δ : ℝ≥0), δ ≠ 0 → μ = δ • μ.map T → (∀ x y, χ x (T y) = χ (T x) y) → SelfDual μ χ → SelfDual (NNReal.sqrt δ • μ) (fun x y => χ x (T y)) := by
  intro V _ _ _ _ _ _ _ _ μ χ T δ hδ hμ hχ hsd
  have hH := hsd.1
  have hs0 : NNReal.sqrt δ ≠ 0 := by simpa using hδ
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul μ hs0, ?_⟩
  intro Φ hc hcs hI z
  set s : ℝ≥0 := NNReal.sqrt δ with hs
  set F : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ with hF
  have hT : ∀ y, ∫ x, Φ x * χ x (T y) ∂(s • μ) = (s : ℂ) * F (T y) := by
    intro y
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hmap : μ.map T = μ.map T.toMeasurableEquiv := rfl
  simp only [hT] at hI ⊢
  have h1 : Integrable (fun y => F (T y)) μ := by
    have h2 : Integrable (fun y => (s : ℂ) * F (T y)) μ := by
      have := hI.smul_measure_nnreal (c := s⁻¹)
      rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
    have := h2.const_mul ((s : ℂ)⁻¹)
    simpa [← mul_assoc, inv_mul_cancel₀ hsC] using this
  have h3 : Integrable F μ := by
    rw [hμ]
    apply Integrable.smul_measure_nnreal
    rw [hmap, integrable_map_equiv]
    exact h1
  have h4 := hsd.2 Φ hc hcs h3 z
  rw [← h4]
  have h5 : ∫ y, F y * χ y z ∂μ = (δ : ℂ) * ∫ y, F (T y) * χ (T y) z ∂μ := by
    conv_lhs => rw [hμ]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, hmap, integral_map_equiv]
    rfl
  have hss : (s : ℂ) * (s : ℂ) = (δ : ℂ) := by
    have : s * s = δ := NNReal.mul_self_sqrt δ
    rw [← this]; push_cast; rfl
  change _ = ∫ y, F y * χ y z ∂μ
  rw [h5, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, ← hss, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  congr 1
  ext y
  rw [hχ, mul_assoc]

end GlobalTheory.GaugeEx
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.hermitian_quadratic_form_orbit_rational_vector_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (a : F), hE σ J (x 0) (x 0) = algebraMap F E a → ∀ g : HA R σ J, qR R σ J ((g • ratTup (F := F) R x) 0) = algebraMap F R a := by
  first | exact @GlobalTheory.GaugeEx.OrbitQuadric.qR_orbit | exact GlobalTheory.GaugeEx.OrbitQuadric.qR_orbit | (intros; apply GlobalTheory.GaugeEx.OrbitQuadric.qR_orbit <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.TameCharUnique
open scoped Pointwise

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]


open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
theorem _root_.GlobalTheory.TameCharUnique.mem_Ine_of_wild {A : ValuationSubring Ω} {σ : _root_.Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A := by
  have hval : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have h1 : A.valuation (σ y / y) = 1 := by
        have := A.valuation.map_one_add_of_lt (hσ y hy)
        rwa [add_sub_cancel] at this
      have h2 : σ y = σ y / y * y := (div_mul_cancel₀ _ hy).symm
      rw [h2, map_mul, h1, one_mul]
  rw [_root_.ReciprocityTheory.Gal.mem_Ine]
  unfold _root_.Formalism.ConjugateSelfDual.Inertia
  refine ⟨?_, fun x hx => ?_⟩
  · change (σ : Gal(Ω/E)) • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, AlgEquiv.smul_def]
    have hx := hval (σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at hx
    rw [← hx]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hsplit : σ x - x = (σ x / x - 1) * x := by
        rw [sub_mul, div_mul_cancel₀ _ hx0, one_mul]
      rw [hsplit, map_mul]
      calc A.valuation (σ x / x - 1) * A.valuation x ≤ A.valuation (σ x / x - 1) :=
            mul_le_of_le_one_right' hx
        _ < 1 := hσ x hx0

variable [IsAlgClosure E Ω]


open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in
theorem _root_.GlobalTheory.TameCharUnique.mem_of_tameGen {A : ValuationSubring Ω} {γ : _root_.Formalism.ConjugateSelfDual.G E Ω}
    (hγ : _root_.Formalism.BasicNotions.TameGenAt A γ)
    (S : Subgroup (_root_.ReciprocityTheory.Gal.Ine (F := E) A)) (hS : IsClosed (S : Set (_root_.ReciprocityTheory.Gal.Ine (F := E) A)))
    (h1 : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ S)
    (h2 : ∀ σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) → σ ∈ S)
    (σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) : σ ∈ S := by
  obtain ⟨C, hC, hCS⟩ := (Topology.IsInducing.subtypeVal.isClosed_iff).mp hS
  have hmapC : ((S.map (_root_.ReciprocityTheory.Gal.Ine (F := E) A).subtype : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)) :
      Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) ⊆ C := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact (Set.ext_iff.mp hCS τ).mpr hτ
  have hle : Subgroup.closure (insert γ {τ : _root_.Formalism.ConjugateSelfDual.G E Ω |
      ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1}) ≤ S.map (_root_.ReciprocityTheory.Gal.Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro τ (rfl | hτ)
    · exact ⟨_, h1, rfl⟩
    · exact ⟨⟨τ, _root_.GlobalTheory.TameCharUnique.mem_Ine_of_wild hτ⟩, h2 _ hτ, rfl⟩
  have hσC : (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ∈ C :=
    closure_minimal ((SetLike.coe_subset_coe.mpr hle).trans hmapC) hC (hγ.2 σ.2)
  exact (Set.ext_iff.mp hCS σ).mp hσC

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in
private lemma exists_pow_fixes_finiteDimensional (K : IntermediateField E Ω)
    [FiniteDimensional E K] (τ : Gal(Ω/E)) : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ K, (τ ^ m) x = x := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => ((τ ^ n : Gal(Ω/E)).toAlgHom.comp K.val : K →ₐ[E] Ω))
  have hfix : ∀ a b : ℕ, a < b → (∀ x ∈ K, (τ ^ a) x = (τ ^ b) x) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ K, (τ ^ m) x = x := by
    intro a b hab hx
    refine ⟨b - a, Nat.sub_pos_of_lt hab, fun x hxK => ?_⟩
    apply (τ ^ a).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    exact (hx x hxK).symm
  have hij' : ∀ x ∈ K, (τ ^ i) x = (τ ^ j) x := fun x hx => by
    simpa using DFunLike.congr_fun heq ⟨x, hx⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hfix i j h hij'
  · exact hfix j i h fun x hx => (hij' x hx).symm


open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in
theorem _root_.GlobalTheory.TameCharUnique.eq_zero_of_wild {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {l : ℕ} [Fact l.Prime] (hlw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (t : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l]) (ht : Continuous t)
    (σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) : (t σ).toAdd = 0 := by
  have hl1 : l ≠ 1 := (Fact.out : l.Prime).ne_one
  rw [← norm_eq_zero]
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
  rw [zero_add]
  have hUo : IsOpen (t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε}) :=
    (isOpen_lt (continuous_norm.comp continuous_toAdd) continuous_const).preimage ht
  obtain ⟨V, hVo, hVU⟩ := (Topology.IsInducing.subtypeVal.isOpen_iff).mp hUo
  have h1V : (1 : Gal(Ω/E)) ∈ V := by
    have h1U : (1 : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε} := by
      simp [hε]
    rw [← hVU] at h1U
    exact h1U
  obtain ⟨K, hK, hKV⟩ := (krullTopology_mem_nhds_one_iff E Ω V).mp (hVo.mem_nhds h1V)
  obtain ⟨m, hm0, hmK⟩ := exists_pow_fixes_finiteDimensional K σ.1
  obtain ⟨e, m', hlm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' l hl1
  have hτ := _root_.GlobalTheory.WildInertiaChar.wild_pow A σ.1 hσ m'
  have hfix : (σ ^ m' : _root_.ReciprocityTheory.Gal.Ine (F := E) A).1 ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [Subgroup.coe_pow]
    refine _root_.GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A _ hτ (l ^ e) (_root_.ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver hlw h e) x ?_
    rw [← pow_mul, mul_comm, ← hm]
    exact hmK x hx
  have hmem : σ ^ m' ∈ t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε} := by
    rw [← hVU]
    exact hKV hfix
  have hnorm : ‖(t (σ ^ m')).toAdd‖ < ε := hmem
  rwa [map_pow, toAdd_pow, nsmul_eq_mul, norm_mul,
    PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hlm'),
    one_mul] at hnorm


open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in
theorem _root_.GlobalTheory.TameCharUnique.exists_eq_mul : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (l : ℕ) [Fact l.Prime], ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (t t' : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l]), Continuous t → Continuous t' → Function.Surjective t' → ∃ c : ℤ_[l], ∀ σ, (t σ).toAdd = c * (t' σ).toAdd := by
  intro E Ω _ _ _ _ _ A w h l _ hlw t t' ht ht' hsurj
  obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := E) A
  have hwild : ∀ s : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l], Continuous s →
      ∀ σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) →
        s σ = 1 := by
    intro s hs σ hσ
    rw [← toAdd_eq_zero]
    exact _root_.GlobalTheory.TameCharUnique.eq_zero_of_wild h hlw s hs σ hσ
  have hb : IsUnit (t' ⟨γ, hγ.1⟩).toAdd := by
    by_contra hb
    let S : Subgroup (_root_.ReciprocityTheory.Gal.Ine (F := E) A) :=
      { carrier := {σ | ‖(t' σ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_mul, toAdd_mul] at *
          exact (PadicInt.nonarchimedean _ _).trans (max_le ha hb)
        one_mem' := by simp
        inv_mem' := fun {a} ha => by simpa using ha }
    have hS : IsClosed (S : Set (_root_.ReciprocityTheory.Gal.Ine (F := E) A)) :=
      isClosed_le (continuous_norm.comp (continuous_toAdd.comp ht')) continuous_const
    have hγS : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ S := by
      show ‖(t' ⟨γ, hγ.1⟩).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)
      rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
      rw [PadicInt.isUnit_iff] at hb
      norm_num
      exact lt_of_le_of_ne (PadicInt.norm_le_one _) hb
    have hall : ∀ σ, σ ∈ S := fun σ =>
      _root_.GlobalTheory.TameCharUnique.mem_of_tameGen hγ S hS hγS
        (fun τ hτ => by
          show ‖(t' τ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)
          rw [hwild t' ht' τ hτ]
          simp) σ
    obtain ⟨σ, hσ⟩ := hsurj (Multiplicative.ofAdd 1)
    have h1 : ‖(t' σ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ) := hall σ
    rw [hσ, toAdd_ofAdd, norm_one, zpow_neg_one] at h1
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact absurd h1 (not_le.mpr (inv_lt_one_of_one_lt₀ hl))
  refine ⟨(t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹, fun σ => ?_⟩
  let f : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l] :=
    (AddMonoidHom.toMultiplicative
      (AddMonoidHom.mulLeft ((t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹))).comp t'
  have hf : Continuous f := by
    show Continuous fun τ => Multiplicative.ofAdd
      ((t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹ * (t' τ).toAdd)
    exact continuous_ofAdd.comp (continuous_const.mul (continuous_toAdd.comp ht'))
  have hγmem : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ MonoidHom.eqLocus t f := by
    show t ⟨γ, hγ.1⟩ = f ⟨γ, hγ.1⟩
    apply Multiplicative.toAdd.injective
    show (t ⟨γ, hγ.1⟩).toAdd = (t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹ * (t' ⟨γ, hγ.1⟩).toAdd
    rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
  have hwmem : ∀ τ : _root_.ReciprocityTheory.Gal.Ine (F := E) A,
      (∀ y : Ω, y ≠ 0 → A.valuation (τ.1 y / y - 1) < 1) → τ ∈ MonoidHom.eqLocus t f := by
    intro τ hτ
    show t τ = f τ
    simp [f, hwild t ht τ hτ, hwild t' ht' τ hτ]
  have hmem := _root_.GlobalTheory.TameCharUnique.mem_of_tameGen hγ (MonoidHom.eqLocus t f)
    (isClosed_eq ht hf) hγmem hwmem σ
  exact congrArg Multiplicative.toAdd hmem

end GlobalTheory.TameCharUnique
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_idealSheaf_map_of_affineCover_preimage : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) [QuasiCompact ρ] (I : Y'.IdealSheafData) (U : X.affineOpens) {ι : Type} (W : ι → Y'.affineOpens) (hW : ∀ i, (W i : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), ρ ⁻¹ᵁ (U : X.Opens) ≤ ⨆ i, (W i : Y'.Opens) → ∀ b : Γ(X, U), (∀ i, (ρ.appLE U (W i) (hW i)).hom b ∈ I.ideal (W i)) → b ∈ (I.map ρ).ideal U := by
  first | exact @GlobalTheory.IdealPushCover.mem_map_ideal_of_cover | exact GlobalTheory.IdealPushCover.mem_map_ideal_of_cover | (intros; apply GlobalTheory.IdealPushCover.mem_map_ideal_of_cover <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem linComb_pow_pow_sec {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ) (hm : m = a * n) (g : Y ⟶ X)
    (s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n))) :
    ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι),
      g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  let M := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)
  let N := LB.LinComb M (K := Fin 1) (fun _ => g) (fun _ => n)
  let P := LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)
  have le : ∀ i : Fin 1 → L.ι, P.U i ≤ N.U (fun k _ => i k) := fun i y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy k
  have gN : ∀ (x : Y) (i j : Fin 1 → L.ι) (hi : x ∈ P.U i) (hj : x ∈ P.U j),
      gm (𝟙 Y) x (P.U i ⊓ P.U j) (P.g i j) =
        gm (𝟙 Y) x (N.U (fun k _ => i k) ⊓ N.U (fun k _ => j k)) (N.g (fun k _ => i k) (fun k _ => j k)) := by
    intro x i j hi hj
    refine (gm_linComb L (fun _ : Fin 1 => g) (fun _ => m) (𝟙 Y) x i j hi hj).trans
      (Eq.trans ?_ (gm_linComb M (fun _ : Fin 1 => g) (fun _ => n) (𝟙 Y) x _ _ (le i hi) (le j hj)).symm)
    simp only [Fintype.prod_unique]
    refine Eq.trans ?_ (congrArg (· ^ n) (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => a) (𝟙 Y ≫ g) x
      (fun _ => i default) (fun _ => j default) (Set.mem_iInter.1 (le i hi) default)
      (Set.mem_iInter.1 (le j hj) default))).symm
    simp only [Fintype.prod_unique, Category.comp_id, hm, zpow_mul]
  refine ⟨⟨fun i => (Y.presheaf.map (homOfLE (le i)).op).hom (s.f (fun k _ => i k)), fun i j => ?_⟩, ?_⟩
  · apply fn_ext
    intro x hx
    have hx' : (𝟙 Y) x ∈ P.U i ⊓ P.U j := hx
    have hN : (𝟙 Y) x ∈ N.U (fun k _ => i k) ⊓ N.U (fun k _ => j k) := ⟨le i hx.1, le j hx.2⟩
    have e := congrArg (gs (𝟙 Y) x _) (s.compat (fun k _ => i k) (fun k _ => j k))
    rw [gs_res _ _ _ hN, gs_mul _ _ _ hN, gs_unit _ _ _ hN, gs_res _ _ _ hN] at e
    have hi : (𝟙 Y) x ∈ P.U i := hx.1
    have hj : (𝟙 Y) x ∈ P.U j := hx.2
    rw [gs_res _ _ _ hx', gs_res (𝟙 Y) x (le i) hi, gs_mul _ _ _ hx', gs_unit _ _ _ hx', gs_res _ _ _ hx',
      gs_res (𝟙 Y) x (le j) hj, e, gN x i j hx.1 hx.2]
  · intro Z r z j hj
    have hz : r z ∈ P.U (fun _ => j) := Set.mem_iInter.2 fun _ => hj
    exact gs_res r z (le _) hz _

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecPowUnflat

theorem unflat : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  intro X Y L a n m hm g s'
  have le : ∀ J : Fin 1 → (Fin 1 → L.ι),
      LB.wchart (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (fun _ : Fin 1 => g) J ≤
        LB.wchart L (fun _ : Fin 1 => g) (fun k => J k 0) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0
  refine ⟨⟨fun J => (Y.presheaf.map (homOfLE (le J)).op).hom (s'.f (fun k => J k 0)), fun J J' => ?_⟩, ?_⟩
  · refine fn_ext fun y hy => ?_
    have hy1 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) := le J hy.1
    have hy2 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := le J' hy.2
    have hS : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := ⟨hy1, hy2⟩
    have c := congrArg (gs (𝟙 Y) y _) (s'.compat (fun k => J k 0) (fun k => J' k 0))
    rw [gs_res (𝟙 Y) y _ hS, gs_mul (𝟙 Y) y _ hS, gs_unit (𝟙 Y) y _ hS, gs_res (𝟙 Y) y _ hS] at c
    erw [gm_linComb L _ _ (𝟙 Y) y _ _ hy1 hy2] at c
    erw [gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy.1, gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy,
      gs_res (𝟙 Y) y _ hy.2, c]
    erw [gm_linComb _ _ _ (𝟙 Y) y J J' hy.1 hy.2]
    have i1 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J 0) := by
      simpa using Set.mem_iInter.1 hy.1 0
    have i2 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J' 0) := by
      simpa using Set.mem_iInter.1 hy.2 0
    simp only [Fin.prod_univ_one]
    erw [gm_linComb L _ _ (𝟙 Y ≫ g) y (J 0) (J' 0) i1 i2]
    simp only [Fin.prod_univ_one, Category.comp_id, Category.id_comp, hm, zpow_mul]
    rfl
  · intro Z r z j h
    exact (gs_res r z (le _) (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => h) _).symm

end GlobalTheory.SecPowUnflat
end
