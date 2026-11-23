module

public import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import GroundTheory.LocalFields.MaximalUnramified
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle122
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle131
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle025
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Bundle001
import GroundTheory.ProfiniteCohomology.Bundle001
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import GroundTheory.LocalFields.Interface
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003

@[expose] public section

section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem conductor_eq_top_of_standardOpen {F : Type} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (h : standardOpenSubgroup F ≤ χ.toIdele.ker) : χ.conductor = ⊤ := by
  have h1 : χ.conductor ∣ (⊤ : Ideal (𝓞 F)) :=
    (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1
      ((map_idealLevel_le_standardOpenSubgroup ⊤).trans h)
  rw [← Ideal.one_eq_top] at h1
  exact Ideal.isUnit_iff.1 (isUnit_of_dvd_one h1)

theorem toIdele_inv_apply {F : Type} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (x : IdeleGroup F) : (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ :=
  rfl

theorem coeff_inv_mul_coeff : ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
    standardOpenSubgroup F ≤ χ.toIdele.ker → ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      (χ⁻¹).coeff J * χ.coeff J = 1 := by
  intro F _ _ χ hχ J hJ
  have hc : χ.conductor = ⊤ := conductor_eq_top_of_standardOpen χ hχ
  have hc' : (χ⁻¹).conductor = ⊤ := by
    refine conductor_eq_top_of_standardOpen _ fun x hx ↦ ?_
    have h1 : χ.toIdele x = 1 := hχ hx
    rw [MonoidHom.mem_ker, toIdele_inv_apply, h1, inv_one]
  have h1 : J ≠ ⊥ ∧ IsCoprime J χ.conductor :=
    ⟨hJ, by rw [hc, ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  have h2 : J ≠ ⊥ ∧ IsCoprime J (χ⁻¹).conductor :=
    ⟨hJ, by rw [hc', ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  obtain ⟨x, hx, hxJ⟩ := exists_mem_primeToLevel (idealUnit_mem_idealsPrimeTo h1.1 h1.2)
  have hx' : x ∈ primeToLevel (χ⁻¹).conductor := by rw [hc', ← hc]; exact hx
  rw [HeckeCharacter.coeff_of_mem _ h1, HeckeCharacter.coeff_of_mem _ h2,
    HeckeCharacter.idealCharacter_apply _ hx _ hxJ,
    HeckeCharacter.idealCharacter_apply _ hx' _ hxJ, toIdele_inv_apply, ← Circle.coe_mul,
    inv_mul_cancel, Circle.coe_one]

end GlobalTheory.CompanionTheory.PartialZeta
end

section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

variable {F : Type} [Field F] [NumberField F]

noncomputable def classCircle (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    ClassGroup (𝓞 F) →* Circle where
  toFun c := AddChar.circleEquivComplex.symm ψ (Additive.ofMul c)
  map_one' := by
    rw [ofMul_one]
    exact AddChar.map_zero_eq_one _
  map_mul' a b := by
    rw [ofMul_mul]
    exact AddChar.map_add_eq_mul _ _ _

theorem coe_classCircle (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (c : ClassGroup (𝓞 F)) :
    (classCircle ψ c : ℂ) = ψ (Additive.ofMul c) := by
  rfl

theorem continuous_comp_toClassGroup (φ : ClassGroup (𝓞 F) →* Circle) :
    Continuous (φ.comp (IdeleClassGroup.toClassGroup (K := F))) := by
  refine continuous_of_continuousAt_one _ ?_
  have hU : IsOpen ((IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F))) :=
    IdeleClassGroup.isOpenMap_mk (K := F) _ (isOpen_standardOpenSubgroup F)
  have h1 : (1 : IdeleClassGroup F) ∈ (IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F)) :=
    ⟨1, (standardOpenSubgroup F).one_mem, map_one _⟩
  rw [ContinuousAt, map_one]
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hU.mem_nhds h1] with y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx1 : IdeleGroup.toFractionalIdeal x = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]
    exact hx
  rw [MonoidHom.comp_apply, IdeleClassGroup.toClassGroup_mk, IdeleGroup.toClassGroup_apply, hx1,
    map_one, map_one]

noncomputable def classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) : HeckeCharacter F where
  toMonoidHom := (classCircle ψ).comp IdeleClassGroup.toClassGroup
  continuous_toFun := continuous_comp_toClassGroup _

theorem classHecke_toIdele (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (x : IdeleGroup F) :
    (classHecke ψ).toIdele x = classCircle ψ (IdeleGroup.toClassGroup x) :=
  rfl

theorem standardOpenSubgroup_le_ker (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    standardOpenSubgroup F ≤ (classHecke ψ).toIdele.ker := by
  intro x hx
  have h1 : IdeleGroup.toFractionalIdeal x = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]
    exact hx
  rw [MonoidHom.mem_ker, classHecke_toIdele, IdeleGroup.toClassGroup_apply, h1, map_one, map_one]

theorem idealLevel_top : idealLevel (⊤ : Ideal (𝓞 F)) = finiteLevel 0 := by
  show finiteLevel (fun v => multiplicity v.asIdeal (⊤ : Ideal (𝓞 F))) = finiteLevel 0
  congr 1
  funext v
  rw [Pi.zero_apply]
  apply multiplicity_eq_zero_of_not_dvd
  intro h
  exact v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))

theorem conductor_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    (classHecke ψ).conductor = ⊤ := by
  have hne : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
  have hle : Subgroup.map ofFinite (idealLevel (⊤ : Ideal (𝓞 F))) ≤ (classHecke ψ).toIdele.ker := by
    rintro _ ⟨z, hz, rfl⟩
    apply standardOpenSubgroup_le_ker ψ
    rw [mem_standardOpenSubgroup_iff_ord]
    intro v
    rw [idealLevel_top] at hz
    apply ord_eq_zero_of_mem_unitsLevel (n := 0)
    rw [← finiteComponent_toFinite, toFinite_ofFinite]
    exact Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp hz v)
  have hd := ((classHecke ψ).map_idealLevel_le_ker_iff hne).mp hle
  exact top_le_iff.mp (Ideal.le_of_dvd hd)

theorem coeff_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    (classHecke ψ).coeff J =
      ψ (Additive.ofMul (ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩)) := by
  have hprime : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (classHecke ψ).coeff v.asIdeal =
        ψ (Additive.ofMul (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) := by
    intro v
    have hv : ¬ v.asIdeal ∣ (classHecke ψ).conductor := by
      rw [conductor_classHecke]
      intro h
      exact v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))
    rw [HeckeCharacter.coeff_asIdeal_of_not_dvd _ hv]
    obtain ⟨x, hx, hxI⟩ := exists_mem_primeToLevel (primeIdealUnit_mem_idealsPrimeTo hv)
    have heq : (primeIdealUnit v : (FractionalIdeal (𝓞 F)⁰ F)ˣ) =
        FractionalIdeal.mk0 F ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ :=
      Units.ext (by rw [coe_primeIdealUnit, FractionalIdeal.coe_mk0])
    rw [HeckeCharacter.idealCharacter_apply _ hx ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ hxI,
      classHecke_toIdele, coe_classCircle, IdeleGroup.toClassGroup_apply, hxI, heq, ClassGroup.mk_mk0]
  refine UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (𝓞 F) => ∀ hI : I ≠ ⊥,
      (classHecke ψ).coeff I =
        ψ (Additive.ofMul (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩))) J ?_ ?_ ?_ hJ
  · intro h
    exact absurd Ideal.zero_eq_bot h
  · intro x hx hx0
    obtain rfl := Ideal.isUnit_iff.mp hx
    have h1 : (⟨⊤, mem_nonZeroDivisors_of_ne_zero hx0⟩ : (Ideal (𝓞 F))⁰) = 1 :=
      Subtype.ext Ideal.one_eq_top.symm
    rw [HeckeCharacter.coeff_top, h1, map_one, ofMul_one, AddChar.map_zero_eq_one]
  · intro a p ha hp ih hpa
    have ha' : a ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact ha
    have hp0 : p ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact hp.ne_zero
    have hv := hprime ⟨p, Ideal.isPrime_of_prime hp, hp0⟩
    have hmk : (⟨p * a, mem_nonZeroDivisors_of_ne_zero hpa⟩ : (Ideal (𝓞 F))⁰) =
        ⟨p, mem_nonZeroDivisors_of_ne_zero hp0⟩ * ⟨a, mem_nonZeroDivisors_of_ne_zero ha'⟩ :=
      Subtype.ext rfl
    rw [HeckeCharacter.coeff_mul, ih ha', hmk, map_mul, ofMul_mul, AddChar.map_add_eq_mul]
    congr 1

end GlobalTheory.CompanionTheory.PartialZeta
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.LocalUnram


open GroundTheory.LocalField.Abstract in
theorem continuous_of_additive_of_frobenius_eq_one :
    ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
      [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (χ : Gal(Ω/K) → ZMod n),
      (∀ g h, χ (g * h) = χ g + χ h) →
      (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → Continuous χ := by
  intro K Ω _ _ _ _ _ _ _ n _ χ hadd h1
  obtain ⟨hcont, hsurj, -⟩ := unramifiedDegree_spec (K := K) (Ω := Ω)
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, NeZero.pos n⟩, rfl⟩
  have hone : χ 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hinv : ∀ g, χ g⁻¹ = -χ g := fun g => by
    have h := hadd g⁻¹ g
    rw [inv_mul_cancel, hone] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hpow : ∀ (g : Gal(Ω/K)) (k : ℕ), χ (g ^ k) = k • χ g := fun g k => by
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]
  obtain ⟨f, hf⟩ := hsurj (Multiplicative.ofAdd 1)
  have hχf : χ f = 1 := h1 f hf
  have hker : ∀ g, unramifiedDegree K Ω g = 1 → χ g = 0 := fun g hg => by
    have h := h1 (g * f) (by rw [map_mul, hg, one_mul, hf])
    rw [hadd, hχf] at h
    exact add_eq_right.mp h
  have key : ∀ g, χ g = ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω g)) := by
    intro g
    set x := Multiplicative.toAdd (unramifiedDegree K Ω g) with hx
    set k : ℕ := (ProfiniteInteger.proj N x).val with hk
    have hkc : ((k : ℕ) : ZMod (N : ℕ)) = ProfiniteInteger.proj N x := ZMod.natCast_zmod_val _
    have hz : ProfiniteInteger.proj N (x - (k : ProfiniteInteger)) = 0 := by
      rw [map_sub, map_natCast, hkc, sub_self]
    obtain ⟨w, hw⟩ := ProfiniteInteger.exists_eq_nsmul_of_proj_eq_zero hz
    obtain ⟨t, ht⟩ := hsurj (Multiplicative.ofAdd w)
    have hdeg : unramifiedDegree K Ω (g * (f ^ k)⁻¹ * (t ^ (N : ℕ))⁻¹) = 1 := by
      simp only [_root_.map_mul, _root_.map_inv, _root_.map_pow, hf, ht]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_mul, toAdd_inv, toAdd_inv, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd,
        toAdd_one, ← hx, ← hw, nsmul_eq_mul, mul_one]
      ring
    have h0 := hker _ hdeg
    rw [hadd, hadd, hinv, hinv, hpow, hpow, hχf] at h0
    have hN : (N : ℕ) • χ t = 0 := by simp
    rw [hN, neg_zero, add_zero, nsmul_eq_mul, mul_one, hkc] at h0
    exact add_neg_eq_zero.mp h0
  have hχ : χ = fun g => ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω g)) :=
    funext key
  rw [hχ]
  exact (ProfiniteInteger.continuous_proj N).comp (continuous_toAdd.comp hcont)

end GlobalTheory.CompanionTheory.LocalUnram
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_character_separating_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A → ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | exact GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | (intros; apply GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne <;> assumption)
end

section

open Matrix
open scoped Topology

theorem _root_.GlobalTheory.T.annihilator_open_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ∧ IsCompact {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact | exact GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.exists_invertible_matrix_last_line_given : ∀ (k : Type) [Field k] (m : ℕ) (a : Fin (m + 1) → k), a ≠ 0 → ∃ g : GL (Fin (m + 1)) k, ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = a j := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq | exact GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

theorem _root_.GlobalTheory.T.modular_character_trivial_finite_covolume : ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (Γ₁ : Subgroup G₁) [Countable Γ₁] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁), IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → ∀ δ : G₁ →* ℝ≥0, Measurable δ → (∀ γ ∈ Γ₁, δ γ = 1) → ∀ u, δ u = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain | exact GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem _root_.GlobalTheory.T.tendsto_of_asymptotic_bounds : ∀ (f : ℕ → ℝ) (G : ℝ) (D : ℕ), (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n) → (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) → Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by
  first | exact @GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds | exact GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds | (intros; apply GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds <;> assumption)
end
