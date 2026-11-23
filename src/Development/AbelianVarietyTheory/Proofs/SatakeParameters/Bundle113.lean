module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle105
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle109
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle106
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
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AbOverSubfield

theorem exists_place_between {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [Algebra F Ω] [IsScalarTower F K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap K Ω (x : K)) :=
      (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hint
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
    ext x
    rw [← hA x, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F K Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

end GlobalTheory.AbOverSubfield

namespace GlobalTheory.AbOverSubfield

end GlobalTheory.AbOverSubfield
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.NormalClosureSolv

open Pointwise

variable {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω]

theorem algebraMap_mem_smul_iff (γ : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) (c : F) :
    algebraMap F Ω c ∈ γ • A ↔ algebraMap F Ω c ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.commutes]

theorem isPlaceOver_smul' [NumberField F] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : Formalism.ConjugateSelfDual.IsPlaceOver A v) (γ : Ω ≃ₐ[F] Ω) : Formalism.ConjugateSelfDual.IsPlaceOver (γ • A) v := by
  intro x
  rw [← h x, valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, algebraMap_mem_smul_iff,
    algebraMap_mem_smul_iff, map_inv₀]

end GlobalTheory.NormalClosureSolv
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.ResDeg

theorem normV_eq_under_pow : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f := by
  intro K M _ _ _ _ _ w
  refine ⟨w.asIdeal.inertiaDeg (𝓞 K), ?_⟩
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

end GlobalTheory.AboveL.ResDeg
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.SatBC

theorem normV_under_pow (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have norm_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [norm_eq, norm_eq]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem tendsto_under (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  haveI := v.isMaximal
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
    ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_) (fun _ _ _ _ h => HeightOneSpectrum.ext h)
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨by rw [← Set.mem_singleton_iff.1 hw, HeightOneSpectrum.under_asIdeal]⟩⟩

theorem isPlaceOver_under {K M Ω : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K Ω]
    [Algebra M Ω] [Algebra K M] [IsScalarTower K M Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 M)}
    (h : Formalism.ConjugateSelfDual.IsPlaceOver A w) : Formalism.ConjugateSelfDual.IsPlaceOver A (w.under (𝓞 K)) := fun x => by
  rw [IsScalarTower.algebraMap_apply K M Ω]
  exact h (algebraMap (𝓞 K) (𝓞 M) x)

end GlobalTheory.AboveL.SatBC
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopLaw

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_form_of_mem_stdAt (a : E) (η : Sp E n →ₗ[E] E) (h : ∀ i, IntAt P (a * η (Pi.single i 1))) {v : Sp E n}
    (hv : v ∈ stdAt E n P) : IntAt P (a * η v) := by
  rw [GlobalTheory.TopInv.form_apply η v, Finset.mul_sum]
  refine GlobalTheory.TopStep.intAt_sum _ fun j _ => ?_
  rw [mul_left_comm]
  exact (mem_stdAt.1 hv j).mul (h j)

theorem intAt_form_comp_iff (a : E) (κ : GLint E n P) (η : Sp E n →ₗ[E] E) :
    (∀ i, IntAt P (a * (η ∘ₗ κ.1.toLinearMap) (Pi.single i 1))) ↔ ∀ i, IntAt P (a * η (Pi.single i 1)) := by
  refine ⟨fun h i => ?_, fun h i => intAt_form_of_mem_stdAt a η h (glint_mem κ (single_mem_stdAt i))⟩
  have h1 := intAt_form_of_mem_stdAt a _ h (glint_mem κ⁻¹ (single_mem_stdAt i))
  have e : κ.1 ((κ⁻¹).1 (Pi.single i 1)) = Pi.single i 1 := LinearEquiv.apply_symm_apply κ.1 _
  have e' : (η ∘ₗ κ.1.toLinearMap) ((κ⁻¹).1 (Pi.single i 1)) = η (Pi.single i 1) := congrArg η e
  rwa [e'] at h1

end SlopeTestRemainingChoices

theorem psi_add_int {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB} (hc : c.Ok) (P : SB) {k : ℕ}
    (hk : k ≤ c.D P) {x z : X.E} (hx : IntAt P.1 ((qOf P.1 : X.E) ^ k * x)) (hz : IntAt P.1 (z - x)) :
    c.psi P ((epsSg : X.E) * z) = c.psi P ((epsSg : X.E) * x) := by
  have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
  have hq := fun m => intAt_pow (GlobalTheory.TopStep.intAt_nat (P := P.1) (qOf P.1)) m
  have hd := he.mul hz
  have h1 : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * ((epsSg : X.E) * x)) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    have := (hq d).mul (he.mul hx)
    convert this using 1
    rw [hd, pow_add]
    ring
  have := hc.psi_add P _ _ h1 ((hq _).mul hd)
  rw [hc.psi_int P _ hd, mul_one] at this
  rw [← this]
  congr 1
  ring

theorem ftY_comp_glint : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (P : rowSG Pr sel mu), (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → ∀ {n : ℕ} (κ : GLint X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E) (y' y'' : Sp X.E n), (P.1 ∈ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → (P.1 ∉ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i)) → (P.1 ∈ Pr.vGs → κ.1 y'' - y' ∈ stdAt X.E n P.1) → (P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 y'' - y') ∈ stdAt X.E n P.1) → ftY sel mu cst P (η ∘ₗ κ.1.toLinearMap) y'' = ftY sel mu cst P η y' := by
  intro X Pr sel S mu cst hc P hD n κ η y' y'' hy1 hy2 hk1 hk2
  have hq := qOf_ne_zero (P := P.1)
  unfold ftY
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP, if_pos hP]
    have hi := intAt_form_comp_iff 1 κ η
    simp only [one_mul] at hi
    by_cases h : ∀ i, IntAt P.1 (η (Pi.single i 1))
    · rw [if_pos h, if_pos (hi.2 h)]
      have h' : ∀ i, IntAt P.1 (1 * η (Pi.single i 1)) := fun i => by rw [one_mul]; exact h i
      refine psi_add_int hc P (hc.D_pos P) ?_ ?_
      · have := intAt_form_of_mem_stdAt 1 η h' (v := (qOf P.1 : X.E) • y') (mem_stdAt.2 (hy1 hP))
        rwa [one_mul, map_smul, smul_eq_mul, ← pow_one (qOf P.1 : X.E)] at this
      · have := intAt_form_of_mem_stdAt 1 η h' (hk1 hP)
        rwa [one_mul, map_sub] at this
    · rw [if_neg h, if_neg fun h' => h (hi.1 h')]
  · rw [if_neg hP, if_neg hP]
    have hi := intAt_form_comp_iff ((qOf P.1 : X.E) ^ cst.M) κ η
    by_cases h : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))
    · rw [if_pos h, if_pos (hi.2 h)]
      refine congrArg _ (psi_add_int hc P (hD hP) ?_ ?_)
      · have := intAt_form_of_mem_stdAt _ η h (v := (qOf P.1 : X.E) ^ cst.M • y') (mem_stdAt.2 (hy2 hP))
        rwa [map_smul, smul_eq_mul, ← mul_assoc, ← pow_add, ← two_mul] at this
      · have := intAt_form_of_mem_stdAt _ η h (hk2 hP)
        rwa [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul, map_sub] at this
    · rw [if_neg h, if_neg fun h' => h (hi.1 h')]

end GlobalTheory.TopLaw
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

theorem _root_.GlobalTheory.T.mem_parahoric_of_cong_one_mod_q : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (kj n c : ℕ) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)), (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E (n + c) P) → (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g⁻¹ x - x) ∈ stdAt E (n + c) P) → g ∈ LocE.JQ P (qOf P) kj n c := by
  first | exact @GlobalTheory.ParahoricOfCong.mem_JQ_of_cong | exact GlobalTheory.ParahoricOfCong.mem_JQ_of_cong | (intros; apply GlobalTheory.ParahoricOfCong.mem_JQ_of_cong <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

theorem _root_.GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  first | exact @GlobalTheory.LamRowCong.lamRow_one_add_q | exact GlobalTheory.LamRowCong.lamRow_one_add_q | (intros; apply GlobalTheory.LamRowCong.lamRow_one_add_q <;> assumption)
end

section

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory
namespace DoubleCosetAdjoint

variable {G : Type} [Group G]

def Rel (J L : Subgroup G) (x : G) (u v : G ⧸ J) : Prop :=
  ∃ h a : G, a ∈ L ∧ (∃ k₁ k₂ : J, a = (k₁ : G) * x * k₂) ∧ u = (h : G ⧸ J) ∧ v = ((h * a : G) : G ⧸ J)

theorem Rel.symm {J L : Subgroup G} {x : G} {u v : G ⧸ J} (h : Rel J L x u v) : Rel J L x⁻¹ v u := by
  obtain ⟨h, a, ha, ⟨k₁, k₂, hk⟩, rfl, rfl⟩ := h
  refine ⟨h * a, a⁻¹, L.inv_mem ha, ⟨k₂⁻¹, k₁⁻¹, ?_⟩, rfl, by simp⟩
  rw [hk]; simp [mul_assoc]

theorem rel_iff {J L : Subgroup G} {x : G} {A : Finset G} (hL : ∀ a ∈ A, a ∈ L) (hA : IsDC J x A)
    (y : G) (v : G ⧸ J) : Rel J L x (y : G ⧸ J) v ↔ ∃ a ∈ A, v = ((y * a : G) : G ⧸ J) := by
  constructor
  · rintro ⟨h, b, -, ⟨k₁, k₂, hk⟩, hy, rfl⟩
    have hy' : y⁻¹ * h ∈ J := QuotientGroup.eq.1 hy
    obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hA.2 (y⁻¹ * h * b) ⟨⟨_, hy'⟩ * k₁, k₂, by rw [hk]; simp [mul_assoc]⟩
    refine ⟨a, ha, (QuotientGroup.eq.2 ?_).symm⟩
    simpa [mul_assoc] using ha'
  · rintro ⟨a, ha, rfl⟩
    exact ⟨y, a, hL a ha, hA.1 a ha, rfl, rfl⟩

theorem injOn_coset {J : Subgroup G} {x : G} {A : Finset G} (hA : IsDC J x A) (y : G) :
    Set.InjOn (fun a : G => ((y * a : G) : G ⧸ J)) (A : Set G) := by
  intro a ha a' ha' h
  have h' : (y * a)⁻¹ * (y * a') ∈ J := QuotientGroup.eq.1 h
  have h'' : a⁻¹ * a' ∈ J := by simpa [mul_assoc] using h'
  exact (hA.2 a' (hA.1 a' ha')).unique ⟨ha, h''⟩ ⟨ha', by simp⟩

theorem char_eq {J L : Subgroup G} (χ : J →* ℂˣ)
    (hd : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) {a b : G} (ha : a ∈ L) (hb : b ∈ L) (k k' : J)
    (h : (k : G) * b = a * k') : χ k = χ k' := by
  obtain ⟨k₁, h₁, k₂, h₂, hL, hk, hc⟩ := hd k k.2
  obtain ⟨m₁, g₁, m₂, g₂, gL, gk, -⟩ := hd k' k'.2
  have e1 : k = ⟨k₁, h₁⟩ * ⟨k₂, h₂⟩ := Subtype.ext hk
  have e2 : k' = ⟨m₁, g₁⟩ * ⟨m₂, g₂⟩ := Subtype.ext gk
  have e3 : k₂ * m₂⁻¹ = (k₁ * b)⁻¹ * (a * m₁) := by
    rw [hk, gk, mul_assoc, (hc b hb).eq] at h
    have : k₂ = (k₁ * b)⁻¹ * (a * (m₁ * m₂)) := by rw [← h]; group
    rw [this]; group
  have e4 : χ (⟨k₂, h₂⟩ * ⟨m₂, g₂⟩⁻¹) = 1 := hχ _ (by
    show k₂ * m₂⁻¹ ∈ L
    rw [e3]; exact L.mul_mem (L.inv_mem (L.mul_mem hL hb)) (L.mul_mem ha gL))
  rw [map_mul, map_inv, mul_inv_eq_one] at e4
  rw [e1, e2, map_mul, map_mul, hχ ⟨k₁, h₁⟩ hL, hχ ⟨m₁, g₁⟩ gL, e4]

theorem exists_pairing {Γ W : Type} [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) {J L : Subgroup G} (χ : J →* ℂˣ) (x : G)
    (hn : ∀ k, ‖(χ k : ℂ)‖ = 1)
    (hd : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ)
    (hF' : F' ∈ AdForms ι ρ J χ) :
    ∃ φ : (G ⧸ J) × (G ⧸ J) → ℂ, ∀ h a : G, a ∈ L → (∃ k₁ k₂ : J, a = (k₁ : G) * x * k₂) →
      φ ((h : G ⧸ J), ((h * a : G) : G ⧸ J)) = inner ℂ (F (h * a)) (F' h) := by
  classical
  refine ⟨fun z => if H : Rel J L x z.1 z.2 then
    inner ℂ (F (H.choose * H.choose_spec.choose)) (F' H.choose) else 0, ?_⟩
  intro h a ha hx
  have H : Rel J L x (h : G ⧸ J) ((h * a : G) : G ⧸ J) := ⟨h, a, ha, hx, rfl, rfl⟩
  simp only [dif_pos H]
  obtain ⟨hb, -, e1, e2⟩ := H.choose_spec.choose_spec
  generalize H.choose_spec.choose = b at hb e2 ⊢
  generalize H.choose = g at e1 e2 ⊢
  have f1 : h⁻¹ * g ∈ J := QuotientGroup.eq.1 e1
  have f2 : (h * a)⁻¹ * (g * b) ∈ J := QuotientGroup.eq.1 e2
  have c := char_eq χ hd hχ ha hb ⟨_, f1⟩ ⟨_, f2⟩ (by simp [mul_assoc])
  have u1 := hF 1 (h * a) ⟨_, f2⟩
  have u2 := hF' 1 h ⟨_, f1⟩
  simp only [map_one, one_mul, mul_inv_cancel_left, Module.End.one_apply] at u1 u2
  rw [u1, u2, c, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hn]
  simp

omit [Group G] in
theorem finsum_fibre {Q : Type} {P : Q → Prop} (s : Set {z // P z}) (A : Finset G) (m : G → Q)
    (hm : Set.InjOn m (A : Set G)) (hs : Subtype.val '' s = m '' (A : Set G)) (φ : Q → ℂ) :
    s.Finite ∧ ∑ᶠ z ∈ s, φ z.1 = ∑ a ∈ A, φ (m a) := by
  constructor
  · refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    rw [hs]; exact A.finite_toSet.image _
  · rw [← finsum_mem_image Subtype.val_injective.injOn, hs, finsum_mem_image hm,
      finsum_mem_coe_finset]

end DoubleCosetAdjoint


open DoubleCosetAdjoint in
theorem adInner_dcOp_adjoint : ∀ {G Γ W I : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J L : Subgroup G) (χ : J →* ℂˣ) (y : I → G) (x : G) (A A' : Finset G), (∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u') → (∀ k, ‖(χ k : ℂ)‖ = 1) → IsReps ι J y → (∀ i, Finite (stab ι J (y i))) → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J x⁻¹ A' → ∀ F ∈ AdForms ι ρ J χ, ∀ F' ∈ AdForms ι ρ J χ, adInner ι J y (dcOp A F) F' = adInner ι J y F (dcOp A' F') := by
  intro G Γ W I _ _ _ _ _ ι ρ J L χ y x A A' hρ hn hy hfin hd hχ hA hA' hD hD' F hF F' hF'
  obtain ⟨φ, hφ⟩ := exists_pairing ι ρ χ x hn hd hχ hF hF'
  letI : MulAction Γ (G ⧸ J) := MulAction.compHom (G ⧸ J) ι
  have hs : ∀ (γ : Γ) (g : G), γ • (g : G ⧸ J) = ((ι γ * g : G) : G ⧸ J) := fun _ _ => rfl
  let S : SubMulAction Γ ((G ⧸ J) × (G ⧸ J)) :=
    { carrier := {z | Rel J L x z.1 z.2}
      smul_mem' := by
        rintro γ ⟨u, v⟩ ⟨h, a, ha, hx, e1, e2⟩
        refine ⟨ι γ * h, a, ha, hx, ?_, ?_⟩
        · show γ • u = _
          rw [show u = _ from e1, hs]
        · show γ • v = _
          rw [show v = _ from e2, hs, mul_assoc] }
  have hst : ∀ g : G, MulAction.stabilizer Γ (g : G ⧸ J) = stab ι J g := by
    intro g
    ext γ
    rw [MulAction.mem_stabilizer_iff, hs, eq_comm, QuotientGroup.eq, mem_stab, mul_assoc]
  have horb : ∀ u : G ⧸ J, ∃! i, u ∈ MulAction.orbit Γ ((y i : G) : G ⧸ J) := by
    intro u
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective u
    refine (existsUnique_congr fun i => ?_).1 (hy h)
    constructor
    · rintro ⟨γ, k, rfl⟩
      exact ⟨γ, by simp only [hs]; exact (QuotientGroup.mk_mul_of_mem _ k.2).symm⟩
    · rintro ⟨γ, hγ⟩
      simp only [hs] at hγ
      exact ⟨γ, ⟨_, QuotientGroup.eq.1 hγ⟩, by simp only [mul_inv_cancel_left]⟩
  have hf : ∀ i, Finite (MulAction.stabilizer Γ ((y i : G) : G ⧸ J)) := fun i => by
    rw [hst]; exact hfin i
  have h1 := fun g : G => finsum_fibre (P := fun z => z ∈ S) {z | z.1.1 = (g : G ⧸ J)} A
    (fun a => ((g : G ⧸ J), ((g * a : G) : G ⧸ J)))
    (fun a ha a' ha' h => injOn_coset hD g ha ha' (congrArg Prod.snd h)) (by
      ext ⟨u, v⟩
      constructor
      · rintro ⟨⟨z, hz⟩, hz', rfl⟩
        obtain rfl : u = _ := hz'
        obtain ⟨a, ha, e⟩ := (rel_iff hA hD g v).1 hz
        exact ⟨a, ha, by rw [e]⟩
      · rintro ⟨a, ha, e⟩
        exact ⟨⟨(_, _), (rel_iff hA hD g _).2 ⟨a, ha, rfl⟩⟩, rfl, e⟩) φ
  have h2 := fun g : G => finsum_fibre (P := fun z => z ∈ S) {z | z.1.2 = (g : G ⧸ J)} A'
    (fun a => (((g * a : G) : G ⧸ J), (g : G ⧸ J)))
    (fun a ha a' ha' h => injOn_coset hD' g ha ha' (congrArg Prod.fst h)) (by
      ext ⟨u, v⟩
      constructor
      · rintro ⟨⟨z, hz⟩, hz', rfl⟩
        obtain rfl : v = _ := hz'
        obtain ⟨a, ha, e⟩ := (rel_iff hA' hD' g u).1 (Rel.symm hz)
        exact ⟨a, ha, by rw [e]⟩
      · rintro ⟨a, ha, e⟩
        have := ((rel_iff hA' hD' g _).2 ⟨a, ha, rfl⟩).symm
        rw [inv_inv] at this
        exact ⟨⟨(_, _), this⟩, rfl, e⟩) φ
  have key := weighted_fibre_sums_eq (Γ := Γ) (Z := S) (fun z => z.1.1) (fun z => z.1.2)
    (fun i => ((y i : G) : G ⧸ J)) (fun i => ((y i : G) : G ⧸ J)) (fun z => φ z.1)
    (fun _ _ => rfl) (fun _ _ => rfl) horb horb hf hf (fun i => (h1 _).1) (fun i => (h2 _).1) (by
      rintro γ ⟨⟨u, v⟩, h, a, ha, hx, e1, e2⟩
      obtain rfl : u = _ := e1
      obtain rfl : v = _ := e2
      show φ (γ • (h : G ⧸ J), γ • ((h * a : G) : G ⧸ J)) = φ (_, _)
      rw [hs, hs, ← mul_assoc, hφ _ a ha hx, hφ _ a ha hx]
      have u1 := hF γ (h * a) 1
      have u2 := hF' γ h 1
      simp only [map_one, OneMemClass.coe_one, mul_one, Units.val_one, one_smul] at u1 u2
      rw [mul_assoc, u1, u2, hρ])
  simp only [(h1 _).2, (h2 _).2, hst] at key
  unfold adInner dcOp
  convert key using 3 with i _ i _
  · rw [sum_inner]
    exact Finset.sum_congr rfl fun a ha => (hφ _ a (hA a ha) (hD.1 a ha)).symm
  · rw [inner_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨k₁, k₂, hk⟩ := hD'.1 a ha
    have := hφ (y i * a) a⁻¹ (L.inv_mem (hA' a ha)) ⟨k₂⁻¹, k₁⁻¹, by rw [hk]; simp [mul_assoc]⟩
    rw [mul_inv_cancel_right] at this
    exact this.symm

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.orbitBound_overSecondEmbedding_anyBasePoint : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D) (C6 C : ℝ), OrbitPlaces.OrbitLetterBoundsAll C6 C → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ (t : HH D) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) → product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be → OrbitPlaces.OrbGe E p h u i (true, t) ep sg be (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  first | exact @GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt | exact GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt | (intros; apply GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.local_basis_unit_scalars_exist : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ρ : D.host.E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) (P' : Matrix (Fin N') (Fin N') D.host.E), L₁.FG → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → TaylorLogMetric.LocBasisW D ρ L P → TaylorLogMetric.LocBasisW D ρ L' P' → ∃ σ σ' : 𝓞 D.host.E, ‖ρ (σ : D.host.E)‖ = 1 ∧ ‖ρ (σ' : D.host.E)‖ = 1 ∧ (∀ (a : Fin N) (x : Fin N → D.host.E), x ∈ L₁ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = (σ : D.host.E) * ∑ j, P⁻¹ a j * x j) ∧ ∀ b : Fin N', (fun i => (σ' : D.host.E) * P' i b) ∈ L₁' := by
  first | exact @GlobalTheory.locBasisW_clear_den | exact GlobalTheory.locBasisW_clear_den | (intros; apply GlobalTheory.locBasisW_clear_den <;> assumption)
end
