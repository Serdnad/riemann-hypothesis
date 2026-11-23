module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagLatticesNearUnderStabiliser
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusRestrictedProduct
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle114
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.SymplecticGroup
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem hermitian_idempotent_eq_isometry_mul_conjTranspose :
    ∀ (n : ℕ) (R : Matrix (Fin n) (Fin n) ℂ), Rᴴ = R → R * R = R →
      ∃ (r : ℕ) (P : Matrix (Fin n) (Fin r) ℂ), Pᴴ * P = 1 ∧ P * Pᴴ = R := by
  apply GlobalTheory.IsoTorus.proj_frame <;> assumption

end GlobalTheory
end

section

noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.DegCnt
open scoped Pointwise nonZeroDivisors

namespace GlobalTheory.RowStab

section Gen
variable {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def gen (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) : V →ₗ[K] V :=
  LinearMap.id + ∑ b ∈ J, ((H.B.flip (e b)).smulRight (ρ b) - (H.B.flip (ρ b)).smulRight (e b) +
    ∑ a ∈ J, (c a b • H.B.flip (e b)).smulRight (e a))

theorem gen_apply (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) (v : V) :
    gen H J e ρ c v = v + ∑ b ∈ J, (H.B v (e b) • ρ b - H.B v (ρ b) • e b +
      ∑ a ∈ J, (c a b * H.B v (e b)) • e a) := by
  simp [gen, LinearMap.sum_apply, mul_smul]

end Gen

section Ideal
variable {K : Type} [Field K] [NumberField K]

theorem ipow_mul_mem {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m n : ℤ} {x y : K} (hx : x ∈ ipow 𝔡 m)
    (hy : y ∈ ipow 𝔡 n) : x * y ∈ ipow 𝔡 (m + n) := by
  have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    simpa using h𝔡
  unfold ipow at *
  rw [zpow_add₀ h0, FractionalIdeal.coe_mul]
  exact Submodule.mul_mem_mul hx hy

theorem one_mem_ipow_mul {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) (m : ℤ) :
    (1 : K) ∈ ipow 𝔡 m * ipow 𝔡 (-m) := by
  have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    simpa using h𝔡
  unfold ipow
  rw [← FractionalIdeal.coe_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, FractionalIdeal.coe_one]
  exact Submodule.one_le.mp le_rfl

theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  simp [ipow]

theorem mem_ipow_of_mul {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m n : ℤ} {x : K}
    (h : ∀ t ∈ ipow 𝔡 (-m), t * x ∈ ipow 𝔡 n) : x ∈ ipow 𝔡 (m + n) := by
  have key : ∀ y ∈ ipow 𝔡 m * ipow 𝔡 (-m), y * x ∈ ipow 𝔡 (m + n) := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha t ht
      rw [mul_assoc]
      exact ipow_mul_mem h𝔡 ha (h t ht)
    · intro a b ha hb
      rw [add_mul]
      exact Submodule.add_mem _ ha hb
  simpa using key 1 (one_mem_ipow_mul h𝔡 m)

end Ideal

section Smul
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem smul_mem_of_mem_ipow_smul {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m : ℤ} {M : Submodule (𝓞 K) V} {v : V}
    (hv : v ∈ ipow 𝔡 m • M) {t : K} (ht : t ∈ ipow 𝔡 (-m)) : t • v ∈ M := by
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro a ha n hn
    have h1 : t * a ∈ ipow 𝔡 0 := by
      simpa [add_comm] using ipow_mul_mem h𝔡 ht ha
    rw [ipow_zero] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
    rw [smul_smul, ← ho, algebraMap_smul]
    exact M.smul_mem o hn
  · intro x y hx hy
    rw [smul_add]
    exact M.add_mem hx hy

theorem mem_ipow_smul_of_smul_mem {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m : ℤ} {M : Submodule (𝓞 K) V} {v : V}
    (h : ∀ t ∈ ipow 𝔡 (-m), t • v ∈ M) : v ∈ ipow 𝔡 m • M := by
  have key : ∀ y ∈ ipow 𝔡 m * ipow 𝔡 (-m), y • v ∈ ipow 𝔡 m • M := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha t ht
      rw [mul_smul]
      exact Submodule.smul_mem_smul ha (h t ht)
    · intro a b ha hb
      rw [add_smul]
      exact Submodule.add_mem _ ha hb
  simpa using key 1 (one_mem_ipow_mul h𝔡 m)

end Smul

section Star
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem star_integral (y : 𝓞 K) : ∃ y' : 𝓞 K, (y' : K) = star (y : K) := by
  have h : IsIntegral ℤ (star (y : K)) := by
    exact (RingOfIntegers.isIntegral_coe y).map ((starRingEnd K).toIntAlgHom)
  exact ⟨⟨star (y : K), h⟩, rfl⟩

theorem star_pow_mem {𝔡 : Ideal (𝓞 K)} (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (k : ℕ) :
    ∀ x ∈ 𝔡 ^ k, ∃ y ∈ 𝔡 ^ k, (y : K) = star (x : K) := by
  induction k with
  | zero =>
    intro x _
    obtain ⟨y, hy⟩ := star_integral x
    exact ⟨y, by simp, hy⟩
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨a', ha', ea⟩ := ih a ha
      obtain ⟨b', hb', eb⟩ := h𝔡s b hb
      refine ⟨a' * b', ?_, ?_⟩
      · rw [pow_succ]; exact Submodule.mul_mem_mul ha' hb'
      · simp [ea, eb, star_mul']
    · rintro a b ⟨a', ha', ea⟩ ⟨b', hb', eb⟩
      exact ⟨a' + b', Submodule.add_mem _ ha' hb', by simp [ea, eb]⟩

theorem star_mem_one {x : K} (hx : x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    star x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_one_iff] at *
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', hy'⟩ := star_integral y
  exact ⟨y', hy'⟩

theorem star_mem_ipow {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥)
    (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℤ) {x : K} (hx : x ∈ ipow 𝔡 n) :
    star x ∈ ipow 𝔡 n := by
  apply GlobalTheory.DegCnt.PosJ.star_mem_ipow <;> assumption

end Star

end GlobalTheory.RowStab
end
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.NilLift

theorem exists_projector {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ P : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤)
    (hsat : ∀ c : O, c ≠ 0 → ∀ v ∈ Λ, c • v ∈ P → v ∈ P) :
    ∃ g : V →ₗ[K] V, (∀ z ∈ Λ, g z ∈ P) ∧ ∀ z ∈ Λ, z ∈ P → g z = z := by
  have hu : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) x) := fun s => by
    have := isLocalizedModule_id (nonZeroDivisors O) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := hu
      surj := fun y => by
        have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
        obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
        rw [Submodule.span_eq] at hs
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := P.comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c (nonZeroDivisors.coe_ne_zero c) v v.2 h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  let g : V →ₗ[K] V := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hu)
  have hg : ∀ y : Λ, g y = π y := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hu y
  refine ⟨g, fun z hz => ?_, fun z hz hP => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact hπ _
  · rw [hg ⟨z, hz⟩, hπ' ⟨z, hz⟩ hP]

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

local notation "𝒽" => Formalism.UG.hform (starRingEnd E) J

theorem form_eq (x y : Fin n → E) : 𝒽 x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply,
    starRingEnd_apply]

theorem form_star (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (x y : Fin n → E) :
    star (𝒽 x y) = 𝒽 y x := by
  have h : ∀ i j, star (J i j) = J j i := fun i j => congrFun (congrFun hJ j) i
  simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_adj (hJ : J.det ≠ 0) (Ψ : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    𝒽 x ((J⁻¹ * Ψᴴ * J) *ᵥ y) = 𝒽 (Ψ *ᵥ x) y := by
  rw [form_eq, form_eq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.one_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem eq_zero_of_form (hJ : J.det ≠ 0) (y : Fin n → E) (h : ∀ x, 𝒽 x y = 0) : y = 0 := by
  have h1 : J *ᵥ y = 0 := by
    funext i
    have := h (Pi.single i 1)
    rw [form_eq] at this
    simpa [Pi.star_single] using this
  exact Matrix.eq_zero_of_mulVec_eq_zero hJ h1

theorem form_span_left (S : Set (Fin n → E)) (y : Fin n → E) (h : ∀ s ∈ S, 𝒽 s y = 0)
    (w : Fin n → E) (hw : w ∈ Submodule.span E S) : 𝒽 w y = 0 := by
  simp only [form_eq] at h ⊢
  induction hw using Submodule.span_induction with
  | mem s hs => exact h s hs
  | zero => simp
  | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
  | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]

theorem inNil_sub_adj (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (hdet : J.det ≠ 0)
    (W : Submodule E (Fin n → E)) (hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd E) J W)
    (Ψ : Matrix (Fin n) (Fin n) E) (h1 : ∀ u, Ψ *ᵥ u ∈ W) (h2 : ∀ u ∈ W, Ψ *ᵥ u = 0) :
    InNil (starRingEnd E) J W (Ψ - J⁻¹ * Ψᴴ * J) ∧
      ∀ u ∈ perpSet (starRingEnd E) J W, (J⁻¹ * Ψᴴ * J) *ᵥ u = 0 := by
  have hA : ∀ u ∈ perpSet (starRingEnd E) J W, (J⁻¹ * Ψᴴ * J) *ᵥ u = 0 := fun u hu =>
    eq_zero_of_form J hdet _ fun v => by rw [form_adj J hdet]; exact hu _ (h1 v)
  have hsr : ∀ a b c : Fin n → E, 𝒽 a (b - c) = 𝒽 a b - 𝒽 a c := fun a b c => by
    simp only [form_eq, Matrix.mulVec_sub, dotProduct_sub]
  have hsl : ∀ a b c : Fin n → E, 𝒽 (b - c) a = 𝒽 b a - 𝒽 c a := fun a b c => by
    simp only [form_eq, star_sub, sub_dotProduct]
  refine ⟨⟨fun u u' => ?_, fun u w hw => ?_, fun u hu => ?_, fun u hu => ?_⟩, hA⟩
  · rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hsr, hsl, form_adj J hdet,
      ← form_star J hJ u' ((J⁻¹ * Ψᴴ * J) *ᵥ u), form_adj J hdet, form_star J hJ]
    ring
  · rw [Matrix.sub_mulVec, hsr, form_adj J hdet, h2 w hw, hW _ (h1 u) w hw, form_eq]
    simp
  · rw [Matrix.sub_mulVec, hA u hu, sub_zero]
    exact h1 u
  · rw [Matrix.sub_mulVec, hA u (hW u hu), sub_zero]
    exact h2 u hu

end Form

theorem mem_perpIn_iff (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) (y : Fin I.n → I.E) :
    y ∈ perpIn I x S ↔ y ∈ lamX I x ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨zero_mem _, fun s _ => by simp [form_eq]⟩
  | add y z _ _ hy hz =>
    exact ⟨add_mem hy.1 hz.1, fun s hs => by
      rw [form_eq, Matrix.mulVec_add, dotProduct_add, ← form_eq, ← form_eq, hy.2 s hs, hz.2 s hs, add_zero]⟩
  | smul c y _ hy =>
    exact ⟨Submodule.smul_mem _ _ hy.1, fun s hs => by
      rw [form_eq, Matrix.mulVec_smul, dotProduct_smul, ← form_eq, hy.2 s hs, smul_zero]⟩

theorem exists_nilInt_lift : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  intro I x R hR Φ hΦ0 hΦ
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨g, hg, hg'⟩ := exists_projector (lamX I x) (perpIn I x R) hfg hspan (fun c hc v hv h => by
    refine (mem_perpIn_iff I x R v).2 ⟨hv, fun s hs => ?_⟩
    have h1 := ((mem_perpIn_iff I x R _).1 h).2 s hs
    rw [form_eq, Matrix.mulVec_smul, dotProduct_smul, ← form_eq] at h1
    exact (smul_eq_zero.1 h1).resolve_left hc)
  set W := Submodule.span I.E (R : Set (Fin I.n → I.E)) with hWdef
  let Ψ : Matrix (Fin I.n) (Fin I.n) I.E := Φ * LinearMap.toMatrix' g
  have hΨ : ∀ u, Ψ *ᵥ u = Φ *ᵥ g u := fun u => by
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  have hPΛ : ∀ y ∈ perpIn I x R, y ∈ lamX I x := fun y hy => ((mem_perpIn_iff I x R y).1 hy).1
  have hΨP : ∀ y ∈ perpIn I x R, Ψ *ᵥ y = Φ *ᵥ y := fun y hy => by rw [hΨ, hg' y (hPΛ y hy) hy]
  have hΨΛ : ∀ y ∈ lamX I x, Ψ *ᵥ y ∈ R := fun y hy => by rw [hΨ]; exact hΦ _ (hg y hy)
  have hP : ∀ y ∈ perpIn I x R, y ∈ perpSet (starRingEnd I.E) I.J W := fun y hy =>
    form_span_left I.J _ y ((mem_perpIn_iff I x R y).1 hy).2
  have hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd I.E) I.J W := fun w hw w' hw' => by
    rw [← form_star I.J I.J_herm, form_span_left I.J _ w' (fun s hs => ?_) w hw, star_zero]
    rw [← form_star I.J I.J_herm, hP s (hR hs) w' hw', star_zero]
  have h1 : ∀ u, Ψ *ᵥ u ∈ W := fun u => by
    have : Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) ≤ W.comap (Matrix.mulVecLin Ψ) :=
      Submodule.span_le.2 fun y hy => Submodule.subset_span (hΨΛ y hy)
    exact this (hspan ▸ Submodule.mem_top)
  have h2 : ∀ u ∈ W, Ψ *ᵥ u = 0 := fun u hu => by
    have : W ≤ LinearMap.ker (Matrix.mulVecLin Ψ) :=
      Submodule.span_le.2 fun y hy => (hΨP y (hR hy)).trans (hΦ0 y hy)
    exact this hu
  obtain ⟨hN, hA⟩ := inNil_sub_adj I.J I.J_herm I.J_det W hW Ψ h1 h2
  refine ⟨_, ⟨hN, fun u hu => ?_⟩, fun y hy => ?_⟩
  · rw [Matrix.sub_mulVec]
    refine sub_mem (hPΛ _ (hR (hΨΛ u hu))) ((hdual _).2 fun z hz => ?_)
    rw [form_adj I.J I.J_det]
    exact (hdual u).1 hu _ (hPΛ _ (hR (hΨΛ z hz)))
  · rw [Matrix.sub_mulVec, hA y (hP y hy), sub_zero, hΨP y hy]

end GlobalTheory.NilLift
end
end

section

open MeasureTheory NumberField Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.unitaryAutomorphicCounting_unbundled : GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀, ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ), (n₁ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧ Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ ∀ P : Ideal (𝓞 I.E), P.IsMaximal → ((g₀ : 𝓞 I.E) ∈ P) → Ideal.absNorm P = g₀ ∧ (g₀ : 𝓞 I.E) ∉ P ^ 2) → ((∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧ I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re) → (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h → Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) → Real.log (Real.log b) ≤ 1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) → |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e| ≤ Real.exp (-(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e := by
  first | exact @GlobalTheory.CountBridge.count_unbundled | exact GlobalTheory.CountBridge.count_unbundled | (intros; apply GlobalTheory.CountBridge.count_unbundled <;> assumption)
end

section

open GlobalTheory.HL
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.mass_genus_restricted_product : ∀ {ι : Type} (G : ι → Type) [∀ i, Group (G i)] (X : ι → Type) [∀ i, MulAction (G i) (X i)] (A : ∀ i, Subgroup (G i)) (H : Type) [Group H] (φ : H →* ∀ i, G i), Function.Injective φ → (∀ h, {i | φ h i ∉ A i}.Finite) → (∃ S : Finset (∀ i, G i), (∀ s ∈ S, {i | s i ∉ A i}.Finite) ∧ ∀ g : ∀ i, G i, {i | g i ∉ A i}.Finite → ∃ s ∈ S, ∃ h : H, ∃ k : ∀ i, G i, (∀ i, k i ∈ A i) ∧ g = φ h * s * k) → (∀ a : ∀ i, G i, {i | a i ∉ A i}.Finite → {h : H | ∀ i, (a i)⁻¹ * φ h i * a i ∈ A i}.Finite) → ∀ x0 : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (A i) ≠ 0 ∧ (A i).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | A i ≠ MulAction.stabilizer (G i) (x0 i)}.Finite → ∃ V1 : ℝ, 0 < V1 ∧ ∀ x : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (MulAction.stabilizer (G i) (x i)) ≠ 0 ∧ (MulAction.stabilizer (G i) (x i)).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | x i ≠ x0 i}.Finite → (∑' o : Quot (fun y y' : (∀ i, X i) => ∃ h : H, φ h • y = y'), if (∀ i, ∃ g : G i, g • x i = o.out i) ∧ {i | o.out i ≠ x i}.Finite then (({h : H | φ h • o.out = o.out}.encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V1 * ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i))) := by
  first | exact @GlobalTheory.HL.mass_restricted_product | exact GlobalTheory.HL.mass_restricted_product | (intros; apply GlobalTheory.HL.mass_restricted_product <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.IotaConj

theorem sigR_inclE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (x : E) :
    sigR σ R (inclE (F := F) R x) = inclE (F := F) R (σ x) := by
  simp [sigR, inclE]

theorem sigR_mem_OAd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) : sigR σ (Ad F) a ∈ OAd F E := by

  have key : OAd F E ≤ (OAd F E).comap (sigR σ (Ad F)) := by
    show tensInt (F := F) (Ad F) (intOE E) (intAd F) ≤
      (tensInt (F := F) (Ad F) (intOE E) (intAd F)).comap (sigR σ (Ad F))
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := hx
      have hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E z)) :=
        (RingOfIntegers.isIntegral_coe z).map (σ : E →+* E).toIntAlgHom
      refine Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E z), ⟨⟨_, hint⟩, rfl⟩⟩, ?_⟩)
      simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
      simp [sigR]
  exact key ha

theorem iota_sigR (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E']
    (σ : E →ₐ[F] E) (σ' : E' →ₐ[F'] E') (e : E ≃+* E') (ι : E ⊗[F] Ad F ≃+* E' ⊗[F'] Ad F')
    (he : ∀ x, e (σ x) = σ' (e x))
    (hι : ∀ x, ι (inclE (F := F) (Ad F) x) = inclE (F := F') (Ad F') (e x))
    (hO : ∀ a, a ∈ OAd F E ↔ ι a ∈ OAd F' E') (a : E ⊗[F] Ad F) :
    ι (sigR σ (Ad F) a) = sigR σ' (Ad F') (ι a) := by
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F E
  obtain ⟨-, -, h3', -, -⟩ := GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F' E'

  set D : E ⊗[F] Ad F → E' ⊗[F'] Ad F' :=
    fun b => ι (sigR σ (Ad F) b) - sigR σ' (Ad F') (ι b) with hD
  have Dadd : ∀ b c, D (b + c) = D b + D c := by
    intro b c; simp only [hD, map_add (f := _)]; abel
  have Dmul : ∀ (m : ℕ) b, D ((m : E ⊗[F] Ad F) * b) = (m : E' ⊗[F'] Ad F') * D b := by
    intro m b; simp only [hD, map_mul, map_natCast]; ring
  have Dincl : ∀ x : E, D (inclE (F := F) (Ad F) x) = 0 := by
    intro x; simp only [hD, sigR_inclE, hι, he, sub_self]
  have DO : ∀ b ∈ OAd F E, D b ∈ OAd F' E' := by
    intro b hb
    exact Subring.sub_mem _ ((hO _).1 (sigR_mem_OAd σ hb)) (sigR_mem_OAd σ' ((hO _).1 hb))
  have Dzero : ∀ b ∈ OAd F E, D b = 0 := by
    intro b hb
    refine h3' (D b) fun m hm => ?_
    obtain ⟨x, t, ht, hbt⟩ := h2 b hb m hm
    exact ⟨D t, DO t ht, by rw [hbt, Dadd, Dincl, Dmul, zero_add]⟩
  obtain ⟨m, hm, hma⟩ := h4 a
  have h0 : (m : E' ⊗[F'] Ad F') * D a = 0 := by rw [← Dmul]; exact Dzero _ hma
  have hu : IsUnit (m : E' ⊗[F'] Ad F') := by
    rw [← map_natCast (inclE (F := F') (E := E') (Ad F')) m]
    exact (IsUnit.mk0 (m : E') (Nat.cast_ne_zero.2 hm.ne')).map _
  have hDa : D a = 0 := hu.mul_right_eq_zero.1 h0
  simp only [hD] at hDa
  exact sub_eq_zero.1 hDa

end GlobalTheory.St.G.IotaConj
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicLatticeFrame_component_localFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (g k : ℕ) (Fr : AdFrame σ J (hat F L) g k) (v : HeightOneSpectrum (𝓞 F)), prV (E := E) v Fr.eps * prV (E := E) v Fr.eps = prV (E := E) v Fr.eps ∧ prV (E := E) v Fr.eps * sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) = 0 ∧ prV (E := E) v Fr.eps ∈ intV E v ∧ (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - prV (E := E) v Fr.eps - sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps)) • y = (g : E ⊗[F] v.adicCompletion F) • z) ∧ (∀ i, prVec v (Fr.b i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.bd i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.b i) = prV (E := E) v Fr.eps • prVec v (Fr.b i)) ∧ (∀ i, prVec v (Fr.bd i) = sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) • prVec v (Fr.bd i)) ∧ (∀ i j, ∃ t ∈ intV E v, hR σ J (v.adicCompletion F) (prVec v (Fr.bd i)) (prVec v (Fr.b j)) - (if i = j then prV (E := E) v Fr.eps else 0) = (g : E ⊗[F] v.adicCompletion F) * t) ∧ (∀ y ∈ loc v L, InModL (loc v L) g (Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))) y) := by
  first | exact @GlobalTheory.St.G.frame_component_local | exact GlobalTheory.St.G.frame_component_local | (intros; apply GlobalTheory.St.G.frame_component_local <;> assumption)
end
