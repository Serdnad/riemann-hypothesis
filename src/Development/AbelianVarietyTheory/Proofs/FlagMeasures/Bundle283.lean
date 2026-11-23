module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle275
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle276
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle209
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLeviRealPlacesProductMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureQuotientUnitaryJVectorStabiliser
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianAmplitudeMassProductStructure
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommutantScalar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

section Global

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_zsmul_mem_of_span (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.span E (M : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℤ, c ≠ 0 ∧ c • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem ..)

theorem exists_zsmul_le (L M : Submodule (𝓞 E) (Fin n → E)) (hL : Module.Finite (𝓞 E) L)
    (hM : Submodule.span E (M : Set (Fin n → E)) = ⊤) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ x ∈ L, c • x ∈ M := by
  obtain ⟨S, hS⟩ : L.FG := Module.Finite.iff_fg.mp hL
  have hfin : ∀ T : Finset (Fin n → E), ∃ c : ℤ, c ≠ 0 ∧ ∀ x ∈ T, c • x ∈ M := by
    classical
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a T _ ih =>
      obtain ⟨c, hc, hcT⟩ := ih
      obtain ⟨d, hd, hda⟩ := exists_zsmul_mem_of_span M hM a
      refine ⟨d * c, mul_ne_zero hd hc, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_comm, mul_smul]
        exact zsmul_mem hda c
      · rw [mul_smul]
        exact zsmul_mem (hcT x hx) d
  obtain ⟨c, hc, hcS⟩ := hfin S
  refine ⟨c, hc, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hcS x hx
  | zero => simp
  | add a b _ _ ha hb =>
    rw [smul_add]
    exact M.add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact M.smul_mem a hy

end Global

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem int_inv_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) (c : ℤ)
    (hv : (c : 𝓞 F) ∉ v.asIdeal) :
    (algebraMap F (v.adicCompletion F) (c : F))⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = 1 := by
    have h2 : (c : F) = algebraMap (𝓞 F) F (c : 𝓞 F) := by simp
    have h3 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = v.valuation F (c : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c : F)
    rw [h3, h2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem loc_le_of_zsmul (v : HeightOneSpectrum (𝓞 F)) (L M : Submodule (𝓞 E) (Fin n → E)) (c : ℤ)
    (hc : c ≠ 0) (hv : (c : 𝓞 F) ∉ v.asIdeal) (h : ∀ x ∈ L, c • x ∈ M) : loc v L ≤ loc v M := by
  have hu := int_inv_mem_adicCompletionIntegers v c hv
  set u : v.adicCompletion F := (algebraMap F (v.adicCompletion F) (c : F))⁻¹ with hudef
  have hne : algebraMap F (v.adicCompletion F) (c : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hc
  have hs : (1 : E) ⊗ₜ[F] u ∈ intV E v :=
    Subring.subset_closure (Or.inr ⟨⟨u, hu⟩, rfl⟩)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  have hgen : (fun i => inclE (F := F) (v.adicCompletion F) ((c • x) i)) ∈ loc (F := F) v M :=
    Submodule.subset_span ⟨c • x, h x hx, rfl⟩
  have hm := (loc (F := F) v M).smul_mem ⟨_, hs⟩ hgen
  suffices heq : (fun i => inclE (F := F) (v.adicCompletion F) (x i)) =
      (⟨(1 : E) ⊗ₜ[F] u, hs⟩ : intV E v) • (fun i => inclE (F := F) (v.adicCompletion F) ((c • x) i)) by
    show (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ loc (F := F) v M
    rw [heq]
    exact hm
  funext i
  have hci : (c • x) i = (c : F) • x i := by
    simp [Int.cast_smul_eq_zsmul]
  have hone : (c : F) • u = 1 := by
    rw [Algebra.smul_def, hudef, mul_inv_cancel₀ hne]
  show (x i) ⊗ₜ[F] (1 : v.adicCompletion F) = ((1 : E) ⊗ₜ[F] u) * ((c • x) i ⊗ₜ[F] (1 : v.adicCompletion F))
  rw [Algebra.TensorProduct.tmul_mul_tmul, hci, one_mul, mul_one, TensorProduct.smul_tmul, hone]

end Local

theorem loc_eq_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M →
    {v : HeightOneSpectrum (𝓞 F) | loc v L ≠ loc v M}.Finite := by
  intro F E _ _ _ _ _ n L M hL hM
  obtain ⟨c, hc, hcLM⟩ := exists_zsmul_le L M hL.1 hM.2
  obtain ⟨d, hd, hdML⟩ := exists_zsmul_le M L hM.1 hL.2
  have hcd : (((c * d : ℤ) : 𝓞 F)) ≠ 0 := by
    exact_mod_cast mul_ne_zero hc hd
  have hI : Ideal.span {(((c * d : ℤ) : 𝓞 F))} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hcd
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  by_contra hn
  have hcv : (c : 𝓞 F) ∉ v.asIdeal := fun h => hn (by
    rw [Int.cast_mul]
    exact Ideal.mul_mem_right _ _ h)
  have hdv : (d : 𝓞 F) ∉ v.asIdeal := fun h => hn (by
    rw [Int.cast_mul]
    exact Ideal.mul_mem_left _ _ h)
  exact hv (le_antisymm (loc_le_of_zsmul v L M c hc hcv hcLM) (loc_le_of_zsmul v M L d hd hdv hdML))

end GlobalTheory.St.G

end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreVolumeGen

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem GG_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ (Hpk k r) hpk_unit).2.1 a ha b hb

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det :=
  ((uHGroup _ (Hpk k r) hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r :=
  ((uHGroup _ (Hpk k r) hpk_unit).2.2 a ha).2

theorem continuous_two (a b : Mat k r) : Continuous (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem measurable_two (a b : Mat k r) :
    Measurable (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) := by
  have h : Continuous (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) := continuous_two a b
  exact h.measurable

def twoEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := Matrix.of.symm (a * Matrix.of x * b)
  invFun x := Matrix.of.symm (a⁻¹ * Matrix.of x * b⁻¹)
  left_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hb]
  right_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ hb]
  measurable_toFun := measurable_two a b
  measurable_invFun := measurable_two _ _

theorem map_twoEquiv {μ : Measure (Mt k r)} {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hl : μ.map (lmulM a) = μ) (hr : μ.map (rmulM b) = μ) : μ.map (twoEquiv a b ha hb) = μ := by
  have hla : Measurable (lmulM a : Mt k r → Mt k r) := by
    have h : (lmulM a : Mt k r → Mt k r) = fun x => (Matrix.of.symm (a * Matrix.of x * 1) : Mt k r) := by
      funext x; apply Matrix.of.injective; (rw [Equiv.apply_symm_apply, Matrix.mul_one]) <;> rfl
    rw [h]; exact measurable_two a 1
  have hrb : Measurable (rmulM b : Mt k r → Mt k r) := (GlobalTheory.SgInf.continuous_rmulM b).measurable
  have h1 : (twoEquiv a b ha hb : Mt k r → Mt k r) = rmulM b ∘ lmulM a := rfl
  rw [h1, ← Measure.map_map hrb hla, hl, hr]

theorem fibre_volume : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' γ → DeOK k r z z' γ De → 0 < s → NormR k r γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yv k r z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset k r z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y / s) := by
  intro k r z z' γ De s μR hr hk hTF hDe hs hNR g₁ hg₁
  obtain ⟨n₁, hn₁, n₂, hn₂, g₀, β, hNorm, rfl, rfl⟩ := hNR
  obtain ⟨hz, hz', hT, hT', -, hGf, hDr⟩ := hTF
  have hg₀G : g₀ ∈ GG k r := hNorm.1
  have hn₁S : n₁ ∈ Sset k r z := GlobalTheory.Amp.YInv.N_sub_S z hn₁
  have hn₂S : n₂ ∈ Sset k r z' := GlobalTheory.Amp.YInv.N_sub_S z' hn₂
  have hn₂G : n₂ ∈ GG k r := hn₂.1
  have hu2 : IsUnit n₂.det := GG_unit hn₂G
  have hn₂i : n₂⁻¹ ∈ Nset k r := (nSubgroup k r).2.2 n₂ hn₂
  have hn₂iS : n₂⁻¹ ∈ Sset k r z' := GlobalTheory.Amp.YInv.N_sub_S z' hn₂i
  have c1 : ∀ B : Mat k r, n₂ * (n₂⁻¹ * B) = B := fun B => Matrix.mul_nonsing_inv_cancel_left n₂ B hu2
  have c2 : ∀ B : Mat k r, n₂⁻¹ * (n₂ * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left n₂ B hu2

  have hDmin : ∀ l, Dmin k r z z' (n₁ * g₀ * n₂) l = Dmin k r z z' g₀ l :=
    fun l => dInv k r z z' hz hz' n₁ hn₁S n₂ hn₂S g₀ l
  have hGf0 : Gf k r z z' (n₁ * g₀ * n₂) = Gf k r z z' g₀ := gInv k r z z' hz hz' n₁ hn₁S n₂ hn₂S g₀
  have hDr0 : Dr k r z z' (n₁ * g₀ * n₂) = Dr k r z z' g₀ := by unfold Dr; rw [hDmin]
  have hTF0 : TwoFl k r z z' g₀ := ⟨hz, hz', hT, hT', hg₀G, by rw [← hGf0]; exact hGf, by rw [← hDr0]; exact hDr⟩
  have hDe0 : DeOK k r z z' g₀ De := by
    refine ⟨hDe.1, fun l hl hne => ?_⟩
    rw [← hDmin] at hne ⊢
    exact hDe.2 l hl hne

  obtain ⟨n', hn', a, ha, m, hm, κ, hκ, hdec⟩ := GlobalTheory.Amp.Iwa.iwasawa k r (n₂ * g₁) (GG_mul hn₂G hg₁)
  have hB := GlobalTheory.T.fibre_gramNumber_null_and_cutoff_integral_bound k r z z' g₀ β De hr hk hTF0 hNorm hDe0 m hm a ha
  set A := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hA
  have hn'G : n' ∈ GG k r := hn'.1
  have hdec' : n₂ * g₁ = n' * A * κ := by rw [hdec, hA]; simp only [mul_assoc]
  have c3 : ∀ B : Mat k r, n'⁻¹ * (n' * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left n' B (GG_unit hn'G)
  have hAK : A * κ ∈ GG k r := by
    have : A * κ = n'⁻¹ * (n₂ * g₁) := by rw [hdec']; simp only [mul_assoc, c3]
    rw [this]; exact GG_mul (GG_inv hn'G) (GG_mul hn₂G hg₁)
  have hg : n₂⁻¹ * (n' * (A * κ)) = g₁ := by rw [← mul_assoc n' A, ← hdec', c2]

  have hl2 : (lebN k r).map (lmulM n₂) = lebN k r := (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r).2.2.2 n₂ hn₂
  have hr2 : (lebN k r).map (rmulM (n₂⁻¹ * n')) = lebN k r :=
    ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT (lebN k r)).2.1 (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r)).1.1 _ ((nSubgroup k r).2.1 _ hn₂i _ hn')
  have hu' : IsUnit (n₂⁻¹ * n').det := GG_unit (GG_mul (GG_inv hn₂G) hn'G)
  obtain ⟨e, he_map, he⟩ : ∃ e : Mt k r ≃ᵐ Mt k r, (lebN k r).map e = lebN k r ∧
      ∀ n, Matrix.of (e n) = n₂ * Matrix.of n * (n₂⁻¹ * n') :=
    ⟨twoEquiv n₂ (n₂⁻¹ * n') hu2 hu', map_twoEquiv hu2 hu' hl2 hr2, fun _ => rfl⟩
  have key : ∀ n : Mt k r, Matrix.of n * g₁ = n₂⁻¹ * (Matrix.of (e n) * A) * κ := by
    intro n; rw [he n]; simp only [mul_assoc, c2, hg]

  have hYv : ∀ W : Mat k r, Yv k r z z' (n₁ * g₀ * n₂) (n₂⁻¹ * W * κ) = Yv k r z z' g₀ W := by
    intro W
    rw [GlobalTheory.Amp.YInv.Yv_N hz hz' g₀ hn₁ hn₂]
    have : n₂ * (n₂⁻¹ * W * κ) = W * κ := by simp only [mul_assoc, c1]
    rw [this, GlobalTheory.Amp.YInv.Yv_K z z' g₀ W hκ.1 hκ.2]
  have hGGW : ∀ W : Mat k r, n₂⁻¹ * W * κ ∈ GG k r ↔ W ∈ GG k r := by
    intro W
    constructor
    · intro h
      have : W = n₂ * (n₂⁻¹ * W * κ) * κ⁻¹ := by
        simp only [mul_assoc, c1, Matrix.mul_nonsing_inv _ (GG_unit hκ.1), Matrix.mul_one]
      rw [this]; exact GG_mul (GG_mul hn₂G h) (GG_inv hκ.1)
    · intro h; exact GG_mul (GG_mul (GG_inv hn₂G) h) hκ.1
  have hSg' : ∀ W ∈ GG k r, Sg k r z' (n₂⁻¹ * W * κ) = Sg k r z' W :=
    fun W hW => ((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 W hW n₂⁻¹ hn₂iS κ hκ).2
  have hSg : ∀ W ∈ GG k r, Sg k r z (n₁ * g₀ * n₂ * (n₂⁻¹ * W * κ)) = Sg k r z (g₀ * W) := by
    intro W hW
    have : n₁ * g₀ * n₂ * (n₂⁻¹ * W * κ) = n₁ * (g₀ * W) * κ := by simp only [mul_assoc, c1]
    rw [this]; exact ((GlobalTheory.Amp.LInv.lengths_basic k r z hz).1 (g₀ * W) (GG_mul hg₀G hW) n₁ hn₁S κ hκ).2
  refine ⟨?_, ?_⟩
  · have hset : {n : Mt k r | Yv k r z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = 0} =
        e ⁻¹' {ν | Yv k r z z' g₀ (Matrix.of ν * A) = 0} := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_preimage, key n, hYv]
    rw [hset, ← MeasurableEquiv.map_apply, he_map]
    exact hB.1
  · intro φ hφ R₀ y hR₀ hy
    have hl : ∀ (b : Mat k r) (x : Mt k r), Matrix.of (lmulM b x) = b * Matrix.of x := fun _ _ => rfl
    have hc : ∀ (b : Mat k r) (x : Mt k r), Matrix.of (conjM b x) = b * Matrix.of x * b⁻¹ := fun _ _ => rfl
    have hmeas : ∀ (f : Mt k r → Mt k r) (b c : Mat k r), (∀ x, Matrix.of (f x) = b * Matrix.of x * c) →
        Measurable f := by
      intro f b c h
      have : f = fun x => (Matrix.of.symm (b * Matrix.of x * c) : Mt k r) :=
        funext fun x => Matrix.of.injective (by rw [h] <;> rfl)
      rw [this]; exact measurable_two b c
    obtain ⟨P, hPm, hP⟩ : ∃ P : Mt k r → Mt k r, Measurable P ∧
        ∀ ν, Matrix.of (P ν) = n₂⁻¹ * Matrix.of ν * (A * κ) :=
      ⟨fun ν => Matrix.of.symm (n₂⁻¹ * Matrix.of ν * (A * κ)), measurable_two _ _, fun _ => rfl⟩

    have hsub : SubCut (Nset k r) (lebR k r β) (fun ν => ENNReal.ofReal s * φ (P ν)) := by
      refine ⟨(hφ.1.comp hPm).const_mul _, fun x hx => ?_⟩
      have hx0 : Matrix.of (P x) ∈ GG k r := by
        rw [hP, mul_assoc]; exact GG_mul (GG_inv hn₂G) (GG_mul hx.1 hAK)
      have h1 := hφ.2 (P x) hx0
      have hm1 : Measurable fun ρ : Mt k r => φ (lmulM (Matrix.of ρ) (P x)) :=
        hφ.1.comp (hmeas _ 1 (Matrix.of (P x)) fun ρ => by simp only [hl, Matrix.one_mul])
      have hm2 : Measurable (conjM n₂⁻¹ : Mt k r → Mt k r) := hmeas _ n₂⁻¹ n₂⁻¹⁻¹ fun x => hc _ _
      rw [lintegral_map hm1 hm2, lintegral_smul_measure] at h1
      have hPl : ∀ ρ : Mt k r, P (lmulM (Matrix.of ρ) x) = lmulM (Matrix.of (conjM n₂⁻¹ ρ)) (P x) := by
        intro ρ
        apply Matrix.of.injective
        simp only [hl, hc, hP, Matrix.nonsing_inv_nonsing_inv _ hu2, mul_assoc, c1]
      calc ∫⁻ ρ, ENNReal.ofReal s * φ (P (lmulM (Matrix.of ρ) x)) ∂lebR k r β
          = ENNReal.ofReal s * ∫⁻ ρ, φ (P (lmulM (Matrix.of ρ) x)) ∂lebR k r β :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal s * ∫⁻ ρ, φ (lmulM (Matrix.of (conjM n₂⁻¹ ρ)) (P x)) ∂lebR k r β := by
            congr 1; exact lintegral_congr fun ρ => by rw [hPl ρ]
        _ ≤ 1 := by first | exact h1 | (rw [smul_eq_mul] at h1; exact h1)
    have hmain := hB.2 (fun ν => ENNReal.ofReal s * φ (P ν)) hsub R₀ y hR₀ hy
    have hmem : ∀ n : Mt k r, rmulM g₁ n ∈ Eset k r z z' (n₁ * g₀ * n₂) R₀ y ↔
        rmulM A (e n) ∈ Eset k r z z' g₀ R₀ y := by
      intro n
      simp only [Eset, Set.mem_setOf_eq, GlobalTheory.SgInf.of_rmulM]
      rw [key n]
      generalize Matrix.of (e n) * A = W
      rw [hGGW W, hYv W]
      constructor
      · rintro ⟨hW, h1, h2, h3, h4⟩
        rw [hSg' W hW] at h1; rw [hSg W hW] at h2; exact ⟨hW, h1, h2, h3, h4⟩
      · rintro ⟨hW, h1, h2, h3, h4⟩
        exact ⟨hW, by rw [hSg' W hW]; exact h1, by rw [hSg W hW]; exact h2, h3, h4⟩
    have hpt : ∀ n : Mt k r, rmulM g₁ n = P (e n) := by
      intro n
      apply Matrix.of.injective
      rw [GlobalTheory.SgInf.of_rmulM, hP, key n]
      simp only [mul_assoc]
    have hint : ∫⁻ n, φ (rmulM g₁ n) * (Eset k r z z' (n₁ * g₀ * n₂) R₀ y).indicator 1 (rmulM g₁ n) ∂lebN k r
        = ∫⁻ ν, φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν) ∂lebN k r := by
      calc _ = ∫⁻ n, (fun ν => φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν)) (e n) ∂lebN k r := by
            refine lintegral_congr fun n => ?_
            have hind : (Eset k r z z' (n₁ * g₀ * n₂) R₀ y).indicator (1 : Mt k r → ℝ≥0∞) (rmulM g₁ n) =
                (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A (e n)) := by
              by_cases h : rmulM g₁ n ∈ Eset k r z z' (n₁ * g₀ * n₂) R₀ y
              · simp only [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem n).1 h), Pi.one_apply]
              · have h' : rmulM A (e n) ∉ Eset k r z z' g₀ R₀ y := fun h' => h ((hmem n).2 h')
                first
                  | rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
                  | rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h']
                  | simp [Set.indicator, h, h']
            dsimp only
            rw [hind, hpt n]
        _ = ∫⁻ ν, φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν) ∂((lebN k r).map e) :=
            (lintegral_map_equiv (fun ν => φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν)) e).symm
        _ = _ := by rw [he_map]
    have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
    rw [hint, ENNReal.ofReal_div_of_pos hs,
      ENNReal.le_div_iff_mul_le (Or.inl hs0) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm _ (ENNReal.ofReal s), ← lintegral_const_mul' (ENNReal.ofReal s) _ ENNReal.ofReal_ne_top]
    refine le_trans (le_of_eq ?_) hmain
    refine lintegral_congr fun ν => ?_
    simp only [mul_assoc]

end GlobalTheory.Amp.FibreVolumeGen
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.flagLevi_realPlaces_product_measure : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (μM : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (μM v)] (c₀ : InfinitePlace I₀.F → ℝ), (∀ v, IsGaugeSub (flagM (I.ε v) (flagAt I S v)) ((I.n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) (μM v)) → IsGaugeAll I₀ c₀ → ∃ (Θ : (∀ i, MatInf I.E (j i)) × I₀.Ginf → I.Ginf) (κ : Fin a → ℝ), Measurable Θ ∧ (∀ i, 0 < κ i) ∧ (∀ m : I.Ginf, (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ↔ ∃ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) ∧ Θ z = m) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, z.1 i ∈ autGL I.E (j i) (Λ i)) → z.2 ∈ latGroup I₀ x₀ → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → ∃ γ ∈ leviGroup I xf S, γ * Θ z' = Θ (fun i => z.1 i * z'.1 i, z.2 * z'.2)) ∧ (∀ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → ∀ i, sizesAt I xf S (Θ z) i = (detNorm I.E (j i) (z.1 i) / κ i) ^ (-(1 / (2 * (I.f : ℝ) * j i)))) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → Θ z = Θ z' → z = z') ∧ ∀ φ : I.Ginf → ENNReal, Measurable φ → ∫⁻ m, φ m ∂(Measure.pi μM) = (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2))) * ENNReal.ofReal (∏ v, c₀ v) * ∫⁻ z₁ in {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)}, ∫⁻ z₂, φ (Θ (z₁, z₂)) ∂(Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) ∂(Measure.pi fun i => haarGL I.E (j i)) := by
  first | exact @GlobalTheory.LeviIso.levi_product | exact GlobalTheory.LeviIso.levi_product | (intros; apply GlobalTheory.LeviIso.levi_product <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.gauge_measure_quotient_unitaryJ_vector_stabiliser : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε), qEps ε x₀ = sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g) → ∀ c c' : ℝ, IsGauge ε c → IsGauge ε' c' → ∀ b : Formalism.REAL.UJ ε → ENNReal, Measurable b → (∀ g, ENNReal.ofReal c' * ∫⁻ h, b (j h * g) ∂(Formalism.REAL.muG ε') = 1) → ENNReal.ofReal c * ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ x₀)) * b g ∂(Formalism.REAL.muG ε) = ENNReal.ofReal (2 ^ (n + 1) * gaussDens ε (sgn ℝ s)) := by
  first | exact @GlobalTheory.GaugeQuot.gauge_quotient | exact GlobalTheory.GaugeQuot.gauge_quotient | (intros; apply GlobalTheory.GaugeQuot.gauge_quotient <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFrames_defectOrder_share_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ C, S.IsCls C → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal (4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹) * S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ := by
  first | exact @GlobalTheory.HL.DefectShare.share_le | exact GlobalTheory.HL.DefectShare.share_le | (intros; apply GlobalTheory.HL.DefectShare.share_le <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitian_amplitude_mass_product_structure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ P : ∀ p, Submodule (A.L p).O (G.S p).V → Prop, (∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ → P p Λ → P p (h • Λ)) → {p | ∃ Λ, (G.S p).IsTerm (d p) Λ ∧ ¬ P p Λ}.Finite → G.amp d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∏ᶠ p, (G.S p).amp (d p) (P p) ∧ G.mass d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∏ᶠ p, (G.S p).mass (d p) (P p) ∧ {p | (G.S p).amp (d p) (P p) ≠ 1 ∨ (G.S p).mass (d p) (P p) ≠ 1}.Finite ∧ {o : Quot G.LRel | G.IsTerm d o.out}.Finite := by
  first | exact @GlobalTheory.HL.ProdStruct.product_structure | exact GlobalTheory.HL.ProdStruct.product_structure | (intros; apply GlobalTheory.HL.ProdStruct.product_structure <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.realUnipotent_integral_discreteSeries_vanish : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  first | exact @GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf | exact GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf | (intros; apply GlobalTheory.RealFibre.integral_phe_eq_zero_of_isKTypeOf <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLev

theorem isCuspHom_of_cusp_lowest : ∀ (B : RowsAut), (∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)) → (∀ v, ‖B.w v‖ = 1) → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) → IsCuspHom B.I A := by
  intro B hDS hw A hA hcusp
  obtain ⟨S, hS, hSc, hSR, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨-, -, -, -, hirr⟩ :=
    GlobalTheory.HilbTensorRep.tensor_rep_rows B fun v => ⟨(hDS v).2.2.1, (hDS v).2.2.2.1⟩
  obtain ⟨T₀, hT₀, rfl⟩ := Submodule.mem_map.mp hA
  have hT₀' : ∀ g : B.I.Ginf, T₀.comp (B.σs g) = (B.R (g, 1)).comp T₀ := hT₀
  have hRe := (GlobalTheory.IdemProj.re_orth_proj B).2.1

  have hint : ∀ (g : B.I.Ginf) (u : B.Hs),
      B.Re (T₀ (B.σs g u)) = B.R (g, 1) (B.Re (T₀ u)) := by
    intro g u
    have h1 := congrArg (fun L => L u) (hT₀' g)
    have h2 := congrArg (fun L => L (T₀ u)) (hRe g)
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [h1, h2]

  let P : Submodule ℂ B.Hs := S.comap (B.Re.comp T₀ : B.Hs →L[ℂ] B.I.L2 B.μf B.fund).toLinearMap
  have hPc : IsClosed (P : Set B.Hs) :=
    hSc.preimage (B.Re.comp T₀).continuous
  have hPs : ∀ g, ∀ u ∈ P, B.σs g u ∈ P := by
    intro g u hu
    change B.Re (T₀ (B.σs g u)) ∈ S
    rw [hint]
    exact hSR _ _ hu
  have hw0 : B.tens B.w ∈ P := by
    change B.Re (T₀ (B.tens B.w)) ∈ S
    rw [hS]
    simpa [ContinuousLinearMap.compL_apply] using hcusp
  have hne : B.tens B.w ≠ 0 := by
    intro h0
    have hn := GlobalTheory.HilbTensorRep.norm_tens B.tens_spec.1 B.w
    rw [h0, norm_zero] at hn
    simp [hw] at hn
  rcases hirr P hPc hPs with hbot | htop
  · exact absurd ((Submodule.mem_bot ℂ).mp (hbot ▸ hw0)) hne
  · intro u
    have hu : u ∈ P := htop ▸ Submodule.mem_top
    have : B.Re (T₀ u) ∈ S := hu
    simpa [ContinuousLinearMap.compL_apply] using (hS _).mp this

end GlobalTheory.RowLev
end
