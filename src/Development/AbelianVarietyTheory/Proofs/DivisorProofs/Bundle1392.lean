module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle063
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.HermLocDualBasis
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))

abbrev locS : Submonoid (𝓞 E) := Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl

theorem locS_le : locS F E v ≤ nonZeroDivisors (𝓞 E) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors

abbrev locR : Subalgebra (𝓞 E) E := Localization.subalgebra.ofField E (locS F E v) (locS_le F E v)

instance : IsDedekindDomain (locR F E v) :=
  IsLocalization.isDedekindDomain (𝓞 E) (locS_le F E v) _

instance : IsPrincipalIdealRing (locR F E v) :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot

omit [NumberField F] in
theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    form σ J (a • x) y = a * form σ J x y := by
  simp [form, smul_dotProduct]

omit [NumberField F] in
theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    form σ J x (a • y) = σ a * form σ J x y := by
  have : (fun i => σ ((a • y) i)) = σ a • (fun i => σ (y i)) := by ext i; simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

omit [NumberField F] in
theorem form_sum_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E)
    (c : Fin n → E) (b : Fin n → Fin n → E) :
    form σ J y (∑ l, c l • b l) = ∑ l, σ (c l) * form σ J y (b l) := by
  have : (fun i => σ ((∑ l, c l • b l) i)) = ∑ l, σ (c l) • (fun i => σ (b l i)) := by
    ext i; simp [Finset.sum_apply, map_sum]
  simp only [form, this, Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

omit [NumberField F] in
theorem form_rows (σ : E →ₐ[F] E) {n : ℕ} (J P Q : Matrix (Fin n) (Fin n) E) (k l : Fin n) :
    form σ J (P k) (Q l) = (P * J * (Q.map σ)ᵀ) k l := by
  simp only [form, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_assoc]

theorem exists_basis (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    ∃ (t : 𝓞 F), t ∉ v.asIdeal ∧ ∃ b : Fin n → Fin n → E, LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (algebraMap (𝓞 F) (𝓞 E) t) • w ∈ Submodule.span (𝓞 E) (Set.range b) := by
  letI := hL
  obtain ⟨s, b, hb, hbL, hs⟩ := GlobalTheory.PlaceInt.LocBasis.exists_basis_up_to (A := locR F E v) (locS F E v) L (Submodule.IsLattice.fg E L)
    Submodule.IsFullLattice.span_eq_top
  obtain ⟨t, ht, hst⟩ := s.2
  exact ⟨t, ht, b, hb, hbL, fun w hw => by rw [hst]; exact hs w hw⟩

end GlobalTheory.HermLocDualBasis


open GlobalTheory.HermLocDualBasis in
theorem GlobalTheory.HermLocDualBasis.exists_locDualBasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n r s : ℕ} (X : Spc F E n), X.IsHerm σ B r s → ∀ v : Pl (F := F),
    ∃ f p : Fin n → Fin n → E, (∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • f k ∈ X.L) ∧
      (∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • p k ∈ X.L) ∧
      ∀ k l, form σ X.J (p k) (f l) = if k = l then 1 else 0 := by
  intro F E _ _ _ _ _ σ B n r s X hX v
  obtain ⟨t, ht, b, hb, hbL, hspan⟩ := exists_basis F E v n X.L hX.lat
  let Bm : Matrix (Fin n) (Fin n) E := Matrix.of b
  have hBm : IsUnit Bm := Matrix.linearIndependent_rows_iff_isUnit.1 hb
  let G : Matrix (Fin n) (Fin n) E := Bm * X.J * (Bm.map σ)ᵀ
  have hG : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    have h1 : (Bm.map σ).det = σ Bm.det := ((σ : E →+* E).map_det Bm).symm
    have h2 : Bm.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det Bm).1 hBm |>.ne_zero
    simp only [G, Matrix.det_mul, Matrix.det_transpose, h1]
    exact mul_ne_zero (mul_ne_zero h2 (GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX))
      ((map_ne_zero σ).2 h2)
  let P : Matrix (Fin n) (Fin n) E := G⁻¹ * Bm
  have hdual : ∀ k l, form σ X.J (P k) (b l) = if k = l then 1 else 0 := by
    intro k l
    refine (form_rows F E σ X.J P Bm k l).trans ?_
    have : P * X.J * (Bm.map σ)ᵀ = 1 := by
      have e : P * X.J * (Bm.map σ)ᵀ = G⁻¹ * G := by simp only [P, G, Matrix.mul_assoc]
      rw [e]
      exact Matrix.nonsing_inv_mul G hG
    rw [this, Matrix.one_apply]
  refine ⟨b, fun k => P k, fun k => ⟨1, fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hbL k⟩,
    fun k => ⟨t, ht, ?_⟩, hdual⟩
  rw [hX.dual]
  intro x hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hspan x hx)
  have hc' : ∑ l, (c l : E) • b l = algebraMap F E (t : F) • x := by
    have e1 : ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) = algebraMap F E (t : F) := rfl
    rw [← e1]
    exact hc
  rw [form_smul_left, ← AlgHom.commutes σ, ← form_smul_right, ← hc', form_sum_right]
  simp only [hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact (c k).2.map (σ.toRingHom.toIntAlgHom)

end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.exists_translation_invariant_functional : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (n d : ℕ), ∃ Λ : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧
      ∃ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), Λ f ≠ 0 := by
  first | exact @GlobalTheory.HaarSB.exists_invariant_form_matrix | exact GlobalTheory.HaarSB.exists_invariant_form_matrix | (intros; apply GlobalTheory.HaarSB.exists_invariant_form_matrix <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.boundedIntegersStableSubgroup_eq_doubleOrthogonal : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ₀ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, ψ₀ (x * y) = 1) ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ A : AddSubgroup (κ → Fv F v), (∀ c ∈ HeightOneSpectrum.adicCompletionIntegers F v, ∀ t ∈ A, c • t ∈ A) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ t ∈ A, ∀ k, c * t k ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ t : κ → Fv F v, (∀ y : κ → Fv F v, (∀ s ∈ A, ψ₀ (s ⬝ᵥ y) = 1) → ψ₀ (t ⬝ᵥ y) = 1) → t ∈ A := by
  first | exact @GlobalTheory.LatticeDual.mem_of_mem_doubleOrth | exact GlobalTheory.LatticeDual.mem_of_mem_doubleOrth | (intros; apply GlobalTheory.LatticeDual.mem_of_mem_doubleOrth <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.skewSelfDual_lattice_localised_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {d r s : ℕ} (Y : Spc F E d), Y.IsSkew σ B r s → ∀ (v : Pl (F := F)) (u : Fin d → E),
    (∀ y ∈ Y.L, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * form σ Y.J u y)) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • u ∈ Y.L := by
  first | exact @GlobalTheory.SkewLocDual.exists_smul_mem_of_integral | exact GlobalTheory.SkewLocDual.exists_smul_mem_of_integral | (intros; apply GlobalTheory.SkewLocDual.exists_smul_mem_of_integral <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.schwartzBruhat_mem_span_coordinateBox_indicators : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (φ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → ∃ N₀ : ℕ, ∀ N ≥ N₀, φ ∈ Submodule.span ℂ (Set.range fun c : κ → Fv F v => Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - c i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) := by
  first | exact @GlobalTheory.BoxDecomp.mem_span_boxes | exact GlobalTheory.BoxDecomp.mem_span_boxes | (intros; apply GlobalTheory.BoxDecomp.mem_span_boxes <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.splitPlace_tensorLattice_component_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)),
    IsSplitBasis t X.L b → IsSplitBasis t W.L c → ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.LatInt.latAtV_comp_integral | exact GlobalTheory.LatInt.latAtV_comp_integral | (intros; apply GlobalTheory.LatInt.latAtV_comp_integral <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.exists_adelicRep_extending_archimedeanSchwartzRep : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (G : Type) [Group G]
    (ρ : G →* (SInf F κ →L[ℂ] SInf F κ)),
    ∃ ω₀ : G →* Module.End ℂ ((κ → AF F) → ℂ), ∀ (g : G) (f : SInf F κ) (h : (κ → Af F) → ℂ),
      ω₀ g (pureA F f h) = pureA F (ρ g f) h := by
  first | exact @GlobalTheory.SliceExt.exists_rep_pure | exact GlobalTheory.SliceExt.exists_rep_pure | (intros; apply GlobalTheory.SliceExt.exists_rep_pure <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem _root_.GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piInf τ (cA σ z) = star (piInf τ z) := by
  first | exact @GlobalTheory.RealPlaceConj.piInf_cA_eq_star | exact GlobalTheory.RealPlaceConj.piInf_cA_eq_star | (intros; apply GlobalTheory.RealPlaceConj.piInf_cA_eq_star <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → ∀ f : SInf F κ,
      ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h := by
  first | exact @GlobalTheory.ArchHeisPure.rho_pureA | exact GlobalTheory.ArchHeisPure.rho_pureA | (intros; apply GlobalTheory.ArchHeisPure.rho_pureA <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (φ φ' : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), φ ≠ 0 → φ' ∈ SB (κ → Fv F v) →
    Rest (evFin F v) φ r → Rest (evFin F v) φ' r := by
  first | exact @GlobalTheory.RestCofactor.rest_of_rest | exact GlobalTheory.RestCofactor.rest_of_rest | (intros; apply GlobalTheory.RestCofactor.rest_of_rest <;> assumption)
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

theorem _root_.GlobalTheory.T.exists_cartanInvolution_hermitianSignature : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  first | exact @GlobalTheory.PlaneSkew.CartanInv.exists_isCartan | exact GlobalTheory.PlaneSkew.CartanInv.exists_isCartan | (intros; apply GlobalTheory.PlaneSkew.CartanInv.exists_isCartan <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HypPairLat

theorem form_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (z w : Fin n → E) : form σ J (c • z) w = c * form σ J z w := by
  simp [form, smul_dotProduct]

theorem form_smul_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (z w : Fin n → E) : form σ J z (c • w) = σ c * form σ J z w := by
  have : (fun i => σ ((c • w) i)) = σ c • fun i => σ (w i) := by ext i; simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_conj {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (z w : Fin n → E) :
    σ (form σ J z w) = form σ J w z := by

  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem isIntegral_sigma {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {e : E}
    (h : IsIntegral ℤ e) : IsIntegral ℤ (σ e) :=
  h.map (σ.toRingHom.toIntAlgHom)

theorem exists_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), Y.IsHerm σ B r s →
    ∀ x : Fin n → E, x ≠ 0 → form σ Y.J x x = 0 →
    ∃ x' y : Fin n → E, form σ Y.J x' x' = 0 ∧ form σ Y.J y y = 0 ∧ form σ Y.J x' y = 1 ∧
      (∀ z ∈ Y.L, form σ Y.J z y • x' ∈ Y.L ∧ form σ Y.J z x' • y ∈ Y.L) ∧
      ∀ v : B.P, ((∀ c : E, c • x' ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • x' ∈ Y.L ∧ Valued.v (B.τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ Y.L ∧ Valued.v (B.τ v c) = 1) := by
  intro F E _ _ _ _ _ σ B hB n Y r s hY x hx0 hxx
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by haveI := hB.unram; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm hfu
  have hfg : Y.L.FG := hY.lat.fg
  obtain ⟨z0, hz0L, hz0⟩ := GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing F E σ hσ n Y.J Y.L hfg hY.herm hY.dual x hx0
  let f : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => form σ Y.J z x
      map_add' := fun a b => by simp [form, add_dotProduct]
      map_smul' := fun c a => by
        show form σ Y.J ((c : E) • a) x = (c : E) * form σ Y.J a x
        exact form_smul_left σ Y.J (c : E) a x }
  have hf : ∀ z, f z = form σ Y.J z x := fun z => rfl
  let I₀ : Submodule (𝓞 E) E := Y.L.map f
  have hI₀fg : I₀.FG := hfg.map f
  have hI₀ne : I₀ ≠ ⊥ := by
    intro h
    have : f z0 ∈ I₀ := Submodule.mem_map_of_mem hz0L
    rw [h, Submodule.mem_bot] at this
    exact hz0 this
  have hT4 := fun (v : B.P) (b : Bool) => GlobalTheory.T.splitEmbedding_integral_and_maximalIdeal F E v.1 (if b then (B.τ v).comp σ else B.τ v)
  choose hle Q hQmax hQ using hT4
  obtain ⟨s, hs0, hsI, hsQ⟩ := GlobalTheory.T.exists_scale_fractionalIdeal_integral_avoid_maximals E I₀ hI₀fg hI₀ne (B.P × Bool) (fun p => Q p.1 p.2) (fun p => hQmax _ _)
  set x' : Fin n → E := σ s • x with hx'def
  have hfx' : ∀ z, form σ Y.J z x' = s * form σ Y.J z x := fun z => by
    rw [hx'def, form_smul_right, hσ]
  have hx'x' : form σ Y.J x' x' = 0 := by
    rw [hfx', hx'def, form_smul_left, hxx, mul_zero, mul_zero]
  obtain ⟨y₀, hy₀1, hy₀L⟩ := GlobalTheory.T.exists_section_hermitianLinearForm_fg_module F E σ n Y.J Y.L hfg x' ⟨z0, hz0L, by rw [hfx']; exact mul_ne_zero hs0 hz0⟩
  obtain ⟨y, hyy, hx'y, hL⟩ := GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice F E σ hσ n Y.J Y.L hY.herm hY.dual θ hθ x' y₀ hx'x' hy₀1 hy₀L
  have hint : ∀ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') := fun z hz => by
    rw [hfx']; exact hsI _ (Submodule.mem_map_of_mem hz)
  have hx'L : x' ∈ Y.L := (hY.dual x').2 fun w hw => by
    rw [← form_conj σ hσ Y.J hY.herm]; exact isIntegral_sigma σ (hint w hw)
  have hyx' : form σ Y.J y x' = 1 := by
    rw [← form_conj σ hσ Y.J hY.herm, hx'y, map_one]

  have hval : ∀ (v : B.P) (b : Bool) (e : E), IsIntegral ℤ e →
      Valued.v ((if b then (B.τ v).comp σ else B.τ v) e) ≤ 1 := fun v b e he =>
    hle v b ⟨e, he⟩
  have hwit : ∀ (v : B.P) (b : Bool), ∃ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') ∧
      Valued.v ((if b then (B.τ v).comp σ else B.τ v) (form σ Y.J z x')) = 1 := by
    intro v b
    obtain ⟨a, ha, o, ho, hoQ⟩ := hsQ (v, b)
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 ha
    refine ⟨z, hz, hint z hz, ?_⟩
    have h1 := hle v b o
    have h2 : ¬ Valued.v ((if b then (B.τ v).comp σ else B.τ v) (o : E)) < 1 := fun h => hoQ ((hQ v b o).2 h)
    rw [ho, hf, ← hfx'] at h1 h2
    exact le_antisymm h1 (not_lt.1 h2)
  refine ⟨x', y, hx'x', hyy, hx'y, hL, fun v => ⟨⟨fun c hc => ?_, 1, by rw [one_smul]; exact hx'L, by simp⟩,
    ⟨fun c hc => ?_, ?_⟩⟩⟩
  · obtain ⟨z, hz, -, hz1⟩ := hwit v true
    have hi : IsIntegral ℤ (form σ Y.J (c • x') z) := (hY.dual _).1 hc z hz
    rw [form_smul_left, ← form_conj σ hσ Y.J hY.herm z x'] at hi
    have := hval v false _ hi
    simp only [Bool.false_eq_true, ↓reduceIte, map_mul] at this
    simp only [↓reduceIte, AlgHom.comp_apply] at hz1
    rw [hz1, mul_one] at this
    exact this
  · have hi := hint _ hc
    rw [form_smul_left, hyx', mul_one] at hi
    simpa using hval v false c hi
  · obtain ⟨z, hz, -, hz1⟩ := hwit v false
    exact ⟨form σ Y.J z x', (hL z hz).2, by simpa using hz1⟩

end GlobalTheory.HypPairLat
end
