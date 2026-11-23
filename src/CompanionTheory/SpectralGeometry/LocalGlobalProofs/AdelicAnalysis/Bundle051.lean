module

import Development.WeilBound.CoreStatements.ThetaDilations.EulerMove
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle015
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import GroundTheory.GlobalFields.Bundle001
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle047
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle034
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle048
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.EulerMove

theorem borel_ainf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := by
  obtain ⟨⟨-, scA, -⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have scA' : SecondCountableTopology (Ainf F × Af F) := scA
  haveI : SecondCountableTopology (Ainf F) :=
    (isEmbedding_prodMkLeft (0 : Af F)).secondCountableTopology
  haveI : T2Space (Ainf F) := GlobalTheory.CompanionTheory.AdeleTop.t2Space_infiniteAdeleRing_of_numberField_field F
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)).2.2.2.2.2.2.2.1 n M

theorem borel_af (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lcA
  haveI := scA
  haveI := t2A
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.2.2.2.2.1 n M

theorem borel_fv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.2.1 n M

theorem euler_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → IsEulerProd b I 1 minf m → IsEulerProd b (I.map e) 1 minf' m' := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.euler_move <;> assumption

end GlobalTheory.CompanionTheory.SW.EulerMove
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.StdChar

variable (F : Type) [Field F] [NumberField F]

def fieldChar (b : F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F b : ℚ) : ℂ))

lemma fieldChar_add (a b : F) : fieldChar F (a + b) = fieldChar F a * fieldChar F b := by
  simp only [fieldChar, map_add (f := _), Rat.cast_add, mul_add, Complex.exp_add]

lemma fieldChar_zero : fieldChar F 0 = 1 := by simp [fieldChar]

lemma norm_fieldChar (b : F) : ‖fieldChar F b‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F b : ℚ) : ℂ) =
      ((-(2 * Real.pi * (Algebra.trace ℚ F b : ℚ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fieldChar, this, Complex.norm_exp_ofReal_mul_I]

lemma trace_integer (r : 𝓞 F) : ∃ n : ℤ, Algebra.trace ℚ F (r : F) = n := by
  have h : IsIntegral ℤ (Algebra.trace ℚ F (r : F)) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe r)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by rw [← hn, eq_intCast]⟩

lemma fieldChar_eq_one_iff (b : F) :
    fieldChar F b = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F b = n := by
  rw [fieldChar, Complex.exp_eq_one_iff]
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have h3 : -((Algebra.trace ℚ F b : ℚ) : ℂ) = (n : ℂ) :=
      mul_right_cancel₀ h2 (by rw [← hn]; ring)
    have h4 : ((Algebra.trace ℚ F b : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
      rw [Int.cast_neg, ← h3]
      ring
    exact_mod_cast h4
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [hn]
    push_cast
    ring

lemma zero_mem_Oh : (0 : A F) ∈ Oh F := by
  intro v
  exact (HeightOneSpectrum.adicCompletionIntegers F v).zero_mem

variable {F} in
lemma add_mem_Oh {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x + y ∈ Oh F := by
  intro v
  exact add_mem (hx v) (hy v)

variable {F} in
lemma sub_mem_Oh {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x - y ∈ Oh F := by
  intro v
  exact sub_mem (hx v) (hy v)

lemma exists_rep (x : A F) : ∃ b : F, x - algebraMap F (A F) b ∈ Oh F := by
  obtain ⟨-, -, -, -, hOpen, hDense, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hW : IsOpen {y : A F | x - y ∈ Oh F} := hOpen.preimage (continuous_const.sub continuous_id)
  obtain ⟨b, hb⟩ := hDense.exists_mem_open hW ⟨x, by simpa using zero_mem_Oh F⟩
  exact ⟨b, hb⟩

def charFun (x : A F) : ℂ := fieldChar F (Classical.choose (exists_rep F x))

lemma charFun_eq (x : A F) (b : F) (h : x - algebraMap F (A F) b ∈ Oh F) :
    charFun F x = fieldChar F b := by
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hc := Classical.choose_spec (exists_rep F x)
  set c := Classical.choose (exists_rep F x) with hcdef
  have hbc : algebraMap F (A F) (b - c) ∈ Oh F := by
    have := sub_mem_Oh hc h
    convert this using 1
    rw [map_sub]
    abel
  obtain ⟨r, hr⟩ := (hint (b - c)).1 hbc
  have h1 : fieldChar F (b - c) = 1 := by
    rw [← hr]
    exact (fieldChar_eq_one_iff F _).2 (trace_integer F r)
  have hb : b = (b - c) + c := by ring
  rw [show charFun F x = fieldChar F c from rfl, hb, fieldChar_add, h1, one_mul]

def stdChar : AddChar (A F) ℂ where
  toFun := charFun F
  map_zero_eq_one' := by
    rw [charFun_eq F 0 0 (by simpa using zero_mem_Oh F), fieldChar_zero]
  map_add_eq_mul' x y := by
    obtain ⟨a, ha⟩ := exists_rep F x
    obtain ⟨b, hb⟩ := exists_rep F y
    have h : x + y - algebraMap F (A F) (a + b) ∈ Oh F := by
      have := add_mem_Oh ha hb
      rw [map_add (f := _)]
      convert this using 1
      ring
    rw [charFun_eq F _ _ h, charFun_eq F _ _ ha, charFun_eq F _ _ hb, fieldChar_add]

lemma stdChar_apply (x : A F) : stdChar F x = charFun F x := rfl

lemma continuous_stdChar : Continuous (stdChar F) := by
  obtain ⟨-, -, -, -, hOpen, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨b, hb⟩ := exists_rep F x
  have hW : IsOpen {y : A F | y - x ∈ Oh F} := hOpen.preimage (continuous_id.sub continuous_const)
  have hxW : x ∈ {y : A F | y - x ∈ Oh F} := by simpa using zero_mem_Oh F
  have hev : ∀ᶠ y in 𝓝 x, stdChar F x = stdChar F y := by
    filter_upwards [hW.mem_nhds hxW] with y hy
    have hy' : y - algebraMap F (A F) b ∈ Oh F := by
      have := add_mem_Oh hy hb
      convert this using 1
      abel
    rw [stdChar_apply, stdChar_apply, charFun_eq F x b hb, charFun_eq F y b hy']
  exact (continuousAt_const : ContinuousAt (fun _ : A F => stdChar F x) x).congr hev

lemma Oh_subset_of_isClosed {S : Set (A F)} (hS : IsClosed S)
    (h : ∀ r : 𝓞 F, algebraMap F (A F) (r : F) ∈ S) : Oh F ⊆ S := by
  obtain ⟨-, -, -, -, hOpen, hDense, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  intro x hx
  rw [← hS.closure_eq, mem_closure_iff]
  intro o ho hxo
  obtain ⟨b, hb⟩ := hDense.exists_mem_open (ho.inter hOpen) ⟨x, hxo, hx⟩
  obtain ⟨r, hr⟩ := (hint b).1 hb.2
  exact ⟨algebraMap F (A F) b, hb.1, hr ▸ h r⟩

theorem main : ∀ (F : Type) [Field F] [NumberField F], (∃ ψ : AddChar (A F) ℂ, IsStdChar F ψ) ∧ ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → (∀ x, ‖ψ x‖ = 1) ∧ (∀ x ∈ Oh F, ψ x = 1) ∧ ∀ b : F, (∀ x ∈ Oh F, ψ (algebraMap F (A F) b * x) = 1) ↔ ∀ r : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (b * (r : F)) = n := by
  intro F _ _
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hψ1 : ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ x ∈ Oh F, ψ x = 1 := by
    intro ψ hψ x hx
    refine Oh_subset_of_isClosed F (S := {y | ψ y = 1}) (isClosed_eq hψ.1 continuous_const) (fun r => ?_) hx
    show ψ (algebraMap F (A F) (r : F)) = 1
    rw [hψ.2]
    exact (fieldChar_eq_one_iff F _).2 (trace_integer F r)
  refine ⟨⟨stdChar F, continuous_stdChar F, fun b => ?_⟩, fun ψ hψ => ⟨fun x => ?_, hψ1 ψ hψ, fun b => ⟨fun h r => ?_, fun h => ?_⟩⟩⟩
  · rw [stdChar_apply, charFun_eq F _ b (by simp [zero_mem_Oh F])]
    rfl
  · obtain ⟨b, hb⟩ := exists_rep F x
    have hx : x = algebraMap F (A F) b + (x - algebraMap F (A F) b) := by abel
    rw [hx, AddChar.map_add_eq_mul, hψ1 ψ hψ _ hb, mul_one, hψ.2]
    exact norm_fieldChar F b
  · have h1 := h (algebraMap F (A F) (r : F)) ((hint _).2 ⟨r, rfl⟩)
    rw [← map_mul, hψ.2] at h1
    exact (fieldChar_eq_one_iff F (b * (r : F))).1 h1
  · intro x hx
    refine Oh_subset_of_isClosed F (S := {y | ψ (algebraMap F (A F) b * y) = 1})
      (isClosed_eq (hψ.1.comp (continuous_const.mul continuous_id)) continuous_const) (fun r => ?_) hx
    show ψ (algebraMap F (A F) b * algebraMap F (A F) (r : F)) = 1
    rw [← map_mul, hψ.2]
    exact (fieldChar_eq_one_iff F _).2 (h r)

end GlobalTheory.CompanionTheory.SW.Core.StdChar
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.modulus_character_unit_action_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F)), μW.IsAddHaarMeasure → μA.IsAddHaarMeasure → ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧ (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p => (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1, Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) = χ a • μW.prod μA) ∧ ∀ x : ℝ, (χ (τ (Multiplicative.ofAdd x)) : ℝ) = Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * x)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi | exact GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi | (intros; apply GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.WBox

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def cK (R : Type) [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E)
    (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

theorem cK_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (y : R ⊗[F] E) (k : Fin d) :
    cK R' b (Algebra.TensorProduct.map f (AlgHom.id F E) y) k = f (cK R b y k) := by
  induction y with
  | add x y hx hy =>
    simp only [cK] at hx hy ⊢
    simp [map_add (f := _), hx, hy]
  | tmul r e =>
    simp [cK, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R] {d : ℕ} {b : Module.Basis (Fin d) F E}

def eK (hK : IsHomeomorph (cK (F := F) (E := E) R b)) : (R ⊗[F] E) ≃ᵐ (Fin d → R) :=
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  (hK.homeomorph _).toMeasurableEquiv

def eW (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ᵐ (Fin n × Fin M × Fin d → R) where
  toFun X p := eK R hK (X p.1 p.2.1) p.2.2
  invFun Y a i := (eK R hK).symm fun k => Y (a, i, k)
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext p
    simp
  measurable_toFun := Measurable.of_eval fun p =>
    (measurable_pi_apply p.2.2).comp ((eK R hK).measurable.comp
      ((measurable_pi_apply p.2.1).comp (measurable_pi_apply p.1)))
  measurable_invFun := Measurable.of_eval fun a => Measurable.of_eval fun i =>
    (eK R hK).symm.measurable.comp (Measurable.of_eval fun k => measurable_pi_apply (a, i, k))

theorem eW_apply (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (n M : ℕ)
    (X : Fin n → Fin M → R ⊗[F] E) (p : Fin n × Fin M × Fin d) :
    eW R hK n M X p = cK R b (X p.1 p.2.1) p.2.2 := rfl

theorem coordK_eq (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R) :
    coordK R b lam = (Measure.pi fun _ : Fin d => lam).map (eK R hK).symm := by
  rw [MeasurableEquiv.map_symm]
  rfl

theorem sigmaFinite_coordK (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R)
    [SigmaFinite lam] : SigmaFinite (coordK R b lam) := by
  rw [coordK_eq R hK lam]
  exact (eK R hK).symm.measurableEmbedding.sigmaFinite_map

theorem map_coordW (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R) [SigmaFinite lam]
    (n M : ℕ) :
    MeasurePreserving (eW R hK n M) (coordW R b lam n M)
      (Measure.pi fun _ : Fin n × Fin M × Fin d => lam) := by
  haveI := sigmaFinite_coordK R hK lam
  refine ⟨(eW R hK n M).measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (eW R hK n M).measurable (MeasurableSet.univ_pi hs)]
  have hset : (eW R hK n M) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun a => Set.pi Set.univ fun i =>
        (eK R hK) ⁻¹' Set.pi Set.univ fun k => s (a, i, k) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h a i k => h (a, i, k), fun h p => h p.1 p.2.1 p.2.2⟩
  have hK1 : ∀ t : Fin d → Set R, (∀ k, MeasurableSet (t k)) →
      coordK R b lam ((eK R hK) ⁻¹' Set.pi Set.univ t) = ∏ k, lam (t k) := by
    intro t ht
    rw [coordK_eq R hK lam, Measure.map_apply (eK R hK).symm.measurable
      ((eK R hK).measurable (MeasurableSet.univ_pi ht))]
    have : (eK R hK).symm ⁻¹' ((eK R hK) ⁻¹' Set.pi Set.univ t) = Set.pi Set.univ t := by
      ext x
      simp
    rw [this, Measure.pi_pi]
  rw [hset, coordW, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simp_rw [hK1 _ (fun k => hs _)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]

end Gen

theorem coordW_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → coordW (Af F) b lf n M {X | (∀ v ∈ S, projV v X ∈ A v) ∧ ∀ v, v ∉ S → projV v X ∈ latV b v} = ∏ v ∈ S, coordW (Fv F v) b (lam v) n M (A v) := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam lf hlf h1 n M S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hKf : IsHomeomorph (cK (F := F) (E := E) (Af F) b) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Af F)).2.2.2.2.2.2.1 d b
  have hKv : ∀ v, IsHomeomorph (cK (F := F) (E := E) (Fv F v) b) := fun v =>
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.1 d b
  have mf := map_coordW (Af F) hKf lf n M
  have mv := fun v => map_coordW (Fv F v) (hKv v) (lam v) n M
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n × Fin M × Fin d → Fv F v) := fun v =>
    (eW (Fv F v) (hKv v) n M).symm ⁻¹' A v
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => (eW (Fv F v) (hKv v) n M).symm.measurable (hA v)
  have hcomm : ∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → Af F ⊗[F] E)
      (p : Fin n × Fin M × Fin d),
      evalV F v (eW (Af F) hKf n M X p) = eW (Fv F v) (hKv v) n M (projV v X) p := by
    intro v X p
    rw [eW_apply, eW_apply, projV, cK_map]
  have hset : {X : Fin n → Fin M → Af F ⊗[F] E | (∀ v ∈ S, projV v X ∈ A v) ∧
      ∀ v, v ∉ S → projV v X ∈ latV b v} =
      (eW (Af F) hKf n M) ⁻¹' {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A' v) ∧
        ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hcomm]
    refine and_congr (forall₂_congr fun v _ => ?_) (forall₂_congr fun v _ => ?_)
    · simp [A']
    · exact ⟨fun h p => h p.1 p.2.1 p.2.2, fun h a i k => h (a, i, k)⟩
  rw [hset, mf.measure_preimage_equiv,
    GlobalTheory.CompanionTheory.SW.AfBox.pi_box F lam hlam lf hlf h1 (Fin n × Fin M × Fin d) S A' hA']
  exact Finset.prod_congr rfl fun v _ => (mv v).symm.measure_preimage_equiv (A v)

end GlobalTheory.CompanionTheory.SW.WBox
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramExist

theorem exists_gramFib : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ m, IsGramFib R σ J n μ ν m := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ ν hμ hν
  have hR' := hR
  obtain ⟨htr, hlc, hsc, ht2, -, -, -, -⟩ := hR'
  obtain ⟨hKtr, hKlc, hKsc, hKt2, -, -, -, hKb, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  have hKu := GlobalTheory.T.units_open_embedding_local_tensor F E σ hCM R hR
  obtain ⟨hXlc, hXsc, hXt2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM R n
  obtain ⟨g, hg, hgf⟩ := hlift M J hJ
  haveI := hKb n M
  have hinj : Function.Injective (Subtype.val : HermR R σ n → Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Subtype.val_injective
  have hBo : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have : {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} =
        (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
          Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage hc
  have hpre : ∀ B' : Set (HermR R σ n), gramR R σ J ⁻¹' (Subtype.val '' B') = g ⁻¹' B' := by
    intro B'
    ext X
    simp only [Set.mem_preimage, Set.mem_image, hgf X]
    exact hinj.mem_set_image
  have hglue := GlobalTheory.CompanionTheory.SW.FibreGlue.glue (Fin n → Fin M → R ⊗[F] E) (HermR R σ n)
    (Matrix (Fin n) (Fin n) (R ⊗[F] E)) μ ν (gramR R σ J) g Subtype.val hinj hg hgf
    {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} hBo ?_
  · obtain ⟨fib, hfib⟩ := hglue
    refine ⟨fib, ?_⟩
    have hU : {X | IsUnit (gramR R σ J X).det} =
        g ⁻¹' {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hgf X]
    unfold IsGramFib
    rw [hU]
    exact hfib
  · intro S hS
    obtain ⟨B, hB, hSB, hBu, fib, hfib⟩ :=
      GlobalTheory.T.gram_fiber_measure_disintegration_formula F E σ hCM M J hJ R hR n μ ν hμ hν S hS
    refine ⟨B, hB, hSB, fun S' hS' => hBu S' hS', fib, ?_⟩
    rw [← hpre]
    exact hfib

end GlobalTheory.CompanionTheory.SW.GramExist
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.finite_adele_haar_pi_restricted_product : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (ι : Type) [Fintype ι] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (ι → Fv F v)), (∀ v, MeasurableSet (A v)) → (Measure.pi fun _ : ι => lf) {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} = ∏ v ∈ S, (Measure.pi fun _ : ι => lam v) (A v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.AfBox.pi_box | exact GlobalTheory.CompanionTheory.SW.AfBox.pi_box | (intros; apply GlobalTheory.CompanionTheory.SW.AfBox.pi_box <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.local_lattice_compact_open_unit_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV (M := M) (n := n) b v) ∧ IsOpen (latV (M := M) (n := n) b v) ∧ (0 : Fin n → Fin M → Fv F v ⊗[F] E) ∈ latV b v ∧ ∀ lam : Measure (Fv F v), IsStdV v lam → coordW (Fv F v) b lam n M (latV b v) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.latV_compact_open_mass | exact GlobalTheory.CompanionTheory.SW.latV_compact_open_mass | (intros; apply GlobalTheory.CompanionTheory.SW.latV_compact_open_mass <;> assumption)
end
