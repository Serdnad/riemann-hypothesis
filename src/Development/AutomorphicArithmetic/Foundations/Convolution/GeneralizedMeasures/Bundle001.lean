module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
import GroundTheory.AutomorphicForms.Bundle011
import GroundTheory.GlobalFields.Bundle001
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem haar_ex {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {K : Set G} (hc : IsCompact K) (ho : IsOpen K) (h1 : (1 : G) ∈ K) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m K = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K, hc⟩, by
    show (interior K).Nonempty
    rw [ho.interior_eq]; exact ⟨1, h1⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

private theorem haar_uniq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {K : Set G} {m m' : Measure G}
    (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure) (h : m K = 1) (h' : m' K = 1) : m = m' := by
  have e := Measure.isMulLeftInvariant_eq_smul m m'
  have e2 : m K = (Measure.haarScalarFactor m m' • m') K := by rw [← e]
  rw [h, Measure.smul_apply, h', ENNReal.smul_def, smul_eq_mul, mul_one] at e2
  have e3 : Measure.haarScalarFactor m m' = 1 := by exact_mod_cast e2.symm
  rw [e3, one_smul] at e
  exact e

private theorem gl_top (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact ⟨inferInstance, Units.isEmbedding_embedProduct.secondCountableTopology⟩

private theorem gl_int {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (n : ℕ)
    (O : Subring R) (hc : IsCompact (O : Set R)) (ho : IsOpen (O : Set R)) :
    IsCompact {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} ∧
    IsOpen {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} := by
  let S : Subring (Matrix (Fin n) (Fin n) R) := (RingHom.mapMatrix O.subtype).range
  have hS : ∀ A : Matrix (Fin n) (Fin n) R, A ∈ S ↔ ∀ i j, A i j ∈ O := by
    intro A
    constructor
    · rintro ⟨B, rfl⟩ i j
      exact (B i j).2
    · intro h
      exact ⟨Matrix.of fun i j => ⟨A i j, h i j⟩, rfl⟩
  constructor
  · have e : {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} =
        (S.toSubmonoid.units : Set (GL (Fin n) R)) := by
      ext g
      rw [SetLike.mem_coe, Submonoid.mem_units_iff, Subring.mem_toSubmonoid, Subring.mem_toSubmonoid, hS, hS]
      rfl
    rw [e]
    apply Submonoid.units_isCompact
    have : (S.toSubmonoid : Set (Matrix (Fin n) (Fin n) R)) =
        Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (O : Set R) := by
      ext A
      change A ∈ S ↔ ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, A i j ∈ (O : Set R)
      rw [hS]
      simp
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
  · simp only [Set.setOf_and, Set.setOf_forall]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_val.matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage ((Units.continuous_val.matrix_elem i j).comp continuous_inv)

open ValuativeRel in
private theorem unitSet_top {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) :
    IsCompact (unitSet E n v) ∧ IsOpen (unitSet E n v) ∧ (1 : GL (Fin n) (CompletionsOver E v)) ∈ unitSet E n v := by
  let O : Subring (CompletionsOver E v) :=
    ⨅ w : PlacesOver E v, (𝒪[w.1.adicCompletion E]).comap
      (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)
  have hO : (O : Set (CompletionsOver E v)) =
      Set.pi Set.univ fun w : PlacesOver E v => (𝒪[w.1.adicCompletion E] : Set (w.1.adicCompletion E)) := by
    ext x
    simp [O, Subring.mem_iInf]
  have hc : IsCompact (O : Set (CompletionsOver E v)) := by
    rw [hO]
    exact isCompact_univ_pi fun w => isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[w.1.adicCompletion E]))
  have ho : IsOpen (O : Set (CompletionsOver E v)) := by
    rw [hO]
    exact isOpen_set_pi Set.finite_univ fun w _ => Valuation.isOpen_integer
  have e : unitSet E n v = {g : GL (Fin n) (CompletionsOver E v) | (∀ i j, g i j ∈ O) ∧
      ∀ i j, (g⁻¹ : GL (Fin n) (CompletionsOver E v)) i j ∈ O} := by
    ext g
    simp only [unitSet, Set.mem_setOf_eq, GLnLocal.mem_integralGL_iff, ← map_inv, O, Subring.mem_iInf, Subring.mem_comap]
    exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
      fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩
  refine ⟨e ▸ (gl_int n O hc ho).1, e ▸ (gl_int n O hc ho).2, fun w => ?_⟩
  rw [map_one]
  exact one_mem _

theorem UpperTheory.ConvolutionTheory.GM.matchOne :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (v : Pl F),
    (∃ (_ : MeasurableSpace (GL (Fin n) (CompletionsOver E v))) (_ : BorelSpace (GL (Fin n) (CompletionsOver E v)))
      (_ : MeasurableSpace (GL (Fin n) (v.adicCompletion F))) (_ : BorelSpace (GL (Fin n) (v.adicCompletion F)))
      (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))),
      mE.IsHaarMeasure ∧ mF.IsHaarMeasure ∧ mE (unitSet E n v) = 1 ∧ mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1) ∧
    ∀ [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
      [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
      (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))),
      mE.IsHaarMeasure → mF.IsHaarMeasure → mE (unitSet E n v) = 1 → mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1 →
      ∀ (c : ℂ) (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : GL (Fin n) (v.adicCompletion F) → ℂ),
      Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF c φ f → MatchAt σ v c φ f := by
  intro F E _ _ _ _ _ σ n v
  obtain ⟨lE, sE⟩ := gl_top (CompletionsOver E v) n
  obtain ⟨lF, sF⟩ := gl_top (v.adicCompletion F) n
  obtain ⟨hc, ho, h1⟩ := unitSet_top (E := E) n v
  constructor
  · borelize (GL (Fin n) (CompletionsOver E v))
    borelize (GL (Fin n) (v.adicCompletion F))
    obtain ⟨mE, hE, hE1⟩ := haar_ex hc ho h1
    obtain ⟨mF, hF, hF1⟩ := haar_ex (GLnLocal.isCompact_integralGL (v.adicCompletion F) n)
      (GLnLocal.isOpen_integralGL (v.adicCompletion F) n) (one_mem _)
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, mE, mF, hE, hF, hE1, hF1⟩
  · intro aE bE aF bF mE mF hE hF hE1 hF1 c φ f hM aE' bE' aF' bF' mE' mF' hE' hF' hE1' hF1'
    obtain rfl : aE = aE' := bE.measurable_eq.trans bE'.measurable_eq.symm
    obtain rfl : aF = aF' := bF.measurable_eq.trans bF'.measurable_eq.symm
    obtain rfl : mE = mE' := haar_uniq hE hE' hE1 hE1'
    obtain rfl : mF = mF' := haar_uniq hF hF' hF1 hF1'
    exact hM
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical

namespace UpperTheory.ConvolutionTheory.GM

section Defs

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def cf (w : Pl K) (x : AdelicGLn.FiniteAdelicGL K n) : GL (Fin n) (w.adicCompletion K) := finAt w (finEmb K n x)

def Free (w : Pl K) (r : AdelicGLn.FiniteAdelicGL K n → ℂ) : Prop := ∀ y x, r (AdelicGLn.localEmbedding w y * x) = r x

def mono (wd : List (Option (Ix K n))) : MvPolynomial (Option (Ix K n)) ℂ := (wd.map X).prod

def atPl (w : Pl K) (p : MvPolynomial (Fin n) ℂ) : MvPolynomial (Pl K × Fin n) ℂ := rename (fun i => (w, i)) p

variable {F : Type} [Field F] [NumberField F] [Algebra F K]

def Sup {q : Pl F} (w₀ : PlacesOver K q) (ν : Fin n → ℤ) (j : ℕ) (Y : ℝ) (f : normOneGL (K := K) (n := n) → ℂ) : Prop :=
  ∀ g : normOneGL (K := K) (n := n), f g ≠ 0 → heightOff q (g : AdelicGLn.AdelicGL K n) ≤ Y ∧
    finAt w₀.1 (g : AdelicGLn.AdelicGL K n) ∈ iwCoset w₀.1 (fun i => (j : ℤ) * ν i) ∧
    ∀ w : PlacesOver K q, w ≠ w₀ → finAt w.1 (g : AdelicGLn.AdelicGL K n) ∈ GLnLocal.iwahori (w.1.adicCompletion K) n

end Defs

def ConvSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β γ : TI K n),
    (∀ g, conv ν β γ g = ∫ x, β x * γ (x⁻¹ * g) ∂ν) ∧
      ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure], Oinf μ ν (conv ν β γ) = Oinf μ ν β ∘L Oinf μ ν γ

def WordHt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a₀ : TI K n), SmoothT a₀ →
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ (wd : List (Option (Ix K n))) (g : archGroup K n), word ν a₀ wd g ≠ 0 →
      AutomorphicForm.height (infEmb K n g) ≤ Y ^ (wd.length + 1)

def SphEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ w : Pl K, (∀ p : MvPolynomial (Fin n) ℂ, ∃ h, IsSph w p h) ∧
    IsSph w (1 : MvPolynomial (Fin n) ℂ) ((GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1) ∧
    ∀ (p : MvPolynomial (Fin n) ℂ) h, IsSph w p h → IsLocallyConstant h ∧ HasCompactSupport h ∧
      ∀ k ∈ GLnLocal.integralGL (w.adicCompletion K) n, ∀ x, h (k * x) = h x ∧ h (x * k) = h x

def SphAct : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (𝔞 : Amp μ) (ev), 𝔞.IsEv ev → ∀ w ∉ 𝔞.S,
    ∀ (p : MvPolynomial (Fin n) ℂ) h, IsSph w p h → ∀ u ∈ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n),
      sphOp μ w h u = ev (map C (atPl w p)) u

def StepFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) →
    ∀ (h : GL (Fin n) (w.adicCompletion K) → ℂ), HasCompactSupport h → (∀ k ∈ J, ∀ x, h (x * k) = h x) →
    ∀ (r : AdelicGLn.FiniteAdelicGL K n → ℂ), Free w r → ∀ e₀ e₁ : TF K n,
      (∀ x, e₀ x = r x * (J : Set _).indicator 1 (cf w x)) → (∀ x, e₁ x = r x * h (cf w x)) →
      (∀ u, Ofin μ m e₀ u ∈ fixL μ w J) ∧
        Ofin μ m e₁ = (∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ J, h c.out • rhoL μ w c.out) ∘L Ofin μ m e₀

def HeckeFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
    (𝔞 : Amp μ) (ev), 𝔞.IsEv ev → ∀ T : Finset (Pl K), (∀ w ∈ T, w ∉ 𝔞.S) →
    ∀ (p : Pl K → MvPolynomial (Fin n) ℂ) (h : ∀ w : Pl K, GL (Fin n) (w.adicCompletion K) → ℂ), (∀ w ∈ T, IsSph w (p w) (h w)) →
    ∀ (r : AdelicGLn.FiniteAdelicGL K n → ℂ), (∀ w ∈ T, Free w r) → ∀ e₀ e₁ : TF K n,
      (∀ x, e₀ x = r x * ∏ w ∈ T, (GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1 (cf w x)) →
      (∀ x, e₁ x = r x * ∏ w ∈ T, h w (cf w x)) → Ofin μ m e₁ = ev (map C (∏ w ∈ T, atPl w (p w))) ∘L Ofin μ m e₀

def UiwFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
    (w : Pl K) (ν : Fin n → ℤ), Antitone ν → ∀ (j : ℕ) (r : AdelicGLn.FiniteAdelicGL K n → ℂ), Free w r → ∀ e₀ e₁ : TF K n,
      (∀ x, e₀ x = r x * (iwCoset w 0).indicator 1 (cf w x)) →
      (∀ x, e₁ x = r x * (iwCoset w fun i => (j : ℤ) * ν i).indicator 1 (cf w x)) → Ofin μ m e₁ = (Uiw μ w ν ^ j) ∘L Ofin μ m e₀

def RepOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (𝔞 : Amp μ) (ev), 𝔞.IsEv ev → ∀ w₀ ∈ 𝔞.S, ∀ ν : Fin n → ℤ, Antitone ν →
    ∀ T : Finset (Pl K), (∀ w ∈ T, w ∉ 𝔞.S) →
    ∀ (p : Pl K → MvPolynomial (Fin n) ℂ) (h : ∀ w : Pl K, GL (Fin n) (w.adicCompletion K) → ℂ), (∀ w ∈ T, IsSph w (p w) (h w)) →
    ∀ (r : AdelicGLn.FiniteAdelicGL K n → ℂ), Free w₀ r → (∀ w ∈ T, Free w r) →
      (∀ u ∈ 𝔞.U, cf w₀ u ∈ GLnLocal.iwahori (w₀.adicCompletion K) n ∧ ∀ x, r (u * x) = r x) →
    ∀ (j : ℕ) (wd : List (Option (Ix K n))) (e₀ e₁ : TF K n),
      (∀ x, e₀ x = r x * (iwCoset w₀ 0).indicator 1 (cf w₀ x) *
        ∏ w ∈ T, (GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1 (cf w x)) →
      (∀ x, e₁ x = r x * (iwCoset w₀ fun i => (j : ℤ) * ν i).indicator 1 (cf w₀ x) * ∏ w ∈ T, h w (cf w x)) →
      RR μ (tens (word 𝔞.ν 𝔞.a₀ (none :: wd)) e₁) =
        𝔞.A ∘L (ev (C (mono wd) * map C (∏ w ∈ T, atPl w (p w))) ∘L Uiw μ w₀ ν ^ j) ∘L RR μ (tens 𝔞.a₀ e₀)

def AvgE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ), 0 < n → ∀ (S : Finset (Pl F)) (β : TI E n)
    (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ), (∀ v ∈ S, IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v)) →
    (∀ v ∉ S, φ v = (unitSet E n v).indicator 1) →
    ∃ e : TF E n, IsLocallyConstant e ∧ (∀ x, e x = ∏ᶠ v, φ v (mapGL n (atFin v) (finEmb E n x))) ∧
      ∀ x, tens β e x = avg (tensE (onInf β) φ) x

def AvgF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ (S : Finset (Pl F)) (β : TI F n)
    (f : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ), (∀ v ∈ S, IsLocallyConstant (f v) ∧ HasCompactSupport (f v)) →
    (∀ v ∉ S, f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1) →
    ∃ e : TF F n, IsLocallyConstant e ∧ (∀ x, e x = ∏ᶠ v, f v (cf v x)) ∧ ∀ x, tens β e x = avg (tensF (onInf β) f) x

def TensHt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ), 0 < n → ∀ q : Pl F, ∃ c : ℕ, ∀ Yf : ℝ, 1 ≤ Yf → ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (β : TI E n) (e : TF E n) (Y : ℝ), 1 ≤ Y →
    (∀ g, β g ≠ 0 → AutomorphicForm.height (infEmb E n g) ≤ Y) →
    (∀ x, e x ≠ 0 → heightOff q (finEmb E n x) ≤ Yf ∧
      ∀ w : PlacesOver E q, Valued.v (cf w.1 x : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).det = 1) →
    ∀ g : normOneGL (K := E) (n := n), tens β e g ≠ 0 → heightOff q (g : AdelicGLn.AdelicGL E n) ≤ C₁ * Y ^ c ∧ e (finPart E n g) ≠ 0

def HtTot : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (q : Pl F) (w₀ : PlacesOver E q) (ν : Fin n → ℤ), ∃ Q : ℝ, 1 ≤ Q ∧
    ∀ (j : ℕ) (Y : ℝ) (f : normOneGL (K := E) (n := n) → ℂ), Sup w₀ ν j Y f → ∀ g, f g ≠ 0 →
      AutomorphicForm.height (g : AdelicGLn.AdelicGL E n) ≤ Y * Q ^ j

def TwLin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ) (ι : Type) (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n) (Z : ℝ),
    (∀ i ∈ s, ∀ x, Z < qht x → twK θ (f i) x = 0) →
    Rop μ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Rop μ (f i) ∧ (∀ x, Z < qht x → twK θ (∑ i ∈ s, c i • f i) x = 0) ∧
      twInt θ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * twInt θ (f i)

def SideE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ (q : Pl F) (w₀ : PlacesOver E q), Split E q →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (aE : TI E n), AmpFn μ νE aE → ∀ (L : Loc σ n q w₀) (ν : Fin n → ℤ),
      ∃ 𝔢 : Side θ (Module.finrank F E), IsSideE L νE aE ν 𝔢

def SideF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL (K := F) (n := n))) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q)
      (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (aF : TI F n), AmpFn μ νF aF → ∀ (L : Loc σ n q w₀) (ν : Fin n → ℤ),
      ∃ 𝔣 : Side (Twist.id μ) (Module.finrank F E), IsSideF L νF aF ν 𝔣


open Classical in
def LocAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (κ : Finset (Pl E)), (∀ w ∈ κ, Unr E (w.under (𝓞 F))) → ∀ t₀ : Pl E → Multiset ℂ, (∀ w ∈ κ, (t₀ w).card = n ∧ 0 ∉ t₀ w) → ∀ D : ℕ,
    ∃ γ : Pl E → MvPolynomial (Fin n) ℂ, (∀ w ∈ κ, eval (fun i : Fin n => (t₀ w).esymm (i + 1)) (γ w) ≠ 0) ∧
      ∀ p : Pl E → MvPolynomial (Fin n) ℂ, (∀ w ∈ κ, (p w).totalDegree ≤ D) → ∀ v : Pl F, Unr E v →
        ∀ (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ) (f : GL (Fin n) (v.adicCompletion F) → ℂ),
          (∀ w ∈ κ, IsSph w (γ w * p w) (h w)) →
          (∀ w ∉ κ, h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1) →
          IsSph v (∏ w ∈ κ.filter fun w => w.under (𝓞 F) = v, aeval (powE (resDeg F w)) (γ w * p w)) f →
          MatchAt σ v 1 (prodFn fun w : PlacesOver E v => h w.1) f

def TermEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL (K := E) (n := n))) [μE.IsHaarMeasure] (μF : Measure (normOneGL (K := F) (n := n))) [μF.IsHaarMeasure] (θ : Twist μE)
      (q : Pl F) (w₀ : PlacesOver E q) (q₀ : PlacesOver F q), Split E q →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (aE : TI E n) (aF : TI F n)
      (ci : ℝ), 0 < ci → ArchPair σ νE νF aE aF ci →
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ (L : Loc σ n q w₀) (ν : Fin n → ℤ), Good ν →
      ∀ (𝔢 : Side θ (Module.finrank F E)) (𝔣 : Side (Twist.id μF) (Module.finrank F E)), IsSideE L νE aE ν 𝔢 → IsSideF L νF aF ν 𝔣 →
      ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ (κ : Finset (Pl E)), (∀ w ∈ κ, w ∉ 𝔢.S) → ∀ t₀ : Pl E → Multiset ℂ, (∀ w ∈ κ, (t₀ w).card = n ∧ 0 ∉ t₀ w) →
      ∀ D : ℕ, ∃ γ : MvPolynomial (Pl E × Fin n) ℂ, (∀ x ∈ γ.vars, x.1 ∈ κ) ∧ eval (hval t₀) γ ≠ 0 ∧
        ∀ β : Pl E × Fin n →₀ ℕ, (∀ x ∈ β.support, x.1 ∈ κ) → β.degree ≤ D → ∃ Y₁ : ℝ, 1 ≤ Y₁ ∧
          ∀ evE evF, 𝔢.toAmp.IsEv evE → 𝔣.toAmp.IsEv evF → ∀ (j : ℕ) (wd : List (Option (Ix E n))), ∃ (fE : TG E n) (fF : TG F n),
            Rop μE fE = 𝔢.toAmp.A ∘L (evE (map C γ * monomial β (mono wd)) ∘L 𝔢.Uq 0 ^ j) ∘L Rop μE 𝔢.g ∧
            Rop μF fF = 𝔣.toAmp.A ∘L (evF (bcPR F (map C γ * monomial β (mono wd))) ∘L 𝔣.Uq 0 ^ j) ∘L Rop μF 𝔣.g ∧
            Sup w₀ ν j (Y₁ * Y₀ ^ wd.length) fE ∧ Sup q₀ ν j (Y₁ * Y₀ ^ wd.length) fF ∧
            GMatch σ μE μF (κ₀ * ∏ v ∈ L.S, L.c v) fE fF

end UpperTheory.ConvolutionTheory.GM
end
end
