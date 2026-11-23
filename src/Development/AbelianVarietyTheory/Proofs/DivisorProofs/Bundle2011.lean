module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∀ φ φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ → φ₁ ∈ GlobalTheory.WeilM.SB _ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ φ₁ →
      ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts | exact GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts | (intros; apply GlobalTheory.LocalIsom.lintegral_sq_eq_of_acts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat


theorem _root_.GlobalTheory.T.hasDerivAt_thetaTransform_heisenberg_real_line : ∀ {F : Type} [Field F] [NumberField F] {U : Type} [AddCommGroup U] [Module (AF F) U] {B : U → U → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ (u : U), ∀ Φ ∈ schA F κ, ∀ Φ' ∈ schA F κ,
    (∀ x, HasDerivAt (fun t : ℝ => co.rho ψ (realAd F t • u) Φ x) (Φ' x) 0) →
    ∀ w : U, HasDerivAt (fun t : ℝ => thetaSum F (co.rho ψ w (co.rho ψ (realAd F t • u) Φ))) (thetaSum F (co.rho ψ w Φ')) 0 := by
  first | exact @GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho | exact GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho | (intros; apply GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
namespace GlobalTheory.SchrCharPure

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
      schr ψ (0, fun i => algebraMap F (AF F) (b i))
          (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)))) =
        pureA F f' ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ))) := by
  intro F _ _ ψ hψ κ _ a ha b hb f f' hf'
  funext x
  simp only [schr, pureA, add_zero, zero_dotProduct, mul_zero]
  rw [hf']
  by_cases hz : (fun i => (x i).2) ∈ GlobalTheory.EvAdm.scaledInt F κ a
  · rw [Set.indicator_of_mem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]
    set u : AF F := x ⬝ᵥ fun i => algebraMap F (AF F) (b i) with hu
    have hsplit : u = (show AF F from (u.1, 0)) + (show AF F from (0, u.2)) := by
      show u = ((u.1 + 0, 0 + u.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
      rw [add_zero, zero_add]
      rfl
    have hu2 : u.2 = ∑ i, (x i).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i) := by
      have e : u.2 = (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u := rfl
      rw [e, hu, dotProduct]
      exact (map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ => rfl)
    have hu1 : u.1 = ∑ i, (x i).1 * algebraMap F (InfiniteAdeleRing F) (b i) := by
      have e : u.1 = (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u := rfl
      rw [e, hu, dotProduct]
      exact (map_sum (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ => rfl)
    have hfin : ψ (show AF F from (0, u.2)) = 1 := by
      have := GlobalTheory.T.scaled_lattice_character_trivial F ψ hψ κ a ha b hb _ hz
      rw [← hu2] at this
      exact this
    have hAt : At (evI F) (show AF F from (u.1, 0)) := by
      intro w hw
      have h1 : w.1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F w.1 = 0 := hw
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
      show ((w.1 * u.1, w.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
      rw [h1, zero_mul, mul_zero]
    have hinf := hψ.2.2 _ hAt
    have hev : evI F (show AF F from (u.1, 0)) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * mixedEmbedding F (b i) := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = _

      rw [hu1, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_mul]
    rw [hsplit, AddChar.map_add_eq_mul, hfin, hinf, hev]
    ring
  · rw [Set.indicator_of_notMem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]
    simp

end GlobalTheory.SchrCharPure
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchrSpan

theorem schr_comp_loc {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

theorem mem_span_schr_of_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) [Invertible (2 : Fv F v)] (χ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ], (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, χ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) →
    ∀ (f₀ : (κ → Fv F v) → ℂ), f₀ ∈ SB (κ → Fv F v) → f₀ ≠ 0 → ∀ (φ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) →
      φ ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr χ w f₀) := by
  intro F _ _ v _ χ κ _ hcond f₀ hf₀ hne φ hφ
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have htriv : ∀ y ∈ v.adicCompletionIntegers F, χ y = 1 := by
    intro y hy
    have := (hcond 1).2 (one_mem _) y hy
    simpa using this
  have hc : Continuous χ := by
    have : IsLocallyConstant χ := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      rw [← map_add_left_nhds_zero, Filter.eventually_map]
      filter_upwards [hO.mem_nhds (zero_mem _)] with s hs
      rw [AddChar.map_add_eq_mul, htriv s hs, mul_one]
    exact this.continuous
  have h1 : χ ≠ 1 := by
    intro h
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have hπ0 : π ≠ 0 := by
      intro h0; rw [h0, map_zero] at hπ; exact WithZero.zero_ne_coe hπ
    have hmem : ((π⁻¹ : F) : Fv F v) ∈ v.adicCompletionIntegers F :=
      (hcond _).1 (fun y _ => by rw [h]; rfl)
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ] at hmem
    exact absurd hmem (by decide)
  set N := Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr χ w f₀) with hNdef
  have hN : N ≤ GlobalTheory.WeilM.SB (κ → Fv F v) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show schr χ w f₀ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)
    convert GlobalTheory.SchrSBFin.schr_mem_SB v χ hc w f₀ hf₀ using 2
    all_goals exact Subsingleton.elim _ _
  have hS : ∀ w, ∀ g ∈ N, schr χ w g ∈ N := by
    intro w g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w', rfl⟩ := hx
      rw [schr_comp_loc]
      exact N.smul_mem _ (Submodule.subset_span ⟨w + w', rfl⟩)
    | zero =>
      have : schr χ w (0 : (κ → Fv F v) → ℂ) = 0 := by funext x; simp [schr]
      rw [this]; exact N.zero_mem
    | add a b _ _ ha hb =>
      have : schr χ w (a + b) = schr χ w a + schr χ w b := by funext x; simp [schr, mul_add]
      rw [this]; exact N.add_mem ha hb
    | smul c a _ ha =>
      have : schr χ w (c • a) = c • schr χ w a := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact N.smul_mem c ha
  have h0 : f₀ ∈ N := by
    have : schr χ (0 : (κ → Fv F v) × (κ → Fv F v)) f₀ = f₀ := by funext x; simp [schr]
    rw [← this]; exact Submodule.subset_span ⟨0, rfl⟩
  have hall := GlobalTheory.SchrIrred.schr_irreducible v χ hc h1 N hN
    (fun w g hg => by convert hS w g hg using 2; exact Subsingleton.elim _ _) f₀ h0 hne
  rw [hall]; exact hφ

end GlobalTheory.SchrSpan
end
end

section

noncomputable section

namespace GlobalTheory.ThetaFacInf.Fib

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F]

theorem rest_finPart {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  have hz0 : ∀ v i, evFin F v (z i) = 0 := fun v i => by
    have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
    have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
    rw [one_mul] at h2
    rw [evFin, AlgHom.comp_apply]
    convert map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
    exact h2
  simp only [Pi.add_apply, map_add (f := _), hz0, add_zero]

theorem hasDerivAt_pure {κ : Type} [Fintype κ] {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h : ActsD (evI F) T f f₁) :
    ∀ x, HasDerivAt (fun t => T t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ x) 0 :=
  h _ (rest_finPart f φ hSB hstd)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

end GlobalTheory.ThetaFacInf.Fib

end

namespace GlobalTheory.ThetaFacInf.Fib

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

end GlobalTheory.ThetaFacInf.Fib
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.VacThetaIndep

theorem vacuum_character_theta_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ' : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) :=
  GlobalTheory.VacThetaInd.psi_half_symp_theta_indep

end GlobalTheory.VacThetaIndep

end
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

theorem _root_.GlobalTheory.T.hasHermitianSignature_hyperbolicPlane_orthComplement : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (r s : ℕ), HasSig M r s → 1 ≤ r → 1 ≤ s →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y ≠ 0 →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  first | exact @GlobalTheory.PlaneSkewSig.hasSig_complement | exact GlobalTheory.PlaneSkewSig.hasSig_complement | (intros; apply GlobalTheory.PlaneSkewSig.hasSig_complement <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.local_fourier_inversion_up_to_constant : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (χ : AddChar (Fv F v) ℂ), Continuous χ → (∀ t, ‖χ t‖ = 1) →
    χ ≠ 1 → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure], ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → Fv F v), ∀ a : κ → Fv F v,
      ∫ y, (∫ x, φ x * χ (x ⬝ᵥ y) ∂μ) * χ (y ⬝ᵥ a) ∂μ = d * φ (-a) := by
  first | exact @GlobalTheory.FourierLocInv.fourier_inversion | exact GlobalTheory.FourierLocInv.fourier_inversion | (intros; apply GlobalTheory.FourierLocInv.fourier_inversion <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.standard_character_almost_unramified : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) ∧ ∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1 := by
  first | exact @GlobalTheory.PsiStdCond.psi_std_conductor | exact GlobalTheory.PsiStdCond.psi_std_conductor | (intros; apply GlobalTheory.PsiStdCond.psi_std_conductor <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.exists_prime_to_place_denominator_unramified_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (v : Pl (F := F)) (e : E),
    (∀ o : 𝓞 E, algebraMap F (Fv F v) (Algebra.trace F E ((o : E) * e)) ∈ v.adicCompletionIntegers F) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * e) := by
  first | exact @GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral | exact GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral | (intros; apply GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section


theorem _root_.GlobalTheory.T.local_lattice_hermitian_skew : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = J i j) → (∀ i j, σ (K j i) = -K i j) →
    ∀ (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x →
    GlobalTheory.AdelicU.evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) =
      ∑ i, ∑ j, (x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j * (-(J.map t * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j -
        ∑ i, ∑ j, (-(J.map t * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j * (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j := by
  first | exact @GlobalTheory.SplitTraceForm.splitTrace | exact GlobalTheory.SplitTraceForm.splitTrace | (intros; apply GlobalTheory.SplitTraceForm.splitTrace <;> assumption)
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.archimedean_fourier_inversion_constant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure],
    ∃ d : ℂ, d ≠ 0 ∧ ∀ (f : SInf F κ) (a : κ → mixedEmbedding.mixedSpace F),
      ∫ y, (∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) ∂μ) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ a) : ℝ)) ∂μ =
      d * f (-a) := by
  first | exact @GlobalTheory.ArchFourier.fourier_twice_sInf | exact GlobalTheory.ArchFourier.fourier_twice_sInf | (intros; apply GlobalTheory.ArchFourier.fourier_twice_sInf <;> assumption)
end
