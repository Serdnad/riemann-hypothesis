module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceLinesRelatedAndVanishOffPlace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle351
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseTripleSpacesOfSeesaw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankAlgebraicDataSchrodingerModelLeAleph0
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.GlobalFields.Adele.Bundle002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.realPlaceLines_related_and_vanish_off_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      ∃ w, (∀ w', w' ≠ w →
          (cS.symm (lineAt θ τ z 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w')) = 0 ∧
          (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w')) = 0) ∧
        (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
          Complex.I • (Vs.θ w * (cS.symm (lineAt θ τ z 1)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ) := by
  first | exact @GlobalTheory.PlaceLines.lines_at_place | exact GlobalTheory.PlaceLines.lines_at_place | (intros; apply GlobalTheory.PlaceLines.lines_at_place <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.StdCharSep

variable {F : Type} [Field F] [NumberField F]

theorem trace_int_of_psi {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F)
    (h : ψ (pairA F 0 (algebraMap F (Af F) x)) = 1) : ∃ z : ℤ, Algebra.trace ℚ F x = z := by
  rw [GlobalTheory.PsiNontriv.isStd_fin_rat hψ, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
    rw [mul_comm (2 * Real.pi * Complex.I : ℂ)] at hn
    push_cast
    exact mul_right_cancel₀ hne hn
  exact_mod_cast h2

theorem psi_of_trace_int {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F)
    (h : ∃ z : ℤ, Algebra.trace ℚ F x = z) : ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 := by
  obtain ⟨z, hz⟩ := h
  rw [GlobalTheory.PsiNontriv.isStd_fin_rat hψ, hz, Complex.exp_eq_one_iff]
  exact ⟨z, by push_cast; ring⟩

theorem psi_int_mul {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (s : F)
    (hs : ∀ a : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F ((a : F) * s) = z)
    (w : Af F) (hw : ∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) :
    ψ (pairA F 0 (w * algebraMap F (Af F) s)) = 1 :=
  GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 s (fun a => psi_of_trace_int hψ _ (hs a)) w hw

theorem mem_of_dual (k : F) (h : ∀ s : F, (∀ a : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F ((a : F) * s) = z) →
    ∃ z : ℤ, Algebra.trace ℚ F (k * s) = z) : ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = k := by
  have h1 : k ∈ FractionalIdeal.dual ℤ ℚ
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) := by
    rw [FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero ℤ ℚ (GlobalTheory.AdLat.one_ne_zero_fracIdeal F))]
    intro s hs
    rw [FractionalIdeal.mem_dual (GlobalTheory.AdLat.one_ne_zero_fracIdeal F)] at hs
    obtain ⟨z, hz⟩ := h s (fun a => by
      obtain ⟨y, hy⟩ := hs (a : F) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      refine ⟨y, ?_⟩
      rw [Algebra.traceForm_apply] at hy
      rw [mul_comm, ← hy]
      simp)
    exact ⟨z, by rw [Algebra.traceForm_apply, hz]; simp⟩
  rw [FractionalIdeal.dual_dual] at h1
  exact (FractionalIdeal.mem_one_iff _).1 h1

theorem exists_sep : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ b : FiniteAdeleRing (𝓞 F) F, ¬ (∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F) →
    ∃ s : F, ψ (((0 : InfiniteAdeleRing F), b * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) ≠ 1 ∧
      ∀ w : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) →
        ψ (((0 : InfiniteAdeleRing F), w * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) = 1 := by
  intro F _ _ ψ hψ b hb
  by_contra H
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) b
  have hbk : b = algebraMap F (Af F) k + (b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) := by abel
  obtain ⟨o, ho⟩ := mem_of_dual k (fun s hs => by
    have hb1 : ψ (pairA F 0 (b * algebraMap F (Af F) s)) = 1 := by
      by_contra hne
      exact H ⟨s, hne, fun w hw => psi_int_mul hψ s hs w hw⟩
    have hc1 := psi_int_mul hψ s hs _ hk
    have e : pairA F 0 (b * algebraMap F (Af F) s) = pairA F 0 (algebraMap F (Af F) (k * s)) +
        pairA F 0 ((b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) * algebraMap F (Af F) s) := by
      refine Prod.ext (add_zero 0).symm ?_
      show b * algebraMap F (Af F) s = algebraMap F (Af F) (k * s) +
        (b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) * algebraMap F (Af F) s
      rw [map_mul]
      ring
    rw [e, AddChar.map_add_eq_mul, hc1, mul_one] at hb1
    exact trace_int_of_psi hψ _ hb1)
  apply hb
  intro v
  rw [hbk]
  refine add_mem ?_ (hk v)
  show ((k : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  rw [← ho]
  exact GroundTheory.Global.coe_algebraMap_mem_adicCompletionIntegers v o

end GlobalTheory.StdCharSep
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open MeasureTheory
open scoped ENNReal

theorem integral_norm_sq_eq_pair_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
        ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ _ T hA μ hμ t f
  obtain ⟨g, hg, hg0⟩ : ∃ g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ,
      g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ g 0 ≠ 0 := by
    refine ⟨_, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _, ?_⟩
    have h0 : (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F (Fin n × Fin d) :=
      fun i _ v => zero_mem (v.adicCompletionIntegers F)
    rw [Set.indicator_of_mem h0]
    exact one_ne_zero
  obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := exists_haar F _ μ g hg hg0
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => g fun i => (x i).2
  have hS : tens (evI F) f r ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := by
    intro x z hz
    refine congrArg g (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    have h := hz (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F) (by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _)
    have h2 : (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) * ((z i).1, (z i).2)).2 =
        (0 : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 := congrArg Prod.snd (congrFun h i)
    have hz0 : (z i).2 = 0 := by simpa using h2
    rw [hz0, add_zero]
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW).unit μA hμA (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) hS
  have hAct : om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) = tens (evI F) (T t f) r := hA t f r ⟨hr, hS⟩
  change ∫⁻ x, ‖om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) x‖ₑ ^ 2 ∂μA = _ at hU
  rw [hAct] at hU
  have h1 := ((hc (T t f)).symm.trans hU).trans (hc f)
  haveI := opensMeasurable F (Fin n × Fin d)
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, (ENNReal.mul_right_inj hc0 hct).1 h1]

end GlobalTheory.ArchimedeanUnitaryL2

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open MeasureTheory
open scoped ENNReal

theorem integral_norm_sq_eq_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ (μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
        ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ _ T hA μ hμ t f
  obtain ⟨g, hg, hg0⟩ : ∃ g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ,
      g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ g 0 ≠ 0 := by
    refine ⟨_, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _, ?_⟩
    have h0 : (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F (Fin n × Fin d) :=
      fun i _ v => zero_mem (v.adicCompletionIntegers F)
    rw [Set.indicator_of_mem h0]
    exact one_ne_zero
  obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := exists_haar F _ μ g hg hg0
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => g fun i => (x i).2
  have hS : tens (evI F) f r ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := by
    intro x z hz
    refine congrArg g (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [snd_eq_zero hz i, add_zero]
  have hU := hW.1.1.unit μA hμA (γ (Multiplicative.ofAdd t)) (tens (evI F) f r) hS
  have hAct : om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) = tens (evI F) (T t f) r := hA t f r ⟨hr, hS⟩
  change ∫⁻ x, ‖om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) x‖ₑ ^ 2 ∂μA = _ at hU
  rw [hAct] at hU
  have h1 := ((hc (T t f)).symm.trans hU).trans (hc f)
  haveI := opensMeasurable F (Fin n × Fin d)
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, (ENNReal.mul_right_inj hc0 hct).1 h1]

end GlobalTheory.ArchimedeanUnitaryL2

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.exists_placewise_triple_spaces_of_seesaw : ∀ (D : D7) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ p q : ℕ, (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) (W.rank - p) p ∧ Formalism.UG.HasSignature (gramAt D W₁ τ) (W₁.rank - q) q ∧
      Formalism.UG.HasSignature (gramAt D X τ) (X.rank - (p + q)) (p + q)) →
    ∀ (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    (∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) →
    ∃ (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (V' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank)
      (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E (W.rank + W₁.rank)),
      V.J = (1 : D.host.E) • W.gram ∧ V'.J = (-1 : D.host.E) • W₁.gram ∧ Ws.J = D.host.xi0 • reindex e e X.gramᵀ ∧
      V.IsHerm D.sp.cm.sig Bs (W.rank - p) p ∧ V'.IsHerm D.sp.cm.sig Bs q (W₁.rank - q) ∧
      Ws.IsSkew D.sp.cm.sig Bs (W.rank + W₁.rank - (p + q)) (p + q) ∧
      ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ V.θ w = A.cart τ ∧ V'.θ w = -A₁.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.PlaceSpaces.spaces_of_triple | exact GlobalTheory.PlaceSpaces.spaces_of_triple | (intros; apply GlobalTheory.PlaceSpaces.spaces_of_triple <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.AdelicLatticeIntegral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nsmul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E)
    (x : Fin n → E) : ∃ D : ℕ, D ≠ 0 ∧ D • x ∈ L := by
  exact _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice L hL x

theorem exists_nsmul_map_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E)
    (N : (Fin n → E) →ₗ[E] (Fin n → E)) : ∃ D : ℕ, D ≠ 0 ∧ ∀ y ∈ L, D • N y ∈ L := by
  obtain ⟨s, hs⟩ := hL.fg
  choose! D hD hDm using fun g => exists_nsmul_mem L hL (N g)
  refine ⟨∏ g ∈ s, D g, Finset.prod_ne_zero_iff.mpr fun g _ => hD g, ?_⟩
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem D hg
      rw [hk, mul_comm, mul_smul]; exact nsmul_mem (hDm g) k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact L.add_mem hx hy
  | smul r x _ hx =>
      have : N (r • x) = r • N x := N.map_smul_of_tower r x
      rw [this, smul_comm]; exact L.smul_mem r hx

end GlobalTheory.AdelicLatticeIntegral

namespace GlobalTheory.AdelicLatticeIntegral

theorem exists_finset_smul_mulVec_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E →
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a →
      GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F → ∀ y ∈ L,
      a • (M *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)} := by
  intro F E _ _ _ _ _ n M L hL
  classical
  let bF := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) bF
  let c : Fin n × Fin n × Fin (Module.finrank F E) → AF F := fun j => B.repr (M j.1 j.2.1) j.2.2
  let Nm : Fin n × Fin n × Fin (Module.finrank F E) → (Fin n → E) →ₗ[E] (Fin n → E) := fun j =>
    (LinearMap.single E (fun _ : Fin n => E) j.1) ∘ₗ (bF j.2.2 • LinearMap.proj j.2.1)
  let incV : (Fin n → E) → (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := fun y i =>
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)
  have key : ∀ y, (M *ᵥ incV y) = ∑ j, c j • incV (Nm j y) := by
    intro y
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
    rw [Fintype.sum_prod_type]
    symm
    rw [Finset.sum_eq_single r]
    · rw [Fintype.sum_prod_type]
      symm
      refine Finset.sum_congr rfl fun q _ => ?_
      conv_lhs => rw [← B.sum_repr (M r q)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Nm, incV, B, c, Algebra.TensorProduct.basis_apply, smul_mul_assoc, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    · intro p _ hp
      simp [Nm, incV, Pi.single_apply, Ne.symm hp]
    · simp
  choose D hD0 hDL using fun j => exists_nsmul_map_mem L hL (Nm j)
  let c' : Fin n × Fin n × Fin (Module.finrank F E) → AF F :=
    fun j => c j * algebraMap F (AF F) ((D j : F)⁻¹)
  have hfin : ∀ j, {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) |
      ¬ GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F}.Finite :=
    fun j => Filter.eventually_cofinite.mp (GlobalTheory.AlgCountDim.eventually_evFin_integral (c' j))
  refine ⟨(Set.finite_iUnion hfin).toFinset, ?_⟩
  intro w hw a ha hai y hy
  have hc' : ∀ j, GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F := by
    intro j
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).mpr (Set.mem_iUnion.mpr ⟨j, h⟩))
  have hterm : ∀ j, a • (c j • incV (Nm j y)) = (a * c' j) • incV (D j • Nm j y) := by
    intro j
    have h1 : incV (D j • Nm j y) = D j • incV (Nm j y) := by
      funext i; simp [incV]
    rw [h1, ← Nat.cast_smul_eq_nsmul (AF F), smul_smul, smul_smul]
    congr 1
    have h2 : (D j : F) ≠ 0 := Nat.cast_ne_zero.mpr (hD0 j)
    simp only [c', mul_assoc]
    rw [← map_natCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ h2, map_one, mul_one]
  change a • (M *ᵥ incV y) ∈ _
  rw [key, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  rw [hterm j]
  refine AddSubgroup.subset_closure ⟨a * c' j, ?_, ?_, D j • Nm j y, hDL j y hy, rfl⟩
  · intro u hu
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u a, ha u hu, zero_mul]
  · rw [map_mul]; exact mul_mem hai (hc' j)

end GlobalTheory.AdelicLatticeIntegral
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.PsiDifferent

open GlobalTheory.Idele WithZero
open scoped nonZeroDivisors
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem not_dvd_different_of_psiUnr : ∀ {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ},
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {v : HeightOneSpectrum (𝓞 F)}, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v →
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  intro F _ _ ψ hψ v hU hdvd
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hcnt := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv] at hcnt
  have hne := (Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 hdvd
  set c := FractionalIdeal.count F v (codiff F) with hc
  have hc1 : c ≤ -1 := by omega
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set x : Fv F v := algebraMap F (Fv F v) (π ^ c) with hx
  have hval : Valued.v x = WithZero.exp (-c) := by
    rw [hx, valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul]
    congr 1; ring
  have hmem : GlobalTheory.AdelicU.singleFin v x ∈ adelicIdeal (codiff F) := by
    refine (mem_adelicIdeal_iff codiff_ne_zero).2 fun u => ?_
    by_cases hu : u = v
    · subst hu
      rw [show (GlobalTheory.AdelicU.singleFin u x) u = x from GlobalTheory.AdelicU.evalV_singleFin_self u x, hval]
    · rw [show (GlobalTheory.AdelicU.singleFin v x) u = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne hu x, map_zero]
      exact zero_le'
  rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ)] at hmem
  have hint : x ∈ v.adicCompletionIntegers F := by
    refine (hU x).1 fun y hy => ?_
    have hα : ∀ u, (GlobalTheory.AdelicU.singleFin v y) u ∈ u.adicCompletionIntegers F := by
      intro u
      by_cases hu : u = v
      · subst hu
        rw [show (GlobalTheory.AdelicU.singleFin u y) u = y from GlobalTheory.AdelicU.evalV_singleFin_self u y]
        exact hy
      · rw [show (GlobalTheory.AdelicU.singleFin v y) u = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne hu y]
        exact zero_mem _
    have e : GlobalTheory.AdelicU.singleFin v y * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (x * y) := by
      apply GlobalTheory.AdelicU.af_ext
      intro u
      by_cases hu : u = v
      · subst hu
        rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self,
          GlobalTheory.AdelicU.evalV_singleFin_self, mul_comm]
      · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu,
          GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
    have := hmem _ hα
    rw [e] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval, ← WithZero.exp_zero, WithZero.exp_le_exp] at hint
  omega

end GlobalTheory.PsiDifferent

end
end
