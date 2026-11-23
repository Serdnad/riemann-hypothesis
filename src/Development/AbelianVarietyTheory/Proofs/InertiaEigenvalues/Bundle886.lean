module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle359
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle877
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle874
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle876
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLastStepRealIntertwiner
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle335
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle512
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockByRealComponentsBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle699
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.heckeChar_infinity_eq_coeff_mul_halfNorm_pow : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (χ : Formalism.L2.Host.HChar D.host.E), ChrEq χW χ → ∀ (k : Type) [Field k] (σ : k →+* ℂ), ConjIn D σ → ∀ a : D.host.Eˣ, ∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : D.host.E) : ℚ) : ℝ)| ^ (-(W.rank : ℝ) / 2) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.LevelSeries.inf_eq_mul_normPow | exact GlobalTheory.LevelSeries.inf_eq_mul_normPow | (intros; apply GlobalTheory.LevelSeries.inf_eq_mul_normPow <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.thetaKernel_fockVector_eq_of_finite_point_move : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (z : GA D V), z ∈ GfC V → ∀ (e e₂ : AE D) (M : ℕ) (O : Subring ℂ) (f f' : WO V W → ℂ) (a : ℂ), f ∈ trSp ψ V W ΛV ΛW f₀ e M O → f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ M O → om (z, 1) f' = a • f → ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), a * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z) g (stdF ψ θ V W sW BW f' Q) := by
  first | exact @GlobalTheory.LevelSeries.thetaKO_flip | exact GlobalTheory.LevelSeries.thetaKO_flip | (intros; apply GlobalTheory.LevelSeries.thetaKO_flip <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem trSp_le_of_subhalf : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (e₂ e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)), IsHalfIdem l₂ e₂ → IsIdemSum e' P' → (∀ PP ∈ P', l₂.Mb ≤ PP.asIdeal) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (M : ℕ) (O : Subring ℂ), trSp ψ V W ΛV ΛW f₀ e' M O ≤ trSp ψ V W ΛV ΛW f₀ e₂ M O := by
  intro D H l₂ e₂ e' P' h₂ h' hP ψ V W ΛV ΛW f₀ M O
  obtain ⟨P₂, ⟨⟨es₂, hes₂, rfl⟩, -⟩, hP₂⟩ := h₂
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  have hsub : P' ⊆ P₂ := fun PP h => (hP₂ PP).2 (hP PP h)
  have key := GlobalTheory.PartialIdemSum.sum_mul_sum_of_subset P' P₂ es' es₂ hes' hes₂ hsub
  unfold trSp
  refine Submodule.span_mono ?_
  rintro f ⟨y, hy, hM, rfl⟩
  refine ⟨y, fun i j => ?_, hM, rfl⟩
  rw [← hy i j, ← mul_assoc, mul_comm (∑ P ∈ P₂, es₂ P), key]

end GlobalTheory.LevelSeries

end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.BumpOrbit
open GlobalTheory.RSTheta

section Local
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T2Space K]

theorem continuousAt_rowGL {a : ℕ} (ℓ : Fin a) :
    ContinuousAt (rowGL ℓ : (Fin a → K) → GL (Fin a) K) (Pi.single ℓ 1) := by
  have hO : {y : Fin a → K | y ℓ ≠ 0} ∈ nhds (Pi.single ℓ (1:K)) :=
    (isOpen_ne_fun (continuous_apply ℓ) continuous_const).mem_nhds (by simp)
  have hv : (fun y => rowMat ℓ y) =ᶠ[nhds (Pi.single ℓ (1:K))]
      fun y => ((rowGL ℓ y : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) :=
    Filter.eventually_of_mem hO fun y hy => (val_rowGL (isUnit_iff_ne_zero.2 hy)).symm
  have hc : Continuous fun y : Fin a → K => rowMat ℓ y := continuous_const.matrix_updateRow ℓ continuous_id
  have hinv : ContinuousAt (fun y : Fin a → K => (rowMat ℓ y)⁻¹) (Pi.single ℓ 1) := by
    refine ContinuousAt.comp (f := fun y => rowMat ℓ y) (g := Inv.inv) ?_ hc.continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [det_rowMat, Ring.inverse_eq_inv']
    simpa using continuousAt_inv₀ (one_ne_zero (α := K))
  have hv' : (fun y => MulOpposite.op (rowMat ℓ y)⁻¹) =ᶠ[nhds (Pi.single ℓ (1:K))]
      fun y => MulOpposite.op (((rowGL ℓ y)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) :=
    hv.mono fun y hy => by simp only [Matrix.coe_units_inv, ← hy]
  rw [Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  exact (hc.continuousAt.congr hv).prodMk ((MulOpposite.continuous_op.continuousAt.comp hinv).congr hv')

end Local

theorem exists_exp_lt {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    ∃ N : ℕ, WithZero.exp (-(N:ℤ)) < c := by
  obtain ⟨k, rfl⟩ : ∃ k, c = WithZero.exp k := ⟨_, (WithZero.exp_log hc).symm⟩
  refine ⟨(-k + 1).toNat, ?_⟩
  rw [WithZero.exp_lt_exp]
  omega

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_of_mem_nhds {a : ℕ} (ℓ : Fin a) (w : HeightOneSpectrum (𝓞 E))
    {V : Set (Fin a → w.adicCompletion E)} (hV : V ∈ nhds (Pi.single ℓ 1)) :
    ∃ N : ℕ, ∀ y : Fin a → w.adicCompletion E,
      (∀ j, Valued.v (y j - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ))) → y ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  have h1 : ∀ j, ∃ N : ℕ, ∀ z : w.adicCompletion E,
      Valued.v (z - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ)) → z ∈ t j := by
    intro j
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 (ht j)
    have hc : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) := by simp
    obtain ⟨N, hN⟩ := exists_exp_lt hc
    refine ⟨N, fun z hz => hγ ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact lt_of_le_of_lt hz hN
  choose N hN using h1
  refine ⟨Finset.univ.sup N, fun y hy => hsub fun j _ => hN j _ ((hy j).trans ?_)⟩
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  exact Finset.le_sup (Finset.mem_univ j)

variable {E : Type} [Field E] [NumberField E]

theorem map_list_prod_locGL {a : ℕ} (g : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin a) (w.adicCompletion E))
    (l : List (HeightOneSpectrum (𝓞 E))) (hl : l.Nodup) (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (pLoc E w) (l.map fun v => locGL E a v (g v)).prod = if w ∈ l then g w else 1 := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih (List.nodup_cons.1 hl).2]
    by_cases h : w = v
    · subst h
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 hl).1, if_pos List.mem_cons_self, mul_one]
    · rw [pLoc_locGL_of_ne h, one_mul]
      simp [h]

theorem pLoc_single {a : ℕ} (ℓ j : Fin a) (w : HeightOneSpectrum (𝓞 E)) :
    pLoc E w ((Pi.single ℓ 1 : Fin a → Af E) j) = (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j := by
  by_cases h : j = ℓ
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem exists_nat_rowGL_mem {a : ℕ} (ℓ : Fin a) {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ N : ℕ, ∀ y : Fin a → w.adicCompletion E,
      (∀ j, Valued.v (y j - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ))) →
      locGL E a w (rowGL ℓ y) ∈ U ∧ rowGL ℓ y ∈ KGL w (n := a) := by
  refine exists_nat_of_mem_nhds ℓ w (V := {y | locGL E a w (rowGL ℓ y) ∈ U ∧
    rowGL ℓ y ∈ KGL w (n := a)}) ?_
  have ho : IsOpen ((locGL E a w) ⁻¹' (U : Set (GL (Fin a) (Af E))) ∩
      (KGL w (n := a) : Set (GL (Fin a) (w.adicCompletion E)))) :=
    (hU.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)).inter
      (GlobalTheory.LFun.IntPtsUnitary.isOpen_GLint _ (Valued.isOpen_integer (w.adicCompletion E)))
  exact (continuousAt_rowGL ℓ).preimage_mem_nhds
    (ho.mem_nhds (by simp only [rowGL_single, Set.mem_inter_iff, Set.mem_preimage, map_one, SetLike.mem_coe,
      one_mem, and_self]))

theorem pLoc_apply (w : HeightOneSpectrum (𝓞 E)) (x : Af E) : pLoc E w x = x w := rfl

theorem val_sub_single_le {a : ℕ} (ℓ : Fin a) {J : (FractionalIdeal (𝓞 E)⁰ E)ˣ} {y : Fin a → Af E}
    (hy : y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J) (w : HeightOneSpectrum (𝓞 E)) (j : Fin a) :
    Valued.v (pLoc E w (y j) - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤
      WithZero.exp (-FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E)) := by
  have h1 := (GroundTheory.Global.mem_idealFiniteAdeles J).1 (hy j) w
  rw [← pLoc_apply, Pi.sub_apply, map_sub, pLoc_single] at h1
  exact h1

theorem exists_bump_ideal_rowGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    ∃ (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ 0 < (Φ (Pi.single ℓ 1)).re ∧
      (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) ∧
      ∀ y : Fin a → Af E, y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J →
        ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (n := a)) ∧
          (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
          ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) ℓ j = pLoc E w (y j) := by
  intro E _ _ _ a ℓ T U hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_rowSet (E := E) ℓ) (Pi.single ℓ 1) (by
    intro w; simp)
  let f : ContDiffBump (Pi.single ℓ 1 : Fin a → Cinf E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  choose Nw hNw using fun w => exists_nat_rowGL_mem (E := E) ℓ hU w
  set N : ℕ := T.sup Nw + 1 with hN
  set n : HeightOneSpectrum (𝓞 E) → ℤ := fun w => if w ∈ T then (N : ℤ) else 0 with hn
  have hfin : ∀ᶠ v in Filter.cofinite, n v = 0 := by
    refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => ?_)
    by_contra h
    simp [hn, h] at hv
  let J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := ∏ᶠ w, GroundTheory.Global.primeIdealUnit w ^ n w
  have hJ : ∀ w, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = n w :=
    GroundTheory.Global.count_finprod_primeIdealUnit_zpow n hfin
  refine ⟨fun u => ((f u : ℝ) : ℂ), J, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_left Complex.ofReal_zero
  · refine (tsupport_comp_subset Complex.ofReal_zero f).trans ?_
    rw [f.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show r / 2 < r; linarith)).trans hball
  · intro u; simp [f.nonneg]
  · simp [f.one_of_mem_closedBall (Metric.mem_closedBall_self (by show (0:ℝ) ≤ r / 4; positivity))]
  · intro w hw; rw [hJ, hn]; simp [hw]
  · intro y hy
    have hloc : ∀ w ∈ T, ∀ j, Valued.v (pLoc E w (y j) - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤
        WithZero.exp (-(N : ℤ)) := by
      intro w hw j
      have h1 := val_sub_single_le ℓ hy w j
      rw [hJ, hn] at h1
      simpa only [hw, if_true] using h1
    have hmem : ∀ w ∈ T, locGL E a w (rowGL ℓ (fun j => pLoc E w (y j))) ∈ U ∧
        rowGL ℓ (fun j => pLoc E w (y j)) ∈ KGL w (n := a) := by
      intro w hw
      refine hNw w _ fun j => (hloc w hw j).trans ?_
      rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le, hN]
      exact (Finset.le_sup hw).trans (Nat.le_succ _)
    have hunit : ∀ w ∈ T, IsUnit (pLoc E w (y ℓ)) := by
      intro w hw
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have h2 := hloc w hw ℓ
      rw [h0, Pi.single_eq_same, zero_sub, Valuation.map_neg, Valuation.map_one, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at h2
      omega
    have key := map_list_prod_locGL (E := E) (a := a) (fun v => rowGL ℓ (fun j => pLoc E v (y j))) T.toList
      T.nodup_toList
    refine ⟨(T.toList.map fun v => locGL E a v (rowGL ℓ (fun j => pLoc E v (y j)))).prod, ?_, ?_, ?_, ?_⟩
    · refine Subgroup.list_prod_mem U fun x hx => ?_
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact (hmem v (Finset.mem_toList.1 hv)).1
    · intro w
      rw [key w]
      split_ifs with h
      · exact (hmem w (Finset.mem_toList.1 h)).2
      · exact one_mem _
    · intro w hw
      rw [key w, if_neg (by simpa using hw)]
    · intro w hw j
      rw [key w, if_pos (Finset.mem_toList.2 hw), val_rowGL (hunit w hw)]
      simp [rowMat]

end GlobalTheory.BumpOrbit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.irreducible_weight_descends_to_polynomial_module : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', (fun t => e.comp (emb t)) t ≠ ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (fun t => e.comp (emb t)) t ∨ σ = ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t)) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W), ρ.IsIrreducible → ∀ lam0 : ι → Fin n → ℤ, (∀ t, NX.HWAtF c ρ.dual (emb t) (lam0 t)) → ∃ lam : ι → DomWeight n, (∀ t, (lam t).w = lam0 t) ∧ ∃ T : W ≃ₗ[K] VV K lam, ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  first | exact @GlobalTheory.WtDescent.weight_descends | exact GlobalTheory.WtDescent.weight_descends | (intros; apply GlobalTheory.WtDescent.weight_descends <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.exists_half_uniformiser_frameMatrix_prescribed_reductions : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP), ∃ u : WO S T, IsHalf e u ∧ IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) ∧ ∀ PP ∈ Q, redM PP (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) = y PP := by
  first | exact @GlobalTheory.HalfFrameLift.exists_half_redM_frMapO | exact GlobalTheory.HalfFrameLift.exists_half_redM_frMapO | (intros; apply GlobalTheory.HalfFrameLift.exists_half_redM_frMapO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → (∀ PP ∈ Q, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) → ∀ N : EAf D, ∀ hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (∑ PP ∈ Q, es PP) * N = N → (toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ PP ∈ Q, resS D.host.F PP ⟨N, hN⟩ = 0) := by
  first | exact @GlobalTheory.IdemKerDiv.integral_div_iff | exact GlobalTheory.IdemKerDiv.integral_div_iff | (intros; apply GlobalTheory.IdemKerDiv.integral_div_iff <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe GlobalTheory.CompactHowe.LastStep
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntertwinerTransfer

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem isItW_transfer (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank)
    (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank)
    (hd : ∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) (hd' : ∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree)
    (ω ω₁ : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt pt₁ : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ))
    (hpt : Function.Injective pt) (hpt₁ : Function.Injective pt₁)
    (hω : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ))
    (hω' : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ))
    (hω₁ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω₁ (atTau θ V τ g, 1) (pt₁ φ) = pt₁ (ρ τ g φ))
    (hω₁' : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω₁ (1, atTau θ W τ h) (pt₁ φ) = pt₁ (ρ' τ h φ))
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hIt : IsItW θ M M' ω pt It) :
    IsItW θ M M' ω₁ pt₁ It := by
  refine ⟨hIt.ne, hIt.bdd, ?_, ?_, ?_, ?_⟩
  · intro τ g hg φ φ' h v
    rw [hω₁ τ g hg] at h
    refine hIt.eqK τ g hg φ φ' ?_ v
    rw [hω τ g hg, hpt₁ h]
  · intro τ X hX φ φ' h v
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (GlobalTheory.CompactIntertwiner.isUnit_gram M τ) hX t
    simp only [oneP, hω₁ τ _ (hm _)] at h
    refine hIt.eqg τ X hX φ φ' (fun z => ?_) v
    simp only [oneP, hω τ _ (hm _)]
    exact GlobalTheory.CompactIntertwiner.hasDerivAt_pol pt₁ hpt₁ (fun t : ℝ => ρ τ (NormedSpace.exp (t • X)) φ) _
      (fun t => hd τ _ φ) φ' h (LinearMap.proj z ∘ₗ pt)
  · intro τ h hh φ φ' v v' e e'
    rw [hω₁' τ h hh] at e
    refine hIt.invK τ h hh φ φ' v v' ?_ e'
    rw [hω' τ h hh, hpt₁ e]
  · intro τ X hX φ φ' v v' h h'
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (GlobalTheory.CompactIntertwiner.isUnit_gram M' τ) hX t
    simp only [oneP, hω₁' τ _ (hm _)] at h
    refine hIt.invg τ X hX φ φ' v v' (fun z => ?_) h'
    simp only [oneP, hω' τ _ (hm _)]
    exact GlobalTheory.CompactIntertwiner.hasDerivAt_pol pt₁ hpt₁ (fun t : ℝ => ρ' τ (NormedSpace.exp (t • X)) φ) _
      (fun t => hd' τ _ φ) φ' h (LinearMap.proj z ∘ₗ pt)


open Classical in
theorem isItW_lastStep_transfer (k : Fin D.R.m) (hk : (k : ℕ) + 1 = D.R.m) (a : ℕ) (ha : a = k) (hV : V.SigOK)
    (hW : W.SigOK) (rV : V.rank = D.R.r + k * D.R.t) (rW : W.rank = V.rank + D.R.t)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) D.R.m)) (θ : InfFam D) (hθ : IsInfFam θ)
    (ψ : AddChar (AF D.host.F) ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (ω ω₁ : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f f₁ : WO V W → ℂ)
    (hω : IsStepWeil k ψ V W ω) (hf : IsVacVec ψ θ M M' f) (hω₁ : IsStepWeil k ψ V W ω₁) (hf₁ : IsVacVec ψ θ M M' f₁)
    (hIt : IsItW θ M M' ω (ptOf ψ θ M M' f) It) : IsItW θ M M' ω₁ (ptOf ψ θ M M' f₁) It := by
  subst ha
  have hp := fun τ => GlobalTheory.T.lastStep_parameters_partition_extended_by_zeros D k τ V.rank W.rank (M.lam τ) (M.ε τ) (M'.lam τ) (M'.ε τ) hk rV rW (M.enum τ) (M'.enum τ)
  have hε := fun τ => (hp τ).1
  have hε' := fun τ => (hp τ).2.1
  choose x₁ x₃ h1 h3 _ using fun τ => (hp τ).2.2
  have act : ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ), IsStepWeil k ψ V W ω →
      IsVacVec ψ θ M M' f →
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (ptOf ψ θ M M' f φ) =
        ptOf ψ θ M M' f (polAct M M' x₁ x₃ (Function.update (fun _ => 1) τ g) (fun _ => 1) φ)) ∧
      (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (ptOf ψ θ M M' f φ) =
        ptOf ψ θ M M' f (polAct M M' x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ h) φ)) := by
    intro ω f hω hf
    refine ⟨fun τ g hg φ => ?_, fun τ h hh φ => ?_⟩
    · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) (one_mem _) φ
      rwa [compAt_atTau hθ τ hg, compAt_one] at this
    · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) W τ h) φ
      rwa [compAt_atTau hθ τ hh, compAt_one] at this
  have a0 := act ω f hω hf
  have a1 := act ω₁ f₁ hω₁ hf₁
  exact isItW_transfer θ M M' (fun τ g => polAct M M' x₁ x₃ (Function.update (fun _ => 1) τ g) fun _ => 1)
    (fun τ h => polAct M M' x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ h))
    (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) ω ω₁
    (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f)
    (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f₁)
    (GlobalTheory.T.fockVectorsOfThetaDatum_injective D V W _ _ ψ θ M M' f hω.choose_spec.choose_spec.1.std hθ hf)
    (GlobalTheory.T.fockVectorsOfThetaDatum_injective D V W _ _ ψ θ M M' f₁ hω₁.choose_spec.choose_spec.1.std hθ hf₁)
    a0.1 a0.2 a1.1 a1.2 It hIt

theorem pItX_of_one : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.chain_ωX → R.chain_vX → ∀ (t₀ : T) (y : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY (D.R.m - 1))), IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t₀) (R.ptX t₀) y → R.PItX y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hω hv t₀ y hy t
  have hm := D.R.two_le_m
  let k : Fin D.R.m := ⟨D.R.m - 1, by omega⟩
  have hk : (k : ℕ) = D.R.m - 1 := rfl
  have hS := fun t => GlobalTheory.T.lastThetaChainStep_exponents_and_nonzero_vacuum D G Pl0 T A Ks R hL hM.inf hω hv t k hk
  have rV : (Yc D (D.R.m - 1)).rank = D.R.r + k * D.R.t := by
    rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (Nat.sub_le _ _)]; rfl
  have rW : D.sp.X'.rank = (Yc D (D.R.m - 1)).rank + D.R.t := by
    rw [rV, D.sp.X'_rank, Ranks.rankX', add_assoc, ← Nat.succ_mul]
    congr 2
    omega
  exact isItW_lastStep_transfer k (by omega) (min (D.R.m - 1) D.R.m) (by omega) (D.sp.Y_sig _) D.sp.X'_sig rV rW
    (R.MY (D.R.m - 1)) R.MX R.θ hM.inf R.ψ y (R.ωX t₀) (R.ωX t) (R.vX t₀) (R.vX t) (hS t₀).1 (hS t₀).2 (hS t).1 (hS t).2 hy

end GlobalTheory.IntertwinerTransfer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.realPoints_act_fock_by_realComponents_basis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∃ (w : GlobalTheory.ExportSeries.Weight D (Vc D i).rank) (BS : GlobalTheory.ExportSeries.GLR D (Vc D i).rank) (r : ↥(GinfC (Vc D i)) →* GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ (u : ↥(GinfC (Vc D i))) (P : PolF D (Wc D i).rank (Vc D i).rank), R.ωP i t ((u : GA D (Vc D i)), 1) (R.ptP i t P) = R.ptP i t (GlobalTheory.ExportSeries.fockGL (Wc D i).rank w BS (r u) P)) ∧ (∀ (u : ↥(GinfC (Vc D i))) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r u) τ : GL (Fin (Vc D i).rank) ℂ) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ (∀ g : GlobalTheory.ExportSeries.GLR D (Vc D i).rank, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin (Vc D i).rank) ℂ) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) → ∃ u, r u = g) ∧ (∀ (τ : D.what₂.Tau) (j : Fin (Wc D i).rank), (R.MW i (sg0 D A)).ε τ j = decide ((j : ℕ) < w.p τ)) := by
  first | exact @GlobalTheory.RealPtsFock.real_points_fock | exact GlobalTheory.RealPtsFock.real_points_fock | (intros; apply GlobalTheory.RealPtsFock.real_points_fock <;> assumption)
end
