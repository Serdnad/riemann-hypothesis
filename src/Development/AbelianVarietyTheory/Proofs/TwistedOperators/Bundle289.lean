module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle229
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumUnramifiedZetaSumUnitaryInert
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle278
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle277
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle167
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle279
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitaryMoverStandardLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm.IsoDeriv

variable {D : D7} {θ : InfFam D}

theorem isoPart_lineAt (hθ : IsInfFam θ) (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (t : ℝ) :
    isoPart V W C (lineAt θ τ z t) = lineAt θ τ (dirAt V W C τ z) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO V W :=
    { toFun := fun t => isoPart V W C (lineAt θ τ z t)
      map_zero' := by unfold isoPart; rw [AddMonoidHom.map_zero, Matrix.zero_mul]
      map_add' := fun s t => by unfold isoPart; rw [AddMonoidHom.map_add (f := _), Matrix.add_mul] }
  have hL' : IsLineAt θ τ (dirAt V W C τ z) L := by
    refine ⟨(continuous_isoPart V W C).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (isoPart V W C (lineAt θ τ z t)).map (finPart D) = 0
      unfold isoPart
      rw [Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' (isoPart V W C (lineAt θ τ z t)) = _
      unfold isoPart
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2]
      have e : compAt θ τ' ((adj D C * V.gram).map (incA D)) = (adj D C * V.gram).map (tauE D τ') := by
        unfold compAt
        rw [Matrix.map_map]
        congr 1
        funext e
        exact GlobalTheory.FockCompare.comp_incA hθ τ' e
      rw [e]
      split_ifs with h
      · subst h
        unfold dirAt
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

end GlobalTheory.MixedTerm.IsoDeriv

namespace GlobalTheory.MixedTerm.IsoDeriv

variable {D : D7} {θ : InfFam D}

theorem phase_lineAt (hθ : IsInfFam θ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hCC : adj D C * V.gram * C' = 1) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (t : ℝ) :
    phase ψ V W C C' y (lineAt θ τ z t) = Complex.exp (2 * Real.pi * Complex.I *
      ((t * (2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re) : ℝ) : ℂ)) := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  rw [GlobalTheory.T.mixedModelHeisenbergPhase_eq_cexp_realPoints D V W r C C' hCC ψ hψ θ hθ y _ (hL.2.1 t)]
  congr 4
  simp only [hL.2.2 t]
  rw [Finset.sum_eq_single τ (fun b _ hb => by rw [if_neg hb, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re,
    mul_zero]) (by simp), if_pos rfl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  ring

end GlobalTheory.MixedTerm.IsoDeriv

namespace GlobalTheory.MixedTerm.IsoDeriv

theorem term_dRho_dirAt : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin r) ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y = (2 * Real.pi * Complex.I * ((2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hs hCC ψ hψ θ hθ μ 𝓨 h G hG τ z y
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * z)).re := ⟨_, rfl⟩
  rw [← hc]
  have hL'r := GlobalTheory.OrientedHeis.isRealDir_lineAt (S := V) (T := W) hθ τ (dirAt V W C τ z)

  have hg : ∀ t : ℝ, term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y =
      Complex.exp (2 * Real.pi * Complex.I * ((t * c : ℝ) : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := fun t => by
    rw [← isoPart_lineAt hθ V W C τ z t, GlobalTheory.T.mixedModelTerm_heisenbergIsotropic_character D V V' W r C C' B hs ψ hψ μ 𝓨 h G hG y _,
      phase_lineAt hθ V W C C' hCC hψ y τ z t, hc]
  have hd1 : HasDerivAt (fun t : ℝ => term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y)
      (2 * Real.pi * Complex.I * (c : ℂ) * term ψ V V' W C C' B μ 𝓨 G y) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * ((t * c : ℝ) : ℂ)) (2 * Real.pi * Complex.I * (c : ℂ)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp).const_mul (2 * Real.pi * Complex.I)
      simpa using this
    have h2 := (h1.cexp).mul_const (term ψ V V' W C C' B μ 𝓨 G y)
    rw [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
    exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hg t)

  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL'r hG)
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : heisO ψ V W (lineAt θ τ (dirAt V W C τ z) 0) (GlobalTheory.OrientedHeis.dLine ψ V W (lineAt θ τ (dirAt V W C τ z)) G) =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G := by
    rw [AddMonoidHom.map_zero, GlobalTheory.OrientedHeis.heisO_zero]
    rfl
  have hd2 : HasDerivAt (fun t : ℝ => term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t) G) y)
      (term ψ V V' W C C' B μ 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ z) G) y) 0 := by
    rw [← e0]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓨) (x₀ := (0 : ℝ))
      (F' := fun t x => heisO ψ V W (isoPart V W C' (Matrix.map y (incA D)))
        (heisO ψ V W (lineAt θ τ (dirAt V W C τ z) t)
          (GlobalTheory.OrientedHeis.dLine ψ V W (lineAt θ τ (dirAt V W C τ z)) G)) (isoPart V W C x + midPart V V' W B 0))
      (bound := fun _ => K) (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const K) ?_).2
    · exact Filter.Eventually.of_forall fun t =>
        (integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 t) hG) _ _).aestronglyMeasurable
    · exact integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 0) hG) _ _
    · exact (integrableOn_heisO V W C hψ h (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hL'r.2 0)
        (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL'r hG)) _ _).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x t _ => ?_
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1, GlobalTheory.HeisOrtho.norm_heisO hψ.1]
      exact hK _
    · refine Filter.Eventually.of_forall fun x t _ => ?_
      exact (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL'r hG _ t).const_mul _
  rw [hd2.unique hd1]

end GlobalTheory.MixedTerm.IsoDeriv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hasSum_unramifiedZetaSum_unitary_inert : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ r) V) (x : V) (α : Fin (r / 2) → ℂˣ), IsSatVecU ϖ q ρ x α → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * ℓ (ρ a.out x)) (eulerFac (bcParam r α) ((z : ℂ) * ((q : ℂ) ^ (t + 1))⁻¹) * (∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((z : ℂ) * ((q : ℂ) ^ (r + t))⁻¹))) * ℓ x) := by
  first | exact @GlobalTheory.ZetaSumU.hasSum_zetaSum_inert | exact GlobalTheory.ZetaSumU.hasSum_zetaSum_inert | (intros; apply GlobalTheory.ZetaSumU.hasSum_zetaSum_inert <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicSphericalEigenfunction_local_heckeAlgebra_eigen : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ v ∉ Sb, ∀ f : GA D V → ℂ, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → f ∈ fixed ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) ∧ ∀ h ∈ Hecke ℂ (Kv V v), ∃ a : ℂ, heckeVec ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) h f = a • f := by
  first | exact @GlobalTheory.FinZeta.eigen_heckeAlg | exact GlobalTheory.FinZeta.eigen_heckeAlg | (intros; apply GlobalTheory.FinZeta.eigen_heckeAlg <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem trace_eq_sum (y : Fld P) : τ.1 (Algebra.trace E (Fld P) y) = ∑ i, psiL P τ i y := by
  letI : Algebra E ℂ := τ.1.toAlgebra
  haveI : Algebra.IsSeparable E (Fld P) := Algebra.IsAlgebraic.isSeparable_of_perfectField

  let emb : Fin r → (Fld P →ₐ[E] ℂ) := fun i =>
    { psiL P τ i with commutes' := fun e => psiL_algebraMap P τ i e }
  have hinj : Function.Injective emb := by
    intro i j h
    apply cxRoots_injective P τ
    have h' := congrArg (fun f : Fld P →ₐ[E] ℂ => f (alpha P)) h
    simpa [emb] using h'
  have hcard : Fintype.card (Fin r) = Fintype.card (Fld P →ₐ[E] ℂ) := by
    rw [Fintype.card_fin, AlgHom.card, finrank_Fld]
  have hbij : Function.Bijective emb :=
    (Fintype.bijective_iff_injective_and_card emb).2 ⟨hinj, hcard⟩
  have htr := trace_eq_sum_embeddings (K := E) (L := Fld P) (E := ℂ) (x := y)
  rw [show τ.1 (Algebra.trace E (Fld P) y) = algebraMap E ℂ (Algebra.trace E (Fld P) y) from rfl, htr]
  exact (Fintype.sum_bijective emb hbij (fun i => psiL P τ i y) (fun g => g y) (fun i => rfl)).symm

theorem psiL_star (hCM : IsCMExt F E σ) (i : Fin r) (hi : ‖cxRoots τ.1 P i‖ = 1) (y : Fld P) :
    psiL P τ i (star' P y) = conj (psiL P τ i y) := by
  have key : ((psiL P τ i).comp (star' P : Fld P →+* Fld P) : AdjoinRoot P.1 →+* ℂ) =
      ((starRingEnd ℂ).comp (psiL P τ i) : AdjoinRoot P.1 →+* ℂ) := by
    apply AdjoinRoot.ringHom_ext
    · ext e
      show psiL P τ i (star' P (algebraMap E (Fld P) e)) = conj (psiL P τ i (algebraMap E (Fld P) e))
      rw [star'_algebraMap, psiL_algebraMap, psiL_algebraMap]
      exact hCM.2.2.2 τ.1 e
    · show psiL P τ i (star' P (alpha P)) = conj (psiL P τ i (alpha P))
      rw [star'_alpha, map_inv₀, psiL_alpha]

      have h1 : cxRoots τ.1 P i * conj (cxRoots τ.1 P i) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hi]
        norm_num
      exact (eq_inv_of_mul_eq_one_right h1).symm
  exact RingHom.congr_fun key y

theorem ext_real (a : w.Completion) (hw : w.IsReal) :
    conj (InfinitePlace.Completion.extensionEmbedding w a) = InfinitePlace.Completion.extensionEmbedding w a := by

  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a, Complex.conj_ofReal]

end GlobalTheory.TrEll.RealTorus


open GlobalTheory.TrEll.RealTorus in
theorem GlobalTheory.TrEll.realTorus_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), CompactSpace (Tor P w.Completion) → ∃ Ψ : w.Completion ⊗[F] Fld P ≃+* (Fin r → ℂ), (∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i)) ∧ (∀ e i, Ψ (algebraMap (w.Completion ⊗[F] E) _ e) i = infEmb τ e) ∧ Ψ (1 ⊗ₜ[F] alpha P) = cxRoots τ.1 P ∧ (∀ y, infEmb τ (trBase P w.Completion y) = ∑ i, Ψ y i) ∧ Function.Injective (cxRoots τ.1 P) ∧ ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  intro F E _ _ _ _ _ σ hCM r P w τ hc
  have hbij := GlobalTheory.T.completionTensorAllRootsMap_bijective_cm F E σ hCM r P w τ
  have hnorm := GlobalTheory.T.torusFieldComplexRoots_norm_eq_one_compact F E σ hCM r P w τ hbij hc
  have hw : w.IsReal := hCM.1.isReal w
  refine ⟨RingEquiv.ofBijective (PsiAll P τ) hbij, ?_, ?_, ?_, ?_, cxRoots_injective P τ, hnorm⟩
  · intro y i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      rw [show sigR w.Completion (star' P) (a ⊗ₜ[F] y) = a ⊗ₜ[F] star' P y from rfl]
      rw [Psi_tmul, Psi_tmul, psiL_star P τ hCM i (hnorm i), map_mul, ext_real a hw]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro e i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction e using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [show algebraMap (w.Completion ⊗[F] E) (w.Completion ⊗[F] Fld P) (a ⊗ₜ[F] e) =
        a ⊗ₜ[F] algebraMap E (Fld P) e from rfl]
      rw [Psi_tmul, infEmb_tmul, psiL_algebraMap]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · funext i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply, Psi_tmul, map_one, psiL_alpha, one_mul]
  · intro y
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      rw [show trBase P w.Completion (a ⊗ₜ[F] y) = a ⊗ₜ[F] Algebra.trace E (Fld P) y from rfl]
      rw [infEmb_tmul, trace_eq_sum P τ y, Finset.mul_sum]
      simp only [Psi_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, Finset.sum_add_distrib]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.mem_conjugatePlacesProductIdeal_of_forall_conj_place : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E), (∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) → x ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
  first | exact @GlobalTheory.LiftLevel.InfMem.main | exact GlobalTheory.LiftLevel.InfMem.main | (intros; apply GlobalTheory.LiftLevel.InfMem.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_multiplier_shifted_lattice_away_from_places : ∀ (D : D7) (r : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (L : Lt D.host.E r) (w : HeightOneSpectrum (𝓞 D.host.F)), (∀ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → ∀ u ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) L, ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • u ∈ L := by
  first | exact @GlobalTheory.TrOffShift.shift_mult | exact GlobalTheory.TrOffShift.shift_mult | (intros; apply GlobalTheory.TrOffShift.shift_mult <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel


theorem _root_.GlobalTheory.T.ideleFrameAdjointMatrix_half_idempotent_smul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (c : D.host.E) (x : WO S T), IsHalf (cA D e) x → adjA S T βS βT (e * incA D (star c)) x = adjA S T βS βT 1 (incA D c • x) := by
  first | exact @GlobalTheory.AdjScalar.adjA_half_smul | exact GlobalTheory.AdjScalar.adjA_half_smul | (intros; apply GlobalTheory.AdjScalar.adjA_half_smul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.liftLattice_exists_nsmul_mem_standardTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.LiftLevel.liftL_nsmul_mem_latO | exact GlobalTheory.LiftLevel.liftL_nsmul_mem_latO | (intros; apply GlobalTheory.LiftLevel.liftL_nsmul_mem_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_finite_unitary_mover_standard_lattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ a : AE D, (∃ b : AE D, a * b = e) → ∃ (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ ∧ IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) := by
  first | exact @GlobalTheory.LiftLevel.exists_mover | exact GlobalTheory.LiftLevel.exists_mover | (intros; apply GlobalTheory.LiftLevel.exists_mover <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel


theorem _root_.GlobalTheory.T.ideleFrameAdjoint_integral_iff_dualLattice : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βT ΛT → ∀ (J : Ideal (𝓞 D.host.E)), Squarefree J → ∀ x : WO S T, IsFinPt x → ((IsIntM (adjA S T βS βT 1 x) ∧ ∀ PP : Formalism.L2.DIV.Pl D.host.E, J ≤ PP.asIdeal → redM PP (adjA S T βS βT 1 x) = 0) ↔ x ∈ hatA S T (tens (stdL D.host.E S.rank) (conjI J • ΛT))) := by
  first | exact @GlobalTheory.DualRed.adj_int_iff | exact GlobalTheory.DualRed.adj_int_iff | (intros; apply GlobalTheory.DualRed.adj_int_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.exists_diagonal_conj_edgeSum_addChar_finiteField : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ {r : ℕ} (ρ k : ℕ) (ψ' ψ0 : AddChar κf ℂ), ψ' ≠ 1 → ψ0 ≠ 1 → ∀ a : Fin r → Fin r → κfˣ, ∃ d : Fin r → κfˣ, ∀ u : GL (Fin r) κf, u ∈ unipSym κf r ρ k → ψ' (∑ i, ∑ j, if symEdge ρ k i j then (a i j : κf) * u.val i j else 0) = ψ0 (edgeSum (symEdge ρ k) ((diagGL d)⁻¹ * u * diagGL d)) := by
  first | exact @GlobalTheory.SeeConjScale.scale_conj | exact GlobalTheory.SeeConjScale.scale_conj | (intros; apply GlobalTheory.SeeConjScale.scale_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.exists_frame_rescale_conj_reductions_diagonal : ∀ {D : D7} {n r : ℕ} (hr : r ≤ n) (β : GL (Fin n) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), IsFrame β Λ → ∀ (Pg : Finset (Pl D.host.E)) (d : ∀ PP : Pl D.host.E, Fin r → (kP PP)ˣ), ∃ β' : GL (Fin n) (EAf D), IsFrame β' Λ ∧ (∀ M, M ∈ St β' ↔ M ∈ St β) ∧ ∀ PP ∈ Pg, ∀ M ∈ St β, upperLeftBlock hr (redFn β' PP M) = (diagGL (d PP))⁻¹ * upperLeftBlock hr (redFn β PP M) * diagGL (d PP) := by
  first | exact @GlobalTheory.FrameRescale.exists_rescale | exact GlobalTheory.FrameRescale.exists_rescale | (intros; apply GlobalTheory.FrameRescale.exists_rescale <;> assumption)
end
