module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle255
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle244
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGL
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle254
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.indexNormalization_inert_norm_eq_neg : ∀ (D : D7) (lam : ℕ →* ℂ), GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → lam (qV D.host.E w) = -((qV D.host.F v : ℕ) : ℂ) := by
  first | exact @GlobalTheory.LamInert.lam_qV_inert | exact GlobalTheory.LamInert.lam_qV_inert | (intros; apply GlobalTheory.LamInert.lam_qV_inert <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem exists_conjInv_root (hCM : IsCMExt F E σ) (m : Fin r) :
    ∃ j, cxRoots τ.1 P j = (conj (cxRoots τ.1 P m))⁻¹ := by
  let φ : Fld P →+* ℂ := (starRingEnd ℂ).comp ((psiL P τ m).comp (star' P : Fld P →+* Fld P))
  have hE : φ.comp (algebraMap E (Fld P)) = τ.1 := by
    ext e
    change conj (psiL P τ m (star' P (algebraMap E (Fld P) e))) = τ.1 e
    rw [star'_algebraMap, psiL_algebraMap, hCM.2.2.2 τ.1 e]
    simp
  have hα : φ (alpha P) = (conj (cxRoots τ.1 P m))⁻¹ := by
    change conj (psiL P τ m (star' P (alpha P))) = _
    rw [star'_alpha, map_inv₀, psiL_alpha, map_inv₀]
  have h0 := congrArg φ (eval_alpha P)
  rw [hom_eval₂, hE, hα, map_zero, ← eval_map, cxRoots_spec, eval_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨j, -, hj⟩ := h0
  refine ⟨j, ?_⟩
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
  exact hj.symm

end GlobalTheory.TrEll.RealTorus


open GlobalTheory.TrEll.RealTorus in
theorem GlobalTheory.TrEll.realTorus_norm_cxRoots : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) → CompactSpace (Tor P w.Completion) → ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  intro F E _ _ _ _ _ σ hCM r P w τ hB hK i
  have hw : w.IsReal := by haveI := hCM.1; exact IsTotallyReal.isReal w
  obtain ⟨π, hπ⟩ : ∃ π : Fin r → Fin r, ∀ m, cxRoots τ.1 P (π m) = (conj (cxRoots τ.1 P m))⁻¹ :=
    ⟨fun m => (exists_conjInv_root P τ hCM m).choose, fun m => (exists_conjInv_root P τ hCM m).choose_spec⟩
  have hinv : ∀ m, π (π m) = m := fun m =>
    cxRoots_injective P τ (by rw [hπ, hπ, map_inv₀, Complex.conj_conj, inv_inv])
  have hpsi : ∀ m, (psiL P τ m).comp (star' P : Fld P →+* Fld P) = (starRingEnd ℂ).comp (psiL P τ (π m)) := by
    intro m
    refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
    · change psiL P τ m (star' P (algebraMap E (Fld P) e)) = conj (psiL P τ (π m) (algebraMap E (Fld P) e))
      rw [star'_algebraMap, psiL_algebraMap, psiL_algebraMap]
      exact hCM.2.2.2 τ.1 e
    · change psiL P τ m (star' P (alpha P)) = conj (psiL P τ (π m) (alpha P))
      rw [star'_alpha, map_inv₀, psiL_alpha, psiL_alpha, hπ, map_inv₀, Complex.conj_conj]
  have hsig : ∀ m y, Psi P τ m (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y) = conj (Psi P τ (π m) y) := by
    intro m y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a l =>
      change Psi P τ m (a ⊗ₜ[F] star' P l) = _
      rw [Psi_tmul, Psi_tmul, map_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a,
        Complex.conj_ofReal]
      exact congrArg _ (RingHom.congr_fun (hpsi m) l)
  have h0 : cxRoots τ.1 P i ≠ 0 := by
    rw [← psiL_alpha P τ i]; exact (_root_.map_ne_zero _).2 (alpha_ne_zero P)
  suffices hfix : π i = i by
    have e := hπ i
    rw [hfix] at e
    have h1 : cxRoots τ.1 P i * conj (cxRoots τ.1 P i) = 1 := by
      nth_rw 1 [e]
      exact inv_mul_cancel₀ ((_root_.map_ne_zero _).2 h0)
    rw [Complex.mul_conj, ← Complex.sq_norm] at h1
    have h2 : ‖cxRoots τ.1 P i‖ ^ 2 = 1 := by exact_mod_cast h1
    nlinarith [norm_nonneg (cxRoots τ.1 P i)]

  by_contra hji

  have hcont : Continuous (fun g : Tor P w.Completion => ‖Psi P τ i (g.1.1 0 0)‖) := by
    letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
    haveI : ContinuousSMul w.Completion ℂ :=
      continuousSMul_of_algebraMap _ _ (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
    haveI : IsModuleTopology w.Completion (w.Completion ⊗[F] Fld P) := ⟨rfl⟩
    let L : w.Completion ⊗[F] Fld P →ₗ[w.Completion] ℂ :=
      { toFun := Psi P τ i
        map_add' := map_add _
        map_smul' := by
          intro c y
          have : c • y = (c ⊗ₜ[F] (1 : Fld P)) * y := by
            rw [Algebra.smul_def]; rfl
          rw [this, map_mul, Psi_tmul, map_one, mul_one]; rfl }
    have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
    have hv : Continuous (fun g : Tor P w.Completion => (g.1.1 : Matrix (Fin 1) (Fin 1) (w.Completion ⊗[F] Fld P))) :=
      Units.continuous_val.comp continuous_subtype_val
    exact continuous_norm.comp (hL.comp (hv.matrix_elem 0 0))
  obtain ⟨M, hM⟩ := (isCompact_range hcont).bddAbove
  obtain ⟨j, hj⟩ : ∃ j, π i = j := ⟨_, rfl⟩
  have hji' : j ≠ i := by rw [← hj]; exact hji
  have hπj : π j = i := by rw [← hj]; exact hinv i
  have hne : ∀ m, m ≠ j → π m ≠ i := fun m hm h => hm (by have := hinv m; rw [h, hj] at this; exact this.symm)
  have hne' : ∀ m, m ≠ i → π m ≠ j := fun m hm h => hm (by have := hinv m; rw [h, hπj] at this; exact this.symm)
  set t : ℝ := max M 0 + 1 with ht
  have ht0 : 0 < t := by positivity
  let v : Fin r → ℂ := fun m => if m = i then (t : ℂ) else if m = j then (t : ℂ)⁻¹ else 1
  obtain ⟨y, hy⟩ := hB.2 v
  have hyv : ∀ m, Psi P τ m y = v m := fun m => congrFun hy m
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hyy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y * y = 1 := by
    apply hB.1
    funext m
    rw [map_mul, map_one, Pi.mul_apply, PsiAll_apply, PsiAll_apply, hsig, hyv, hyv, Pi.one_apply]
    by_cases hmi : m = i
    · rw [hmi, hj]
      simp [v, hji', htc]
    · by_cases hmj : m = j
      · rw [hmj, hπj]
        simp [v, hji', htc]
      · simp [v, hmi, hmj, hne m hmj, hne' m hmi]
  let u : (w.Completion ⊗[F] Fld P)ˣ := ⟨y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y, by rw [mul_comm]; exact hyy, hyy⟩
  let g : Tor P w.Completion := ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) u, by
    change Formalism.UG.cT _ _ * _ * _ = _
    ext a b
    simp [Formalism.UG.cT, Matrix.mul_apply, Subsingleton.elim a 0, Subsingleton.elim b 0, JR, inclR, u, ← Algebra.TensorProduct.one_def, hyy]⟩
  have hg : ‖Psi P τ i (g.1.1 0 0)‖ = t := by
    have : g.1.1 0 0 = y := by simp [g, u]
    rw [this, hyv]
    simp [v, abs_of_pos ht0]
  have hle : ‖Psi P τ i (g.1.1 0 0)‖ ≤ M := hM ⟨g, rfl⟩
  rw [hg] at hle
  have : M < t := by rw [ht]; linarith [le_max_left M 0]
  linarith
end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrUnitLat

theorem gramOne_herm_nd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), IsHermND σ (GlobalTheory.TrUnitLat.gramOne P) := by
  intro F E _ _ _ _ _ σ hcm r P
  have hσ : ∀ e, σ (σ e) = e := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have hs := star'_star'_of_invol hσ P
  have htr := trace_star'_eq F E σ hσ r P
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [gramOne, Matrix.of_apply]
    rw [← htr, map_mul, hs, mul_comm]
  · intro hdet
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hw0
    set b := powB P
    set z : Fld P := ∑ j, w j • b j with hz
    have h1 : ∀ i, Algebra.trace E (Fld P) (z * star' P (b i)) = 0 := by
      intro i
      have := congr_fun hw i
      simp only [Matrix.mulVec, dotProduct, gramOne, Matrix.of_apply, Pi.zero_apply] at this

      rw [hz, Finset.sum_mul, map_sum]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
    have h2 : ∀ u : Fld P, Algebra.trace E (Fld P) (z * u) = 0 := by
      intro u
      have hu : u = ∑ i, σ (b.repr (star' P u) i) • star' P (b i) := by
        conv_lhs => rw [← hs u, ← b.sum_repr (star' P u)]

        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, star'_algebraMap]

      rw [hu, Finset.mul_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mul_smul_comm, map_smul, h1, smul_zero]
    have hz0 : z = 0 := (traceForm_nondegenerate E (Fld P)).1 z fun u => by
      rw [Algebra.traceForm_apply]; exact h2 u
    funext j
    exact Fintype.linearIndependent_iff.1 b.linearIndependent w (by rw [← hz0]) j

end GlobalTheory.TrUnitLat
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

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section

namespace GlobalTheory.SplitIdx.LocIndex

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m n : ℕ}

private theorem mulL_apply' {K : Type} [CommRing K] {a b : ℕ} (P : Matrix (Fin a) (Fin a) K)
    (y : Matrix (Fin a) (Fin b) K) : GlobalTheory.SplitIdx.mulL (n := b) P y = P * y := rfl

private theorem mem_intMat_iff' (y : Matrix (Fin m) (Fin n) (v.adicCompletion F)) :
    y ∈ GlobalTheory.SplitIdx.intMat F v m n ↔ ∀ i j, y i j ∈ v.adicCompletionIntegers F := Iff.rfl

theorem mulL_mul (A B : Matrix (Fin m) (Fin m) (v.adicCompletion F)) :
    GlobalTheory.SplitIdx.mulL (n := n) (A * B) = (GlobalTheory.SplitIdx.mulL (n := n) A).comp (GlobalTheory.SplitIdx.mulL B) :=
  AddMonoidHom.ext fun y => by
    rw [AddMonoidHom.comp_apply, mulL_apply', mulL_apply', mulL_apply', Matrix.mul_assoc]

theorem mulL_mem {P : Matrix (Fin m) (Fin m) (v.adicCompletion F)}
    (hP : ∀ i j, P i j ∈ v.adicCompletionIntegers F) {y : Matrix (Fin m) (Fin n) (v.adicCompletion F)}
    (hy : y ∈ GlobalTheory.SplitIdx.intMat F v m n) : GlobalTheory.SplitIdx.mulL P y ∈ GlobalTheory.SplitIdx.intMat F v m n := by
  refine (mem_intMat_iff' v _).2 fun i j => ?_
  rw [mulL_apply', Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hP i k) ((mem_intMat_iff' v _).1 hy k j)

private theorem entries_mem_integers_of_mem_KGL {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v (n := m)) :
    (∀ i j, k.1 i j ∈ v.adicCompletionIntegers F) ∧ (∀ i j, (k⁻¹).1 i j ∈ v.adicCompletionIntegers F) :=
  (GlobalTheory.LatHecke.mem_GLint_iff_entry _ _).1 hk

theorem mulL_mem_iff {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v (n := m))
    (y : Matrix (Fin m) (Fin n) (v.adicCompletion F)) :
    GlobalTheory.SplitIdx.mulL k.1 y ∈ GlobalTheory.SplitIdx.intMat F v m n ↔ y ∈ GlobalTheory.SplitIdx.intMat F v m n := by
  refine ⟨fun h => ?_, fun h => mulL_mem v (entries_mem_integers_of_mem_KGL v hk).1 h⟩
  have e : y = GlobalTheory.SplitIdx.mulL (k⁻¹).1 (GlobalTheory.SplitIdx.mulL (n := n) k.1 y) := by
    rw [mulL_apply', mulL_apply', ← Matrix.mul_assoc, k.inv_mul, Matrix.one_mul]
  rw [e]
  exact mulL_mem v (entries_mem_integers_of_mem_KGL v hk).2 h

theorem map_mulL {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v (n := m)) :
    (GlobalTheory.SplitIdx.intMat F v m n).map (GlobalTheory.SplitIdx.mulL k.1) = GlobalTheory.SplitIdx.intMat F v m n := by
  ext y
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mulL_mem v (entries_mem_integers_of_mem_KGL v hk).1 hx
  · intro hy
    refine ⟨GlobalTheory.SplitIdx.mulL (k⁻¹).1 y, mulL_mem v (entries_mem_integers_of_mem_KGL v hk).2 hy, ?_⟩
    rw [mulL_apply', mulL_apply', ← Matrix.mul_assoc, k.mul_inv, Matrix.one_mul]

theorem comap_mulL {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v (n := m))
    (P : Matrix (Fin m) (Fin m) (v.adicCompletion F)) :
    (GlobalTheory.SplitIdx.intMat F v m n).comap (GlobalTheory.SplitIdx.mulL (k.1 * P)) =
      (GlobalTheory.SplitIdx.intMat F v m n).comap (GlobalTheory.SplitIdx.mulL P) := by
  ext y
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, mulL_mul, AddMonoidHom.comp_apply, mulL_mem_iff v hk]

theorem zpow_mul_mem_iff {ϖ : v.adicCompletion F} (hϖ : IsUnifV F v ϖ) (hϖO : ϖ ∈ v.adicCompletionIntegers F)
    (d : ℤ) (x : v.adicCompletionIntegers F) :
    ϖ ^ d * (x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ↔
      x ∈ Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d) 0).toNat} := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hne : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have ht : Valued.v (((⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d) 0).toNat : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    rw [SubmonoidClass.coe_pow, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff _).2 hne)
  rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v ht, SubmonoidClass.coe_pow, map_pow]
  change Valued.v (ϖ ^ d * (x : v.adicCompletion F)) ≤ 1 ↔ _
  rw [map_mul, map_zpow₀, hv]
  have hx1 : Valued.v (x : v.adicCompletion F) ≤ 1 := x.2
  by_cases hx : (x : v.adicCompletion F) = 0
  · rw [hx, map_zero]
    simp
  · have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    rw [← WithZero.exp_log hx0] at hx1 ⊢
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp, WithZero.exp_le_exp] at *
    simp only [smul_eq_mul, nsmul_eq_mul] at *
    omega

theorem card_quot_pow {ϖ : v.adicCompletion F} (hϖ : IsUnifV F v ϖ) (hϖO : ϖ ∈ v.adicCompletionIntegers F)
    (e : ℕ) :
    Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ e}) =
      qV F v ^ e := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  refine (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 _ e ?_
  rw [SubmonoidClass.coe_pow, map_pow, hv, ← WithZero.exp_nsmul]
  congr 1
  simp

end GlobalTheory.SplitIdx.LocIndex

namespace GlobalTheory.SplitIdx.LocIndex

theorem toNat_sum {m : ℕ} (d : Fin m → ℤ) :
    (∑ i, max (-d i) 0).toNat = ∑ i, (max (-d i) 0).toNat := by
  have h : ∀ i, 0 ≤ max (-d i) 0 := fun i => le_max_right _ _
  apply @Nat.cast_injective ℤ
  rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => h i), Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => (Int.toNat_of_nonneg (h i)).symm

theorem relIndex_intMat : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m n : ℕ) (ϖ : v.adicCompletion F), IsUnifV F v ϖ → ∀ (d : Fin m → ℤ) (t : GL (Fin m) (v.adicCompletion F)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL v (n := m), ∀ k₂ ∈ KGL v (n := m), (GlobalTheory.SplitIdx.intMat F v m n).relIndex ((GlobalTheory.SplitIdx.intMat F v m n).map (GlobalTheory.SplitIdx.mulL (n := n) (k₁ * t * k₂).1)) = qV F v ^ (n * (∑ i, max (-d i) 0).toNat) := by
  intro F _ _ v m n ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖO : ϖ ∈ v.adicCompletionIntegers F := by
    change Valued.v ϖ ≤ 1
    rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  rw [← AddSubgroup.relIndex_comap, Units.val_mul, Units.val_mul, Matrix.mul_assoc, comap_mulL v hk₁,
    mulL_mul, ← AddSubgroup.comap_comap, AddSubgroup.relIndex_comap, map_mulL v hk₂, ht]
  let ψ : GlobalTheory.SplitIdx.intMat F v m n →+
      ((i : Fin m) → Fin n → v.adicCompletionIntegers F ⧸ Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}) :=
    { toFun := fun y i j => Ideal.Quotient.mk _ ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩
      map_zero' := by
        funext i j
        exact map_zero (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}))
      map_add' := fun y z => by
        funext i j
        exact map_add (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}))
          ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩ ⟨z.1 i j, (mem_intMat_iff' v z.1).1 z.2 i j⟩ }
  have hψ : ∀ (y : GlobalTheory.SplitIdx.intMat F v m n) i j, ψ y i j =
      Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}) ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩ :=
    fun _ _ _ => rfl
  have hker : ψ.ker = (AddSubgroup.comap (GlobalTheory.SplitIdx.mulL (n := n) (Matrix.diagonal fun i => ϖ ^ d i))
      (GlobalTheory.SplitIdx.intMat F v m n)).addSubgroupOf (GlobalTheory.SplitIdx.intMat F v m n) := by
    ext y
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, mem_intMat_iff',
      mulL_apply']
    simp only [Matrix.diagonal_mul]
    constructor
    · intro h i j
      have h1 : ψ y i j = 0 := congrFun (congrFun h i) j
      rw [hψ, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact (zpow_mul_mem_iff v hϖ hϖO (d i) ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩).2 h1
    · intro h
      funext i j
      show ψ y i j = 0
      rw [hψ, Ideal.Quotient.eq_zero_iff_mem]
      exact (zpow_mul_mem_iff v hϖ hϖO (d i) ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩).1 (h i j)
  have hsurj : Function.Surjective ψ := by
    intro z
    choose w hw using fun i j => Ideal.Quotient.mk_surjective (z i j)
    refine ⟨⟨fun i j => (w i j : v.adicCompletion F), (mem_intMat_iff' v _).2 fun i j => (w i j).2⟩, ?_⟩
    funext i j
    rw [hψ]
    exact hw i j
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    AddSubgroup.card_top, Nat.card_pi]
  simp only [Nat.card_pi, card_quot_pow v hϖ hϖO, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [toNat_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.SplitIdx.LocIndex
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

theorem _root_.GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ ϖ, IsUnifV E w ϖ → ∀ t : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (t d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∀ c : (Fin r → ℤ) → ℂ, (∀ d, heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (t d)) x = c d • x) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  first | exact @GlobalTheory.FinZeta.GLSeries.hasSum_hecke_eigenvalues | exact GlobalTheory.FinZeta.GLSeries.hasSum_hecke_eigenvalues | (intros; apply GlobalTheory.FinZeta.GLSeries.hasSum_hecke_eigenvalues <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.cmHostFractionalIdeal_partitionOfUnity : ∀ (D : D7), ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ D.host.AA) ∧ (∀ i, ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = 1 := by
  first | exact @GlobalTheory.HostAAPartition.host_AA_partition | exact GlobalTheory.HostAAPartition.host_AA_partition | (intros; apply GlobalTheory.HostAAPartition.host_AA_partition <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.kernelProjection_preserves_good_forms_base_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j, ∀ y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j, ((LinearMap.ker ((R.toCx3 F).θ' j A3.A.fam.μ0)).starProjection y : (R.toCx3 F).FLC j A3.A.fam.μ0) ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j := by
  first | exact @GlobalTheory.kerProj_goodL | exact GlobalTheory.kerProj_goodL | (intros; apply GlobalTheory.kerProj_goodL <;> assumption)
end
