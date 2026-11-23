module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePlaceCharacterFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAtIdempotentHermitianHomIsometryTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

open GlobalTheory.FlipMatch

namespace GlobalTheory.SwapHeis

theorem heis_sliceT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    G.V'.J.det ≠ 0 → G.W.J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd →
    ∀ (u₁ u₂ : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u₁ → At (evFin F v) u₂ →
    GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 u₁ᵀ) (GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₁ᵀ) = 0 →
    GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 u₂ᵀ) (GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₂ᵀ) = 0 →
    ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
    ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) Φ) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 u₁ᵀ) +
                     GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 u₂ᵀ)) *
          GlobalTheory.SwapSlice.sliceT ι Φ (Z.1 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₁ᵀ,
            Z.2 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₂ᵀ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT hdV hdW v t ι hι d' hd' dd hdd u₁ u₂ hu₁ hu₂ hp₁ hp₂ Φ hΦ Z
  set ψv := GlobalTheory.LatVac.psiAt B.ψ v with hψv
  have hc : Continuous ψv := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v
  have hstar : ∀ y, starRingEnd ℂ (ψv y) = ψv (-y) := fun y => GlobalTheory.DblVacLine.star_psiAt B.ψ hT.base.std.1 v y
  have hatT : ∀ u : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → At (evFin F v) uᵀ :=
    fun u hu r hr => by rw [← Matrix.transpose_smul, hu r hr, Matrix.transpose_zero]
  have Heisenberg₂ : ∀ u : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u →
      pairM (coX t 1 1 uᵀ) (coY σ G.V' G.W t 1 1 uᵀ) = 0 →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ Y,
        ι (schr ψv (GlobalTheory.LatVac.locCo G.M'.co v uᵀ) φ) Y =
          ψv (-pairM Y (coX t 1 1 uᵀ)) * ι φ (Y + coY σ G.V' G.W t 1 1 uᵀ) := by
    intro u hu hp φ hφ Y
    exact (GlobalTheory.HeisFlip.heis_trans_char hT.base.cm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew hdV hdW G.M' B.ψ
      hT.base.std t 1 1 uᵀ (hatT u hu) hp φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v uᵀ (hatT u hu) φ)).2 ι hι Y
  have hloc : GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v u₁ᵀ).1 (GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v u₁ᵀ).2 (-(GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ).2)) := by
    have e1 := hd' u₁ᵀ
    have e2 := hd' u₂ᵀ
    rw [Matrix.transpose_transpose] at e1 e2
    have h := hdd u₁ u₂
    ext k <;> cases k <;> simp [GlobalTheory.LatVac.locCo, h, e1, e2]
  have hconjSB : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (fun x => starRingEnd ℂ (φ x)) ∈ SB _ :=
    fun φ hφ => ⟨hφ.1.comp _, hφ.2.comp_left (map_zero _)⟩
  have hconj : ∀ (w : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v))
      (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (fun x => starRingEnd ℂ (schr ψv (w.1, -w.2) φ x)) = schr ψv w (fun x => starRingEnd ℂ (φ x)) := by
    intro w φ
    funext x
    simp only [GlobalTheory.WeilM.schr, map_mul, hstar]
    congr 2
    rw [dotProduct_neg, dotProduct_neg]
    ring
  have hbox : ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) (boxFun φ₁ φ₂)) Z =
        ψv (-pairM Z.1 (coX t 1 1 u₁ᵀ) + pairM Z.2 (coX t 1 1 u₂ᵀ)) *
          GlobalTheory.SwapSlice.sliceT ι (boxFun φ₁ φ₂) (Z.1 + coY σ G.V' G.W t 1 1 u₁ᵀ, Z.2 + coY σ G.V' G.W t 1 1 u₂ᵀ) := by
    intro φ₁ h₁ φ₂ h₂
    rw [hloc, GlobalTheory.BoxSpan.schr_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Prod.mk.eta]
    rw [GlobalTheory.SwapSlice.barL_apply, GlobalTheory.SwapSlice.barL_apply, hconj (GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ),
      Heisenberg₂ u₁ hu₁ hp₁ φ₁ h₁, Heisenberg₂ u₂ hu₂ hp₂ _ (hconjSB φ₂ h₂), map_mul, hstar, neg_neg, AddChar.map_add_eq_mul]
    ring
  let Lw : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ]
      ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    { toFun := schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂))
      map_add' := fun f g => by funext x; simp [schr, mul_add]
      map_smul' := fun c f => by funext x; simp [schr]; ring }
  let Z' : Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    (Z.1 + coY σ G.V' G.W t 1 1 u₁ᵀ, Z.2 + coY σ G.V' G.W t 1 1 u₂ᵀ)
  let c : ℂ := ψv (-pairM Z.1 (coX t 1 1 u₁ᵀ) + pairM Z.2 (coX t 1 1 u₂ᵀ))
  let Λ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj Z).comp ((GlobalTheory.SwapSlice.sliceT ι).comp Lw) - c • (LinearMap.proj Z').comp (GlobalTheory.SwapSlice.sliceT ι)
  have hΛ : ∀ Ψ, Λ Ψ = GlobalTheory.SwapSlice.sliceT ι (schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) Ψ) Z -
      c * GlobalTheory.SwapSlice.sliceT ι Ψ Z' := fun Ψ => rfl
  have h0 := GlobalTheory.BoxSpan.boxSpan_ker F v (Fin a' × Fin (a + a')) (Fin a' × Fin (a + a')) ψv hc
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v) Λ
    (fun φ₁ h₁ φ₂ h₂ => by rw [hΛ, hbox φ₁ h₁ φ₂ h₂, sub_self]) Φ hΦ
  rw [hΛ, sub_eq_zero] at h0
  exact h0

end GlobalTheory.SwapHeis
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.NormExact

theorem heisO_finPt_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Reads ψ θ hS hT cc δ r G f → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
    Reads ψ θ hS hT cc δ r (U D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G) (heisO ψ S T (finPt hS hT r z) f) := by
  intro D ψ θ S T a d hS hT cc δ r hs G f hf z
  subst hS hT
  have hc := hs.crv
  have hr := hs.scale
  have hr0 : r ≠ 0 := IsScale.ne_zero hc.1.1 hr
  rw [reads_iff hc hr] at hf ⊢
  refine ⟨GlobalTheory.TwistFactorCompare.isTheta_heisO hs.std hf.1 _, fun w hw => ?_⟩
  set X : VC D S.rank T.rank := fun τ i j => embT D τ (r⁻¹ * z i j) with hXdef
  have hX : (fun τ a b => -(((GlobalTheory.FockPos.frAt (1 : GL (Fin T.rank) D.host.E) τ)⁻¹ *
      Matrix.of (GlobalTheory.VacUnique.infRat S T (Matrix.of fun i j => -(r⁻¹ * z i j)) τ) *
      GlobalTheory.FockPos.frAt (1 : GL (Fin S.rank) D.host.E) τ) a b)) = X := by
    funext τ a b
    have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
      Matrix.map_one _ (map_zero _) (map_one _)
    simp only [e, inv_one, Matrix.one_mul, Matrix.mul_one]
    show -(embT D τ (-(r⁻¹ * z a b))) = embT D τ (r⁻¹ * z a b)
    rw [map_neg, neg_neg]
  have h := GlobalTheory.MovedTrans.heisO_finRat_real ψ θ S T 1 1 (by simp [Formalism.UG.cT_one, hs.gS])
    (by simp [Formalism.UG.cT_one, hs.gT]) hs.std hs.inf f hf.1 (fun Z => G fun τ i j => δ * embT D τ r * Z τ i j) hf.2
    (Matrix.of fun i j => -(r⁻¹ * z i j)) _ hX.symm w hw
  have e1 : finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) r z =
      GlobalTheory.VacUnique.finRat S T (Matrix.of fun i j => -(r⁻¹ * z i j)) := rfl
  have hpt : pt D (tor0 D cc δ) δ z = fun τ i j => δ * embT D τ r * X τ i j := by
    funext τ i j
    show δ * embT D τ (z i j) = δ * embT D τ r * embT D τ (r⁻¹ * z i j)
    rw [mul_assoc, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
  rw [e1, h, hpt]
  simp only [U]
  rw [Hf_scale hc hr, Hf_scale hc hr]
  have hY : ((fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j) + fun τ i j => δ * embT D τ r * X τ i j) =
      fun τ i j => δ * embT D τ r * (GlobalTheory.FockPos.zCo θ 1 1 w + X) τ i j := by
    funext τ i j
    simp only [Pi.add_apply]
    ring
  rw [hY]

end GlobalTheory.NormExact
end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isFockVacuum_of_readsGaussianEntire : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f := by
  first | exact @GlobalTheory.NormExact.reads_isFockVacAt | exact GlobalTheory.NormExact.reads_isFockVacAt | (intros; apply GlobalTheory.NormExact.reads_isFockVacAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

namespace GlobalTheory.BotPointDict

theorem chr_at_finIdl : ∀ {D : D7} (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    ∀ x y, IsFinIdl x y → ((c x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) :=
  fun c χ h x y hxy => GlobalTheory.FinIdlRead.chr_finIdl c χ h x y hxy

end GlobalTheory.BotPointDict
end

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.heckeCharacter_finiteIdele_value_eq : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq ν χ → ∀ x y, IsFinIdl x y →
  ((ν x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.FinIdlRead.chr_finIdl | exact GlobalTheory.FinIdlRead.chr_finIdl | (intros; apply GlobalTheory.FinIdlRead.chr_finIdl <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockVector_minorProduct_origin_eq_periods_jet : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ (n : D.what₂.Tau → ℕ) (t : Tup D a d n),
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f
        (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hT.symm k.2.1, Fin.cast hS.symm k.2.2) : FVar D T.rank S.rank))
          (minorPol D t)) 0 =
      (∏ τ, period D δ r τ ^ (a * n τ)) * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D t) G := by
  first | exact @GlobalTheory.NormExact.fock_minorPol_zero | exact GlobalTheory.NormExact.fock_minorPol_zero | (intros; apply GlobalTheory.NormExact.fock_minorPol_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)


theorem _root_.GlobalTheory.T.base_place_character_factor : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ),
    ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 →
    ∃ (b : D.what₂.LL) (g g' : 𝓞 D.what₂.LL), GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      g ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      g' ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      ((chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v)) z) =
        D.what₂.embLL (b * ((g : D.what₂.LL) / (g' : D.what₂.LL))) * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) := by
  first | exact @GlobalTheory.SqStepArith.base_place_factor_zero | exact GlobalTheory.SqStepArith.base_place_factor_zero | (intros; apply GlobalTheory.SqStepArith.base_place_factor_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)


theorem _root_.GlobalTheory.T.gaussSum_stepCharacter_twistPlace_dvd : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (ψ : AddChar (AF D.host.F) ℂ), PsiUnr ψ v →
      GlobalTheory.AdelicU.splitPrime τ ∈ locPl G t → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) = 1 →
      ∃ g : 𝓞 D.what₂.LL, D.what₂.embLL (g : D.what₂.LL) = gauss ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) ∧
        g ∣ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.what₂.LL) := by
  first | exact @GlobalTheory.TwistGaussInt.gauss_dvd | exact GlobalTheory.TwistGaussInt.gauss_dvd | (intros; apply GlobalTheory.TwistGaussInt.gauss_dvd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)


theorem _root_.GlobalTheory.T.stepCharacter_uniformiserValue_unit_away_twist : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ twPl G t →
      ∃ x : D.what₂.LL, D.what₂.embLL x = ((chrW (GlobalTheory.SqStep.chs G i j t).ν τ (unifAt v) : ℂˣ) : ℂ) ∧
        GlobalTheory.Square.IsAwayUnit (Qn G t) x := by
  first | exact @GlobalTheory.TwistStepVal.step_val | exact GlobalTheory.TwistStepVal.step_val | (intros; apply GlobalTheory.TwistStepVal.step_val <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)


theorem _root_.GlobalTheory.T.twistPlace_stepCharacter_conductorExponent_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ Lc.Q t → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) = 1 := by
  first | exact @GlobalTheory.TwistCond.condExp_twist_eq_one | exact GlobalTheory.TwistCond.condExp_twist_eq_one | (intros; apply GlobalTheory.TwistCond.condExp_twist_eq_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.TriMove in
theorem GlobalTheory.TriMove.transport_bottom : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (W : G.Weil) (i j : Fin D.R.m) {A A' WW B B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T B B' WW₁),
  IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ Y' : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j 0 0 Y' ∧ ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Y'.IsConst W.ψ W.θ c := by
  intro D T Lc sc G W i j A A' WW B B' WW₁ X Y hX hY
  obtain ⟨hp, hq, rX1, negRightMulLetterShift, nX1, nX2, nX3, isX⟩ := GlobalTheory.SqTower.IsBottomTri.isStageC hX
  obtain ⟨-, -, rY1, rY2, nY1, nY2, nY3, isY⟩ := hY
  have e1 : B.rank = A.rank := by omega
  have e2 : B'.rank = A'.rank := by omega
  have e3 : WW₁.rank = WW.rank := by rw [← isY.rank, ← isX.rank, e1, e2]
  obtain ⟨IA⟩ := GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank e1 nY1 nX1
  obtain ⟨IA'⟩ := GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank e2 nY2 nX2
  obtain ⟨IW⟩ := GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank e3 nY3 nX3
  refine ⟨triMove IA IA' IW Y, ⟨hp, hq, rX1, negRightMulLetterShift, nX1, nX2, nX3, ?_⟩,
    fun c hc => GlobalTheory.T.isConst_seesawTriple_transport_isometries IA IA' IW Y W.ψ W.θ isY.isVac.2.inf c hc⟩
  exact
    { rank := isX.rank
      rigA := GlobalTheory.T.isometryMovedRigging_is IA _ isY.rigA
      rigA' := GlobalTheory.T.isometryMovedRigging_is IA' _ isY.rigA'
      rigW := GlobalTheory.T.isometryMovedRigging_is IW _ isY.rigW
      weil := fun t => GlobalTheory.T.isWeilDatumSignedHomPair_transport_isometries W.ψ true IA IW _ _ (Y.ω t) (isY.weil t)
      weil' := fun t => GlobalTheory.T.isWeilDatumSignedHomPair_transport_isometries W.ψ false IA' IW _ _ (Y.ω' t) (isY.weil' t)
      isVac := GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices W.ψ W.θ true IA IW Y.rA.s Y.rW.s Y.rA.Λ Y.rW.Λ Y.vac isY.isVac
      isVac' := GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices W.ψ W.θ false IA' IW Y.rA'.s Y.rW.s Y.rA'.Λ Y.rW.Λ Y.vac' isY.isVac'
      idem := isY.idem
      expo := isY.expo
      fst := fun t => by
        have h5 := GlobalTheory.T.thetaAtIdempotent_hermitianHomIsometry_transport W.ψ true IA IW (Y.e t) Y.rA.Λ Y.rW.Λ Y.vac _ (Y.f t) (isY.fst t)
        rw [← GlobalTheory.T.standardPairFirstMemberHalf_isometry_moved] at h5
        exact h5
      snd := fun t => by
        have h5 := GlobalTheory.T.thetaAtIdempotent_hermitianHomIsometry_transport W.ψ false IA' IW _ Y.rA'.Λ Y.rW.Λ Y.vac' _ (Y.f' t) (isY.snd t)
        rw [← GlobalTheory.T.standardPairSecondMemberHalf_isometry_moved, e1] at h5
        exact h5
      meas := GlobalTheory.T.haar_fundamentalDomain_map_isometry_conj IA Y.m Y.fd isY.meas
      meas' := GlobalTheory.T.haar_fundamentalDomain_map_isometry_conj IA' Y.m' Y.fd' isY.meas' }
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

theorem _root_.GlobalTheory.T.frameConj_standardRational_mem_unitaryRational : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ γ ∈ GlobalTheory.NormSum.ratG D V.rank, ∃ q ∈ ratFin V, finG V q = GlobalTheory.FrameTransport.frConj fr γ.1 := by
  first | exact @GlobalTheory.FrameTransport.frConj_ratG | exact GlobalTheory.FrameTransport.frConj_ratG | (intros; apply GlobalTheory.FrameTransport.frConj_ratG <;> assumption)
end
