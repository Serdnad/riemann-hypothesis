module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle314
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceUnitaryAdelicHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalFieldData
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.linear_bar_model_local_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∀ S : (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ) →
        ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ,
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v)) →
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      ∀ Φ' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ, S (c • Φ + Φ') = c • S Φ + S Φ') →
    (∀ u, At (evFin F v) u → ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (actB (cA σ) w u)) (S Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (S Φ) = c • (GlobalTheory.SwapSlice.sliceT ι Φ ∘ GlobalTheory.SwapSlice.swapNeg) := by
  first | exact @GlobalTheory.SwapSchur.sliceT_swap_eq_smul | exact GlobalTheory.SwapSchur.sliceT_swap_eq_smul | (intros; apply GlobalTheory.SwapSchur.sliceT_swap_eq_smul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel


theorem _root_.GlobalTheory.T.datumPhiA_splitPlace_transport_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E) (hw : w ∈ locPl G t) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ = w → ∀ n : ℕ,
    ∃ (μ : @Measure (GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)) Units.instMeasurableSpace)
      (_ : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace μ)
      (σ' : Fin (spW G i j).rank ⊕ Fin (spW₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)),
      (∀ (Ψ : Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) Z,
        phiA (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) (stdSplit ((locGrid G t w).rank_square i j))
          ((locGrid G t w).nu i j) (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ψ (trA t hv e Z) =
        phiA μ σ' (((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n
          (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) (fun Y => Ψ (trB t hv e Y)) Z) ∧
      ∀ Ξ, HasDepth (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) Ξ →
        ∃ Ξ', HasDepth (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ξ' ∧ ∀ Y, Ξ' (trB t hv e Y) = Ξ Y := by
  first | exact @GlobalTheory.PureMatch.phiA_transport_split_place | exact GlobalTheory.PureMatch.phiA_transport_split_place | (intros; apply GlobalTheory.PureMatch.phiA_transport_split_place <;> assumption)
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


theorem _root_.GlobalTheory.T.twistPlace_stepFactor_inverse_awayUnit : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ (GlobalTheory.SqStep.chs G i j t).T →
    v.1 ∉ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ), ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 → ∃ b : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      D.what₂.embLL b * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) = 1 := by
  first | exact @GlobalTheory.SqTwist.twist_factor | exact GlobalTheory.SqTwist.twist_factor | (intros; apply GlobalTheory.SqTwist.twist_factor <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

theorem _root_.GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.FrameTransport.Cong.conj_mem_congLev | exact GlobalTheory.FrameTransport.Cong.conj_mem_congLev | (intros; apply GlobalTheory.FrameTransport.Cong.conj_mem_congLev <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ThK.ConeEulerChr

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_liftV (a : ∀ v : Pl F, Fv F v) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    Tendsto (fun v => GlobalTheory.LatVac.liftV v (a v)) cofinite (𝓝 0) := by
  have hf : ∀ v w : Pl F, evalV F w (singleFin v (a v)) ∈ w.adicCompletionIntegers F := fun v w => by
    by_cases h : w = v
    · subst h; rw [evalV_singleFin_self]; exact ha w
    · rw [evalV_singleFin_ne h]; exact zero_mem _
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := cofinite)).continuous
  have ht : Tendsto (fun v : Pl F => fun w : HeightOneSpectrum (𝓞 F) =>
      (⟨evalV F w (singleFin v (a v)), hf v w⟩ : (w.adicCompletionIntegers F : Set (w.adicCompletion F)))) cofinite
      (𝓝 fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩) := by
    refine tendsto_pi_nhds.2 fun w => tendsto_subtype_rng.2 ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cofinite_ne w] with v hv
    exact (evalV_singleFin_ne (Ne.symm hv) _).symm
  have h2 : Tendsto (fun v : Pl F => singleFin v (a v)) cofinite (𝓝 (0 : Af F)) := (hc.tendsto _).comp ht
  have hp : Continuous fun β : Af F => pairA F 0 β := continuous_const.prodMk continuous_id
  exact (hp.tendsto 0).comp h2

theorem exists_coords {v : Pl F} {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v, (∀ i, a i ∈ v.adicCompletionIntegers F) ∧
      y = ∑ i, a i ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
  refine intLoc_induction (p := fun y => ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v,
    (∀ i, a i ∈ v.adicCompletionIntegers F) ∧ y = ∑ i, a i ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E))
    (fun a ha x => ?_) ⟨0, fun _ => zero_mem _, by simp⟩ ?_ ?_ hy
  · refine ⟨fun i => (RingOfIntegers.basis E).repr x i • a, fun i => zsmul_mem ha _, ?_⟩
    have hx : (x : E) = ∑ i, (RingOfIntegers.basis E).repr x i • ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr x]
      simp
    rw [hx, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul _ _ _).symm
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨a + c, fun i => add_mem (ha i) (hc i), by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, fun i => neg_mem (ha i), by simp [TensorProduct.neg_tmul]⟩

theorem tendsto_zero_of_intLoc (x : Pl F → AE F E)
    (h : ∀ᶠ v in cofinite, At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v) :
    Tendsto x cofinite (𝓝 0) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have key : ∀ v : Pl F, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v,
      (∀ i, a i ∈ v.adicCompletionIntegers F) ∧ (At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v →
      x v = ∑ i, GlobalTheory.LatVac.liftV v (a i) • ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E))) := fun v => by
    by_cases hv : At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v
    · obtain ⟨a, ha, e⟩ := exists_coords hv.2
      obtain ⟨h1, h2⟩ := at_evFin_iff.1 hv.1
      refine ⟨a, ha, fun _ => GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_⟩

      · rw [h1, map_sum]
        exact (Finset.sum_eq_zero fun i _ => by
          rw [compInf_smul, show evInf F w (GlobalTheory.LatVac.liftV v (a i)) = 0 from rfl, zero_smul]).symm

      · rw [map_sum]
        by_cases hw : w = v
        · subst hw
          rw [e]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [compFin_smul, GlobalTheory.LatVac.evFin_liftV]
          change _ = a i • (evFin F w 1 ⊗ₜ[F] _)
          rw [map_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rfl
        · rw [h2 w hw]
          exact (Finset.sum_eq_zero fun i _ => by
            rw [compFin_smul, show evFin F w (GlobalTheory.LatVac.liftV v (a i)) = 0 from evalV_singleFin_ne hw _,
              zero_smul]).symm
    · exact ⟨0, fun _ => zero_mem _, fun h => absurd h hv⟩
  choose a ha e using key
  have ht : Tendsto (fun v => ∑ i, GlobalTheory.LatVac.liftV v (a v i) •
      ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) : AE F E)) cofinite
      (𝓝 (∑ i, (0 : AF F) • ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) : AE F E))) :=
    tendsto_finsetSum _ fun i _ => (tendsto_liftV (fun v => a v i) fun v => ha v i).smul_const _
  simp only [zero_smul, Finset.sum_const_zero] at ht
  refine ht.congr' ?_
  filter_upwards [h] with v hv using (e v hv).symm

theorem tendsto_one_of_unitsAt (m : Pl F → (AE F E)ˣ) (h : ∀ᶠ v in cofinite, m v ∈ unitsAt E v) :
    Tendsto m cofinite (𝓝 1) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have key : ∀ m : Pl F → (AE F E)ˣ, (∀ᶠ v in cofinite, m v ∈ unitsAt E v) →
      Tendsto (fun v => (m v : AE F E)) cofinite (𝓝 1) := fun m h => by
    have := (tendsto_zero_of_intLoc (fun v => (m v : AE F E) - 1) (h.mono fun v hv => ⟨hv.1, by
      rw [map_sub, map_one]; exact sub_mem (mem_unitsAt.1 hv).2.1 (one_mem _)⟩)).add_const 1
    simpa using this
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact (key m h).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp
    (key (fun v => (m v)⁻¹) (h.mono fun v hv => inv_mem hv)))

theorem eventually_chr_eq_one {ν : Chr F E} (hν : Continuous ν) (m : Pl F → (AE F E)ˣ)
    (h : ∀ᶠ v in cofinite, m v ∈ unitsAt E v) : ∀ᶠ v in cofinite, ν (m v) = 1 := by
  have key : ∀ v, ∃ n : ℕ, ‖(ν (m v) : ℂ) ^ n - 1‖ < 1 → ν (m v) = 1 := fun v => by
    by_contra hc
    push Not at hc
    exact (hc 0).2 (GlobalTheory.CharDualMat.circle_eq_one_of_pow_near _ fun n => (hc n).1)
  choose n hn using key
  have ht := tendsto_one_of_unitsAt (fun v => m v ^ n v) (h.mono fun v hv => pow_mem hv _)
  have hc : Continuous fun x : (AE F E)ˣ => ‖(ν x : ℂ) - 1‖ :=
    ((continuous_subtype_val.comp hν).sub continuous_const).norm
  have h1 := ((hc.tendsto 1).comp ht).eventually (gt_mem_nhds (show ‖(ν 1 : ℂ) - 1‖ < 1 by simp))
  filter_upwards [h1] with v hv
  exact hn v (by simpa using hv)

theorem cutIdele_eq (S : Finset (Pl F)) (l : (AE F E)ˣ) :
    GlobalTheory.Doubling.cutIdele S l = unitArch F E l * ∏ v ∈ S, unitAt E v l := by
  have h1 : (eInf F).1 = 1 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by
    rw [map_one]; exact evI_realAd_one)
  have ha : GlobalTheory.Doubling.cutIdele ∅ l = unitArch F E l := by
    refine GlobalTheory.Doubling.idele_ext (fun w => ?_) fun v => ?_
    · rw [GlobalTheory.Doubling.unitInf_cutIdele]
      refine Units.ext ?_
      change compInf F E w l = compInf F E w (eInf F • (l : AE F E) + (1 - eInf F) • 1)
      have h : evInf F w (eInf F) = 1 := congrFun h1 w
      rw [map_add (f := _), compInf_smul, compInf_smul, map_sub, map_one, h, sub_self, zero_smul, one_smul, add_zero]
    · rw [GlobalTheory.Doubling.unitFin_cutIdele_of_notMem _ (Finset.notMem_empty v)]
      have := at_evI_iff.1 (unitArch_mem l) v
      rw [map_sub, map_one, sub_eq_zero] at this
      exact Units.ext this.symm
  rw [← ha, GlobalTheory.Doubling.cutIdele, GlobalTheory.Doubling.cutIdele, Finset.prod_empty, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← ideleAt_unitFin (unitAt_mem v l)]
  exact congrArg _ (Units.ext (compFin_unitAt_self v l).symm)

theorem chr_abs_eq_finprod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : Chr F E), Continuous ν → ∀ (l : (AE F E)ˣ) (z : ℕ),
    (Function.mulSupport fun v : Pl F => (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z).Finite ∧
    (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z = (ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z *
      ∏ᶠ v : Pl F, (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z := by
  intro F E _ _ _ _ _ ν hν l z
  have hu := eventually_unitAt_mem_unitsAt F E l
  have hfin : (Function.mulSupport fun v : Pl F =>
      (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z).Finite := by
    refine (eventually_cofinite.1 (hu.and (eventually_chr_eq_one hν _ hu))).subset fun v hv h => hv ?_
    simp only [h.2, absE_of_mem_unitsAt h.1]
    simp
  refine ⟨hfin, ?_⟩
  let χ : (AE F E)ˣ →* ℂ :=
    { toFun := fun x => (ν x : ℂ) * ((absE F E x : ℝ) : ℂ) ^ z
      map_one' := by simp
      map_mul' := fun x y => by simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul]; ring }
  have hχ : Continuous χ := (continuous_subtype_val.comp hν).mul
    ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow z)
  refine tendsto_nhds_unique ((hχ.tendsto l).comp (GlobalTheory.Doubling.tendsto_cutIdele l)) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop hfin.toFinset] with S hS
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin hS, Function.comp_apply, cutIdele_eq, map_mul, map_prod]
  rfl

end GlobalTheory.ThK.ConeEulerChr

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.tensorHermitianForm_inertPoint_eq_localForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin m) (Fin m) (w.adicCompletion E))
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      Aᵀ * JA.map (algebraMap E (w.adicCompletion E)) * A.map σL = 1 →
      Bmᵀ * JB.map (algebraMap E (w.adicCompletion E)) * Bm.map σL = δ • 1 →
      ∀ x y, hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
        ptAt hw h (GlobalTheory.Hk3.locH σL δ (1 : GL (Fin m) (w.adicCompletion E)) (1 : GL (Fin n) (w.adicCompletion E)) x y) := by
  first | exact @GlobalTheory.InertTens.hTens_kap_eq_locH | exact GlobalTheory.InertTens.hTens_kap_eq_locH | (intros; apply GlobalTheory.InertTens.hTens_kap_eq_locH <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_inertPlace_unitary_adelicHom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {n : ℕ} (X : Spc F E n) (P : GL (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      (P : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) *
        (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = δ • 1 →
      ∀ {Γ : Type} [Group Γ] (φ : Γ →* GL (Fin n) (w.adicCompletion E)),
        (∀ g, (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = 1) →
        ∃ ι : Γ →* UA σ X.J, (∀ g, ι g ∈ UAt σ X (evFin F v)) ∧
          (∀ g, (mat (ι g)).map (locW h) = ((P * φ g * P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
          (IsFrameAt w X.L P → ∀ g, φ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (w.adicCompletion E)) → ι g ∈ GlobalTheory.InertSph.KAt σ X v) := by
  first | exact @GlobalTheory.InertPlace.exists_hom_inert | exact GlobalTheory.InertPlace.exists_hom_inert | (intros; apply GlobalTheory.InertPlace.exists_hom_inert <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_action_on_tensorCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  first | exact @GlobalTheory.InertCoordAct.act_kap | exact GlobalTheory.InertCoordAct.act_kap | (intros; apply GlobalTheory.InertCoordAct.act_kap <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlacePoint_supported_and_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  first | exact @GlobalTheory.InertCoord.kap_at_and_onto | exact GlobalTheory.InertCoord.kap_at_and_onto | (intros; apply GlobalTheory.InertCoord.kap_at_and_onto <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.finite_covolume_GL_adelicTensor_rationalTimesExpInt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ) [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (ν : Measure (GL (Fin k) (AF F ⊗[F] E))) (D : Set (GL (Fin k) (AF F ⊗[F] E))), ν.IsHaarMeasure → IsFundamentalDomain (GlobalTheory.GLOneVol.latR F E k) D ν → ν D ≠ ⊤ := by
  first | exact @GlobalTheory.GLOneVol.finvol_tens | exact GlobalTheory.GLOneVol.finvol_tens | (intros; apply GlobalTheory.GLOneVol.finvol_tens <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.log_tensorIdeleAbs_det_expScalarCentre_eq_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ), 1 ≤ k → ∃ a : ℝ, a ≠ 0 ∧ ∀ t : ℝ, Real.log ((absE F E (Matrix.GeneralLinearGroup.det (GlobalTheory.GLOneVol.cR F E k t)) : ℝ≥0) : ℝ) = a * t := by
  first | exact @GlobalTheory.GLOneVol.log_absE_det_cR | exact GlobalTheory.GLOneVol.log_absE_det_cR | (intros; apply GlobalTheory.GLOneVol.log_absE_det_cR <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_inertPlace_localField_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v),
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (ψL : AddChar (w.adicCompletion E) ℂ),
      IsConjAt σ h σL ∧ Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
      (∀ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z → ψL z = 1) ∧
      (∃ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
      ∀ z, ψL ((z + σL z) / 2) = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (-1 * ptAt hw h z)) := by
  first | exact @GlobalTheory.InertPsi.exists_field_data | exact GlobalTheory.InertPsi.exists_field_data | (intros; apply GlobalTheory.InertPsi.exists_field_data <;> assumption)
end
