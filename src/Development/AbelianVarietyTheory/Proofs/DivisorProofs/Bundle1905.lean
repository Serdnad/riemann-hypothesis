module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle711
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

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

noncomputable section

namespace GlobalTheory.LatVac

theorem restrict_liftV_mem_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (fun t : κ → Fv F v => Φ (fun i => GlobalTheory.LatVac.liftV v (t i))) ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ κ _ v Φ hΦ
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    let s : (κ → Fv F v) → (κ → Af F) := fun t i => GlobalTheory.AdelicU.singleFin v (t i)
    have hs : Continuous s := continuous_pi fun i => (GlobalTheory.AdelicU.continuous_singleFin v).comp (continuous_apply i)
    have hinv : Function.LeftInverse (fun x : κ → Af F => fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (x i)) s :=
      fun t => funext fun i => GlobalTheory.AdelicU.evalV_singleFin_self v (t i)
    have hev : Continuous (fun x : κ → Af F => fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (x i)) :=
      continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
    have hce : Topology.IsClosedEmbedding s := hinv.isClosedEmbedding hev hs
    have hmem : g ∘ s ∈ GlobalTheory.WeilM.SB (κ → Fv F v) :=
      ⟨hg.1.comp_continuous hs, hg.2.comp_isClosedEmbedding hce⟩
    have e : (fun t : κ → Fv F v => GlobalTheory.WeilM.pureA F (⇑f) g (fun i => GlobalTheory.LatVac.liftV v (t i))) =
        f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F 0) • (g ∘ s) := by
      funext t
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ hmem
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

end GlobalTheory.LatVac

end
end

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

noncomputable section

namespace GlobalTheory.SplitAdeleTrace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul_comp (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]


omit [NumberField F] [NumberField E] in
theorem trace_baseChange_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem add_conj_eq_trace {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) :
    x + σ x = algebraMap F E (Algebra.trace F E x) := by
  classical
  have hc := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (by ext y; simp [GlobalTheory.AdelicU.cm_conj_conj h])
    (by ext y; simp [GlobalTheory.AdelicU.cm_conj_conj h])
  have hs : (1 : E ≃ₐ[F] E) ≠ s := by
    intro h1
    obtain ⟨y, hy⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne h
    exact hy (DFunLike.congr_fun h1 y).symm
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hs, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h.2.2.1]
  rw [trace_eq_sum_automorphisms, hu, Finset.sum_pair hs]
  rfl

theorem trace_at_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v)
    (z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z →
    Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z =
      GlobalTheory.LatVac.liftV v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ z + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) z) := by
  intro F E _ _ _ _ _ σ hcm v τ z hz
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  set l : AF F := GlobalTheory.LatVac.liftV v 1 with hl
  have hz1 : z = l • z := by
    have h0 := hz (1 - l) (by rw [map_sub, map_one, hl, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    exact h0
  have hpiW : ∀ (t : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (l • w) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t w := by
    intro t w
    rw [Algebra.smul_def, map_mul]
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (algebraMap (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) l) = 1 := by
      change evFin F v l * t 1 = 1
      rw [hl, GlobalTheory.LatVac.evFin_liftV, map_one, one_mul]
    rw [this, one_mul]
  have key : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (l • w) =
      GlobalTheory.LatVac.liftV v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ w + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, ← map_add (f := _)]; congr 1; simp only [map_add (f := _)]; ring
    | tmul b e =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, trace_baseChange_tmul, mul_assoc, liftV_one_mul_comp, map_mul,
        AlgHom.commutes]
      congr 1
      change evFin F v b * algebraMap F (Fv F v) (Algebra.trace F E e) = evFin F v b * τ e + evFin F v b * τ (σ e)
      rw [← mul_add, ← map_add (f := _), add_conj_eq_trace hcm, AlgHom.commutes]
  rw [hz1, key, hpiW, hpiW]

end GlobalTheory.SplitAdeleTrace
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SplitPlaceLat

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tmul_smul_gen {n d : ℕ} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) (o : 𝓞 E) (c : AF F) (x : Fin n → E)
    (y : Fin d → E) :
    ((GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E) : AE F E) • (c • incM F (Matrix.vecMulVec x y))) =
      (GlobalTheory.LatVac.liftV v a * c) • incM F (Matrix.vecMulVec (o • x) y) := by
  ext i j
  simp [incM, inclR, Matrix.vecMulVec_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_assoc]

theorem tmul_smul_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    ∀ γ ∈ latAtV X Y v, ((GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E) : AE F E) • γ) ∈ latAtV X Y v := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, hci, x, hx, y, hy, rfl⟩ := hz
    rw [tmul_smul_gen]
    refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * c, ?_, ?_, o • x, X.L.smul_mem o hx, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u c, hc u hu, mul_zero]
    · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
      exact mul_mem ha hci
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_lift {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    ∃ e : AE F E, compFin F E v e = y ∧ ∀ γ ∈ latAtV X Y v, e • γ ∈ latAtV X Y v := by
  refine intLoc_induction (p := fun y => ∃ e : AE F E, compFin F E v e = y ∧ ∀ γ ∈ latAtV X Y v, e • γ ∈ latAtV X Y v)
    ?_ ?_ ?_ ?_ hy
  · intro a ha o
    refine ⟨GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E), ?_, tmul_smul_mem X Y v ha o⟩
    simp [compFin, GlobalTheory.LatVac.evFin_liftV]
  · exact ⟨0, map_zero _, fun γ _ => by rw [zero_smul]; exact zero_mem _⟩
  · intro y z hy hz
    obtain ⟨e, he, he'⟩ := hy
    obtain ⟨f, hf, hf'⟩ := hz
    exact ⟨e + f, by rw [map_add (f := _), he, hf], fun γ hγ => by rw [add_smul]; exact add_mem (he' γ hγ) (hf' γ hγ)⟩
  · intro y hy
    obtain ⟨e, he, he'⟩ := hy
    exact ⟨-e, by rw [map_neg, he], fun γ hγ => by rw [neg_smul]; exact neg_mem (he' γ hγ)⟩

theorem map_piW_smul {n d : ℕ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (e : AE F E)
    (γ : Matrix (Fin n) (Fin d) (AE F E)) : (e • γ).map (piW t) = piW t e • γ.map (piW t) := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, map_mul]

end GlobalTheory.SplitPlaceLat

namespace GlobalTheory.SplitPlaceLat

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem latAtV_eq_add_parts : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γA ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γB ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
        γ = γA + γB ∧ γA.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
          γB.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ γ hγ
  have h := hTr.base.cm
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitPlaceLat.exists_lift {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁
    (splitIdem_mem h Bs.τ₁)
  have p1 : piW Bs.τ₁ e = 1 := by
    change splitProj Bs.τ₁ (compFin _ _ _ e) = 1
    rw [he]; exact splitProj_splitIdem h _
  have p2 : piW (Bs.τ₁.comp D.sp.cm.sig) e = 0 := by
    change splitProj (Bs.τ₁.comp D.sp.cm.sig) (compFin _ _ _ e) = 0
    rw [he]; exact splitProj_comp_splitIdem h _
  refine ⟨γ - e • γ, sub_mem hγ (he' γ hγ), e • γ, he' γ hγ, (sub_add_cancel _ _).symm, ?_, ?_⟩
  · ext i j
    simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, map_sub, map_mul, p1]
  · rw [GlobalTheory.SplitPlaceLat.map_piW_smul, p2, zero_smul]

end GlobalTheory.SplitPlaceLat
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.PsiNontriv

variable {F : Type} [Field F] [NumberField F]

theorem trace_re (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  first
  | exact @_root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re
  | exact _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re
  | (apply _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re ..)

theorem trace_mixedEmbedding (x : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [trace_re, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfinitePlace.sum_eq_sum_add_sum]
  simp only [Algebra.trace_complex_apply, mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex, Algebra.trace_self_apply]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.embedding_of_isReal_apply w.2,
      Complex.ofReal_re]
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isComplex]
    push_cast
    rfl

end GlobalTheory.PsiNontriv

namespace GlobalTheory.PsiNontriv

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA_zero (a : Ainf F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (pairA F a 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · change u.1 * a = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem isStd_fin_rat {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  have hev : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (pairA F (algebraMap F (Ainf F) (-x)) 0) = mixedEmbedding F (-x) :=
    (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm
  rw [e, AddChar.map_add_eq_mul, hψ.2.1, one_mul, hψ.2.2 _ (at_pairA_zero _), hev, map_neg, map_neg,
    trace_mixedEmbedding]
  congr 1
  push_cast
  ring

theorem psiAt_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.psiAt ψ v ≠ 1 := by
  intro F _ _ ψ hψ v h1
  set c := FractionalIdeal.count F v (codiff F) with hc
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set x : Fv F v := algebraMap F (Fv F v) (π ^ (c - 1)) with hx
  have hmem : GlobalTheory.AdelicU.singleFin v x ∈ adelicIdeal (codiff F) := by
    rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (isStd_fin_rat hψ)]
    intro α hα
    have e : α * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (α v * x) := by
      apply GlobalTheory.AdelicU.af_ext
      intro u
      by_cases hu : u = v
      · subst hu
        rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
        rfl
      · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
    rw [e]
    have := DFunLike.congr_fun h1 (α v * x)
    rw [AddChar.one_apply] at this
    exact this
  have h2 := (mem_adelicIdeal_iff codiff_ne_zero).1 hmem v
  rw [show (GlobalTheory.AdelicU.singleFin v x) v = x from GlobalTheory.AdelicU.evalV_singleFin_self v x, hx, valued_algebraMap,
    map_zpow₀, hπ, ← WithZero.exp_zsmul, WithZero.exp_le_exp, smul_eq_mul] at h2
  omega

end GlobalTheory.PsiNontriv
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour

variable {F : Type} [Field F] [NumberField F]

def IsSelfDualFor {v : Pl (F := F)} (χ : AddChar (Fv F v) ℂ) (ν : Measure (Fv F v)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∀ f ∈ SB (Fv F v), ∫ y, (∫ x, f x * χ (x * y) ∂ν) ∂ν = f 0

open Classical in
def measV (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) : Measure (Fv F v) :=
  if h : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν then h.choose else 0

def fourV (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) {κ : Type} [Fintype κ] (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) : ℂ :=
  ∫ x, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) ∂(Measure.pi fun _ : κ => measV ψ v)


open Classical in
variable (F) in
def measI (κ : Type) [Fintype κ] : Measure (κ → mixedEmbedding.mixedSpace F) :=
  Measure.pi fun _ : κ => (Measure.pi fun _ : {w : InfinitePlace F // w.IsReal} => (volume : Measure ℝ)).prod
    (Measure.pi fun _ : {w : InfinitePlace F // w.IsComplex} => (volume : Measure ℂ))

def eInf {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ))

end GlobalTheory.WeylFour

end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SwapAtSplit

open scoped TensorProduct
open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right sigR_tensAt)

theorem exists_swap_elt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∃ f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f ∧ f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧
      f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧ piW t f = 1 ∧ piW (t.comp σ) f = -1 := by
  intro F E _ _ _ _ _ σ h v t
  set y : Fv F v ⊗[F] E := (splitAlgEquiv h t).symm (1, -1) with hy
  have hQ : algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) = tensAt E v 1 := rfl
  have hpi : ∀ τ : E →ₐ[F] Fv F v, piW τ (tensAt E v y) = splitProj τ y := fun τ => by
    change splitProj τ (compFin F E v (tensAt E v y)) = _
    rw [compFin_tensAt]
  refine ⟨tensAt E v y, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
    have e : compFin F E v (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) = 1 := by
      change GlobalTheory.AdelicU.evFin F v (GlobalTheory.LatVac.liftV v 1) ⊗ₜ[F] (1 : E) = 1
      rw [GlobalTheory.LatVac.evFin_liftV]; rfl
    rw [e, mul_one]
  · rw [hQ, tensAt_mul_right, compFin_tensAt]
    congr 1
    exact split_ext h t (by simp [hy]) (by simp [hy])
  · have hc : cA σ (tensAt E v y) = tensAt E v (sigR (Fv F v) σ y) := sigR_tensAt v σ y
    rw [hc, hQ, tensAt_mul_right, compFin_tensAt, ← map_neg]
    congr 1
    refine split_ext h t ?_ ?_
    · rw [map_mul, ← splitProj_comp, map_neg, map_one]; simp [hy]
    · rw [map_mul, splitProj_comp_sigR h, map_neg, map_one]; simp [hy]
  · rw [hpi]; simp [hy]
  · rw [hpi]; simp [hy]

end GlobalTheory.SwapAtSplit
end
end
