module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeRatioPosOfPublished
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.InputsHecke
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle162
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem integrable_quotHeight_pow_mul_norm_of_rapidDec : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (u : GA D A → ℂ), GlobalTheory.Grow.RapidDec A u → ∀ N : ℕ, Integrable (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) (autMeasure A m) := by
  intro D A m hm u hu N
  haveI := hm
  have : BorelSpace (GA D A) := ⟨rfl⟩
  set f : GA D A → ℝ := fun g => GlobalTheory.Grow.quotHeight A g ^ N * ‖u g‖ with hf
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) f := fun γ hγ g => by
    simp only [f, GlobalTheory.Grow.quotHeight_left A hγ, hu.left hγ]
  have hfc : Continuous f := ((GlobalTheory.Grow.continuous_quotHeight A).pow N).mul hu.continuous.norm
  have e : (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) = GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f := rfl
  rw [e]
  have hfd : IsFundamentalDomain (GQ A) (GlobalTheory.AutomorphicL2Unitary.stdDom (GQ A)) m := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ m
  haveI : IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.autMeasure A m) := ⟨by
    rw [GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hfd]
    exact GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol A m _ hm hfd⟩
  obtain ⟨C, hC⟩ := hu.decay N
  have hmeas : Measurable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f) := by
    refine measurable_from_quotient.2 ?_
    have h' : (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f ∘ Quotient.mk'') = f := funext fun g => hL.descend_mk g
    rw [h']
    exact hfc.measurable
  refine Integrable.of_bound hmeas.aestronglyMeasurable C (.of_forall fun q => ?_)
  have hq : 0 ≤ GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f q :=
    mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos A _).le N) (norm_nonneg _)
  rw [Real.norm_of_nonneg hq]
  show GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖ ≤ C
  rw [mul_comm]
  exact hC _

end GlobalTheory.Core.Rk.IP
end

section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One


open Formalism.L2.SG.NGCut.CorankRelation in
theorem corankOne_isEquivalence_nonzeroGram_terms : CorankOneIsEquivalenceOnRow := by
  intro D X Y u u' _hT
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t ∈ (Y.tO u u').nzSet, Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro t ht h
    apply ht
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]
  have hlat : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      Submodule.IsFullLattice D.host.E t.lam := fun t => ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      IsLift t.lam (lf D (X.Fu u)) := fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), IsLift t.lam t.frame :=
    fun t => t.rep.2.2.2.2.1
  refine ⟨fun t ht => ?_, fun t ht t' ht' hr h1 => ?_, fun t ht t' ht' t'' ht'' hr1 hr2 h1 h2 => ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨rfl, rfl⟩, mul_inv_cancel]
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t.frame 1 (hLF t) (hLt t) (hGv t ht)).2
      (Th_one _ _ _)
  · have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' ⊢
    rw [if_pos ⟨hlam, hlam'⟩] at h1'
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    have hth := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
    have hsym := Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
      (hGv t ht) (hGv t' ht') (frame_mem_iff t t') hth
    have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
    rw [hinv] at hsym
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' ht')).2 hsym
  · have hl1 : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl1' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl2 : t'.lam = t''.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have hl2' : t'.lam' = t''.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    have h2' : Formalism.L2.SG.TermOp.s0T t' t'' = 1 := h2
    show Formalism.L2.SG.TermOp.s0T t t'' = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' h2' ⊢
    rw [if_pos ⟨hl1, hl1'⟩] at h1'
    rw [if_pos ⟨hl2, hl2'⟩, ← hl1] at h2'
    rw [if_pos ⟨hl1.trans hl2, hl1'.trans hl2'⟩]
    have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
    have hth1 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hth2 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t''.frame _ (hLF t) hL'
      (hGv t' ht')).1 h2'
    have htr := Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹) (t''.lin * t'.lin⁻¹)
      (fun x hx => (frame_mem_iff t' t'' x).1 hx) hth1 hth2
    have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
    rw [hmul] at htr
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t''.frame _ (hLF t) (hLt t) (hGv t ht)).2 htr

end GlobalTheory.Core.One
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatAgree

open GlobalTheory.AdelicU GlobalTheory.LFun Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem valued_natCast_eq_one {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    Valued.v (N : v.adicCompletion K) = 1 := by
  have e : (N : v.adicCompletion K) = ((algebraMap R K (N : R) : K) : v.adicCompletion K) := by
    rw [map_natCast]; exact (map_natCast (algebraMap K (v.adicCompletion K)) N).symm
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hN ((v.intValuation_lt_one_iff_mem _).1 h))

theorem natCast_ne_zero_of {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    (N : v.adicCompletion K) ≠ 0 := fun h => by
  have := valued_natCast_eq_one (K := K) hN
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem inv_natCast_mem {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    (N : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one hN, inv_one]

theorem latLoc_le {L L' : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {N : ℕ}
    (hN : (N : 𝓞 F) ∉ v.asIdeal) (h : ∀ x ∈ L, (N : E) • x ∈ L') : latLoc F L v ≤ latLoc F L' v := by
  intro y hy
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  have hN0 := natCast_ne_zero_of (K := F) hN
  have e : (fun i => a ⊗ₜ[F] x i) = fun i => (a * (N : Fv F v)⁻¹) ⊗ₜ[F] (((N : E) • x) i) := by
    funext i
    rw [Pi.smul_apply, show (N : E) • x i = (N : F) • x i by
      rw [Algebra.smul_def, Algebra.smul_def, map_natCast, map_natCast], TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, map_natCast]
    congr 1
    field_simp
  rw [e]
  exact tmul_mem_latLoc (mul_mem ha (inv_natCast_mem hN)) (h x hx)

theorem latAt_le {L L' : Submodule (𝓞 E) (Fin n → E)} {w : HeightOneSpectrum (𝓞 E)} {N : ℕ}
    (hN : (N : 𝓞 E) ∉ w.asIdeal) (h : ∀ x ∈ L, (N : E) • x ∈ L') : latAt w L ≤ latAt w L' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have hN0 := natCast_ne_zero_of (K := E) hN
  have hm : (⟨(N : w.adicCompletion E)⁻¹, inv_natCast_mem hN⟩ : Ov E w) •
      (fun i => algebraMap E (w.adicCompletion E) (((N : E) • x) i)) = fun i => algebraMap E (w.adicCompletion E) (x i) := by
    funext i
    change (N : w.adicCompletion E)⁻¹ * algebraMap E _ ((N : E) • x i) = _
    rw [smul_eq_mul, map_mul, map_natCast, inv_mul_cancel_left₀ hN0]
  change (fun i => algebraMap E (w.adicCompletion E) (x i)) ∈ latAt w L'
  rw [← hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h x hx, rfl⟩)

end GlobalTheory.LatAgree

namespace GlobalTheory.LatAgree

open GlobalTheory.AdelicU GlobalTheory.LFun Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem stabLoc_congr (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (hs : latLoc F L v = latLoc F L' v) : stabLoc σ J L v = stabLoc σ J L' v := by
  simp only [stabLoc, hs]

theorem isParamVec_congr {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    (hs : latLoc F L v = latLoc F L' v) (ha : latAt w L = latAt w L') {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GLoc σ J v) V) (x : V) (B : Multiset ℂˣ) :
    IsParamVec σ J L h ρ x B ↔ IsParamVec σ J L' h ρ x B := by
  have hst := stabLoc_congr σ J hs
  simp only [IsParamVec, IsSplitChart, IsInertChart, IsFrameAt, hst, ha]

theorem isParamFun_congr {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    {S : Set (HeightOneSpectrum (𝓞 F))} (hs : ∀ v ∉ S, latLoc F L v = latLoc F L' v)
    (ha : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → latAt w L = latAt w L')
    {V : Type} [AddCommGroup V] [Module ℂ V] (f : GAd σ J → V) (c : Fam E) :
    IsParamFun σ J L S f c ↔ IsParamFun σ J L' S f c := by
  unfold IsParamFun IsParamVecOff
  refine forall₂_congr fun v hv => forall₂_congr fun w h => ?_
  exact isParamVec_congr h (hs v hv) (ha w (h ▸ hv)) _ _ _

theorem exists_under_eq (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem latLoc_latAt_eq {L L' : Submodule (𝓞 E) (Fin n → E)} {S : Set (HeightOneSpectrum (𝓞 F))} {N : ℕ}
    (h₁ : ∀ x ∈ L, (N : E) • x ∈ L') (h₂ : ∀ x ∈ L', (N : E) • x ∈ L)
    (hN : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → (N : 𝓞 E) ∉ w.asIdeal) :
    (∀ v ∉ S, latLoc F L v = latLoc F L' v) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → latAt w L = latAt w L' := by
  refine ⟨fun v hv => ?_, fun w hw => le_antisymm (latAt_le (hN w hw) h₁) (latAt_le (hN w hw) h₂)⟩
  obtain ⟨w, rfl⟩ := exists_under_eq (E := E) v
  have hv' : (N : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal := fun h => hN w hv (by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h
    exact h)
  exact le_antisymm (latLoc_le hv' h₁) (latLoc_le hv' h₂)

end GlobalTheory.LatAgree

namespace GlobalTheory.ChainOnto

theorem stabLoc_isParamFun_frameLat : ∀ D : D7, ForStage D fun c _ s =>
    (∀ v ∉ c.S, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v =
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram (GlobalTheory.AdelicU.frameLat s.V) v) ∧
    ∀ (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
      GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔
        GlobalTheory.LFun.IsParamFunV s.V c.S f B := by
  intro D c _ j _ s hs
  obtain ⟨N, ⟨-, -, -, h₁, h₂⟩, hN⟩ := hs.base
  have h₁' : ∀ x ∈ GlobalTheory.AdelicU.frameLat s.V, (N : D.host.E) • x ∈ s.Λ := fun x hx =>
    h₁ x (by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact hx)
  have h₂' : ∀ x ∈ s.Λ, (N : D.host.E) • x ∈ GlobalTheory.AdelicU.frameLat s.V := fun x hx => by
    have := h₂ x hx
    rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice] at this
    exact this
  obtain ⟨hloc, hat⟩ := GlobalTheory.LatAgree.latLoc_latAt_eq (S := (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) h₂' h₁'
    (fun w hw => hN w hw)
  exact ⟨fun v hv => GlobalTheory.LatAgree.stabLoc_congr _ _ (hloc v hv),
    fun f B => GlobalTheory.LatAgree.isParamFun_congr hloc hat f B⟩

end GlobalTheory.ChainOnto
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.QuotL

theorem e_strictMono {R : Ranks} (P : HCParam R) : StrictMono P.e := by
  have ht : (0 : ℚ) ≤ R.t := by positivity
  have step : ∀ (a : ℕ) (h : a + 1 < R.m), P.e ⟨a, by omega⟩ < P.e ⟨a + 1, h⟩ := fun a h => by
    have g1 := P.gap_eb ⟨a, by omega⟩ h
    have g2 := P.gap_be ⟨a + 1, h⟩
    linarith
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
  induction d with
  | zero => exact step a hb
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := step (a + d + 1) (by omega)
    have e1 : (⟨a + (d + 1) + 1, hb⟩ : Fin R.m) = ⟨a + d + 1 + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1]
    exact h1.trans h2

variable {D : D7}

theorem trivialOnF {c : Com D} (hc : c.Is) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.TrivialOnF (c.μ k) := fun a => by
  obtain ⟨⟨η, hη⟩, h⟩ := (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2
  exact (h η hη a).trans (pow_zero _)

theorem isHecke {c : Com D} (hc : c.Is) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) : IsHeckeChar D (c.μ k) :=
  (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).1

theorem quotL_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m →
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
  intro D c hc i j hi hij hj
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.μ (i' + 1)) τ (-e) ∧
      HasInfExp D (c.μ (j' + 1)) τ (-e') ∧ e ≠ e' :=
    ⟨τ, (D.hc τ).e ⟨i', by omega⟩, (D.hc τ).e ⟨j', by omega⟩, hc.exp ⟨i', by omega⟩ τ, hc.exp ⟨j', by omega⟩ τ,
      (e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
        Fin.mk_lt_mk.2 (by omega))).ne⟩
  obtain ⟨Λ, ⟨hd, hp⟩, hpos⟩ := (GlobalTheory.HeckeRatio.heckeRatioPos D (c.μ (i' + 1)) (c.μ (j' + 1))
    (isHecke hc (by omega) (by omega)) (isHecke hc (by omega) hj) (trivialOnF hc (by omega) (by omega))
    (trivialOnF hc (by omega) hj) hexp D.R.t).2 c.S
  refine ⟨Λ, hd, fun z hz => ?_, fun n h1 h2 h0 => ?_⟩
  · have hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
        GlobalTheory.LFun.UnrAt (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w := fun w hw =>
      (hc.unr ⟨i', by omega⟩ w hw).mul (hc.unr ⟨j', by omega⟩ w hw).inv
    have hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) :=
      fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl
    let e := Equiv.subtypeEquivRight hoff
    have k := hp z hz
    rw [GlobalTheory.HeckeRatio.lfac_eq] at k
    have k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
        GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w}) w.1 z) (Λ z) := by
      refine (e.hasProd_iff).1 (k.congr_fun fun P => ?_)
      have hu := hunr P.1 ((hoff P.1).1 P.2)
      rw [GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]
      simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL,
        GlobalTheory.LFun.charFam_of_unrAt hu]
    exact k2.tprod_eq.symm
  · have := (hpos n h1 h2).2
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this

end GlobalTheory.ChainOnto.QuotL
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem pet_val_sum {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (y : s.CC c) (w : SmT s.M) (n : ℕ)
    (ys : Fin n → s.CC c) (ws : Fin n → SmT s.M) :
    s.pet (PiLocalization₂.val y w) (∑ i, PiLocalization₂.val (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i) := by
  have hs : ∀ i, s.pet (PiLocalization₂.val y w) (PiLocalization₂.val (ys i) (ws i)) = ip y (ys i) * ipD w (ws i) :=
    fun i => h.schur y (ys i) w (ws i)
  rw [← Finset.sum_congr rfl (fun i _ => hs i)]

  simp only [PiLocalization₂.pet, Lift.pet, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => h.integ y (ys i) w (ws i))

theorem stepUp : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  intro D hFin hPV hSpan hAdj hPar hNe
  intro hgap c hc k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' u B hB hL
  have hk' : k + 1 ≤ D.R.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := hFin c hc (k + 1) hk' s' hs'
  obtain ⟨x, hx, -⟩ := GlobalTheory.T.hermitian_adjoint_exists_unique_of_posDef (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
  obtain ⟨φ, v, hv, hF⟩ := hNe hgap c hc k hk s s' hs hs' p hp u B hB hL
  have key := GlobalTheory.T.mem_range_adjoint_of_mem_span_evaluation_values (GA D s'.V) (SmT s'.M) (s'.CC c) (s'.CC c).subtype s'.KF ipD' ip' s'.pet
    hM'.hermD hM'.posD hM'.herm hM'.pos (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x
    (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v) (hSpan hgap c hc k hk s s' hs hs' p hp u φ v hv)
    (fun y w hw => by
      rw [hx y]
      exact (hAdj hgap c hc k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)) hF
  obtain ⟨-, w₀, -, hFx⟩ := key
  have hPF := hPar hgap c hc k hk s s' hs hs' p hp u B φ hB v hv hF
  refine ⟨x, hx, hPV c hc (k + 1) hk' s' hs' x w₀ _ ?_ ?_⟩
  · have : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
    rw [← this]; exact hF
  · have : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
    rw [← this]; exact hPF

end GlobalTheory.ChainOnto
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem step_chars_unrAt : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, ∀ v ∉ c.S, ∀ w : HeightOneSpectrum (𝓞 D.host.E),
    w.under (𝓞 D.host.F) = v → UnrAt (c.chS (k + 1)) w ∧ UnrAt (c.chT (k + 1)) w := by
  intro D c hc k hk v hv w hw
  have hμ : UnrAt (c.μ (k + 1)) w := by
    have := hc.unr ⟨k, hk⟩ w
    exact this (by rw [GlobalTheory.LFun.above, Set.mem_setOf_eq, hw]; exact hv)
  have hη : UnrAt c.η⁻¹ w := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w).inv
  have hμη : UnrAt (c.μ (k + 1) * c.η⁻¹) w := hμ.mul hη
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs <;> exact ⟨by assumption, by assumption⟩

end GlobalTheory.ChainOnto
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.norms_matrixSteps_coupledFactor_bounded_anyLevelPrime : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (B : Base D D.host.ccK dl) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok), FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), (∀ i, i + 2 < N.R.m → StepBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) i (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (i + 1))) ∧ CplBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (N.R.m - 1) + liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ N.R.m)  := by
  first | exact @GlobalTheory.Core.Ht2.factors_leS | exact GlobalTheory.Core.Ht2.factors_leS | (intros; apply GlobalTheory.Core.Ht2.factors_leS <;> assumption)
end
