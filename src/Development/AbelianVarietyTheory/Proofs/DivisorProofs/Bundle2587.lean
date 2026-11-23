module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpanCuspOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_weilRep_hermitianPair_rationalSchrodinger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∃ om, GlobalTheory.WeilM.IsUWeilPair (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
            (incM D.host.F JA) (incM D.host.F JB) co χT χS om := by
  first | exact @GlobalTheory.WeilSchrodinger.exists_isUWeilPair_hsp | exact GlobalTheory.WeilSchrodinger.exists_isUWeilPair_hsp | (intros; apply GlobalTheory.WeilSchrodinger.exists_isUWeilPair_hsp <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RankBergman

open MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt (ptN petE muOn muPart framesOn bergE bergOn modelWt mem_cuspW cuspW_le_secZ cuspOn_le classesOver
  isProbabilityMeasure_muPart muPart_univ_le petE_ne_top bergE_le_iff)
open scoped ENNReal


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem rkC_le_of_bergLe : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ (la : AllWt.Weight (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (β : ℝ), 0 ≤ β →
    BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β → (Y.rkC la Z : ℝ) ≤ β := by
  intro D T j Y e o hY la Z β hβ hB
  classical
  obtain ⟨G, hG⟩ : ∃ G : WTZ D.host.E, G = wtOf (T.Q.Dw j) la 0 := ⟨_, rfl⟩
  set σ : Y.d.c₂.F →+* ℂ := goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom with hσdef
  have hσ : GoodEmb Y.d.c₂ σ := goodEmb_goodOf _ _
  obtain ⟨th, hr, hth, hdU⟩ := hY.dictU σ hσ
  have hd : ∀ g, (Y.dict σ g).2 ∈ ((Y.U σ).X (Y.dict σ g).1).dom := hdU.2.2.2.1
  have hu := hY.unit σ hσ
  set Cw := cuspOn Y.U Z G with hCw
  set S : Submodule ℂ (FDSec (Y.U σ).X) := Submodule.span ℂ (rdU (Y.U σ) '' (Cw : Set (Rul Y.d.Xo₂ Y.d.c₂))) with hS
  set μ := muOn (Y.U σ) (D.sp.W j) (Y.dict σ) Z with hμdef
  set lw := modelWt (Y.U σ) G with hlw
  have hSsub : S ≤ holSub (Y.U σ).X lw :=
    Submodule.span_le.2 (by rintro _ ⟨f, hf, rfl⟩; exact (mem_cuspW.1 hf.1).2 σ hσ)
  have hoff : ∀ P ∈ S, ∀ z, z ∉ framesOn (Y.U σ) Z → P z.1 z.2 = 0 := fun P hP z hz =>
    eq_zero_of_mem_span_cuspOn hP hz
  have hμ1 : μ Set.univ ≤ 1 := muPart_univ_le _ _ _
  have hfin : ∀ P ∈ holSub (Y.U σ).X lw, petE (D.sp.W j) (Y.dict σ) μ lw P ≠ ⊤ := fun P hP =>
    petE_ne_top _ _ μ hμ1 hd hP

  have hpt : ∀ P ∈ S, ∀ z, ptN lw P z ^ 2 ≤ β * (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal ^ 2 := by
    intro P hP z
    by_cases hz : z ∈ framesOn (Y.U σ) Z
    · have hzd := hz.1
      have hb := hB σ hσ ⟨z.1, z.2, hzd⟩ hz
      have hb' : bergE (D.sp.W j) (Y.dict σ) μ lw ⟨z.1, z.2, hzd⟩ ≤ ENNReal.ofReal β := by
        rw [hlw, hG]; exact hb
      have h := (bergE_le_iff (D.sp.W j) (Y.dict σ) μ hfin ⟨z.1, z.2, hzd⟩ ENNReal.ofReal_ne_top).1 hb' P (hSsub hP)
      have hf := hfin P (hSsub hP)
      have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hf)) h
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (GlobalTheory.AllWt.ptN_nonneg _ _ _), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hβ, ENNReal.toReal_pow] at h2
      exact h2
    · have h0 : ptN lw P z = 0 := by
        simp only [ptN, Data.pnorm, hoff P hP z hz, norm_zero, zero_mul]
      rw [h0]
      nlinarith [sq_nonneg (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal]
  have hzero : ∀ P ∈ S, petE (D.sp.W j) (Y.dict σ) μ lw P = 0 → P = 0 := by
    intro P hP h0
    funext k x
    by_cases hz : (⟨k, x⟩ : Σ k, Frame ((Y.U σ).X k).Ψ D.R.r) ∈ framesOn (Y.U σ) Z
    · have h1 := hpt P hP ⟨k, x⟩
      rw [h0, ENNReal.toReal_zero] at h1
      have h2 : ptN lw P ⟨k, x⟩ = 0 := by nlinarith [GlobalTheory.AllWt.ptN_nonneg lw P ⟨k, x⟩]
      have h3 := GlobalTheory.LevGeo.RankBd.pnorm_fac_pos ((Y.U σ).X k) (lw k) hz.1
      have h4 : ‖P k x‖ * _ = 0 := h2
      rcases mul_eq_zero.1 h4 with h5 | h5
      · simpa using h5
      · exact absurd h5 h3.ne'
    · exact hoff P hP ⟨k, x⟩ hz
  have hptd : ∀ (P : FDSec (Y.U σ).X) g, ptN lw P (Y.dict σ g) = ‖P (Y.dict σ g).1 (Y.dict σ g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  have hmeasQ : ∀ P ∈ S, AEStronglyMeasurable
      (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) (muQ1 (D.sp.W j)) := by
    intro P hP
    have h := aesm_of_holSub (adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := σ) (GlobalTheory.PetDef.adelAut_good Y hY σ hσ))
      _ (hSsub hP)
    have e : (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) =
        fun q => ‖onQ (D.sp.W j) (adel (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) P) q‖ := by
      funext q
      simp [onQ, adel]
    rw [e]
    exact h.norm
  have hmeas : ∀ P ∈ S, AEStronglyMeasurable
      (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) μ := by
    intro P hP
    rw [hμdef]
    unfold GlobalTheory.AllWt.muOn GlobalTheory.AllWt.muPart ProbabilityTheory.cond
    exact ((hmeasQ P hP).restrict).smul_measure _

  have hSfin : FiniteDimensional ℂ S ∧ (Module.finrank ℂ S : ℝ) ≤ β := by
    by_cases hA : muQ1 (D.sp.W j) (classesOver (D.sp.W j) (Y.dict σ) (framesOn (Y.U σ) Z)) = 0
    · have hμ0 : μ = 0 := ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hA
      have hsub : Subsingleton S := ⟨fun a b => by
        have ha := hzero a a.2 (by rw [hμ0]; unfold GlobalTheory.AllWt.petE; exact eLpNorm'_measure_zero_of_pos (by norm_num))
        have hb := hzero b b.2 (by rw [hμ0]; unfold GlobalTheory.AllWt.petE; exact eLpNorm'_measure_zero_of_pos (by norm_num))
        exact Subtype.ext (ha.trans hb.symm)⟩
      refine ⟨inferInstance, ?_⟩
      rw [Module.finrank_zero_of_subsingleton]
      simpa using hβ
    · haveI : IsProbabilityMeasure μ := isProbabilityMeasure_muPart _ _ hA
      have hpet : ∀ P ∈ S, (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal ^ 2 =
          ∫ q, ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖ ^ 2 ∂μ := by
        intro P hP
        obtain ⟨M, -, hM⟩ := exists_ptN_le (hSsub hP)
        have e : petE (D.sp.W j) (Y.dict σ) μ lw P =
            eLpNorm (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) 2 μ := by
          unfold GlobalTheory.AllWt.petE
          rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) (hmeas P hP)]
          congr 1
          funext q
          exact hptd P _
        have h2 := GlobalTheory.LevGeo.RankBd.eLpNorm_sq_eq (μ := μ) (fun _ => norm_nonneg _) (hmeas P hP) (B := M)
          fun q => by rw [← hptd]; exact hM ⟨_, _, hd q.out⟩
        rw [← e] at h2
        rw [← ENNReal.toReal_pow, h2, ENNReal.toReal_ofReal (integral_nonneg fun _ => by positivity)]
      refine GlobalTheory.Bergman.finite_and_finrank_le_of_pointwise (μ := μ)
        (fun q (P : S) => ‖(P : FDSec (Y.U σ).X) (Y.dict σ q.out).1 (Y.dict σ q.out).2‖)
        (fun q => ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : Frame ((Y.U σ).X (Y.dict σ q.out).1).Ψ D.R.r => ℂ)
          (Y.dict σ q.out).2 ∘ₗ LinearMap.proj (R := ℂ) (φ := fun k => Frame ((Y.U σ).X k).Ψ D.R.r → ℂ)
          (Y.dict σ q.out).1) ∘ₗ S.subtype, fun P => rfl⟩)
        (fun P => hmeas P P.2) ?_ hβ ?_
      · intro P hP0
        refine Subtype.ext (hzero P P.2 ?_)
        unfold GlobalTheory.AllWt.petE
        have e : (fun q : AutQ (D.sp.W j) => ptN lw (P : FDSec (Y.U σ).X) (Y.dict σ q.out)) = fun _ => 0 := by
          funext q
          rw [hptd]
          exact hP0 q
        rw [e]
        exact eLpNorm'_zero (by norm_num)
      · intro P q
        have h1 := hpt P P.2 (Y.dict σ q.out)
        rw [hptd, hpet P P.2] at h1
        exact h1

  obtain ⟨hSf, hSle⟩ := hSfin
  have hcard : ∀ s : Finset Cw, LinearIndependent Y.d.c₂.F (fun i : s => (i : Cw)) → s.card ≤ Module.finrank ℂ S := by
    intro s hs
    let eq : Fin s.card ≃ s := s.equivFin.symm
    let b : Fin s.card → Rul Y.d.Xo₂ Y.d.c₂ := fun i => ((eq i : Cw) : Rul Y.d.Xo₂ Y.d.c₂)
    have hb : LinearIndependent Y.d.c₂.F b := (hs.comp eq eq.injective).map' Cw.subtype (Submodule.ker_subtype _)
    have hrd := GlobalTheory.reading_linearIndependent_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange (Y.U σ) (hY.unf σ hσ)
      (exZ _ G) s.card b (fun i => cuspW_le_secZ G (cuspOn_le Y.U Z G (eq i : Cw).2)) hb
    let v : Fin s.card → S := fun i => ⟨rdU (Y.U σ) (b i), Submodule.subset_span ⟨b i, (eq i : Cw).2, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp S.subtype hrd
    simpa using hv.fintype_card_le_finrank
  haveI : Module.Free Y.d.c₂.F Cw := Module.Free.of_divisionRing Y.d.c₂.F Cw
  have hrank : Module.rank Y.d.c₂.F Cw ≤ ((Module.finrank ℂ S : ℕ) : Cardinal) := rank_le hcard
  haveI hCf : FiniteDimensional Y.d.c₂.F Cw :=
    Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)
  have h2 : Module.finrank Y.d.c₂.F Cw ≤ Module.finrank ℂ S := Module.finrank_le_of_rank_le hrank
  have h3 : GlobalTheory.AllWt.rankOn Y.U Z G ≤ Module.finrank Y.d.c₂.F Cw := by
    unfold GlobalTheory.AllWt.rankOn Formalism.HN.rkK
    exact Submodule.finrank_le _
  show (GlobalTheory.AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) la 0) : ℝ) ≤ β
  rw [← hG]
  exact le_trans (Nat.cast_le.2 (h3.trans h2)) hSle

end GlobalTheory.RankBergman
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

noncomputable section

namespace GlobalTheory.VacTriv

theorem one_suppSplit {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q _ _ i j k
  refine ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, ?_⟩
  simp

theorem one_suppInert {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.SuppInert D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q _ _ i j k
  refine ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, ?_⟩
  simp

theorem one_intG {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.IntG D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro i j
  simp only [inv_one, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact ⟨one_mem _, one_mem _⟩
  · exact ⟨zero_mem _, zero_mem _⟩

theorem vacuum_const_trivial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∃ c : ℂ, Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x₁ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₁ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₁ : GA D S) (h₁ : GA D T)
    (x₂ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₂ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₂ : GA D S) (h₂ : GA D T) (c₁ c₂ : ℂ),
    IsFinPt S g₁ x₁ → IsFinPt T h₁ y₁ → IsFinPt S g₂ x₂ → IsFinPt T h₂ y₂ →
    Reads ψ θ hS hT cc δ r (c₁ • W.Om x₁ y₁ e0) (om (g₁, h₁) f₀) → Reads ψ θ hS hT cc δ r (c₂ • W.Om x₂ y₂ e0) (om (g₂, h₂) f₀) →
    Reads ψ θ hS hT cc δ r ((c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0) (om (g₁ * g₂, h₁ * h₂) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.IntG D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset e0 W χS χT om hW hInp t0 ht0 hev hodd hχS hχT f₀ hf₀ hline hmul hsplit hinert
  subst hS
  subst hT
  have hnz : ∀ x y, W.Om x y e0 ≠ 0 := GlobalTheory.T.weilOperator_normalisingVector_ne_zero cc δ t0 e0 W hset.crv hodd
  have huniq : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T) (c c' : ℂ),
      Reads ψ θ rfl rfl cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
      Reads ψ θ rfl rfl cc δ r (c' • W.Om x y e0) (om (g, h) f₀) → c = c' :=
    fun x y g h c c' h1 h2 => GlobalTheory.T.readsGaussian_smul_const_unique ψ θ S T rfl rfl cc δ r hset _ _ c c' (hnz x y) h1 h2
  have hone : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T),
      Reads ψ θ rfl rfl cc δ r (W.Om x y e0) (om (g, h) f₀) →
      Reads ψ θ rfl rfl cc δ r ((1 : ℂ) • W.Om x y e0) (om (g, h) f₀) := fun x y g h hr => by rwa [one_smul]
  have p1S : IsFinPt S (1 : GA D S) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) := GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_one S rfl
  have p1T : IsFinPt T (1 : GA D T) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) := GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_one T rfl
  have exS : ∀ x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank, ∃ g, IsFinPt S g x :=
    fun x => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one S hset.gS x rfl
  have exT : ∀ y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank, ∃ h, IsFinPt T h y :=
    fun y => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one T hset.gT y rfl
  choose gx hgx using exS
  choose hy hhy using exT
  have gx1 : gx 1 = 1 := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ 1 (hgx 1) p1S
  have hy1 : hy 1 = 1 := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ 1 (hhy 1) p1T
  have gxm : ∀ x₁ x₂, gx x₁ * gx x₂ = gx (x₁ * x₂) :=
    fun x₁ x₂ => GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ _ (GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_mul S _ _ _ _ (hgx x₁) (hgx x₂)) (hgx (x₁ * x₂))
  have hym : ∀ y₁ y₂, hy y₁ * hy y₂ = hy (y₁ * y₂) :=
    fun y₁ y₂ => GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ _ (GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_mul T _ _ _ _ (hhy y₁) (hhy y₂)) (hhy (y₁ * y₂))
  choose cS hcS using fun x => hline x 1 (gx x) 1 (hgx x) p1T
  choose cT hcT using fun y => hline 1 y 1 (hy y) p1S (hhy y)

  have cS1 : cS 1 = 1 := by
    have h1 := hcS 1
    rw [gx1] at h1
    exact huniq _ _ _ _ _ _ h1 (hone _ _ _ _ (hsplit 1 1 1 1 p1S p1T (by simpa using one_suppSplit) (by simpa using one_suppSplit)))
  have cSm : ∀ x₁ x₂, cS (x₁ * x₂) = cS x₁ * cS x₂ := by
    intro x₁ x₂
    have h1 := hmul x₁ 1 (gx x₁) 1 x₂ 1 (gx x₂) 1 (cS x₁) (cS x₂) (hgx _) p1T (hgx _) p1T (hcS x₁) (hcS x₂)
    rw [mul_one, mul_one, gxm] at h1
    exact huniq _ _ _ _ _ _ (hcS (x₁ * x₂)) h1
  have cT1 : cT 1 = 1 := by
    have h1 := hcT 1
    rw [hy1] at h1
    exact huniq _ _ _ _ _ _ h1 (hone _ _ _ _ (hsplit 1 1 1 1 p1S p1T (by simpa using one_suppSplit) (by simpa using one_suppSplit)))
  have cTm : ∀ y₁ y₂, cT (y₁ * y₂) = cT y₁ * cT y₂ := by
    intro y₁ y₂
    have h1 := hmul 1 y₁ 1 (hy y₁) 1 y₂ 1 (hy y₂) (cT y₁) (cT y₂) p1S (hhy _) p1S (hhy _) (hcT y₁) (hcT y₂)
    rw [mul_one, mul_one, hym] at h1
    exact huniq _ _ _ _ _ _ (hcT (y₁ * y₂)) h1
  let νS : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank →* ℂ := { toFun := cS, map_one' := cS1, map_mul' := cSm }
  let νT : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank →* ℂ := { toFun := cT, map_one' := cT1, map_mul' := cTm }
  have tS : ∀ x, cS x = 1 := by
    intro x
    have := GlobalTheory.T.unitaryAdelicCharacter_eq_one_split_inert S hset.gS νS.toHomUnits
      (fun k hk => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcS k) (hone _ _ _ _ (hsplit k 1 (gx k) 1 (hgx k) p1T hk (by simpa using one_suppSplit)))))
      (fun k hk hki => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcS k) (hone _ _ _ _ (hinert k 1 (gx k) 1 (hgx k) p1T hk (by simpa using one_suppInert)
          hki (by simpa using one_intG))))) x
    have := congrArg Units.val this
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  have tT : ∀ y, cT y = 1 := by
    intro y
    have := GlobalTheory.T.unitaryAdelicCharacter_eq_one_split_inert T hset.gT νT.toHomUnits
      (fun k hk => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcT k) (hone _ _ _ _ (hsplit 1 k 1 (hy k) p1S (hhy k) (by simpa using one_suppSplit) hk))))
      (fun k hk hki => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcT k) (hone _ _ _ _ (hinert 1 k 1 (hy k) p1S (hhy k) (by simpa using one_suppInert) hk
          (by simpa using one_intG) hki)))) y
    have := congrArg Units.val this
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  intro x y g h hg hh
  have eg : g = gx x := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ x hg (hgx x)
  have eh : h = hy y := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ y hh (hhy y)
  subst eg eh
  have h1 := hmul x 1 (gx x) 1 1 y 1 (hy y) (cS x) (cT y) (hgx x) p1T p1S (hhy y) (hcS x) (hcT y)
  rw [tS, tT] at h1
  simp only [mul_one, one_mul, one_smul] at h1
  exact h1

end GlobalTheory.VacTriv
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelMove_stabiliser_character_det : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, phiAt T i σ hV (fun _ => 1) (actLev T.Q.c (O i).lev2 g f) h = σ y * phiAt T i σ hV (fun _ => 1) f (h * k) := by
  first | exact @GlobalTheory.StabMove.phiAt_actLev_of_comp_eq | exact GlobalTheory.StabMove.phiAt_actLev_of_comp_eq | (intros; apply GlobalTheory.StabMove.phiAt_actLev_of_comp_eq <;> assumption)
end
