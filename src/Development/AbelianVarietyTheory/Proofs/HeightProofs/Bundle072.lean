module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle058
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle008
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyZeroChoice
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLift
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RankOneOperatorMemOfTranslationAverageClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin




namespace GlobalTheory.FinalJoin

theorem inputs4_of_inputsR : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (X : WeightAlgebra.Prov D B P) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL → Inputs4 large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  intro D B P X j h1 h2 large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF T nP nW h0 nus hI hTC hPA hPS
  obtain ⟨⟨hH, hLat, hLAM, hQ, hSub⟩, hSup, hHerm, G, Gc, PH, Prw, Pet, Pd, hLogD,
    ⟨hW, hTh, hEt, hPGd, hPG4, hPGq, hRd, hRho, hRhoP, hPoly, hB, hM⟩, hComb, Qf, hC, hTie, hLift, hHt⟩ := hI
  have hSet := hH.2.1
  have hH2 := hH.2.2.2.2.1
  obtain ⟨hS0, hSK⟩ := shortG_of_scalB hH.2.2.1 hPG4
  have hDT : WeightFamilies.dimY D j ≤ T := hSet.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwt : SizeBoundsAlt.wtIter wadd wL ((X j h1 h2).wF0 wL wF) (a0 D j T) = ka := by
    rw [iterated_weight_at_vanishingOrder (X j h1 h2) wL wF T hDT]; exact (ka_eq_addL_of_setC hSet).symm
  obtain ⟨rz, alz, th0, zc, hTZ, hZ⟩ := exists_global_family_zero_choice G S T Gc hwt hS0 hH2.2.2.1
  obtain ⟨th, hTQ⟩ := exists_global_family_quotient_bounded
    ({ G with rz := rz, alz := alz, th0 := th0, zc := zc } : GlobalFamilyData (X j h1 h2) ka wL wF) large₂ S K.CRm T
    (cc D large₂ C2 A2 CR wL) (Gc * ka.size) Ch Ah hSK hH2.2.2.2
    (mul_le_mul_of_nonneg_right hPGq (by linarith [ka.one_le_size]))
  obtain ⟨hR1, hR2⟩ := GlobalTheory.shareRho_and_shareRhoT_of_shareRhoR D B P j (X j h1 h2) ka wL wF
    (G.setZQ rz alz th0 zc _ th) S T _ Gc hRho hTZ hZ
  have hM' : ∀ la, InContainM (G.setZQ rz alz th0 zc _ th) la K.CRm T (cc D large₂ C2 A2 CR wL) :=
    fun la => inContainM_of _ la S _ T _ (hM la) (hZ la)
  have hLift' : ∀ la, ((Qf la).tr G rz alz th0 zc _ th).InLiftC S Gc Prw T :=
    fun la => tr_InLiftC G rz alz th0 zc _ th (Qf la) S Gc Prw T (hLift la)
  refine ⟨hH, hLat, hSup, hLAM, hQ, hTC, hPA, hPS, G.setZQ rz alz th0 zc _ th, Gc, PH, Prw, Pet, Pd,
    hW, hTh, hTZ, hTQ, hEt, hHerm, hSub, hLogD, pageGd4_iff.mpr hPGd, hRd, hR2, hRhoP, polyDom4_iff.mpr hPoly, hZ, hM',
    fun hj => ⟨fun la => (Qf la).tr G rz alz th0 zc _ th, hB, hC, hTie, hLift',
      combBound4_of hj (tr_CombBound G rz alz th0 zc _ th S _ nus hComb) _, hHt⟩,
    fun hj => depthAtM_of hj hComb, fun _ _ => ?_,
    fun _ => ⟨fun la => (Qf la).tr G rz alz th0 zc _ th, hB, hC, hTie, hLift', hHt⟩⟩
  exact theorem_zero_of_named_inputs large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH hLat hSup hLAM hQ
    (G.setZQ rz alz th0 zc _ th) Gc PH Prw Pet Pd (fun la => (Qf la).tr G rz alz th0 zc _ th)
    hW hTh hTZ hTQ hEt hHerm hSub hLogD hPGd hRd hR1 hRhoP hPoly hB hC hTie hLift' hZ hM' hComb hHt

end GlobalTheory.FinalJoin
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

theorem pageRun_sq_le_rd_and_eight_le_rank : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → (D.R.f : ℝ) ^ 2 ≤ D.host.rdE ∧ 8 ≤ D.R.r := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 _ h
  obtain ⟨Q, _, hS, -, -⟩ := h.page
  have h1 := host_f_sq_le_rd Q
  rw [hostSize_f, hostSize_rd] at h1
  refine ⟨h1, ?_⟩
  have hm4 := host_m_pow_four_le_f hS
  rw [hostSize_f] at hm4
  have hm2 := D.R.two_le_m
  have h16 : 16 ≤ D.R.f := by
    have : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4
    omega
  have h2 := D.R.f_le_k
  unfold Ranks.f Ranks.n at *
  unfold Ranks.r
  omega

end GlobalTheory.FinalJoin
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (n : SecNorm B)




theorem hypC_secNorm (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    HypC large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) H C2 A2 CR Bx CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S)
        ka wL wF T nP nW h0 nus ↔
      HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus := Iff.rfl




theorem deepSubMul_secNorm : DeepSubMul (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ↔ DeepSubMul X := Iff.rfl

end




theorem baseIn_secNorm : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (n : SecNorm B), BaseIn large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → BaseIn large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n h
  obtain ⟨a1, a2, a3, a4, a5⟩ := h
  exact ⟨(hypC_secNorm X n large₂ H C2 A2 CR 0 CT S ka wL wF Tn nP nW h0 nus).2 a1,
    (latAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4).2 a2,
    (lamwAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4 large₂ K.CL K.AL).2 a3,
    fun hj => (qAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4 large₂ _ _ _ _ _ _ _ _).2 (a4 hj),
    (deepSubMul_secNorm X n).2 a5⟩

end GlobalTheory.FinalJoin
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem weberSet_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) : weberSet L n = weberSet L' n := by
  have hG : ∀ k, L.G k = L'.G k := fun k => by unfold PeriodPair.G; rw [h]
  have h2 : L.g₂ = L'.g₂ := by unfold PeriodPair.g₂; rw [hG]
  have h3 : L.g₃ = L'.g₃ := by unfold PeriodPair.g₃; rw [hG]
  have hP : ∀ z, L.weierstrassP z = L'.weierstrassP z := fun z => by unfold PeriodPair.weierstrassP; rw [h]
  unfold weberSet
  simp only [h2, h3, hP, h]

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

end GlobalTheory.FieldSize
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace


theorem _root_.GlobalTheory.T.casimir_unitaryGroup_acts_by_scalar_smoothVectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ χ : ℂ, ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v) := by
  first | exact @GlobalTheory.TypeSum.CasBasis.casimir_scalar | exact GlobalTheory.TypeSum.CasBasis.casimir_scalar | (intros; apply GlobalTheory.TypeSum.CasBasis.casimir_scalar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_rightKFourierSeries_unitary_moderateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ e : ℕ → (Formalism.REAL.KG ε → ℂ), (∀ i, Continuous (e i)) ∧
    (∀ i, KFinFun ε (e i)) ∧ ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → UMG ε f →
    ∃ (N : ℕ) (Φ : ℕ → List (Mx n) → Mx n → ℂ) (B : ℕ → ℕ → ℝ),
      (∀ i, ∀ y ∈ UJset ε, Φ i [] y = ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
      (∀ i (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
        ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ i l (y * NormedSpace.exp (t • X))) (Φ i (X :: l) y) 0) ∧
      (∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
        ∀ y ∈ UJset ε, ‖Φ i w y‖ ≤ B i k * (1 + hs y) ^ N) ∧
      (∀ k, Summable fun i => B i k) ∧
      ∀ y ∈ UJset ε, HasSum (fun i => ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (f y) := by
  first | exact @GlobalTheory.KFourier.exists_rightKFourier | exact GlobalTheory.KFourier.exists_rightKFourier | (intros; apply GlobalTheory.KFourier.exists_rightKFourier <;> assumption)
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.rankOneOperator_mem_of_translation_average_closed : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ Q : (H → H) → Prop, (∀ g ∈ UJset ε, Q (σ g)) → (∀ T T' : H → H, Q T → Q T' → Q (fun w => T w + T' w) ∧ Q (fun w => T (T' w))) → (∀ (c : ℂ) (T : H → H), Q T → Q (fun w => c • T w)) → (∀ e : KG ε → ℂ, KFinFun ε e → Q (kAvg ε σ e)) → Q (fun _ => 0) → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), (∀ j, IsKFin ε σ (a j)) ∧ (∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j) ∧ ∀ j u, IsKFin ε σ u → Q (fun w => ⟪c j, w⟫_ℂ • u) := by
  first | exact @GlobalTheory.TypeSum.rank_one_mem_of_closed | exact GlobalTheory.TypeSum.rank_one_mem_of_closed | (intros; apply GlobalTheory.TypeSum.rank_one_mem_of_closed <;> assumption)
end
