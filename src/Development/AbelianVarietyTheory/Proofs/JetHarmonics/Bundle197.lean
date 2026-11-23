module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle157
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle175
public import Formalism.HermitianCurvature.Bundle006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle196
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle113
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ModulusPosOfThirdHypothesis
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle181
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
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup

@[expose] public section

section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem PageOK.runNum {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (hj : InR D j) {large₂ : SizeData₂ D} {X : PJ D B P j}
    {H : KHyp} {C2 A2 CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0) :
    GlobalTheory.PtTie.RunNum D wL (cc D large₂ C2 A2 7 wL) ∧ 0 < cc D large₂ C2 A2 7 wL := by
  obtain ⟨hA, hS, h3, -, -⟩ := hP.hyp
  constructor
  · let n : ℕ := (D.host.g 0 * D.host.g 1) ^ DF wL
    refine GlobalTheory.PtTie.runNum_of_sizes D large₂ B P j hj X H C2 A2 7 ⟨(n : 𝓞 B.KO), 0, 0, 0⟩ ka wL wF Tn nP nW h0 hA hS h3
      ⟨hP.p13, fun σ => ?_, hP.frd, hP.r8, hP.df⟩ (by norm_num)
    have e : σ ((n : 𝓞 B.KO) : B.KO) = (n : ℂ) := by
      rw [show ((n : 𝓞 B.KO) : B.KO) = (n : B.KO) from map_natCast (algebraMap (𝓞 B.KO) B.KO) n, map_natCast]
    show _ ≤ Real.log ‖σ ((n : 𝓞 B.KO) : B.KO)‖
    rw [e, Complex.norm_natCast]
    have e2 : Real.log (n : ℝ) = (DF wL : ℝ) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
      simp only [n]
      push_cast
      rw [Real.log_pow]
    have p : 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
      rw [← Nat.cast_mul]
      exact Real.log_natCast_nonneg _
    have p' : (0 : ℝ) ≤ (DF wL : ℝ) := Nat.cast_nonneg _
    rw [e2]
    nlinarith [mul_nonneg p' p]
  · have hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
    have hf : 0 < D.R.f := by
      have := D.R.two_le_m
      have := D.R.m_le_f
      unfold Ranks.f Ranks.n
      omega
    have hm : 0 < D.R.m := hj.1.trans hj.2
    have hs : (0 : ℝ) < 2 * (D.R.f : ℝ) * D.R.m := by positivity
    have hR : 0 < WeightFamilies.RRv D 7 := Real.rpow_pos_of_pos (hs.trans_le hrd) _
    have h5 : (2 * D.R.f * D.R.m : ℝ) ^ 4 * nW + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D large₂ C2 A2 :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hP.p13
    have hPP : 0 < WeightFamilies.PPv D large₂ C2 A2 := lt_of_lt_of_le (by positivity) h5
    have hD : 0 < DF wL := lt_of_lt_of_le (by norm_num) hP.df
    have hq := modulus_pos_of_third_hypothesis h3
    unfold cc
    positivity




theorem combBound_run : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), GlobalTheory.PtTie.Oriented T EX → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → CombBound G (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (cc D large₂ C2 A2 7 wL) (nusR h j wL) ∧ 0 < (cc D large₂ C2 A2 7 wL) := by
  intro hH D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hO hP G hG
  obtain ⟨hR, hc⟩ := hP.runNum hj
  exact ⟨GlobalTheory.T.combinedValuationBound_algebraicPoints hH D T h j hj hinj EX wL _ hO hR ka wF _ G rfl (fun hm => ⟨(hG hm).1, (hG hm).2.2.1⟩), hc⟩

end GlobalTheory.RunJoin
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.capelli_eigenfunction_bound_three_places : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → N ≤ 2 * p₀ → ∀ (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs : ℝ), (∀ y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (y : ℂ) f g = ((∏ s, (y + lam' s) : ℝ) : ℂ) • f g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) ≤ cs - 1) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnp y) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnm y) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  first | exact @GlobalTheory.EigenThreePlaces.main | exact GlobalTheory.EigenThreePlaces.main | (intros; apply GlobalTheory.EigenThreePlaces.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory

theorem leafDepthGood_of_chartForm : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  intro hUp
  obtain ⟨C0, h⟩ := GlobalTheory.T.depthLeaf_goodPrimes_of_point_data
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T hT EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm hR
  exact h D L Pm Tp hK T hT EX K Bs Df S P oc O ι Nm hR
    (fun j => GlobalTheory.T.allGoodPrimeDepthDataExist_proof hUp _ _ _ _ (T.Q.Xo (ι j)) T.Q.c)

end GlobalTheory
end
