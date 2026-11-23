module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle040
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle022
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin




namespace GlobalTheory.RunJoin

theorem genOK_refill {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (c : ℝ) (hG : GenOK h j hj large₂ G S c)
    (del th' rz alz th0 zc rq th iet et) :
    GenOK h j hj large₂ (FamilyHypotheses.refill G del th' rz alz th0 zc rq th iet et) S c := hG

end GlobalTheory.RunJoin
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem three_le_dimY_of_rank (D : D7) (j : ℕ) (hj : InR D j) (hr : 8 ≤ D.R.r) : 3 ≤ WeightFamilies.dimY D j := by
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.ord_pos
    omega
  have hs : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  unfold WeightFamilies.dimY
  generalize (D.R.sigW j).1 = a at hs ⊢
  generalize (D.R.sigW j).2 = b at hs ⊢
  have key : ∀ c : ℕ, 3 ≤ c → 3 ≤ c * (c - 1) / 2 := fun c hc => by
    have : 3 * 2 ≤ c * (c - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have h3 : 3 ≤ a * b + a * (a - 1) / 2 + b * (b - 1) / 2 := by
    rcases le_or_gt 3 a with h | h
    · have := key a h; omega
    · have := key b (by omega); omega
  calc 3 = 1 * 3 := rfl
    _ ≤ _ := Nat.mul_le_mul hf h3

theorem DF_add_one_le_size {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) : (DF w : ℝ) + 1 ≤ w.size := by
  unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
  have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
  push_cast at h2 ⊢
  linarith

theorem lamConst_lamR_rows : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 CL : ℝ) (N del : ℕ), InR D j → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → 0 < CL → 0 < N → 0 < del → Real.log N ≤ nbR large₂ wL → Real.log del ≤ 1041 * Zb D large₂ ^ 3 → LamConst j large₂ CL 2 (wsmul (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL) (lamR large₂ CL wL) (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL.size ∧ 3 ≤ WeightFamilies.dimY D j ∧ wL.n = nW ∧ 0 < wL.n ∧ (DF wL : ℝ) ≤ wL.size ∧ 2 ≤ wL.size ∧ 1 ≤ PO D large₂ ∧ 1 ≤ zBase large₂ ∧ cc D large₂ C2 A2 7 wL * (g0 D : ℝ) ≤ 1 / 2 ∧ PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2) ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 CL N del hj hP hCL hN hdel hlN hld
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.ord_pos
    omega
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hPO : 1 ≤ PO D large₂ := by
    unfold PO
    have h1 : 0 ≤ 19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * large₂.sc.L := by positivity
    have h2 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 2 * large₂.sc.L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf') hL
    nlinarith
  obtain ⟨-, hS, h3, -⟩ := hP.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hIL, -, -, -, -, h40, -, h22, -⟩ := hS
  obtain ⟨-, -, -, hc, -⟩ := h3
  obtain ⟨-, -, t1, t2, t3, -⟩ := hP.tie
  rw [t1, t2, t3] at hc
  have hdf : (3 : ℝ) ≤ DF wL := by exact_mod_cast hP.df
  have hsz := DF_add_one_le_size wL
  have hn : wL.n = nW := hIL.1
  refine ⟨?_, three_le_dimY_of_rank D j hj hP.r8, hn, by omega, by linarith, by linarith, hPO,
    WeightFamilies.one_le_zBase large₂, ?_, le_max_right _ _⟩
  · set n : ℕ := 8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊) with hndef
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (by rw [hndef]; positivity)
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hs1 : (wsmul n wL).size ≤ (n : ℝ) * wL.size :=
      GlobalTheory.RunWeights.size_le_mul _ _ n hn1 (fun _ _ => le_rfl) (fun _ _ => le_rfl) le_rfl
    have hs0 : 1 ≤ (wsmul n wL).size := by
      have := DF_add_one_le_size (wsmul n wL)
      have h0 : (0 : ℝ) ≤ DF (wsmul n wL) := Nat.cast_nonneg _
      linarith
    have hP0 : 0 ≤ WeightFamilies.PP0v D large₂ CL 2 := by
      unfold WeightFamilies.PP0v
      rw [Real.rpow_two]
      positivity
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hdel' : (0 : ℝ) < del := by exact_mod_cast hdel
    have hceil : (1 : ℝ) + (⌈PO D large₂⌉₊ : ℝ) ≤ 2 + PO D large₂ := by
      have := Nat.ceil_lt_add_one (a := PO D large₂) (by linarith)
      linarith
    have hd0 : (0 : ℝ) ≤ WeightFamilies.dimY D j := Nat.cast_nonneg _
    have hnle : (n : ℝ) ≤ 8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂) * (N : ℝ) ^ 2 * del := by
      rw [hndef]
      push_cast
      calc 8 * (((WeightFamilies.dimY D j : ℝ) + 2) * N) ^ 2 * ((WeightFamilies.dimY D j : ℝ) + 1) * del * (1 + (⌈PO D large₂⌉₊ : ℝ))
          ≤ 8 * (((WeightFamilies.dimY D j : ℝ) + 2) * N) ^ 2 * ((WeightFamilies.dimY D j : ℝ) + 2) * del * (2 + PO D large₂) := by
            gcongr; norm_num
        _ = _ := by ring
    have hA : (0 : ℝ) < 8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂) := by positivity
    have hlogn := Real.log_le_log (by linarith) hnle
    rw [Real.log_mul (by positivity) hdel'.ne', Real.log_mul hA.ne' (by positivity), Real.log_pow] at hlogn
    push_cast at hlogn
    have hlogs := Real.log_le_log (by linarith) hs1
    rw [Real.log_mul (by linarith) (by linarith)] at hlogs
    have hl0 : 0 ≤ Real.log (wsmul n wL).size := Real.log_nonneg hs0
    have hmain : WeightFamilies.PP0v D large₂ CL 2 * (1 + Real.log (wsmul n wL).size) ≤ lamR large₂ CL wL := by
      refine le_trans ?_ (le_max_right _ _)
      exact mul_le_mul_of_nonneg_left (by linarith) hP0
    have hlam : 0 ≤ lamR large₂ CL wL := le_trans zero_le_one (le_max_left _ _)
    unfold LamConst
    rw [mul_assoc (lamR large₂ CL wL)]
    exact mul_le_mul hmain hs1 (by linarith) hlam
  · have hT : (2 : ℝ) ≤ Tn := by
      have : 2 ≤ Tn := by omega
      exact_mod_cast this
    rw [mul_assoc] at hc
    by_contra hcon
    push Not at hcon
    nlinarith

end GlobalTheory.RunJoin
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.unitaryLatticeDenominatorHeightBound_proof : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), DenomBound θ V := by
  first | exact @GlobalTheory.SmoothForms.denomBound | exact GlobalTheory.SmoothForms.denomBound | (intros; apply GlobalTheory.SmoothForms.denomBound <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothForms.RealPts

theorem infEmb_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ) (h' : IsInfEmb τ θ') :
    θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (D : D7) (σ : D.host.E →+* ℂ) :
    (∃ τ, tauE D τ = σ) ↔ ¬ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have hcm := D.host.isCMField_hostE
    have h : IsCMField.complexConj D.host.E x = D.host.conj x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.toHostAx.conjE_apply _ x).symm
    show starRingEnd ℂ (D.host.emb g x) = D.host.emb g (D.host.conj x)
    rw [← h, IsCMField.complexEmbedding_complexConj]
  have h : ∀ g, (∃ τ, tauE D τ = D.host.emb g) ↔ g ∈ D.R.Psi := fun g => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g]
    exact exists_congr fun τ => eq_comm
  rw [hc, h, h]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem gramAt_herm {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  ext i j
  have hcm := D.host.isCMField_hostE
  have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
  simp only [conjTranspose_apply, gramAt, map_apply, HSpace.gram]
  rw [← h1]
  exact (IsCMField.complexEmbedding_complexConj _ (tauE D τ) _).symm

theorem gramAt_unit {D : D7} (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det _ _).symm
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero _).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)

theorem infMat_eq {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram θ g = (infHom V g).1.map θ := rfl

theorem finMat_eq {D : D7} (V : HSp D) (g : GA D V) :
    finMat D.sp.cm.sig V.gram g = (finHom V g).1 := rfl

theorem glue {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) :
    (∀ g : GA D V, (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = 1) → g ∈ GfC V) ∧
    ∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
      ∃ g ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = u τ := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.image (tauE D)
  have hm : ∀ σ, σ ∈ Ψ ↔ ∃ τ, tauE D τ = σ := fun σ => by simp [Ψ]
  choose s hs using fun σ : Ψ => (hm σ.1).1 σ.2
  have hst : ∀ τ, s ⟨tauE D τ, (hm _).2 ⟨τ, rfl⟩⟩ = τ := fun τ => tauE_injective D (hs _)
  obtain ⟨h1, -, -, h4⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ (fun σ => θ (s σ))
    (fun σ => by rw [hm, hm]; exact tauE_cm D σ) (fun σ => by rw [← hs σ]; exact hθ (s σ))
  refine ⟨fun g hg => h1 g fun σ => hg (s σ), fun u hu => ?_⟩
  obtain ⟨h, hh, hhu⟩ := h4 (fun σ => u (s σ)) (fun σ => by rw [← hs σ]; exact hu (s σ))
  refine ⟨h, hh, fun τ => ?_⟩
  have := hhu ⟨tauE D τ, (hm _).2 ⟨τ, rfl⟩⟩
  simp only [hst] at this
  exact this

theorem realPoints : ∀ D : D7, (∀ θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → IsInfFam θ' → θ = θ') ∧ ∀ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → ∀ V : HSp D, RealPoints θ V := by
  intro D
  refine ⟨fun θ θ' h h' => funext fun ρ => infEmb_unique _ _ _ (h ρ) (h' ρ), fun θ hθ V => ?_⟩
  obtain ⟨g1, g2⟩ := glue θ hθ V
  obtain ⟨s1, s2, s3, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  have hmul : ∀ g g' τ, infMat D.sp.cm.sig V.gram (θ τ) (g * g') =
      infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g' := fun g g' τ => by
    rw [infMat_eq V, infMat_eq V, infMat_eq V, map_mul, Units.val_mul, Matrix.map_mul]
  have hfin : ∀ k ∈ GfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = 1 := fun k hk τ => by
    have hk' : infHom V k = 1 := hk
    rw [infMat_eq V, hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨fun τ => ⟨gramAt_herm V τ, gramAt_unit V τ⟩, g2, fun g hg g' hg' h => ?_, hmul, hfin, s2,
    fun g => ?_, fun g a ha => ?_⟩
  · refine mul_inv_eq_one.1 (s3 _ (mul_mem hg (inv_mem hg')) (g1 _ fun τ => ?_))
    rw [hmul, h, ← hmul, mul_inv_cancel, hfin 1 (one_mem _)]
  · obtain ⟨a, ha, k, hk, e⟩ := s1 g
    exact ⟨k, hk, a, ha, e.trans (s2 a ha k hk)⟩
  · have ha' : finHom V a = 1 := ha
    rw [finMat_eq V, finMat_eq V, map_mul, ha', mul_one]

end GlobalTheory.SmoothForms.RealPts

end
end

section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped Topology ContDiff

namespace GlobalTheory.TypeSum.CoefClos

theorem integral_rder_eq_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant] (c : ℝ → G) (hc : Continuous c) (h0 : c 0 = 1)
    (hadd : ∀ a b, c (a + b) = c a * c b) (h h' : G → ℂ) (hh : Continuous h) (hh' : Continuous h')
    (hs : HasCompactSupport h) (hs' : HasCompactSupport h')
    (hd : ∀ x, HasDerivAt (fun t => h (x * c t)) (h' x) 0) : ∫ x, h' x ∂μ = 0 := by
  have i0 : Integrable h μ := hh.integrable_of_hasCompactSupport hs
  have i1 : Integrable h' μ := hh'.integrable_of_hasCompactSupport hs'
  have pt : ∀ x, ∫ t in Set.Ioc (0 : ℝ) 1, h' (x * c t) = h (x * c 1) - h x := by
    intro x
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (f := fun t => h (x * c t))
      (f' := fun t => h' (x * c t)) (fun r _ => ?_)
      ((hh'.comp (continuous_const.mul hc)).intervalIntegrable 0 1)
    · simpa only [h0, mul_one] using this
    · have h1 : HasDerivAt (fun t => h (x * c r * c t)) (h' (x * c r)) (r - r) := by
        rw [sub_self]; exact hd _
      have h2 := h1.comp_sub_const r r
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [mul_assoc, ← hadd, add_sub_cancel]
  have hint : Integrable (Function.uncurry fun (x : G) (t : ℝ) => h' (x * c t))
      (μ.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hcont : Continuous (Function.uncurry fun (x : G) (t : ℝ) => h' (x * c t)) :=
      hh'.comp (continuous_fst.mul (hc.comp continuous_snd))
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun t => i1.comp_mul_right (c t), ?_⟩
    simp only [Function.uncurry_apply_pair, fun t => integral_mul_right_eq_self (μ := μ) (fun x => ‖h' x‖) (c t)]
    exact integrable_const _
  have sw := integral_integral_swap hint
  simp only [pt, fun t => integral_mul_right_eq_self (μ := μ) h' (c t)] at sw
  rw [integral_sub (i0.comp_mul_right _) i0, integral_mul_right_eq_self h, sub_self] at sw
  simpa using sw.symm

variable {n : ℕ} {ε : Fin n → Bool}

noncomputable def mkU (g : Mx n) (hg : g ∈ UJset ε) : UJ ε :=
  ⟨(isUnit_of_UJ hg).unit, show inUJ ε _ from hg⟩

theorem umat_mkU (g : Mx n) (hg : g ∈ UJset ε) : umat (mkU g hg) = g := rfl

theorem umat_emb (ε : Fin n → Bool) : Topology.IsClosedEmbedding (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1

theorem CSm.continuous {f : Mx n → ℂ} (h : CSm ε f) : Continuous fun g : UJ ε => f (umat g) := by
  obtain ⟨F, h1, -, h3⟩ := h
  exact ((h3 [] (by simp)).congr fun g hg => (h1 g hg).symm).comp_continuous (umat_emb ε).continuous fun g => g.2

theorem cSm_of_contDiff (φ : Mx n → ℂ) (hφ : ContDiff ℝ ∞ (fun y : Fin n → Fin n → ℂ => φ (Matrix.of y))) :
    CSm ε φ := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  have hφ' : ContDiff ℝ ∞ φ := by
    let L : Mx n →L[ℝ] (Fin n → Fin n → ℂ) :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
    exact hφ.comp L.contDiff
  let F : List (Mx n) → Mx n → ℂ := fun l => l.foldr (fun X f g => fderiv ℝ f g (g * X)) φ
  have hF : ∀ l, ContDiff ℝ ∞ (F l) := by
    intro l
    induction l with
    | nil => exact hφ'
    | cons X l ih =>
      exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_id.mul contDiff_const)
  refine ⟨F, fun _ _ => rfl, fun l _ X _ g _ => ?_, fun l _ => (hF l).continuous.continuousOn⟩
  have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).const_mul g
  have h2 : HasFDerivAt (F l) (fderiv ℝ (F l) g) (g * NormedSpace.exp ((0 : ℝ) • X)) := by
    rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact (((hF l).differentiable (by simp)) g).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h3
  exact h3

def IsTest (ε : Fin n → Bool) (φ : Mx n → ℂ) : Prop := CSm ε φ ∧ HasCompactSupport fun g : UJ ε => φ (umat g)

theorem IsTest.integrable {φ F : Mx n → ℂ} (hφ : IsTest ε φ) (hF : CSm ε F) :
    Integrable (fun g : UJ ε => φ (umat g) * F (umat g)) (muG ε) :=
  (hφ.1.continuous.mul hF.continuous).integrable_of_hasCompactSupport hφ.2.mul_right

theorem exists_adjoint_ltr (x : Ltr ε) {φ : Mx n → ℂ} (hφ : IsTest ε φ) : ∃ ψ, IsTest ε ψ ∧ ∀ F, CSm ε F →
    ∫ g : UJ ε, φ (umat g) * ltrF x F (umat g) ∂(muG ε) = ∫ g : UJ ε, ψ (umat g) * F (umat g) ∂(muG ε) := by
  haveI : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  rcases x with ⟨X, hX⟩ | ⟨k, hk⟩
  · let c : ℝ → UJ ε := fun t => mkU (NormedSpace.exp (t • X)) (exp_mem_UJ hX t)
    have hc : Continuous c := (umat_emb ε).isInducing.continuous_iff.2 (continuous_exp_smul X)
    have h0 : c 0 = 1 := (umat_emb ε).injective (by
      change NormedSpace.exp ((0 : ℝ) • X) = 1
      simp)
    have hadd : ∀ a b, c (a + b) = c a * c b := fun a b => (umat_emb ε).injective (exp_add_smul X a b)
    have ht : IsTest ε (rder X φ) := by
      refine ⟨hφ.1.rder hX, hφ.2.mono' fun g hg => ?_⟩
      by_contra hn
      apply hg
      have h1 := notMem_tsupport_iff_eventuallyEq.1 hn
      have h2 : Filter.Tendsto (fun t => g * c t) (𝓝 0) (𝓝 g) := by
        have h4 : Continuous fun t => g * c t := continuous_const.mul hc
        simpa only [h0, mul_one] using h4.tendsto 0
      have h3 : (fun t : ℝ => φ (umat g * NormedSpace.exp (t • X))) =ᶠ[𝓝 0] fun _ => 0 := h2.eventually h1
      show deriv _ 0 = 0
      rw [h3.deriv_eq, deriv_const]
    refine ⟨(-1 : ℂ) • rder X φ, ⟨ht.1.smul _, ht.2.mul_left⟩, fun F hF => ?_⟩
    have key := integral_rder_eq_zero (muG ε) c hc h0 hadd (fun g => φ (umat g) * F (umat g))
      (fun g => rder X φ (umat g) * F (umat g) + φ (umat g) * rder X F (umat g))
      (hφ.1.continuous.mul hF.continuous)
      ((ht.1.continuous.mul hF.continuous).add (hφ.1.continuous.mul (hF.rder hX).continuous))
      hφ.2.mul_right (ht.2.mul_right.add hφ.2.mul_right) (fun g => by
        have := (hφ.1.hasDerivAt hX g.2).fun_mul (hF.hasDerivAt hX g.2)
        simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at this
        exact this)
    rw [integral_add (ht.integrable hF) (hφ.integrable (hF.rder hX))] at key
    simp only [Pi.smul_apply, smul_eq_mul, neg_mul, one_mul, integral_neg]
    exact eq_neg_of_add_eq_zero_right key
  · have hkU := K_le_UJ hk
    have hk' : k⁻¹ ∈ Kset ε := by
      refine ((maximal_compact_facts n ε).2.2.2.2 _).2 ⟨inv_mem_UJ hkU, ?_⟩
      rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hk.1)]
      exact Unitary.star_mem hk.1
    refine ⟨fun g => φ (g * k⁻¹), ⟨hφ.1.rt hk', ?_⟩, fun F hF => ?_⟩
    · exact hφ.2.comp_homeomorph (Homeomorph.mulRight (mkU k⁻¹ (K_le_UJ hk')))
    · rw [← integral_mul_right_eq_self (fun g : UJ ε => φ (umat g * k⁻¹) * F (umat g)) (mkU k hkU)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      show φ (umat g) * F (umat g * k) = φ (umat g * k * k⁻¹) * F (umat g * k)
      rw [Matrix.mul_assoc, mul_inv_UJ hkU, Matrix.mul_one]

theorem exists_adjoint_word (u : List (Ltr ε)) : ∀ {φ : Mx n → ℂ}, IsTest ε φ → ∃ ψ, IsTest ε ψ ∧ ∀ F, CSm ε F →
    ∫ g : UJ ε, φ (umat g) * wordF u F (umat g) ∂(muG ε) = ∫ g : UJ ε, ψ (umat g) * F (umat g) ∂(muG ε) := by
  induction u with
  | nil => exact fun hφ => ⟨_, hφ, fun _ _ => rfl⟩
  | cons x u ih =>
    intro φ hφ
    obtain ⟨ψ, h1, h2⟩ := exists_adjoint_ltr x hφ
    obtain ⟨χ, h3, h4⟩ := ih h1
    exact ⟨χ, h3, fun F hF => (h2 _ (hF.wordF u)).trans (h4 F hF)⟩

theorem eq_zero_of_test (H : UJ ε → ℂ) (hH : Continuous H)
    (h : ∀ φ, IsTest ε φ → ∫ g : UJ ε, φ (umat g) * H g ∂(muG ε) = 0) (y : UJ ε) : H y = 0 := by
  by_contra hy
  have hc : Continuous fun g => (star (H y) * H g).re := by fun_prop
  have hpos : 0 < (star (H y) * H y).re := by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  have hU : {g | 0 < (star (H y) * H g).re} ∈ 𝓝 y := (isOpen_lt continuous_const hc).mem_nhds hpos
  have hemb : Topology.IsClosedEmbedding (fun g : UJ ε => (Matrix.of.symm (umat g) : Fin n → Fin n → ℂ)) :=
    umat_emb ε
  rw [hemb.isInducing.nhds_eq_comap] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.1 hU
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hV
  have hψ : Continuous fun g : UJ ε => φ (Matrix.of.symm (umat g)) := hφd.continuous.comp hemb.continuous
  have hψc : HasCompactSupport fun g : UJ ε => φ (Matrix.of.symm (umat g)) := hφc.comp_isClosedEmbedding hemb
  have ht : IsTest ε (fun g => (φ (Matrix.of.symm g) : ℂ)) :=
    ⟨cSm_of_contDiff _ (Complex.ofRealCLM.contDiff.comp hφd), hψc.comp_left Complex.ofReal_zero⟩
  have hi : Integrable (fun g : UJ ε => star (H y) * ((φ (Matrix.of.symm (umat g)) : ℂ) * H g)) (muG ε) :=
    ((ht.1.continuous.mul hH).integrable_of_hasCompactSupport ht.2.mul_right).const_mul _
  have h1 := integral_re hi
  rw [integral_const_mul, h _ ht] at h1
  have h2 : 0 < ∫ g : UJ ε, φ (Matrix.of.symm (umat g)) * (star (H y) * H g).re ∂(muG ε) := by
    refine (hψ.mul hc).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := y) hψc.mul_right (fun g => ?_) ?_
    · by_cases h0 : φ (Matrix.of.symm (umat g)) = 0
      · rw [h0, zero_mul]; exact le_rfl
      · exact mul_nonneg (hφr ⟨_, rfl⟩).1 (le_of_lt (hVU (hφs (subset_tsupport _ h0))))
    · rw [hφ1, one_mul]; exact hpos.ne'
  refine h2.ne' ?_
  simp only [mul_left_comm (star (H y)), RCLike.re_to_complex, Complex.re_ofReal_mul] at h1
  simpa using h1

end GlobalTheory.TypeSum.CoefClos
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology


theorem _root_.GlobalTheory.T.continuousOn_integral_mul_right_translate_toMK : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) := by
  first | exact @GlobalTheory.AvgCont.continuousOn_avg_right_translates | exact GlobalTheory.AvgCont.continuousOn_avg_right_translates | (intros; apply GlobalTheory.AvgCont.continuousOn_avg_right_translates <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology


theorem _root_.GlobalTheory.T.exp_second_kind_coordinates : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    LinearIndependent ℝ b → (∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) →
    ∀ c : Fin d → ℝ, ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod := by
  first | exact @GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero | exact GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero | (intros; apply GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero <;> assumption)
end
