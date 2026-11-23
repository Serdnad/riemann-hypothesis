module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle040
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle060
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle059
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeTranslationOperatorEqPhaseMulNegComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsOrthogonalFrameNormsCoprimeOfUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle108
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle106
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle105
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle107
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle028
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle102
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle103
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle089
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle104
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle109
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.isOrthogonalComplementUnitaryFrame_of_matrix : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ x : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x ≠ 0 → ∀ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ, Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' → (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0 → ∀ ι : UpqT P' Q' → UpqT P Q, (∀ b, UpqT.mat (ι b) * C = C * UpqT.mat b ∧ UpqT.mat (ι b) *ᵥ x = x) → ActionCoordinates.IsPerpFrame x (Matrix.toLin' C) ι := by
  first | exact @GlobalTheory.PerpFrameOfMatrix.isPerpFrame_of_matrix | exact GlobalTheory.PerpFrameOfMatrix.isPerpFrame_of_matrix | (intros; apply GlobalTheory.PerpFrameOfMatrix.isPerpFrame_of_matrix <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

theorem _root_.GlobalTheory.T.dual_lattice_different_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ₀, IsStdChar F ψ₀ → ∀ v : HeightOneSpectrum (𝓞 F), (∀ t : Fv F v, t ∈ dualV F ψ₀ v ↔ ∀ d ∈ differentV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) ∧ dualIndex F ψ₀ v = normDifferentV F v := by
  first | exact @GlobalTheory.StdDual.dualV_eq_inv_different_cm | exact GlobalTheory.StdDual.dualV_eq_inv_different_cm | (intros; apply GlobalTheory.StdDual.dualV_eq_inv_different_cm <;> assumption)
end

section

namespace GlobalTheory.StabOrbit

theorem stabTransitive : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive :=
  GlobalTheory.Proof.SelfDualStabilizer.stabTransitive_iff.1 (stabTransitive_of_lemmas GlobalTheory.T.selfDual_lattices_unramified_place_no_hypothesis)

end GlobalTheory.StabOrbit
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem sign_of_sq_eq_one {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (h : χ ^ 2 = 1) (b : ℕ)
    (hb : Nat.Coprime b M) (θ : ℤ) (hθ : χ (b : ZMod M) = (θ : ℂ)) : θ = 1 ∨ θ = -1 := by
  have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  have h1 : (χ ^ 2) (b : ZMod M) = 1 := by rw [h]; exact MulChar.one_apply hu
  rw [MulChar.pow_apply' χ (by norm_num), hθ] at h1
  have h2 : θ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : (θ - 1) * (θ + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · left; omega
  · right; omega

theorem primesRel_holds : GlobalTheory.Lin.PrimesRel := by
  obtain ⟨a, ha, hA⟩ := GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion
  obtain ⟨a', ha', hA'⟩ := GlobalTheory.T.chebyshevPsiProgression_relative_error
  have hc₁ : 0 < min (1 / 8 : ℝ) (min a a') := lt_min (by norm_num) (lt_min ha ha')
  obtain ⟨c, hc, hE⟩ := hA _ hc₁ ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨c₂, c₃, C, h₂, h₃, hC, hP⟩ := hA' _ hc₁ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨c₂', c₃', C', h₂', h₃', hC', hQ⟩ := GlobalTheory.T.primeCount_relative_error_of_psi_relative_error c₂ c₃ C c h₂ h₃ hC hc
  refine ⟨_, c₂', c₃', C', c, hc₁, min_le_left _ _, h₂', h₃', hC', hc, fun M _ hM => ?_⟩
  obtain ⟨hU, hB, -⟩ := hE M hM
  refine ⟨hU, fun χ β h => (hB χ β h).2.2.2.2, fun b θ β hb hD X hX => ?_⟩
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hφ1 : (1 : ℝ) ≤ (M.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (by omega)
  have hφ2 : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hθ : θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ c / (M : ℝ) ^ 3 ≤ 1 - β) := by
    rcases hD with h | ⟨χ, hχ, hb'⟩
    · exact Or.inl h.1
    · obtain ⟨-, h78, -, -, hS⟩ := hB χ β hχ
      refine Or.inr ⟨sign_of_sq_eq_one χ hχ.1 b hb θ hb', h78, le_trans ?_ hS⟩
      have hl : 0 < Real.log M := Real.log_pos (by linarith)
      have hl2 : Real.log M ≤ M := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      apply div_le_div_of_nonneg_left hc.le (by positivity)
      calc (M : ℝ) ^ 2 * Real.log M ≤ (M : ℝ) ^ 2 * M := by gcongr
        _ = (M : ℝ) ^ 3 := by ring
  have := hQ M M.totient β θ (fun n => n ≡ b [MOD M]) hM3 hφ1 hφ2 hθ
    (fun u hu => by
      have := hP M b θ β u hM hb hD hu
      unfold psiAP at this
      convert this) X hX
  convert this

end GlobalTheory.Lin
end

section

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

noncomputable section
namespace GlobalTheory.MomTrans

variable {g : ℕ}

theorem ok_natCast_mul {d : ℕ} (n : ℕ) {z : ℂ} (h : z ∈ OK d) : (n : ℂ) * z ∈ OK d := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

theorem nnBasis_of_frame (q : ℕ) (S : Setup g) (hO : S.Ok) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ)
    (hx : ∀ i, x i ∈ S.La) (hb : ∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    (ha : ∀ i, 0 < a i ∧ Nat.Coprime (a i) q) : S.NNBasis q x := by
  classical
  have key : ∀ (c : Fin g → ℂ) (j : Fin g), beta S.d S.Hm (∑ i, c i • x i) (x j) = c j * a j := by
    intro c j
    rw [GlobalTheory.MomOne.Translates.beta_sum_left]
    simp [hb]
  have hli : LinearIndependent ℂ x := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := key c j
    rw [hc] at h
    have h0 : beta S.d S.Hm 0 (x j) = 0 := by simp [beta, hf]
    rw [h0] at h
    have : (a j : ℂ) ≠ 0 := by exact_mod_cast (ha j).1.ne'
    exact (mul_eq_zero.1 h.symm).resolve_right this
  let B := Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (by simp)).ge
  have hB : ∀ i, B i = x i := fun i => by simp [B]
  refine ⟨hx, fun y hy => ?_, fun c _ hc i => ?_⟩
  · have hy' : y = ∑ i, B.repr y i • x i := by
      conv_lhs => rw [← B.sum_repr y]
      simp only [hB]
    have hr : ∀ i, beta S.d S.Hm y (x i) = B.repr y i * a i := by
      intro i; conv_lhs => rw [hy']
      exact key _ i
    refine ⟨∏ i, a i, Nat.Coprime.prod_left fun i _ => (ha i).2,
      fun i => ((∏ j ∈ Finset.univ.erase i, a j : ℕ) : ℂ) * beta S.d S.Hm y (x i), fun i => ?_, ?_⟩
    · exact ok_natCast_mul _ (hO.2.2.2.2.2.2.1 y hy (x i) (hx i))
    · conv_lhs => rw [hy']
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [smul_smul, hr i, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      push_cast
      congr 1
      ring
  · exact (Fintype.linearIndependent_iff.1 hli) c hc i

theorem latInt_translate : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) (g : ℕ) (S : Setup g) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), Per S.d ι δ₀ θ Ω → S.Ok → GlobalTheory.MomOne.Split S.d q → S.IsTheta e → S.AlgJets δ₀ e → S.PrimeTo q t → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup e → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup (opU S.Hm t e) := by
  intro q _ ι δ₀ θ Ω g S e t hPer hO hS hth halg ht hLe
  obtain ⟨hIsTh, -, hδ, hall, hΩ, hLaws, -⟩ := hPer
  have hp : S.d.Prime := hO.1
  have h7 : S.d % 16 = 7 := hO.2.1
  have hq : q.Prime := Fact.out
  let lam : Qbar →+* ℂ_[q] := (ι : ℂ →+* ℂ_[q]).comp (algebraMap Qbar ℂ)
  have hlam : ∀ z : Qbar, ι (z : ℂ) = lam z := fun z => rfl
  have hqd : ¬ q ∣ S.d := (GlobalTheory.MomOne.okArith S.d q ι hp h7 hS).2.2.2.2.2.2
  obtain ⟨x, a, hx, hb, ha⟩ := GlobalTheory.MomOne.exists_orthFrame q g S hq hO hqd
  have hNN := nnBasis_of_frame q S hO x a hx hb ha
  obtain ⟨N, hN⟩ := GlobalTheory.MomOne.Translates.moments_of_translates S.d q lam δ₀ θ ι Ω hp h7 hS hIsTh hδ hall hlam hΩ
    hLaws g S rfl hO g x hNN e hth halg
  have h0 : S.PrimeTo q 0 := ⟨1, one_pos, Nat.coprime_one_left q, by simp [S.La.zero_mem]⟩
  obtain ⟨μ0, hμ0, hM0⟩ := hN 0 h0
  obtain ⟨μt, hμt, hMt⟩ := hN t ht
  have hU0 : opU S.Hm 0 e = e := by funext z; simp [opU, hf]
  have b0 := GlobalTheory.T.momentMeasure_norm_le_one_iff_latticeIntegral q ι lam δ₀ Ω g S g x 0 (opU S.Hm 0 e) μ0 hlam hδ hΩ hO hS hNN h0
    (GlobalTheory.MomOne.Translates.contDiff_opU S.Hm 0 hth.1) hM0
  have bt := GlobalTheory.T.momentMeasure_norm_le_one_iff_latticeIntegral q ι lam δ₀ Ω g S g x t (opU S.Hm t e) μt hlam hδ hΩ hO hS hNN ht
    (GlobalTheory.MomOne.Translates.contDiff_opU S.Hm t hth.1) hMt
  rw [hU0] at b0
  have hN1 : N ≤ 1 := hμ0 ▸ b0.2 hLe
  exact bt.1 (hμt ▸ hN1)

end GlobalTheory.MomTrans
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.highestWeightVector_mem_of_lt_stable_dualWeyl : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → ∀ M M' : Submodule k (MvPolynomial (Fin N × Fin N) k), Good M → Good M' → M < M' → M' ≤ dualWeyl k N N ν → hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  first | exact @GlobalTheory.Alc.hw_mem_of_lt | exact GlobalTheory.Alc.hw_mem_of_lt | (intros; apply GlobalTheory.Alc.hw_mem_of_lt <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.isRowOperatorStable_dualWeyl_and_GLSubmodules : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N), Good (nablaSq k N lam) ∧ ∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), GlobalTheory.Published.IsGLSubmodule k N lam M → Good M := by
  first | exact @GlobalTheory.Alc.good_nablaSq_and_submodules | exact GlobalTheory.Alc.good_nablaSq_and_submodules | (intros; apply GlobalTheory.Alc.good_nablaSq_and_submodules <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

private theorem szRow_eleven_le_splitBound : SzRow (fun _ D _ => 11 ≤ D.host.splitBound) := by
  intro eps heps _ C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(11 : ℝ) ^ (eps / C.P.Cpde / 5)⁻¹, ?_⟩⟩⟩
  intro D L hε hx hV
  have hH := hV.host
  have hC : (0 : ℝ) < C.P.Cpde := lt_of_lt_of_le one_pos hH.one_le
  have ha : 0 < eps / C.P.Cpde / 5 := by positivity
  have h1 : (11 : ℝ) ≤ L.sc.x ^ (eps / C.P.Cpde / 5) := by
    have h2 := Real.rpow_le_rpow (by positivity) hx ha.le
    rwa [Real.rpow_inv_rpow (by norm_num) ha.ne'] at h2
  have h3 : L.sc.x ^ (eps / C.P.Cpde / 5) ≤ L.sc.x ^ (L.sc.ez / 5) := by
    refine Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_
    have := hH.eps_div_le_ez
    rw [hε] at this
    linarith
  have h4 : 11 ≤ ⌊L.sc.x ^ (L.sc.ez / 5)⌋₊ := Nat.le_floor (by exact_mod_cast h1.trans h3)
  exact h4.trans hH.split_tie

theorem szRow_sizesAt : SzRow (fun _ _ L => SizesAt L) := by
  have h := ((((((((((GlobalTheory.T.sizes_sizeN_sizeM_sizeK_sizeT_sizeTT_sizeDe2_sizeLw.and GlobalTheory.T.sizes_sizeKRel).and GlobalTheory.T.sizes_sizeCond_sizeQD_sizePde).and GlobalTheory.T.sizes_sizeLa_sizeRho_sizeBot).and GlobalTheory.T.explicitChoice_sizeEta).and
    GlobalTheory.T.explicitChoice_sizeNodes).and GlobalTheory.T.explicitChoice_sizeLstar).and GlobalTheory.T.sizes_sizeDel).and GlobalTheory.T.sizes_sizeW_sizeBm_sizeXpp).and GlobalTheory.T.sizes_sizeG_sizeWords).and
    szRow_eleven_le_splitBound)
  refine h.imp ?_
  rintro C cD ch D L - - ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hM, hK, hT, hTT, hDe, hLw⟩, hKR⟩, hCo, hQD, hP⟩, hLa, hRho, hBot⟩, hEta⟩,
    hNo⟩, hLs⟩, hDel⟩, hW, hBm, hX⟩, hG, hWo⟩, h11⟩
  exact ⟨hN, hM, hK, hKR, hT, hCo, hQD, hTT, hLa, hRho, hBot, hDe, hLw, hEta, hNo, hLs, hDel, hW, hBm, hX, hG,
    hP, hWo, h11⟩

end GlobalTheory.EX
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.UnitTr

theorem lamC_mul_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left (mul_mem hx hy), ← map_mul]
  rfl

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem coc_nat_left (n : ℕ) (x y : HomE X.E a b) : coc A ((n : X.E) • x) y = n * coc A x y := by
  have h := (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.1
  induction n with
  | zero =>
    have := (h 0 0 y).1
    simp only [add_zero] at this
    simp only [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h _ _ _).1, ih]; push_cast; ring

theorem coc_nat_right (n : ℕ) (x y : HomE X.E a b) : coc A x ((n : X.E) • y) = n * coc A x y := by
  have h := (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.1
  induction n with
  | zero =>
    have := (h x 0 0).2.1
    simp only [add_zero] at this
    simp only [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h _ _ _).2.1, ih]; push_cast; ring

theorem coc_rat (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (hX : X.Ok) (hL : A.LaHyp a b ∅)
    (hA : A.AA ≠ ⊥) (hN : IsSdLat N) (hN' : IsSdLat N') (x y : HomE X.E a b) : ∃ r : ℚ, coc A x y = (r : ℝ) := by
  obtain ⟨hδ, -, -, -, hFG, hLa⟩ := hL
  have hfull := (GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hFG hA hN hN').2.1
  have hint := (GlobalTheory.T.heisenbergCocycleForm_integral_selfDual X A a b N N' hX hδ (hLa N N' hN hN').2).2.2
  obtain ⟨n, hn, hx⟩ := hfull x
  obtain ⟨n', hn', hy⟩ := hfull y
  obtain ⟨k, hk⟩ := hint ((n : X.E) • x) ((n' : X.E) • y) fun Q =>
    ⟨1, one_ne_zero, by simpa using le_locP Q _ hx, by simpa using le_locP (conjPrime₂ Q) _ hy⟩
  rw [coc_nat_left, coc_nat_right] at hk
  refine ⟨(k : ℚ) / (n * n'), ?_⟩
  have h1 : (n : ℝ) ≠ 0 := by positivity
  have h2 : (n' : ℝ) ≠ 0 := by positivity
  push_cast
  rw [← hk]
  field_simp

theorem Wx_const_mul (x : HomE X.E a b) (c : ℂ) (F : VCx X.Tau a b → ℂ) :
    Wx A x (fun z => c * F z) = fun z => c * Wx A x F z := by
  funext z
  simp only [Wx, opU]
  ring

theorem Wx_per (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (hL : A.LaHyp a b ∅)
    (hN : IsSdLat N) (hN' : IsSdLat N') (l : HomE X.E a b) (hl : l ∈ per A N N') :
    Wx A l (A.e a b N N') = A.e a b N N' := by
  funext z
  exact (hL.2.2.2.2.2 N N' hN hN').1 (emb A l) ⟨l, hl, rfl⟩ z

theorem moments_unit_translate : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]), X.Ok → A.LaHyp a b ∅ → A.AA ≠ ⊥ → A.ESmooth a b → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → IsSdLat N → IsSdLat N' → PtMom A a b lam ι un (star (ϖ : X.E) / (ϖ : X.E)) → ∀ (t : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * (ϖ : X.E)) • t ∈ per A N N' → (∀ m, jetC A.cD (Wx A t (A.e a b N N')) m ∈ TaylorLogMetric.Qbar) ∧ InIntClosure (per A N N' : Set (HomE X.E a b)) (ptTab ι un) Set.univ fun m => TaylorLogMetric.lamC lam (jetC A.cD (Wx A t (A.e a b N N')) m) := by
  intro X A a b ϖ p N N' _ lam ι un hX hL hA hS hϖ hcop hN hN' hP t n hn ht
  have hp : p.Prime := Fact.out
  have hH := GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b
  have hroot := (GlobalTheory.T.algebraicNumbers_padicPlaces_facts X.K p A.σ₀ ι).2.2 lam
  have hϖE : (ϖ : X.E) * star (ϖ : X.E) = (p : X.E) := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) hϖ
    simpa [Fields.conjO, starRingEnd_apply] using this
  have hϖ0 : (ϖ : X.E) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hϖE
    exact hp.ne_zero (by exact_mod_cast hϖE.symm)
  have hbar : ((X.conjO ϖ : 𝓞 X.E) : X.E) = star (ϖ : X.E) := by
    simp [Fields.conjO, starRingEnd_apply]
  have hnϖ : IsCoprime (n : 𝓞 X.E) ϖ := by
    have h1 : IsCoprime (n : 𝓞 X.E) (p : 𝓞 X.E) := Nat.Coprime.cast hn
    rw [← hϖ] at h1
    exact h1.of_mul_right_left
  obtain ⟨α, β, hαβ⟩ := hnϖ.mul_left hcop.symm
  have hαβE : (α : X.E) * (n * star (ϖ : X.E)) + β * ϖ = 1 := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) hαβ
    simpa [hbar] using this
  have hsm : ∀ (r : 𝓞 X.E) (x : HomE X.E a b), x ∈ per A N N' → (r : X.E) • x ∈ per A N N' := fun r x hx =>
    Submodule.smul_mem _ r hx
  set t' : HomE X.E a b := ((β : X.E) * ϖ) • t with ht'
  have ht'M : (n : X.E) • t' ∈ per A N N' := by
    have := hsm β _ ht
    rw [smul_smul] at this
    rw [ht', smul_smul]
    convert this using 2
    ring
  obtain ⟨N₀, hN₀, hJ, hC⟩ := hP N N' hN hN' t' ⟨n, hn, ht'M⟩
  obtain ⟨α', β', h'⟩ : IsCoprime (N₀ : 𝓞 X.E) (p : 𝓞 X.E) := Nat.Coprime.cast hN₀
  have h'E : (α' : X.E) * N₀ + β' * (ϖ * star (ϖ : X.E)) = 1 := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) h'
    rw [hϖE]
    simpa using this
  set m₁ : HomE X.E a b := ((α' * α : 𝓞 X.E) : X.E) • (((n : X.E) * (ϖ : X.E)) • t) with hm₁
  set l : HomE X.E a b := ((β' * X.conjO ϖ * X.conjO ϖ * α : 𝓞 X.E) : X.E) • (((n : X.E) * (ϖ : X.E)) • t) with hl
  have hm₁M : m₁ ∈ per A N N' := hsm _ _ ht
  have hlM : l ∈ per A N N' := hsm _ _ ht
  set y : HomE X.E a b := ((N₀ : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • m₁ with hy
  have hdec : y + (t' + l) = t := by
    rw [hy, hm₁, hl, ht']
    simp only [smul_smul, ← add_smul]
    conv_rhs => rw [← one_smul X.E t]
    congr 1
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at hbar hαβE h'E hϖ0 ⊢
    rw [hbar]
    field_simp
    linear_combination (α * n * star (ϖ : X.E)) * h'E + hαβE
  obtain ⟨r₁, hr₁⟩ := coc_rat A N N' hX hL hA hN hN' t' l
  obtain ⟨r₂, hr₂⟩ := coc_rat A N N' hX hL hA hN hN' y (t' + l)
  set ζ : ℂ := Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((-(r₁ + r₂) : ℚ) : ℝ) : ℂ)) with hζ
  have hkey : Wx A t (A.e a b N N') = fun z => ζ * Wx A y (Wx A t' (A.e a b N N')) z := by
    have e1 := hH.1 t' l (A.e a b N N')
    rw [Wx_per A N N' hL hN hN' l hlM] at e1
    rw [e1, Wx_const_mul, hH.1 y (t' + l), hdec, hr₁, hr₂]
    funext z
    rw [hζ, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    have : -(2 * (Real.pi : ℂ)) * Complex.I * (((-(r₁ + r₂) : ℚ) : ℝ) : ℂ) + -(2 * (Real.pi : ℂ)) * Complex.I * ((r₁ : ℝ) : ℂ) +
        -(2 * (Real.pi : ℂ)) * Complex.I * ((r₂ : ℝ) : ℂ) = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero, one_mul]
  have hjet : ∀ m, jetC A.cD (Wx A t (A.e a b N N')) m = ζ * jetC A.cD (Wx A y (Wx A t' (A.e a b N N'))) m := by
    intro m
    have := hH.2.2.2.2.2.2.2 Unit {()} (fun _ => ζ) (fun _ => Wx A y (Wx A t' (A.e a b N N')))
      (fun _ _ => hH.2.2.2.2.2.2.1 _ _ (hH.2.2.2.2.2.2.1 _ _ (hS N N' hN hN'))) m
    rw [hkey]
    simpa only [Finset.sum_singleton] using this
  have hζQ := hroot (-(r₁ + r₂))
  refine ⟨fun m => ?_, ?_⟩
  · rw [hjet]
    exact mul_mem hζQ.1 (hJ m₁ hm₁M m)
  · have hbrk : ∀ x, ‖TaylorLogMetric.lamC lam (brkE A y x)‖ = 1 := by
      intro x
      obtain ⟨s₁, hs₁⟩ := coc_rat A N N' hX hL hA hN hN' x y
      obtain ⟨s₂, hs₂⟩ := coc_rat A N N' hX hL hA hN hN' y x
      have := (hroot (s₁ - s₂)).2
      rw [hH.2.2.2.2.1, hH.2.2.1, hs₁, hs₂]
      rwa [Rat.cast_sub] at this
    have := clo_comb (Sup' := (per A N N' : Set (HomE X.E a b))) (tab' := ptTab ι un) (M' := Set.univ) hC ({()} : Finset Unit)
      (fun _ _ => TaylorLogMetric.lamC lam ζ) (fun _ m => (m₁, m)) (fun _ _ _ _ => hm₁M)
      (fun x => TaylorLogMetric.lamC lam ζ * TaylorLogMetric.lamC lam (brkE A y x))
      (fun x _ => by rw [norm_mul, hbrk, hζQ.2, one_mul]) (fun _ h h' => absurd h h')
      (fun x _ m _ => by simp only [Finset.sum_singleton]; rw [mul_assoc])
    refine clo_congr this subset_rfl subset_rfl fun m _ => ?_
    simp only [Finset.sum_singleton]
    rw [hjet, lamC_mul_of_mem lam hζQ.1 (hJ m₁ hm₁M m)]

end GlobalTheory.MomT.UnitTr
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryGroup_neg_form_compatible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E), J' = -J → ∃ φ : HA (AF F) σ J ≃ₜ* HA (AF F) σ J', (∀ h, HA.mat (AF F) σ J' (φ h) = HA.mat (AF F) σ J h) ∧ (∀ h, h ∈ HFinIn (AF F) σ J ↔ φ h ∈ HFinIn (AF F) σ J') ∧ ∀ (L : Set (Fin M → E)) h, h ∈ StabFin.SFin σ J L ↔ φ h ∈ StabFin.SFin σ J' L := by
  first | exact @GlobalTheory.unitary_neg_same | exact GlobalTheory.unitary_neg_same | (intros; apply GlobalTheory.unitary_neg_same <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.negDefinite_selfDualStabilizer_volume_one : ∀ (D : D7) (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) → ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram), IsVolMeas D W 0 n μ → μ (StabFin.SFin D.sp.cm.sig W.gram (L0c D W) : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) = 1 := by
  first | exact @GlobalTheory.NegDefStab.measure_SFin_negDef | exact GlobalTheory.NegDefStab.measure_SFin_negDef | (intros; apply GlobalTheory.NegDefStab.measure_SFin_negDef <;> assumption)
end
