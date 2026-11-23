module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle340
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle009
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle242
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle017
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle020
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle462
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PsiInnerSIns
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle005
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle035

@[expose] public section

section

noncomputable section

open scoped Matrix ComplexConjugate
open Matrix Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Inertia NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open ReciprocityTheory.ChartRestriction.G


theorem wittLBlt : WittLBlt := by
  intro D V k hk hS
  letI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hH := GlobalTheory.Doubling.isHermND_gram V
  have hσ : ∀ x : D.host.E, D.sp.cm.sig x = FD.cc x := fun x => rfl
  have hT : ∀ a b, FD.cc (V.gram a b) = V.gram b a := fun a b => by rw [← hσ]; exact hH.1 b a
  have hTt : V.gramᵀ = V.gram.map FD.cc := Matrix.ext fun a b => (hT a b).symm
  have hG : ∀ a b, FD.cc (V.gramᵀ a b) = V.gramᵀ b a := fun a b => by
    simp only [transpose_apply]; exact hT b a
  have hd : V.gramᵀ.det ≠ 0 := by rw [det_transpose]; exact hH.2

  have hsigτ : ∀ τ0 : D.what₂.Tau, k ≤ posIndex (V.gram.map (tauE D τ0)) ∧ k ≤ negIndex (V.gram.map (tauE D τ0)) := by
    intro τ0
    obtain ⟨ε, fr, hu, hfr, hp, hq⟩ := hS τ0
    have hP : (fr.map (starRingEnd ℂ)).det ≠ 0 := by
      have : (fr.map (starRingEnd ℂ)).det = starRingEnd ℂ fr.det := (RingHom.map_det (starRingEnd ℂ) fr).symm
      rw [this]
      exact (map_ne_zero _).2 hu.ne_zero
    have hd' : (fr.map (starRingEnd ℂ))ᵀ * V.gram.map (tauE D τ0) * (fr.map (starRingEnd ℂ)).map (starRingEnd ℂ) =
        diagonal (PositivityTheory.Rg.Sw.sgn ε) := by
      have h1 : (fr.map (starRingEnd ℂ)).map (starRingEnd ℂ) = fr := by
        ext a b; simp
      rw [h1]
      exact hfr
    rw [posIndex_eq_card_of_congr_diagonal hP hd', negIndex_eq_card_of_congr_diagonal hP hd']
    have e1 : (Finset.univ.filter fun a => 0 < (PositivityTheory.Rg.Sw.sgn ε a).re) = Finset.univ.filter fun a => ε a = true := by
      apply Finset.filter_congr
      intro a _
      simp only [PositivityTheory.Rg.Sw.sgn]
      cases ε a <;> norm_num
    have e2 : (Finset.univ.filter fun a => (PositivityTheory.Rg.Sw.sgn ε a).re < 0) = Finset.univ.filter fun a => ε a = false := by
      apply Finset.filter_congr
      intro a _
      simp only [PositivityTheory.Rg.Sw.sgn]
      cases ε a <;> norm_num
    rw [e1, e2]
    exact ⟨hp, hq⟩
  have hsig : ∀ φ : D.host.E →+* ℂ, k ≤ posIndex (V.gram.map φ) ∧ k ≤ negIndex (V.gram.map φ) := by
    intro φ
    obtain ⟨τ0, h | h⟩ := Formalism.L2.Fam.ThC.tauE_or (D := D) φ
    · rw [← h]; exact hsigτ τ0
    · have hφ : φ = ComplexEmbedding.conjugate (tauE D τ0) := by rw [h]; exact (star_star φ).symm
      rw [hφ, posIndex_map_conjugate _ hT, negIndex_map_conjugate _ hT]
      exact hsigτ τ0
  have hsigT : ∀ φ : D.host.E →+* ℂ, k ≤ posIndex (V.gramᵀ.map φ) ∧ k ≤ negIndex (V.gramᵀ.map φ) := by
    intro φ
    have hm : V.gramᵀ.map φ = V.gram.map (ComplexEmbedding.conjugate φ) := by
      rw [hTt]
      ext a b
      simp only [Matrix.map_apply]
      exact WLt.emb_cc φ _
    rw [hm]
    exact hsig _
  obtain ⟨W, hWr, hW⟩ := WLt.main_iso k V.gramᵀ hG hd (by simpa using hk) hsigT
  rw [← GlobalTheory.SiegelWeilLitCompare.wittIdx_eq]
  refine le_csSup ⟨V.rank, ?_⟩ ⟨W, fun x hx y hy => ?_, hWr⟩
  · rintro r ⟨W', -, rfl⟩
    exact (Submodule.finrank_le W').trans (by simp)
  · have h := hW y hy x hx
    simp only [WLt.hf, dotProduct, mulVec, Function.comp_apply] at h
    show ∑ i, ∑ j, FD.cc (x i) * V.gram i j * y j = 0
    rw [Finset.sum_comm, ← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    show FD.cc (x b) * V.gram b a * y a = y a * (V.gram b a * FD.cc (x b))
    ring

end PositivityTheory.Rg.Sw.Glob

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OG

variable {D : D7}

theorem compAt_zero' (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} : compAt θ τ (0 : Mx D m n) = 0 := by
  ext i j
  simp [compAt]

theorem compAt_one' (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} : compAt θ τ (1 : Mx D n n) = 1 := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem compAt_J (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} :
    compAt θ τ (blk4 (0 : Mx D n n) 1 (-1) 0) = blk4 0 1 (-1) 0 := by
  rw [component_block_matrix, GlobalTheory.RealParamSize.compAt_neg, compAt_zero', compAt_one']

theorem fin_J {n : ℕ} : (blk4 (0 : Mx D n n) 1 (-1) 0).map (finPart D) = blk4 0 1 (-1) 0 := by
  rw [finite_part_block_matrix, Matrix.map_neg _ (map_neg (finPart D)), Matrix.map_zero _ (map_zero (finPart D)),
    Matrix.map_one _ (map_zero (finPart D)) (map_one (finPart D))]

theorem iota_conj {θ : InfFam D} {τ : D.what₂.Tau} {n : ℕ} {ι : GR n →* G D n} (hθ : IsInfFam θ)
    (hι : IsPlaceEmb θ τ ι) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) (y yn : GR n) (c : Matrix (Fin n) (Fin n) ℂ)
    (hyc : mR y = nbar c) (hyn : mR yn = nU (-c)) : ι yn = w⁻¹ * ι y * w := by
  apply g_ext
  have hm : mat (w⁻¹ * ι y * w) = mat w⁻¹ * mat (ι y) * mat w := rfl
  rw [hm, mat_inv_w w hw, hw]
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [Matrix.map_mul, Matrix.map_mul, (hι.2 yn).2.2, (hι.2 y).2.2, Matrix.map_neg _ (map_neg (finPart D)), fin_J, mul_one,
      neg_mul, jsq, neg_neg]
  · intro τ'
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.RealParamSize.compAt_neg, compAt_J]
    by_cases h : τ' = τ
    · subst h
      rw [(hι.2 yn).1, (hι.2 y).1, hyn, hyc]
      change blk4 1 (-c) 0 1 = -blk4 0 1 (-1) 0 * blk4 1 0 c 1 * blk4 0 1 (-1) 0
      rw [neg_block_matrix, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul]
      simp
    · rw [(hι.2 yn).2.1 τ' h, (hι.2 y).2.1 τ' h, mul_one, neg_mul, jsq, neg_neg]

end PositivityTheory.Rg.Sw.Glob.OG
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def rr (m n : ℕ) : ℝ := ((Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 : ℕ) : ℝ)

theorem integrable_rho : Integrable (fun u : Fin m → Fin n → ℂ => (1 + ‖u‖) ^ (-rr m n)) := by
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  apply integrable_one_add_norm
  unfold rr; push_cast; linarith


set_option synthInstance.maxHeartbeats 400000 in
theorem hloc_away {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    (K : Set (Fin m → Fin n → ℂ)) (hK : IsCompact K) :
    ∫⁻ z, K.indicator 1 (piF θ τ fr z) * ‖Ψ z‖ₑ ∂μ ≠ ∞ := by
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) 1 one_pos
  have hmem := hΨ.2 (gs 1) ⟨S, funext hS⟩
  have hI := GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ μ ⟨_, hmem⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hgc : Continuous fun u : Fin m → Fin n → ℂ => ‖gs (n := n) 1 u‖ :=
    continuous_norm.comp (S.continuous.congr fun u => hS u)
  obtain ⟨u0, -, hu0⟩ := hK.exists_isMinOn hne hgc.continuousOn
  have hδ : 0 < ‖gs (n := n) 1 u0‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hle : ∀ z, K.indicator 1 (piF θ τ fr z) * ‖Ψ z‖ₑ ≤
      ENNReal.ofReal (‖gs (n := n) 1 u0‖)⁻¹ * ‖tens θ τ fr (gs 1) Ψ z‖ₑ := by
    intro z
    by_cases hz : piF θ τ fr z ∈ K
    · rw [Set.indicator_of_mem hz, Pi.one_apply, one_mul]
      have h1 : tens θ τ fr (gs 1) Ψ z = gs (n := n) 1 (piF θ τ fr z) * Ψ z := rfl
      rw [h1, enorm_mul, ← mul_assoc]
      conv_lhs => rw [← one_mul ‖Ψ z‖ₑ]
      gcongr
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [← div_eq_inv_mul, one_le_div hδ]
      exact hu0 hz
    · rw [Set.indicator_of_notMem hz, zero_mul]; exact zero_le
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.hasFiniteIntegral.ne



theorem hint_int {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure]
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (x : Mx D V.rank n) :
    Integrable (fun z => (1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n) * ‖Bw ψ V θ τ fr Ψ x z‖) μ := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hΨc := cont_of_away hθ hΨ
  have hπ := continuous_piF (n := n) hθ τ fr
  obtain ⟨c, hc⟩ := Fib.fib_meas μ (piF θ τ fr) hπ (sIns τ fr) (piF_sIns hθ τ hdet) (fun z => ‖Ψ z‖ₑ)
    hΨc.enorm.measurable (fun z u => by simp only [away_add hθ hΨ]) (hloc_away hθ μ hΨ)
  have hρc : Continuous fun u : Fin V.rank → Fin n → ℂ => (1 + ‖u‖) ^ (-rr V.rank n) :=
    (continuous_const.add continuous_norm).rpow_const fun u => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg u)).ne'
  refine ⟨((hρc.comp hπ).mul (continuous_Bw hθ hψ hΨ x).norm).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have e1 : ∀ z, ‖(1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n) * ‖Bw ψ V θ τ fr Ψ x z‖‖ₑ =
      ENNReal.ofReal ((1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n)) * ‖Ψ z‖ₑ := by
    intro z
    rw [enorm_mul, norm_Bw hψ, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm (Ψ z), Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      enorm_norm, ofReal_norm_eq_enorm]
  simp_rw [e1]
  have e2 : ∫⁻ z, ENNReal.ofReal ((1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n)) * ‖Ψ z‖ₑ ∂μ =
      ∫⁻ u, ENNReal.ofReal ((1 + ‖u‖) ^ (-rr V.rank n)) ∂((μ.withDensity fun z => ‖Ψ z‖ₑ).map (piF θ τ fr)) := by
    rw [lintegral_map (f := fun u : Fin V.rank → Fin n → ℂ => ENNReal.ofReal ((1 + ‖u‖) ^ (-rr V.rank n)))
      (ENNReal.measurable_ofReal.comp hρc.measurable) hπ.measurable]
    have e := lintegral_withDensity_eq_lintegral_mul μ hΨc.enorm.measurable
      ((ENNReal.measurable_ofReal.comp hρc.measurable).comp hπ.measurable)
    simp only [Function.comp_def] at e
    rw [e]
    congr 1; ext z; simp [mul_comm]
  rw [e2, hc, lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have hI := (integrable_rho (m := V.rank) (n := n)).hasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) hI
  congr 1; ext u
  rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def ker (ε : Fin m → Bool) (t : ℝ) (v u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ) * (((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℂ))

theorem ftLoc_eq_ker (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (v : Fin m → Fin n → ℂ) :
    ftLoc ε t f v = ∫ u, f u * ker ε t v u := rfl



theorem integrand_eq {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) :
    tens θ τ fr f Ψ y * ψ (trA (Matrix.trace (inner V x y))) =
      (f (piF θ τ fr y) * ker ε (tLoc l τ) (piF θ τ fr x) (piF θ τ fr y)) * Bw ψ V θ τ fr Ψ x y := by
  have hsplit : inner V x y = inner V x (y - sIns τ fr (piF θ τ fr y)) + inner V x (sIns τ fr (piF θ τ fr y)) := by
    rw [← GlobalTheory.CompanionTheory.EisCovar.Weyl.inner_add_right, sub_add_cancel]
  have hψ2 : ψ (trA (Matrix.trace (inner V x y))) =
      ψ (trA (Matrix.trace (inner V x (y - sIns τ fr (piF θ τ fr y))))) *
        ψ (trA (Matrix.trace (inner V x (sIns τ fr (piF θ τ fr y))))) := by
    rw [hsplit, Matrix.trace_add, GlobalTheory.CompanionTheory.EisCovar.Weyl.trA_add, AddChar.map_add_eq_mul]
  rw [hψ2, psi_inner_sIns hθ hl hfr]
  have hp : (fr⁻¹ * compAt θ τ y : Matrix (Fin V.rank) (Fin n) ℂ) = piF θ τ fr y := rfl
  unfold Bw tens ker
  rw [hp]
  ring

end PositivityTheory.Rg.Sw.Glob.FTH
end
end
