module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle011
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle442
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle443
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle475
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.HighestWeightDifferencesNat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
public import Formalism.RealPlaceAnalysis.Bundle002
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Formalism.UnipotentAdelicQuotients.SWXSDefs

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CfFJ

open _root_.Metric Set

variable {D : D7} {n ρ p : ℕ}

theorem conj_chz (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) :
    Continuous (fun z : hermA D ρ => conj (chz ψ b₀ z)) ∧ ∀ z : hermA D ρ, ‖conj (chz ψ b₀ z)‖ = 1 := by
  obtain ⟨hc, -⟩ := GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar D ρ ψ hψ b₀
  have h1 : ∀ z : hermA D ρ, conj (chz ψ b₀ z) =
      ψ (-halfTr (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ))) := by
    intro z
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 _)]
    rfl
  refine ⟨by simpa only [h1] using hc, fun z => ?_⟩
  rw [RCLike.norm_conj]
  exact hψ.2.1 _

theorem cf_eq (d : Polynomial ℂ) (E : ℂ → G D n → ℂ) (s₀ : ℂ) (ε : ℝ) (k : ℕ) (g : G D n) :
    cf d E s₀ ε k g = ∮ w in C(s₀, ε),
      ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * E w g := by
  have h : ∀ w : ℂ, ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * E w g =
      (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) * (E w g / d.eval w)) := fun w => by ring
  simp only [h, circleIntegral.integral_const_mul, cf]

theorem ker_eq (d : Polynomial ℂ) (F : ℂ → ℂ) (s₀ : ℂ) (ε : ℝ) (k : ℕ) :
    ∮ w in C(s₀, ε), ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * F w =
      (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(s₀, ε), (w - s₀) ^ (k - 1) * (F w / d.eval w) := by
  have h : ∀ w : ℂ, ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * F w =
      (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) * (F w / d.eval w)) := fun w => by ring
  simp only [h, circleIntegral.integral_const_mul]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem cfFJ_of_pcBound : PcBound → CfFJ := by
  intro hPc D n H φ s₀ U d E σ hC ε hR
  obtain ⟨hε, hB, hroot⟩ := hR
  have hU := hC.isOpen
  have hS : sphere s₀ ε ⊆ U := sphere_subset_closedBall.trans hB
  have hsne : ∀ z ∈ sphere s₀ ε, z ≠ s₀ := by
    rintro z hz rfl
    simp [hε.ne] at hz
  set a : ℕ → ℂ → ℂ := fun k w => (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w) with ha_def
  have ha : ∀ k, ContinuousOn (a k) (sphere s₀ ε) := fun k =>
    continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).pow _).div
      d.continuous.continuousOn (fun z hz => hroot z (sphere_subset_closedBall hz) (hsne z hz)))
  have hcf : ∀ k g, cf d E s₀ ε k g = ∮ w in C(s₀, ε), a k w * E w g := fun k g => cf_eq d E s₀ ε k g
  refine ⟨fun k => ⟨?_, ?_⟩, ⟨d.rootMultiplicity s₀ + 1, fun k hk => funext fun g => ?_⟩, ?_⟩
  · have : cf d E s₀ ε k = fun g => ∮ w in C(s₀, ε), a k w * E w g := funext (hcf k)
    rw [this]
    exact circle_cont hC.cont hε.le hS (ha k)
  · intro γ hγ g
    rw [hcf, hcf]
    exact circleIntegral.integral_congr hε.le fun w hw => by
      simp only [hC.inv w (hS hw) γ hγ g]
  · have h0 := circle_zero hU (hC.hol g) hC.ne hε hB hroot (j := k - 1) (by omega)
    simp only [cf, h0, mul_zero, Pi.zero_apply]
  · intro ρ p hn M m ψ hψ b₀ g η hη
    obtain ⟨-, hcov⟩ := hPc D n ρ p hn M m ψ hψ b₀
    obtain ⟨C, hCc, hcover, -⟩ := hcov g
    obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ p
    haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
    haveI : FirstCountableTopology (Mx D ρ p) := inferInstance
    haveI : FirstCountableTopology (Mx D ρ p × Mx D ρ p) := inferInstance
    obtain ⟨hμh, -, hμ1⟩ := m.hμ
    obtain ⟨-, -, hl1⟩ := m.hz
    haveI : SFinite m.μ := inferInstance
    haveI : IsFiniteMeasure (m.lz.restrict m.𝓖) := ⟨by rw [Measure.restrict_apply_univ, hl1]; exact ENNReal.one_lt_top⟩
    haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top⟩
    obtain ⟨hχc, hχ1⟩ := conj_chz ψ hψ b₀
    have hκ1 : Integrable (fun z : hermA D ρ => conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖) :=
      Integrable.of_bound hχc.aestronglyMeasurable 1 (Eventually.of_forall fun z => (hχ1 z).le)
    have hκ2 : Integrable (fun _ : Mx D ρ p => (1 : ℂ)) (m.μ.restrict m.𝓕) := integrable_const _
    have hκ3 : Integrable (fun y => conj (η y)) m.μ :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hη
    set pt : (Mx D ρ p × Mx D ρ p) × hermA D ρ → G D n :=
      fun u => M.nzx u.2 0 * (M.nzx 0 u.1.2 * (M.sh u.1.1 * g)) with hpt_def
    have hpt : Continuous pt :=
      (M.nzx_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => (u.2, (0 : Mx D ρ p))) (by fun_prop)).mul
        ((M.nzx_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => ((0 : hermA D ρ), u.1.2)) (by fun_prop)).mul
          ((M.sh_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => u.1.1) (by fun_prop)).mul continuous_const))
    have h0 : Fam U (fun w u => E w (pt u)) := by
      refine ⟨hC.cont.comp (continuous_fst.prodMk (hpt.comp continuous_snd)).continuousOn
        (fun q hq => ⟨hq.1, mem_univ _⟩), fun u => hC.hol _, fun K hK hKc => ?_⟩
      obtain ⟨B, hBd⟩ := (hKc.prod hCc).exists_bound_of_continuousOn
        (hC.cont.mono (prod_mono hK (subset_univ _)))
      refine ⟨B, fun w hw u => ?_⟩
      obtain ⟨γ, hγ, hmem⟩ := hcover u.2 u.1.2 u.1.1
      rw [show E w (pt u) = E w (γ * pt u) from (hC.inv w (hK hw) γ hγ _).symm]
      exact hBd (w, γ * pt u) ⟨hw, hmem⟩
    have h1 : Fam U (fun w (u : Mx D ρ p × Mx D ρ p) => zc M m ψ b₀ (E w) (M.nzx 0 u.2 * (M.sh u.1 * g))) :=
      h0.stage hU hκ1
    have h2 : Fam U (fun w (y : Mx D ρ p) => pc M m ψ b₀ (E w) (M.sh y * g)) := by
      have := h1.stage hU hκ2
      simp only [mul_one] at this
      exact this
    have h3 : Fam U (fun w (_ : Unit) => FJ M m ψ b₀ (E w) g η) :=
      (h2.comp (φ := fun u : Unit × Mx D ρ p => u.2) continuous_snd).stage hU hκ3
    refine ⟨h3.hol (), fun k => ?_⟩
    have e1 : ∀ y x, zc M m ψ b₀ (cf d E s₀ ε k) (M.nzx 0 x * (M.sh y * g)) =
        ∮ w in C(s₀, ε), a k w * zc M m ψ b₀ (E w) (M.nzx 0 x * (M.sh y * g)) := by
      intro y x
      have := (h0.comp (φ := fun z : hermA D ρ => ((y, x), z)) (by fun_prop)).swap hκ1 hε hS (ha k)
      simp only [zc, hcf, pt] at this ⊢
      exact this
    have e2 : ∀ y, pc M m ψ b₀ (cf d E s₀ ε k) (M.sh y * g) =
        ∮ w in C(s₀, ε), a k w * pc M m ψ b₀ (E w) (M.sh y * g) := by
      intro y
      have := (h1.comp (φ := fun x : Mx D ρ p => (y, x)) (by fun_prop)).swap hκ2 hε hS (ha k)
      simp only [mul_one] at this
      simp only [PositivityTheory.Rg.Rsw.pc, e1]
      exact this
    have e3 : FJ M m ψ b₀ (cf d E s₀ ε k) g η = ∮ w in C(s₀, ε), a k w * FJ M m ψ b₀ (E w) g η := by
      have := h2.swap hκ3 hε hS (ha k)
      simp only [FJ, e2]
      exact this
    rw [e3]
    exact ker_eq d _ s₀ ε k

end GlobalTheory.CompanionTheory.CfFJ
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.EisCovar PositivityTheory.GramSchwartzFunctions.EC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTw

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

section Blocks

variable {R : Type} [CommRing R]

theorem block_mul₂ (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one (hn : ρ + p = n) : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (1 : Matrix (Fin p) (Fin p) R) = 1 := by
  simp only [bl, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_zero (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem bl_add (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  simp only [bl]
  rw [← Matrix.fromBlocks_add]
  rfl

theorem blockMatrix_inj (hn : ρ + p = n) {a a' : Matrix (Fin ρ) (Fin ρ) R} {b b' : Matrix (Fin ρ) (Fin p) R}
    {c c' : Matrix (Fin p) (Fin ρ) R} {d d' : Matrix (Fin p) (Fin p) R}
    (h : bl hn a b c d = bl hn a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix (finSumFinEquiv.trans (finCongr hn)) (finSumFinEquiv.trans (finCongr hn))) h
  simp only [bl, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

theorem block_matrix_injective {a a' b b' c c' d d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

end Blocks

theorem mat_nzx_sh (M : Maps D hn) (z : hermA D ρ) (x y : Mx D ρ p) :
    mat (M.nzx z x * M.sh y) = blk4 (bl hn 1 y 0 1) (bl hn (z.1 - x ⬝ adj y) x (adj x) 0) 0 (bl hn 1 0 (-adj y) 1) := by
  rw [mat_mul', M.nzx_mat, M.sh_mat, submatrix_fromBlocks_mul]
  congr 1
  · simp
  · rw [Matrix.mul_zero, zero_add, block_mul₂]
    simp [sub_eq_add_neg]
  · simp
  · simp

theorem nzx_sh_inj (M : Maps D hn) {z z' : hermA D ρ} {x x' y y' : Mx D ρ p}
    (h : M.nzx z x * M.sh y = M.nzx z' x' * M.sh y') : z = z' ∧ x = x' ∧ y = y' := by
  have h2 := congrArg mat h
  rw [mat_nzx_sh, mat_nzx_sh] at h2
  obtain ⟨h3, h4, -, -⟩ := block_matrix_injective h2
  obtain ⟨-, rfl, -, -⟩ := blockMatrix_inj hn h3
  obtain ⟨h5, rfl, -, -⟩ := blockMatrix_inj hn h4
  exact ⟨Subtype.ext (sub_left_injective h5), rfl, rfl⟩


theorem gl_levi (M : Maps D hn) (g : G D p) (a : GL (Fin p) (AE D)) (hg : mat g = blk4 a.1 0 0 (adj (a⁻¹).1))
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx z (x ⬝ adj a.1) * M.sh (y ⬝ (a⁻¹).1) * M.emb g := by
  have h1 : (a⁻¹).1 * a.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    have := adj_mul (a⁻¹).1 a.1
    rw [show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D p p) from h1, adj_one] at this
    exact this.symm
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, blockMatrix_zero, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have h3 : ∀ w : Mx D p ρ, adj a.1 ⬝ (adj (a⁻¹).1 ⬝ w) = w := fun w => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h4 : ∀ w : Mx D ρ p, w ⬝ adj a.1 ⬝ adj (a⁻¹).1 = w := fun w => by
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have h5 : ∀ w : Mx D ρ p, w ⬝ (a⁻¹).1 ⬝ a.1 = w := fun w => by
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, adj_mul, adj_adj, Matrix.one_mul,
    Matrix.mul_one, h4, h5, Matrix.mul_assoc x, h3, Matrix.mul_neg, Matrix.neg_mul, neg_zero]

theorem adj_sub' {k l : ℕ} (u v : Mx D k l) : adj (u - v) = adj u - adj v := by
  rw [sub_eq_add_neg, adj_add, adj_neg, sub_eq_add_neg]

def zU (z : hermA D ρ) (y : Mx D ρ p) (b : Mx D p p) (hb : adj b = b) : hermA D ρ :=
  ⟨z.1 - y ⬝ (b ⬝ adj y), by
    show adj _ = _
    rw [adj_sub', adj_mul, adj_mul, adj_adj, hb, z.2, Matrix.mul_assoc]⟩


theorem gl_unip (M : Maps D hn) (g : G D p) (b : Mx D p p) (hb : adj b = b) (hg : mat g = blk4 1 b 0 1)
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx (zU z y b hb) (x - y ⬝ b) * M.sh y * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, blockMatrix_zero, blockRowSubstitution_one, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, block_mul₂, bl_add, adj_sub', adj_mul, hb]
  have e1 : (zU z y b hb).1 - (x - y ⬝ b) ⬝ adj y = z.1 - x ⬝ adj y := by
    simp only [zU, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have e2 : y ⬝ b + (x - y ⬝ b) = x := by abel
  have e3 : adj x + b ⬝ -adj y = adj x - b ⬝ adj y := by rw [Matrix.mul_neg, sub_eq_add_neg]
  rw [e1, e2, e3]

def zW (z : hermA D ρ) (x y : Mx D ρ p) : hermA D ρ :=
  ⟨z.1 - x ⬝ adj y - y ⬝ adj x, by
    show adj _ = _
    rw [adj_sub', adj_sub', adj_mul, adj_mul, adj_adj, adj_adj, z.2]
    abel⟩


theorem gl_weyl (M : Maps D hn) (g : G D p) (hg : mat g = blk4 0 1 (-1) 0)
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx (zW z x y) (-y) * M.sh x * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have e1 : (zW z x y).1 - -y ⬝ adj x = z.1 - x ⬝ adj y := by
    simp only [zW, Matrix.neg_mul]
    abel
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, bl_add, adj_neg, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_zero]
  rw [show (zW z x y).1 - -(y ⬝ adj x) = z.1 - x ⬝ adj y by rw [← Matrix.neg_mul]; exact e1]

end GlobalTheory.CompanionTheory.ThTw
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

theorem _root_.GlobalTheory.T.standard_compact_entries_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)),
    IsStdK (σ := σ) (Y := Y) B b K → ∀ k ∈ K, ∀ (v : Pl (F := F)) (i j : Fin n ⊕ Fin n), absFin F v (compFin F E v (inFrame b k i j)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one | exact GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one | (intros; apply GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem sl2_square_kills : ∀ {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (E : Fin n → Fin n → Module.End ℂ Z), Formalism.REAL.GlRel E →
    (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) → ∀ {i j : Fin n}, i ≠ j → ∀ {a : Z}, a ≠ 0 →
    ∀ {p r : ℝ}, E i i a = (p : ℂ) • a → E j j a = (r : ℂ) • a → (∃ m : ℤ, p - r = m) → -1 ≤ p - r →
    (E i j a = 0 ∨ E j i a = 0) → ((E i j) ^ 2) a = 0 := by
  intro n Z _ _ E hG hA i j hij a ha p r hp hr hm hd hor
  have hji : j ≠ i := hij.symm
  have c1 : ∀ v, E i j (E j i v) - E j i (E i j v) = E i i v - E j j v := by
    intro v
    have h := LinearMap.congr_fun (hG i j j i) v
    simpa [Module.End.mul_apply] using h
  have c2 : ∀ v, E i i (E i j v) - E i j (E i i v) = E i j v := by
    intro v
    have h := LinearMap.congr_fun (hG i i i j) v
    simpa [Module.End.mul_apply, hji] using h
  have c3 : ∀ v, E j j (E i j v) - E i j (E j j v) = - E i j v := by
    intro v
    have h := LinearMap.congr_fun (hG j j i j) v
    simpa [Module.End.mul_apply, hji] using h
  have hsq : ((E i j) ^ 2) a = E i j (E i j a) := by
    simp [pow_two, Module.End.mul_apply]
  rw [hsq]
  rcases hor with h | h
  · simp [h]
  have hYX : E j i (E i j a) = ((r : ℂ) - p) • a := by
    have h1 := c1 a
    rw [h, map_zero, hp, hr, zero_sub] at h1
    rw [sub_smul, ← neg_sub ((p : ℂ) • a), ← h1, neg_neg]
  have hn : ‖E i j a‖ ^ 2 = (r - p) * ‖a‖ ^ 2 := by
    have h1 : ⟪E i j a, E i j a⟫_ℂ = ((r : ℂ) - p) * ⟪a, a⟫_ℂ := by
      rw [hA, hYX, inner_smul_right]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h2 : (((‖E i j a‖ ^ 2 : ℝ)) : ℂ) = (((r - p) * ‖a‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simpa using h1
    exact_mod_cast h2
  have hapos : 0 < ‖a‖ ^ 2 := by positivity
  have hle : 0 ≤ r - p := by
    by_contra hc
    have : (r - p) * ‖a‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hc) hapos
    nlinarith [sq_nonneg ‖E i j a‖]
  obtain ⟨m, hm⟩ := hm
  have hm1 : (-1 : ℤ) ≤ m := by
    have : ((-1 : ℤ) : ℝ) ≤ (m : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hm2 : m ≤ 0 := by
    have : (m : ℝ) ≤ ((0 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hcases : m = 0 ∨ m = -1 := by omega
  rcases hcases with h0 | h0
  · have hpr : r - p = 0 := by rw [h0] at hm; push_cast at hm; linarith
    rw [hpr, zero_mul] at hn
    have h3 : E i j a = 0 := by
      have : ‖E i j a‖ = 0 := by simpa using hn
      exact norm_eq_zero.mp this
    simp [h3]
  · have hpr : r - p = 1 := by rw [h0] at hm; push_cast at hm; linarith
    have hprC : (r : ℂ) - p = 1 := by exact_mod_cast hpr
    have hYX' : E j i (E i j a) = a := by rw [hYX, hprC, one_smul]
    have e1 : E i i (E i j a) = ((p : ℂ) + 1) • E i j a := by
      have h1 := c2 a
      rw [hp, map_smul] at h1
      rw [add_smul, one_smul, add_comm]
      exact sub_eq_iff_eq_add.mp h1
    have e2 : E j j (E i j a) = ((r : ℂ) - 1) • E i j a := by
      have h1 := c3 a
      rw [hr, map_smul] at h1
      rw [sub_smul, one_smul, sub_eq_add_neg, ← h1]
      abel
    have hY2 : E j i (E i j (E i j a)) = 0 := by
      have h1 := c1 (E i j a)
      rw [hYX', e1, e2] at h1
      have h2 : E j i (E i j (E i j a)) =
          (1 - (((p : ℂ) + 1) - ((r : ℂ) - 1))) • E i j a := by
        rw [sub_smul, sub_smul, one_smul, ← h1]
        abel
      have h3 : (1 - (((p : ℂ) + 1) - ((r : ℂ) - 1))) = 0 := by
        linear_combination hprC
      rw [h2, h3, zero_smul]
    have h4 : ⟪E i j (E i j a), E i j (E i j a)⟫_ℂ = 0 := by
      rw [hA, hY2, inner_zero_right]
    exact inner_self_eq_zero.mp h4

end GlobalTheory.CompanionTheory.RealCount
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem highestWeight_antitone_of_finiteDimensional_stable :
    ∀ {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V)
    (ν : Fin n → ℝ) (v : V), Formalism.REAL.GlRel Kf → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) → v ∈ S → v ≠ 0 →
    Formalism.REAL.KHighest (fun _ => true) Kf ν v → Antitone ν := by
  intro n V _ _ Kf S ν v hG hfd hS hv hv0 hK a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.HW.exists_nat_weight_sub_eq_of_highest_vector_in_stable (ε := fun _ => true) (F := Kf)
      (Formalism.REAL.glRel_kRel (fun _ => true) Kf hG) (ne_of_lt hlt) rfl S (fun y hy => hS b a y hy)
      hv hv0 (hK.1 a) (hK.1 b) (hK.2 a b hlt rfl)
    have hm' : ν a - ν b = (m : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact hm
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

end GlobalTheory.CompanionTheory.RealCount
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.fibre_volume_cover_countable : ∀ (V K ι : Type) [Countable ι] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ [IsLocallyFiniteMeasure lam], μ Zᶜ = 0 → ∀ A : Set V, IsCompact A → IsOpen A → ∀ (P : ι → Set V) (c : ι → ℝ≥0), (∀ i, IsCompact (P i) ∧ IsOpen (P i) ∧ P i ⊆ Z) → A ∩ Z ⊆ ⋃ i, P i → Summable c → (∀ i (S : Set K), MeasurableSet S → μ (P i ∩ Q ⁻¹' S) ≤ (c i : ℝ≥0∞) * lam S) → (∀ i s, m s (P i) ≤ (c i : ℝ≥0∞)) → ∀ s₀ : K, m s₀ A < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 s₀, ∀ S : Set K, MeasurableSet S → S ⊆ U → |(μ (A ∩ Q ⁻¹' S)).toReal - (m s₀ A).toReal * (lam S).toReal| ≤ ε * (lam S).toReal := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity.density_of_summable_cover | exact GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity.density_of_summable_cover | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity.density_of_summable_cover <;> assumption)
end
