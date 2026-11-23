module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle037
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.InvMulSelfMatrixDoubled
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.LRhoOm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.CongUnip
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.IncMFromBlocks
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle036
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.HolValueAtConstMulCpow
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

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.UpToPf
open PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem w_cols_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) :
    mat2 w * incM F d.b.1.toCols₂ = incM F d.b.1.toCols₁ ∧
    mat2 w⁻¹ * incM F d.b.1.toCols₂ = ((ε : ℤ) : AE F E) • incM F d.b.1.toCols₁ := by
  obtain ⟨t0, hB, -, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  have h1 := inFrame_mul hw
  have he : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hN : (Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 :
        Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) *
      Matrix.fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp [smul_smul, he]
  have h2 := inv_mul_frame h1 hN
  rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
  obtain ⟨-, h1b⟩ := Matrix.fromCols_inj h1
  obtain ⟨-, h2b⟩ := Matrix.fromCols_inj h2
  refine ⟨?_, ?_⟩
  · rw [h1b]; simp
  · rw [h2b]; simp
theorem tt_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (X Z : Mx F E d.m d.n) :
    d.tt (d.gram (((ε : ℤ) : AE F E) • X) Z) = ((ε : ℤ) : AF F) * d.tt (d.gram X Z) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul]
  rw [Int.cast_smul_eq_zsmul, map_zsmul, zsmul_eq_mul]
theorem upTo_of_k (hU : _root_.PositivityTheory.SiegelWeilFormula.TW.Uniq_k) : _root_.PositivityTheory.SiegelWeilFormula.TW.UpTo_k := by
  intro F E _ _ _ _ _ σ d ν hν ε w hw
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  obtain ⟨hw1, hw2⟩ := _root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.w_cols_k d hw
  have hsp := h.weil.2.1.toIsSplitting
  obtain ⟨C, hC⟩ := hU F E σ d ν hν (d.l ∘ₗ d.om w) (hsp.adm w d.l h.adm) (by
    intro Z Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hsp.impl w _ Φ hΦ]
    have e : actB (cA σ) w (Z * (incM F d.b.1.toCols₂)ᵀ) =
        (Z * (incM F t0.1)ᵀ) * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ := by
      change Z * (incM F d.b.1.toCols₂)ᵀ * (mat2 w)ᵀ = _
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hw1, hBx, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e]
    convert h.kill (Z * (incM F t0.1)ᵀ) _ (hsp.pres w Φ hΦ) using 4
    all_goals rfl)
  refine ⟨C, fun Φ hΦ X => ?_⟩
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) = _
  have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ =
      (((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hw2, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hr := l_rho_om h w (X * (incM F d.b.1.toCols₂)ᵀ) (Φ := Φ) hΦ
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) =
    d.l (d.om w (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ) Φ)) at hr
  rw [hr, key]
  have hm : d.dd.rho d.B.ψ ((((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ) Φ ∈ d.sch :=
    GlobalTheory.HeisSchA.schr_mem_schA _ hψ _ Φ hΦ
  have e1 := hC _ hm
  simp only [LinearMap.comp_apply] at e1
  rw [e1]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only
  rw [(_root_.PositivityTheory.SiegelWeilFormula.Tunit.tHeis_k F E σ d Φ hΦ (((ε : ℤ) : AE F E) • X) Z).2, _root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.tt_smul_k]
end PositivityTheory.SiegelWeilFormula.TW.UpToPf
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cong_unip_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (M : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (h0 : ∀ i, M L.i₀ i = 0 ∧ M i L.i₀ = 0) (u : Fin L.n → AE F E) :
    ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)).map (cA σ))ᵀ * M * (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)) = M := by
  have h1 : M * (∑ j, Matrix.single L.i₀ (L.em j) (u j)) = 0 := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [(h0 r).2]
    · simp [hk]
  have h2 : ((∑ j, Matrix.single L.i₀ (L.em j) (u j)).map (cA σ))ᵀ * M = 0 := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.zero_apply, Matrix.transpose_apply,
      Matrix.map_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [(h0 s).1]
    · simp [hk]
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add,
    Matrix.transpose_one, Matrix.add_mul, Matrix.one_mul, h2, add_zero, Matrix.mul_add, Matrix.mul_one, h1, add_zero]
theorem fc_U_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G}
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (T : nF σ d.Y d.b)
    (T' : nF σ L.Y L.b) (hs : L.IsSub T T') (φ : d.G → ℂ) (hφ : ∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g)
    (u : Fin L.n → AE F E) (hu : u ∈ L.ratV) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T x := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hb : IsFrame2 σ d.Y d.b := d.ok.frame
  have hψ : ∀ z : F, d.B.ψ (algebraMap F (AF F) z) = 1 := d.ok.good.std.2.1
  have hcc : ∀ z, cA σ (cA σ z) = z := _root_.PositivityTheory.SiegelWeilFormula.kfour.cA_cA' σ hσ
  obtain ⟨v, rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Afc.mem_ratV_iff_k L u).1 hu
  obtain ⟨a', ha'⟩ := hU.1 (GlobalTheory.ThK.incV F v)
  set N0 : Matrix (Fin d.n) (Fin d.n) E := ∑ j, Matrix.single L.i₀ (L.em j) (v j) with hN0
  have hne : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  have hN2 : N0 * N0 = 0 := by
    rw [hN0, Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun j' _ => ?_
    ext r s
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [hne j]
    · simp [hk]
  let a : GL (Fin d.n) E := ⟨1 + N0, 1 - N0, by
      rw [mul_sub, mul_one, add_mul, one_mul, hN2, add_zero, add_sub_cancel_right], by
      rw [mul_add, mul_one, sub_mul, one_mul, hN2, sub_zero, sub_add_cancel]⟩
  obtain ⟨g, hg, hgf⟩ := levi_ex hσ hb a
  have hA : (1 + ∑ j, Matrix.single L.i₀ (L.em j) (GlobalTheory.ThK.incV F v j)) = incM F (1 + N0) := by
    ext r s
    simp [hN0, incM, Matrix.sum_apply, Matrix.single_apply, GlobalTheory.ThK.incV, Matrix.one_apply, apply_ite]
  rw [hA] at ha'
  have hgu : uM (GlobalTheory.ThK.incV F v) = g := by
    apply inFrame_injective d.b
    rw [ha', hgf]
    have r1 := (blk_rel hb _ ha').1
    have r2 := (blk_rel hb _ hgf).1
    have r1' := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 r1
    have e1 : a'.map (cA σ) = (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ) := by
      calc a'.map (cA σ) = a'.map (cA σ) * ((incM F (a.1))ᵀ * (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ)) := by
            rw [r2, Matrix.mul_one]
        _ = (a'.map (cA σ) * (incM F (a.1))ᵀ) * (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ) := by rw [Matrix.mul_assoc]
        _ = _ := by rw [r1', Matrix.one_mul]
    have e2 : a' = incM F (((a⁻¹).1)ᵀ.map σ) := by
      have := congrArg (fun M => M.map (cA σ)) e1
      simpa [Matrix.map_map, Function.comp_def, hcc] using this
    rw [e2]
  have hgm : uM (GlobalTheory.ThK.incV F v) ∈ rat2 σ d.Y := hgu ▸ hg
  refine fc_levi hσ hb hψ hc _ hgm ha' T T ?_ φ hφ x
  rw [← hA]
  exact _root_.PositivityTheory.SiegelWeilFormula.Afc.cong_unip_k L T.1.1 hs.1 _
theorem fc_deg_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (hT : ¬ IsND T) :
    ∃ γ ∈ rat2 σ d.Y, ∃ T₀ T', L.IsSub T₀ T' ∧ ∀ φ : d.G → ℂ, Continuous φ →
      (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ x,
        fc d.B.ψ d.b nb lam 𝓖 φ T x = fc d.B.ψ d.b nb lam 𝓖 φ T₀ (γ * x) := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hb : IsFrame2 σ d.Y d.b := d.ok.frame
  have hψ : ∀ z : F, d.B.ψ (algebraMap F (AF F) z) = 1 := d.ok.good.std.2.1
  obtain ⟨ε, hε⟩ := hb.1
  obtain ⟨ε', hε'⟩ := L.ok.frame.1
  have hee := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  obtain ⟨T0, hT0⟩ := (mem_nF_iff T.1).1 T.2
  have hC : incM F T0 ∈ nCond σ d.n ε := hT0 ▸ (mem_nA_iff hσ hε T.1.1).1 T.1.2
  have hdet : T0.det = 0 := by
    have h1 : T.1.1.det = 0 := not_not.1 hT
    rw [hT0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
    exact kfour.inclR_injective (F := F) (h1.trans (map_zero _).symm)
  obtain ⟨v, hv0, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨a', ha'⟩ := exists_gl_col v hv0 L.i₀
  obtain ⟨γ, hγ, hγf⟩ := levi_ex hσ hb a'⁻¹
  set M0 : Matrix (Fin d.n) (Fin d.n) E := (a'.1.map σ)ᵀ * T0 * a'.1 with hM0
  have hMc : incM F M0 = ((incM F a'.1).map (cA σ))ᵀ * incM F T0 * incM F a'.1 := by
    rw [incM_mapc, incM_tr, hM0, incM_mul', incM_mul']
  have hM0C : incM F M0 ∈ nCond σ d.n ε := hMc ▸ cong_nCond hσ _ _ hC
  have hM0A : incM F M0 ∈ nA σ d.Y d.b := (mem_nA_iff hσ hε _).2 hM0C
  let T₀ : nF σ d.Y d.b := ⟨⟨incM F M0, hM0A⟩, (mem_nF_iff _).2 ⟨M0, rfl⟩⟩
  have hsubC : (incM F M0).submatrix L.em L.em ∈ nCond σ L.n ε' := hee ▸ sub_nCond L.em _ hM0C
  let T' : nF σ L.Y L.b := ⟨⟨(incM F M0).submatrix L.em L.em, (mem_nA_iff hσ hε' _).2 hsubC⟩,
    (mem_nF_iff _).2 ⟨M0.submatrix L.em L.em, rfl⟩⟩
  have hcol : ∀ k, M0 k L.i₀ = 0 := fun k => by
    have e1 : M0 k L.i₀ = (((a'.1.map σ)ᵀ * T0) *ᵥ v) k := by
      simp only [hM0, Matrix.mul_apply, Matrix.mulVec, dotProduct, ha']
    rw [e1, ← Matrix.mulVec_mulVec, hTv, Matrix.mulVec_zero, Pi.zero_apply]
  have hrow : ∀ k, M0 L.i₀ k = 0 := fun k => by
    have e0 : ∀ l, ∑ p, σ (v p) * T0 p l = 0 := fun l => by
      have h1 := congrArg σ (congrFun hTv l)

      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at h1
      calc ∑ p, σ (v p) * T0 p l = ∑ p, σ (v p) * -(((ε : ℤ) : E) * σ (T0 l p)) :=
            Finset.sum_congr rfl fun p _ => by rw [nCond_rat T0 hC l p]
        _ = -(((ε : ℤ) : E) * ∑ p, σ (T0 l p) * σ (v p)) := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun p _ => by ring
        _ = 0 := by rw [h1, mul_zero, neg_zero]
    simp only [hM0, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, ha']
    simp only [e0, zero_mul, Finset.sum_const_zero]
  refine ⟨γ, hγ, T₀, T', ⟨fun i => ⟨?_, ?_⟩, rfl⟩, fun φ _ hφ x => ?_⟩
  · show inclR (F := F) (AF F) (M0 L.i₀ i) = 0
    rw [hrow, map_zero]
  · show inclR (F := F) (AF F) (M0 i L.i₀) = 0
    rw [hcol, map_zero]
  refine (fc_levi hσ hb hψ hc γ hγ hγf T₀ T ?_ φ hφ x).symm
  show ((incM F (a'⁻¹).1).map (cA σ))ᵀ * incM F M0 * incM F (a'⁻¹).1 = T.1.1
  rw [hT0, incM_mapc, incM_tr, ← incM_mul', ← incM_mul', hM0]
  congr 1
  have ha : a'.1 * (a'⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc ((a'⁻¹).1.map σ)ᵀ * ((a'.1.map σ)ᵀ * T0 * a'.1) * (a'⁻¹).1
      = ((a'.1 * (a'⁻¹).1).map σ)ᵀ * T0 * (a'.1 * (a'⁻¹).1) := by
        rw [mapσ_mul', Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = T0 := by rw [ha, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
theorem fcConj_of_k : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.FcConj_k := fun _ _F _E _ _ _ _ _ _σ _d L _nb _lam _𝓖 hc =>
  ⟨fun T hT => _root_.PositivityTheory.SiegelWeilFormula.Afc.fc_deg_k L hc T hT, fun _uM _ν _𝓤 hU T T' hs φ _ hφ u hu x => _root_.PositivityTheory.SiegelWeilFormula.Afc.fc_U_k L hc hU T T' hs φ hφ u hu x⟩
end PositivityTheory.SiegelWeilFormula.Afc
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def emS_k : Fin L.n ⊕ Fin L.n → Fin d.n ⊕ Fin d.n := Sum.map L.em L.em
def padM_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  fun r c => if h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c then M h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) r c
theorem emS_inj_k : Function.Injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) := Sum.map_injective.2 ⟨L.inj, L.inj⟩
theorem padM_emS_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (a a' : Fin L.n ⊕ Fin L.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = M a a' := by
  have h : (∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) ∧ ∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dite_eq_left h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.1.choose_spec, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.2.choose_spec]
theorem padM_out_row_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) (c : Fin d.n ⊕ Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dite_eq_right (fun h => hr h.1)]
theorem padM_out_col_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dite_eq_right (fun h => hc h.2)]
theorem mem_out_k {r : Fin d.n ⊕ Fin d.n} (h : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) :
    r ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases r with i | i
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inl a, by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, ha]⟩).elim
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inr a, by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, ha]⟩).elim
theorem em_ne_k (a : Fin L.n) : L.em a ≠ L.i₀ := (L.rng (L.em a)).2 ⟨a, rfl⟩
theorem not_inl_k (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inl i := by
  rintro ⟨a | a, ha⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inl, Sum.inl.injEq] at ha
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L a (ha.trans hi)
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] at ha
theorem not_inr_k (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inr i := by
  rintro ⟨a | a, ha⟩
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] at ha
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.inr.injEq] at ha
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L a (ha.trans hi)
theorem inFrame_j_k (g : G2 σ L.Y) : inFrame d.b (L.j g) = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (inFrame L.b g) := by
  ext r c
  by_cases h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c
  · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := h
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
    have := congrFun (congrFun (L.j_in g) a) a'
    simpa [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] using this
  · rcases not_and_or.1 h with h1 | h1
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L _ h1]
      exact (L.j_out g r (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L h1) c).1
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L _ r h1]
      exact (L.j_out g c (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L h1) r).2
theorem sub_mem_nA_k (β : nA σ d.Y d.b) : β.1.submatrix L.em L.em ∈ nA σ L.Y L.b := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  rw [kunf.mem_nA_iff hε']
  have h1 : β.1 ∈ kfour.nCond σ d.n ε := (kunf.mem_nA_iff hε β.1).1 β.2
  exact Afc.sub_nCond (σ := σ) L.em β.1 h1
def prj_k : nA σ d.Y d.b →+ nA σ L.Y L.b where
  toFun β := ⟨β.1.submatrix L.em L.em, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.sub_mem_nA_k L β⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' β β' := by
    apply Subtype.ext
    rfl
theorem prj_val_k (β : nA σ d.Y d.b) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β).1 = β.1.submatrix L.em L.em := rfl
theorem continuous_prj_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.matrix_submatrix L.em L.em
theorem pad_matrix_lower_block_zero (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (hM : M.toBlocks₂₁ = 0) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M).toBlocks₂₁ = 0 := by
  ext i k
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  by_cases hi : i = L.i₀
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L M (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L i hi)]
    simp
  · by_cases hk : k = L.i₀
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L M _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L k hk)]
      simp
    · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
      obtain ⟨a', rfl⟩ := (L.rng k).1 hk
      have h1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L M (Sum.inr a) (Sum.inl a')
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.map_inl] at h1
      rw [h1]
      have h2 := congrFun (congrFun hM a) a'
      simpa [Matrix.toBlocks₂₁] using h2
theorem embedding_lower_block_zero {x : G2 σ L.Y} (hx : ∃ t, IsPar x t) : (inFrame d.b (L.j x)).toBlocks₂₁ = 0 := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨-, t₀, ht₀⟩ := L.ok.frame
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_matrix_lower_block_zero L _ ((kunf.isPar_frame ht₀ x t).1 ht).1
theorem j_par_k {g : G2 σ L.Y} (h : g ∈ par2 σ L.Y) : L.j g ∈ par2 σ d.Y := by
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 h
  obtain ⟨-, t₁, ht₁⟩ := d.ok.frame
  set P := inFrame d.b (L.j g)
  set Q := inFrame d.b (L.j g⁻¹)
  have hP : P.toBlocks₂₁ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.embedding_lower_block_zero L ⟨t, ht⟩
  have hQ : Q.toBlocks₂₁ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.embedding_lower_block_zero L ⟨t⁻¹, ht.inv⟩
  have hPQ : P * Q = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hQP : Q * P = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have e1 := upper_block_mul_of_lower_zero hQ hPQ
  have e2 := upper_block_mul_of_lower_zero hP hQP
  set T0 := incM F t₁.1
  set Ti := incM F (t₁⁻¹).1
  have hT : T0 * Ti = 1 := by
    show incM F t₁.1 * incM F (t₁⁻¹).1 = 1
    rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
  have hT' : Ti * T0 = 1 := by
    show incM F (t₁⁻¹).1 * incM F t₁.1 = 1
    rw [← kunf.incM_mul', Units.inv_mul]; ext i j; simp [incM, Matrix.one_apply]
  let t' : GL (Fin d.n) (AE F E) := ⟨T0 * P.toBlocks₁₁ * Ti, T0 * Q.toBlocks₁₁ * Ti, by
      calc T0 * P.toBlocks₁₁ * Ti * (T0 * Q.toBlocks₁₁ * Ti) = T0 * (P.toBlocks₁₁ * (Ti * T0) * Q.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e1, Matrix.mul_one, hT], by
      calc T0 * Q.toBlocks₁₁ * Ti * (T0 * P.toBlocks₁₁ * Ti) = T0 * (Q.toBlocks₁₁ * (Ti * T0) * P.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e2, Matrix.mul_one, hT]⟩
  exact mem_parabolic_GL2_iff.2 ⟨t', (kunf.isPar_frame ht₁ (L.j g) t').2 ⟨hP, rfl⟩⟩
def padE_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  fun r c => if h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c then N h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r c
theorem padM_incM_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (incM F N) = incM F (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N) := by
  ext r c
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k, incM, Matrix.map_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
theorem j_rat_k {g : G2 σ L.Y} (h : g ∈ rat2 σ L.Y) : L.j g ∈ rat2 σ d.Y := by
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 h
  have hm : mat2 g = incM F γ.1 := by
    show g.1.1 = _
    rw [← hγ]
    rfl
  have hf : inFrame L.b g = incM F ((L.b⁻¹).1 * γ.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]
    rfl
  refine kunf.rat_of_inFrame (b := d.b) (M := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L ((L.b⁻¹).1 * γ.1 * L.b.1)) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, hf, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_incM_k]
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem coreX_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k := by
  intro ok vac c hT hA hS hU hW hD F E _ _ _ _ _ σ d R hok hE Φ hΦ P gf hpg hv x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨dd, J, T', bs, ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c', C, hDat, hAn, ⟨e, he⟩, hC, ⟨t, ht⟩,
    μH, 𝓕, hH, hF, horb⟩ := hD hT hA F E σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t', ht'⟩ := hU F E σ d (s0 d.m d.n) (d.sec0 Φ) (hS F E σ d Φ hΦ) (hE Φ hΦ)
  have hG := hW F E σ d.m d.n dd J T' bs ψ (InfinitePlace F) θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν hDat hok
    (Or.inr hAn) (fun h => ⟨fun i => congrFun (hv h) i, e, he⟩)
    ⟨max t t', fun z hz => (ht z (lt_of_le_of_lt (le_max_left _ _) hz)).1
      ((ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hcd ε w hw x).1)⟩ μH 𝓕 hH hF
  rw [horb, mul_left_comm]
  exact ((holValueAt_const_mul_cpow c' hC (s0 d.m d.n)).mul hG).congr ⟨t, fun z hz => ((ht z hz).2).symm⟩
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
