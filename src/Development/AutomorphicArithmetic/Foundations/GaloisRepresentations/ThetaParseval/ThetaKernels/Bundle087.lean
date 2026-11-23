module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle069
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle081
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle084
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle007
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle004
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle009
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.ExpAlg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle077
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle085
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle002
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.IsExtAtOfDiff
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.JjMulJj
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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

@[expose] public section

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.SplitLagrF
end GlobalTheory.SplitLagrF
open GlobalTheory.SplitLagrF in
theorem PositivityTheory.ThKW.fundamental_domain_parseval_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle,
        (∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f) →
      ∀ f₀, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f₀ ≠ 0 →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) → α t = χS (Matrix.GeneralLinearGroup.det t) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd α hlaw f₀ hf₀ hne e he t ht
  obtain ⟨h, hhC, hsupp, ⟨M, hM, hMy⟩, x, hx, hχx⟩ := _root_.GlobalTheory.SplitLagrF.exists_levi_k F E σ B hB nT JT hT e he t ht
  obtain ⟨ℓ, hinv, ⟨f, hf, hℓf⟩, hcmp⟩ := _root_.GlobalTheory.SplitLagrF.exists_form_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 e he f₀ hf₀ hne
  obtain ⟨R, hR, hRk⟩ := hcmp M hM
  obtain ⟨r, hr, hsp⟩ := hωd.om_split e he 1 h (suppAtF_one σ e JS) hsupp 1 x (isDetAtF_one σ e JS) hx
  set m : ℝ := (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
    (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) with hm_def
  have hm : 0 < m := Real.rpow_pos_of_pos (modu_pos _) _
  have h1 := hsp ℓ hinv f hf
  have h2 : ℓ (ωd (1, h) f) = (R : ℂ) * ((α t : ℂ) * (m : ℂ)) * ℓ f := by
    refine hRk f (ωd (1, h) f) _ hf (hωd.om_pres _ f hf) (fun y _ => ?_)
    have hth : IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ
        (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (aC F E nT * (M * y)) f) :=
      _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS (nT + nT) JS _ ξ₀ _ f hf
    have hh := hωd.om_heis 1 h (aC F E nT * (M * y)) f hf
    have hact : actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h (aC F E nT * (M * y)) = aC F E nT * y := by
      unfold actOF
      rw [← hMy nS y, ← Matrix.mul_assoc, ← GlobalTheory.WeilPartsF.mtF_mul, mul_inv_cancel, inv_one]
      simp only [mtF_one', Matrix.one_mul, Matrix.mul_one]
    unfold prof
    rw [← hact, ← hh]
    exact hlaw h t hhC _ hth
  have h3 : (R : ℂ) * ((α t : ℂ) * (m : ℂ)) = (r : ℂ) * (χS x : ℂ) := by
    have := h2.symm.trans h1
    simp only [splitFacOF, MonoidHom.one_apply, inv_one, one_mul] at this
    exact mul_right_cancel₀ hℓf this
  have hu : α t * (χS x)⁻¹ = 1 := by
    apply circle_eq_one_of_pos (t := r / (R * m)) (div_pos hr (mul_pos hR hm))
    have hx0 : ((χS x : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [Circle.coe_mul, Circle.coe_inv]
    push_cast
    field_simp
    linear_combination h3
  rw [← hχx χS nS hωd.resS]
  exact mul_inv_eq_one.mp hu
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem B_vline_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ (C : ℂ) (c s : ℝ) (ν : Measure (Mx F E d.m d.n)) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)), C ≠ 0 ∧ s ≠ 0 ∧
      ν.IsAddHaarMeasure ∧ νf.IsAddHaarMeasure ∧
      ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → ∀ Φ ∈ d.sch, ∀ W : Mx F E d.m d.n, finOne F • W = 0 → ∀ z : ℂ,
        _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) = C * Real.exp (-(c * ‖z‖ ^ 2 * ‖s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2)) *
          (Complex.exp (-(z ^ 2 * ‖s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2 / (16 * Real.pi))) *
            ∫ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
              Complex.exp (z * ⟪s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W, u⟫_ℝ)) := by
  obtain ⟨νf, hνf, hν⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.exists_nuf_k R
  refine ⟨1, 1 / (16 * Real.pi), -(4 * Real.pi), Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KFP.jnp_k R) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf), νf,
    one_ne_zero, neg_ne_zero.2 (by positivity), hν, hνf, ?_⟩
  intro g hg' Ω hΩ hTΩ Φ hΦ W hW z
  set w := _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W with hw
  let e : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z
  let b : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k w z
  have hTv : ∀ X, d.T (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) X = b (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) :=
    _root_.PositivityTheory.SiegelWeilFormula.KFP.T_vline_k hH R hΩ hTΩ hW z
  have hb : Continuous b := _root_.PositivityTheory.SiegelWeilFormula.KFP.continuous_bv_k w z
  have hb1 : ∀ u, ‖b u‖ ≤ 1 := _root_.PositivityTheory.SiegelWeilFormula.KFP.norm_bv_le_k w z
  have hTΦ : d.T Φ ∈ d.schM := (hT.1 F E σ d).1 Φ hΦ
  have e1 : _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k (Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KFP.jnp_k R) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)) Φ (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) =
      ∫ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.B_k, hTv]
    exact _root_.PositivityTheory.SiegelWeilFormula.KFP.integral_jnp_k R hνf hTΦ hg' hb hb1
  refine e1.trans ?_
  have key : ∀ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u =
      ((Real.exp (-(1 / (16 * Real.pi) * ‖z‖ ^ 2 * ‖(-(4 * Real.pi)) • w‖ ^ 2)) : ℝ) : ℂ) *
        Complex.exp (-(z ^ 2 * (‖(-(4 * Real.pi)) • w‖ ^ 2 : ℝ) / (16 * Real.pi))) *
          (_root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
            Complex.exp (z * ⟪(-(4 * Real.pi)) • w, u⟫_ℝ)) := by
    intro u
    have hz : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
    have h1 := exp_alg z.re z.im (‖w‖ ^ 2) ⟪w, u⟫_ℝ (‖u‖ ^ 2)
    rw [← hz] at h1
    have hn : ‖(-(4 * Real.pi)) • w‖ ^ 2 = 16 * Real.pi ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    have hi : ⟪(-(4 * Real.pi)) • w, u⟫_ℝ = -(4 * Real.pi) * ⟪w, u⟫_ℝ := real_inner_smul_left _ _ _
    have hzn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [b, _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k, star_star, hn, hi, hzn]
    have h2 : _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z u = 2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
        4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
        ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ) := by
      rfl
    rw [h2, h1]
    ring
  simp_rw [key]
  rw [integral_const_mul]
  simp only [one_mul, Complex.ofReal_exp]
  push_cast
  ring
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem ndZero_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n))
    {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b} (hT : IsND T) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x = 0 := by
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  have hL : (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ∈ d.lamSet := ⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩
  obtain ⟨hadd, hbd⟩ := H.lamBd F E σ d _ hL
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  have hAc := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n) :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  have hLI : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = 0 := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x]; exact (H.orbRes F E σ d).1 hmn T hT _
  have hB : _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) • d.I Φ +
      (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) := by
    funext g; simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have h1 := hadd (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) (d.I Φ) (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n))
    hIc hAc hIi hAi
  rw [hB, h1, hLI, mul_zero, zero_add, ← hComm _ hs j]
  obtain ⟨t', ht'⟩ := H.unfold F E σ d _ _ hsec hEis
  obtain ⟨ε, w, hw, -⟩ := (H.auxEx F E σ d).2.1
  have hWL := H.whitLow F E σ d R hmn Φ hΦ hv nb lam 𝓖 hc ε w hw T hT x
  rw [zero_mul] at hWL
  have := ordVal U p (fun z => fc d.B.ψ d.b nb lam 𝓖 (Ê z) T x)
    (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) (max t t')
    (s0 d.m d.n) 0 hUo hR hs hp hDiff ?_ hWL j hj
  · rw [this, mul_zero]
  · intro z hz
    have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
    have h2 := (ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hc ε w hw x).2 T hT
    rw [← h2]
    simp only [fc, h1, mul_assoc]
    exact integral_const_mul _ _
theorem stepJ_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g = 0 := by
  obtain ⟨nb, lam, 𝓖, hc⟩ := H.coefEx F E σ d
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  have hBc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) :=
    (famCont U Ê hUo hd hcont _ hs j).sub (continuous_const.mul (continuous_const.mul hIc))
  have hBr : ∀ γ ∈ rat2 σ d.Y, ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j (γ * g) = _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g := fun γ hγ g => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j, hIi γ hγ g]
  have hz := H.fourierZero F E σ d nb lam 𝓖 hc (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) hBc (fun β hβ g => hBr _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.nbRat_k d hc β hβ) g) ?_
  · intro g; exact congrFun hz g
  · intro T g
    by_cases hT : IsND T
    · exact _root_.PositivityTheory.SiegelWeilFormula.AStep.ndZero_k H R hmn hΦ hv hE j hj hc hT g
    · obtain ⟨γ, hγ, T₀, T', hsub, hfc⟩ := (H.fcConj F E σ d L nb lam 𝓖 hc).1 T hT
      rw [hfc _ hBc hBr g]
      exact _root_.PositivityTheory.SiegelWeilFormula.AStep.deg_k H R L R' hmn hIH hΦ hv hE j hj hlow hc hsub _
theorem step_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) : _root_.PositivityTheory.SiegelWeilFormula.Step_k := by
  intro F E _ _ _ _ _ σ d R L R' hmn hIH Φ hΦ hv x
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d _ _ hsec (s0 d.m d.n)
  have hall : ∀ j ≤ p.rootMultiplicity (s0 d.m d.n), ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      refine _root_.PositivityTheory.SiegelWeilFormula.AStep.stepJ_k H R L R' hmn hIH hΦ hv hE j hj fun i hi g => ?_
      have := ih i hi (hi.le.trans hj) g
      simpa only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, pderiv_lt p _ i (lt_of_lt_of_le hi hj), zero_mul, sub_zero] using this
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  refine wrap U p (Ê · x) (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) t _ _ hUo hR hs hp (hd x)
    (fun z hz => (hfar z hz).2 x) (fun j hj => ?_) ?_
  · have := hall j hj.le x
    simpa only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, pderiv_lt p _ j hj, zero_mul, sub_zero] using this
  · exact sub_eq_zero.1 (hall _ le_rfl x)
theorem stepOf_k : _root_.PositivityTheory.SiegelWeilFormula.StepOf_k := fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 =>
  _root_.PositivityTheory.SiegelWeilFormula.AStep.step_k ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.RatWeilOp
namespace PositivityTheory.SiegelWeilFormula.Tunit
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij PositivityTheory.SiegelWeilFormula.TBij.Adp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_chart_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ (τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)
    (d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) d.κ),
    GlobalTheory.TowU.IsRat d' ∧ ∀ w, d'.e w = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w := by
  classical
  have hD := d.ok.dbl
  let τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d := Fintype.equivOfCardEq (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.card_ix d)
  obtain ⟨a, ha, hact⟩ := exists_symp d.dd.e (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ) (fun w w' => by rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.symplecticForm_coordinates, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq]) (by
    rintro w ⟨y, z, h⟩
    obtain ⟨x, hx⟩ := rat_surj d.bs d.dd.e (fun x => hD.rat x) y z
    obtain rfl : w = incM F x := d.dd.e.injective (h.trans hx.symm)
    exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_rational d τ x)
  set J := jj d.κ F with hJ
  set b := -(J * aᵀ * J) with hb
  have hba : b * a = 1 := by
    rw [hb, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᵀ, ha, jj_mul_jj, neg_neg]
  have hab : a * b = 1 := mul_eq_one_comm.1 hba
  have hinv : ∀ w, act (b.map (algebraMap F (AF F))) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) = d.dd.e w := fun w => by
    rw [hact w, ← act_mul, ← Matrix.map_mul, hba, Matrix.map_one _ (map_zero _) (map_one _), act_one']
  have hright : ∀ u, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (d.dd.e.symm (act (b.map (algebraMap F (AF F))) u)) = u := fun u => by
    rw [hact, LinearEquiv.apply_symm_apply, ← act_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), act_one']
  let e' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) ≃ₗ[AF F] (d.κ → AF F) × (d.κ → AF F) :=
    { _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ with
      invFun := fun u => d.dd.e.symm (act (b.map (algebraMap F (AF F))) u)
      left_inv := fun w => by
        show d.dd.e.symm (act (b.map (algebraMap F (AF F))) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w)) = w
        rw [hinv, LinearEquiv.symm_apply_apply]
      right_inv := hright }
  refine ⟨τ, ⟨e', fun w w' => ?_⟩, fun x => ?_, fun w => rfl⟩
  · rw [d.dd.form]
    show om (d.dd.e w) (d.dd.e w') = om (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w')
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.symplecticForm_coordinates, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq]
  · obtain ⟨y, z, h⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_rational d τ x
    exact ⟨y, z, h⟩
theorem T_chart_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ (τ : d.κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (S0 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ))
    (S0' : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ)) (C : ℂ),
    GlobalTheory.TowU.IsOp d.B.ψ (fun w => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (d.dd.e.symm w)) S0 S0' ∧
    ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S0 Φ (fun k => d.crd X (τ k)) := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨τ, d', hrat, he'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tunit.exists_chart_k d
  obtain ⟨S0, S0', hS⟩ := GlobalTheory.T.darbouxCoordinateChange_realised_with_double F E σ d.ok.good.cm d.B.ψ hψ (Fin d.m) (Fin d.n ⊕ Fin d.n) d.κ d.κ _ d.dd d'
    (by exact d.ok.dbl.rat) hrat
  have hop := hS.1
  have hs : (fun w => d'.e (d.dd.e.symm w)) = fun w => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (d.dd.e.symm w) := funext fun w => he' _
  rw [hs] at hop
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ, LinearEquiv.symm_apply_apply]
  have rhoS' : ∀ w, ∀ φ ∈ schA F d.κ, S0' (schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  set l' : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ℂ := d.l ∘ₗ S0' with hl'
  have hadm : l' ∈ (adeleClass F).adm d.κ := hop.adm' d.l d.ok.dbl.adm
  have hinv : ∀ (y : d.κ → AF F), ∀ φ ∈ schA F d.κ, l' (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l' φ := by
    intro y φ hφ
    obtain ⟨w, hw⟩ : ∃ w, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w = (0, y) := ⟨d'.e.symm (0, y), by rw [← he', LinearEquiv.apply_symm_apply]⟩
    obtain ⟨Z, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_fst_eq_zero d τ w (by rw [hw])
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = schr d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ)) φ := by
      rw [hw]; funext x; simp [schr]
    rw [e1, hl', LinearMap.comp_apply, rhoS' _ φ hφ, LinearMap.comp_apply]
    exact d.ok.dbl.kill Z _ (hop.pres' φ hφ)
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ d.κ l' hadm hinv
  refine ⟨τ, S0, S0', c, hop, fun Φ hΦ X => ?_⟩
  have hΨ : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ ∈ schA F d.κ :=
    GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ hΦ
  have e0 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (X * (incM F d.b.1.toCols₂)ᵀ) = (fun k => d.crd X (τ k), 0) := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_frame d τ X
  have e1 : d.T Φ X = l' (S0 (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)) := by
    rw [hl', LinearMap.comp_apply, hop.left _ hΨ]
    rfl
  rw [e1, hc _ (hop.pres _ hΨ), rhoS _ _ hΦ, e0]
  simp [schr]
end PositivityTheory.SiegelWeilFormula.Tunit
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
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem paddedMatrix_mul_submatrix (A : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L A * N).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = A * N.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L) _ _ ?_ ?_
  · intro l hl
    have hl' : ¬ ∃ b, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L b = l := fun ⟨b, hb⟩ => hl ⟨b, hb⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L A _ hl', Matrix.one_apply_ne, zero_mul]
    rintro rfl
    exact hl' ⟨a, rfl⟩
  · intro b
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
theorem mul_paddedMatrix_submatrix (B : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (N * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L B).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = N.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) * B := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L) _ _ ?_ ?_
  · intro l hl
    have hl' : ¬ ∃ b, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L b = l := fun ⟨b, hb⟩ => hl ⟨b, hb⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L B hl', Matrix.one_apply_ne, mul_zero]
    rintro rfl
    exact hl' ⟨c, rfl⟩
  · intro b
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
theorem conj_rationalParabolic_embed (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {p' : G2 σ L.Y} (hp : p' ∈ par2 σ L.Y) (hpr : p' ∈ rat2 σ L.Y) (c : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ c₂ : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L, w₁ * (cM c.1 * L.j p') = p * (w₁ * cM c₂.1) := by
  have hx : (L.j p')⁻¹ * cM c.1 * L.j p' ∈ rat2 σ d.Y :=
    mul_mem (mul_mem (inv_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L hpr)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_rat'_k h c.2.1 c.2.2)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L hpr)
  have hf : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L ((L.j p')⁻¹ * cM c.1 * L.j p') :=
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_mul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_mul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_inv_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_j_k p')) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_cM'_k h c.1)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_j_k p')
  obtain ⟨s, c₂, γ', hs, hsP, -, hγ', hx'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.stab_dec_k h hx hf
  have hsub : (inFrame d.b ((L.j p')⁻¹ * cM c.1 * L.j p')).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = 1 := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_inv, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k,
      _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mul_paddedMatrix_submatrix, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.paddedMatrix_mul_submatrix, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.emS_cM_k h, Matrix.mul_one, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel,
      GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hγ1 : γ' = 1 := kunf.inFrame_injective L.b (by rw [hγ', hsub, GlobalTheory.EisBL.DoubledParabolic.inFrame_one])
  rw [hγ1, map_one, mul_one] at hx'
  refine ⟨L.j p' * (w₁ * s * w₁⁻¹), mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L hp) hsP,
    mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L hpr) (mul_mem (mul_mem h.wr hs) (inv_mem h.wr)), c₂, ?_⟩
  have hw := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.weyl_commutes_embedding h p'
  calc w₁ * (cM c.1 * L.j p') = w₁ * L.j p' * ((L.j p')⁻¹ * cM c.1 * L.j p') := by group
    _ = L.j p' * w₁ * (s * cM c₂.1) := by rw [hw, hx']
    _ = L.j p' * (w₁ * s * w₁⁻¹) * (w₁ * cM c₂.1) := by group
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end
