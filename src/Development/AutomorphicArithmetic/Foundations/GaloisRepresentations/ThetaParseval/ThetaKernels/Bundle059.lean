module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle046
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.ActUDiagMonomial
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle038
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle047
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle044
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.GIinvCut
import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle001
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle042
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle045
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle032
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.PsiZeroGram
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle052
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section



section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : w₀ * w₀ * w₀ * w₀ = 1 := _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf h
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.nbar_conj' {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ (y' : GR d.n) (x : Matrix (Fin d.n) (Fin d.n) ℂ), xᴴ = x ∧ mR y' = nU x ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ :=
  R.nbar_conj_pf w h
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem T_lin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) (a : ℂ) : d.T (Φ + a • Φ') = d.T Φ + a • d.T Φ' := by
  funext X
  have e : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (Φ + a • Φ') =
      d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ + a • d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ' := by
    funext x
    simp only [Darboux.rho, schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  show d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (Φ + a • Φ')) =
    d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ) + a • d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ')
  rw [e, map_add (f := _), map_smul]
theorem mu_right_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.μ.IsMulRightInvariant := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitA.mu_right_k d
theorem thetaSum_S_rat_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∀ Φ ∈ d.sch, ∀ γ ∈ ratU σ d.A.J, thetaSum F (d.S γ Φ) = thetaSum F Φ := by
  intro Φ hΦ γ hγ
  obtain ⟨γ0, hγ0⟩ := hγ
  have hS : d.S γ Φ ∈ d.sch := d.ok.dbl.lin.pres _ _ hΦ
  have h1 := (hT.2.2.2.1 F E σ d (d.S γ Φ) hS).1
  have h2 := (hT.2.2.2.1 F E σ d Φ hΦ).1
  have e : ∀ X : Matrix (Fin d.m) (Fin d.n) E, d.T (d.S γ Φ) (incM F X) = d.T Φ (incM F ((γ0⁻¹).1 * X)) := by
    intro X
    rw [(hT.2.1 F E σ d Φ hΦ).2.2 γ (incM F X)]
    congr 1
    have hm : mat γ⁻¹ = incM F (γ0⁻¹).1 := by
      have hγ1 : ((γ : UA σ d.A.J) : GL (Fin d.m) (AE F E)) =
          Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) γ0 := hγ0.symm
      show (((γ⁻¹ : UA σ d.A.J) : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) = _
      rw [Subgroup.coe_inv, hγ1, ← map_inv]
      rfl
    rw [hm]
    simp only [incM, Matrix.map_mul]
  simp only [e] at h1
  let eqv : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E :=
    { toFun := fun X => (γ0⁻¹).1 * X, invFun := fun X => γ0.1 * X,
      left_inv := fun X => by simp [← Matrix.mul_assoc],
      right_inv := fun X => by simp [← Matrix.mul_assoc] }
  have h3 : HasSum (fun X => d.T Φ (incM F X)) (thetaSum F (d.S γ Φ)) :=
    (eqv.hasSum_iff (f := fun X => d.T Φ (incM F X))).1 h1
  exact h3.unique h2
theorem thetaSum_lin_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ Φ' : d.Fn} (hΦ : Φ ∈ d.sch) (hΦ' : Φ' ∈ d.sch) (a : ℂ) :
    thetaSum F (Φ + a • Φ') = thetaSum F Φ + a * thetaSum F Φ' := by
  have h1 := (hT.2.2.2.1 F E σ d (Φ + a • Φ') (d.sch.add_mem hΦ (d.sch.smul_mem a hΦ'))).1
  have h2 := (hT.2.2.2.1 F E σ d Φ hΦ).1
  have h3 := (hT.2.2.2.1 F E σ d Φ' hΦ').1
  rw [_root_.PositivityTheory.SiegelWeilFormula.KSplit.T_lin_k] at h1
  exact h1.unique (h2.add (h3.mul_left a))
theorem I_S_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∀ Φ ∈ d.sch, ∀ g x, d.I (d.S g Φ) x = d.I Φ x := by
  intro Φ hΦ g x
  have := d.ok.haar
  have := _root_.PositivityTheory.SiegelWeilFormula.KSplit.mu_right_k d
  have := PositivityTheory.ThKF.countable_ratU σ d.A.J
  have : BorelSpace (UA σ d.A.J) := ⟨rfl⟩
  have hinv : ∀ γ ∈ ratU σ d.A.J, ∀ h, thetaSum F (d.om x (d.S (γ * h) Φ)) = thetaSum F (d.om x (d.S h Φ)) := by
    intro γ hγ h
    have hSh : d.S h Φ ∈ d.sch := d.ok.dbl.lin.pres _ _ hΦ
    rw [map_mul, Module.End.mul_apply, (hT.2.2.2.1 F E σ d (d.S h Φ) hSh).2 x γ,
      _root_.PositivityTheory.SiegelWeilFormula.KSplit.thetaSum_S_rat_k hT d _ (d.ok.dbl.weil.2.1.pres _ _ hSh) γ hγ]
  have e : ∀ h, thetaSum F (d.om x (d.S h (d.S g Φ))) = thetaSum F (d.om x (d.S (h * g) Φ)) := fun h => by
    rw [map_mul, Module.End.mul_apply]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, MeasureTheory.setAverage_eq, e]
  rw [PositivityTheory.ThKF.L2.integral_right d.ok.dom (fun h => thetaSum F (d.om x (d.S h Φ))) hinv g]
theorem I_lin_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ Φ' : d.Fn} (hΦ : Φ ∈ d.sch) (hΦ' : Φ' ∈ d.sch) (a : ℂ) (x : d.G) :
    d.I (Φ + a • Φ') x = d.I Φ x + a * d.I Φ' x := by
  have hi : ∀ Ξ ∈ d.sch, MeasureTheory.IntegrableOn (fun h => thetaSum F (d.om x (d.S h Ξ))) d.D d.μ :=
    fun Ξ hΞ => ((hT.2.2.2.2 F E σ d).2.2 Ξ hΞ).1 x
  have e : ∀ h, thetaSum F (d.om x (d.S h (Φ + a • Φ'))) =
      thetaSum F (d.om x (d.S h Φ)) + a * thetaSum F (d.om x (d.S h Φ')) := fun h => by
    rw [map_add (f := _), map_smul, map_add (f := _), map_smul]
    exact _root_.PositivityTheory.SiegelWeilFormula.KSplit.thetaSum_lin_k hT d (d.ok.dbl.weil.2.1.pres _ _ (d.ok.dbl.lin.pres _ _ hΦ))
      (d.ok.dbl.weil.2.1.pres _ _ (d.ok.dbl.lin.pres _ _ hΦ')) a
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, MeasureTheory.setAverage_eq, e]
  rw [MeasureTheory.integral_add (hi Φ hΦ) ((hi Φ' hΦ').const_mul a), MeasureTheory.integral_const_mul, smul_add,
    mul_smul_comm]
theorem exists_embU_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (u : Matrix (Fin d.m) (Fin d.m) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d.m) ℂ) : ∃ g : UA σ d.A.J, ∀ X : Mx F E d.m d.n,
      R.loc w (mat g⁻¹ * X) = (u * Matrix.of (R.loc w X) : Matrix (Fin d.m) (Fin d.n) ℂ) ∧ (∀ w', w' ≠ w → d.cw w' (mat g⁻¹ * X - X) = 0) ∧
        finOne F • (mat g⁻¹ * X - X) = 0 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitA.exists_embU_k d R w u hu
theorem S_lift_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ)
    (hΨ : Ψ ∈ R.away w) (φ : PX d.m d.n →ₗ[ℂ] d.Fn) (hφ : R.IsLift w Ψ φ) (u : Matrix (Fin d.m) (Fin d.m) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d.m) ℂ) : ∃ g : UA σ d.A.J, ∀ P, d.S g (φ P) = φ (actU u P) := by
  obtain ⟨g, hg⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.exists_embU_k d R w u hu
  refine ⟨g, fun P => ?_⟩
  have hP := hφ P
  have hQ := hφ (actU u P)
  have hΨi := ((hF F E σ d R).2.1 w Ψ hΨ).2
  have hS : d.S g (φ P) ∈ d.sch := d.ok.dbl.lin.pres _ _ hP.1
  have hsub : d.S g (φ P) + (-1 : ℂ) • φ (actU u P) ∈ d.sch := d.sch.add_mem hS (d.sch.smul_mem _ hQ.1)
  have hT0 : d.T (d.S g (φ P) + (-1 : ℂ) • φ (actU u P)) = 0 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplit.T_lin_k]
    funext X
    rw [Pi.add_apply, Pi.smul_apply, (hT.2.1 F E σ d (φ P) hP.1).2.2 g X, hP.2, hQ.2]
    obtain ⟨h1, h2, h3⟩ := hg X
    have eX : mat g⁻¹ * X = X + (mat g⁻¹ * X - X) := by abel
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, smul_eq_mul, Pi.zero_apply]
    rw [h1, eX, hΨi X _ h2 h3, show fP P (u * Matrix.of (R.loc w X)) = fP (actU u P) (R.loc w X) from
      fP_unitary u hu P _]
    ring
  have h0 := (hT.1 F E σ d).2.2 _ hsub hT0
  have : d.S g (φ P) = -((-1 : ℂ) • φ (actU u P)) := eq_neg_of_add_eq_zero_left h0
  rw [this, neg_smul, one_smul, neg_neg]
theorem gIinv_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.GIinv_k := by
  intro hT hF F E _ _ _ _ _ σ d R w Ψ hΨ φ hφ g a b P
  have hI0 : d.I 0 g = 0 := by
    have e := _root_.PositivityTheory.SiegelWeilFormula.KSplit.I_lin_k hT d (Submodule.zero_mem _) (Submodule.zero_mem _) 1 g
    rw [one_smul, add_zero, one_mul] at e
    linear_combination -e
  let Λ : PX d.m d.n →ₗ[ℂ] ℂ :=
    { toFun := fun P => d.I (φ P) g
      map_add' := fun P Q => by
        have e := _root_.PositivityTheory.SiegelWeilFormula.KSplit.I_lin_k hT d (hφ P).1 (hφ Q).1 1 g
        rw [one_smul, one_mul] at e
        simp only [map_add (f := _)]; exact e
      map_smul' := fun c P => by
        have e := _root_.PositivityTheory.SiegelWeilFormula.KSplit.I_lin_k hT d (Submodule.zero_mem _) (hφ P).1 c g
        rw [zero_add, hI0, zero_add] at e
        simp only [map_smul, RingHom.id_apply, smul_eq_mul]; exact e }
  have hΛ : ∀ u ∈ Matrix.unitaryGroup (Fin d.m) ℂ, ∀ P, Λ (actU u P) = Λ P := by
    intro u hu P
    obtain ⟨g', hg'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.S_lift_k hT hF d R w Ψ hΨ φ hφ u hu
    show d.I (φ (actU u P)) g = d.I (φ P) g
    rw [← hg', _root_.PositivityTheory.SiegelWeilFormula.KSplit.I_S_k hT d _ (hφ P).1 g' g]
  exact hOp_kill Λ hΛ (2 * Real.pi) a b P
end PositivityTheory.SiegelWeilFormula.KSplit
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def Tl_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Ψ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, ← map_add (f := _)]
    congr 1
    funext z
    exact mul_add _ _ _
  map_smul' c Φ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, RingHom.id_apply, ← map_smul]
    congr 1
    funext z
    exact mul_left_comm _ _ _
def TK_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Submodule ℂ (Mx F E d.m d.n → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d).map (_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d)
theorem D_dg_mem_k {Φ : d.Fn} (hΦ : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z) :
    Box.D (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d :=
  _root_.PositivityTheory.SiegelWeilFormula.KK.D_kfS_k (fun c hc => by rw [← Matrix.smul_mul, hZ c hc, Matrix.zero_mul]) hΦ
theorem mul_var_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) : (fun X => evX (MvPolynomial.X k) (R.loc w X) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  obtain ⟨Φ, hΦ, rfl⟩ := hf
  obtain ⟨Z₁, Z₂, c₁, c₂, h1, h2, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.var_span'_k R w k
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨(c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ +
    (c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ,
    add_mem (Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KK.D_dg_mem_k hΦ h1)) (Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KK.D_dg_mem_k hΦ h2)), funext fun X => ?_⟩
  have t := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d).map_add ((c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ)
    ((c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ)) X
  simp only [map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = _ at t
  change d.T _ X = _ * d.T Φ X
  rw [t]
  change _ * d.T _ X + _ * d.T _ X = _
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k hΦ) h1, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k hΦ) h2, e X]
  field_simp
theorem mul_pol_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Q : PX d.m d.n) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) :
    (fun X => evX Q (R.loc w X) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  induction Q using MvPolynomial.induction_on generalizing f with
  | C a =>
    have : (fun X => evX (MvPolynomial.C a) (R.loc w X) * f X) = a • f := funext fun X => by
      simp [evX]
    rw [this]; exact Submodule.smul_mem _ _ hf
  | add p q hp hq =>
    have : (fun X => evX (p + q) (R.loc w X) * f X) = (fun X => evX p (R.loc w X) * f X) + fun X => evX q (R.loc w X) * f X :=
      funext fun X => by simp [evX, add_mul]
    rw [this]; exact add_mem (hp hf) (hq hf)
  | mul_X p k hp =>
    have : (fun X => evX (p * MvPolynomial.X k) (R.loc w X) * f X) =
        fun X => evX (MvPolynomial.X k) (R.loc w X) * (evX p (R.loc w X) * f X) := funext fun X => by
      simp only [evX, map_mul]; ring
    rw [this]; exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_var_k R w k (hp hf)
theorem mul_prod_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) (s : Finset (InfinitePlace F)) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) : (fun X => (∏ w ∈ s, evX (P w) (R.loc w X)) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert w s hw ih =>
    have : (fun X => (∏ w ∈ insert w s, evX (P w) (R.loc w X)) * f X) =
        fun X => evX (P w) (R.loc w X) * ((∏ w ∈ s, evX (P w) (R.loc w X)) * f X) := funext fun X => by
      rw [Finset.prod_insert hw, mul_assoc]
    rw [this]; exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_pol_k R w (P w) ih
theorem vac_mem_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ}
    (hg : g ∈ SB _) : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  have hgen : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g ∈ R.fock := Submodule.subset_span ⟨fun _ => 1, g, hg, funext fun X => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, fP, evX]⟩
  obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 hgen)
  refine ⟨Φ, _root_.PositivityTheory.SiegelWeilFormula.KK.vac_kfS_k (_root_.PositivityTheory.SiegelWeilFormula.KK.thA_k R) (_root_.PositivityTheory.SiegelWeilFormula.KK.thB_k d R.ε) (fun k hk w => _root_.PositivityTheory.SiegelWeilFormula.KK.commute_thB_k R hk w) (fun _ => 1) hΦ fun u u' hu hu' hr => ?_, e⟩
  have m1 : Box.D (d.dd.e u') Φ ∈ d.sch := Box.DP_mem hΦ _ _
  have m2 : Box.D (d.dd.e u) Φ ∈ d.sch := Box.DP_mem hΦ _ _
  refine sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem m1 (Submodule.smul_mem _ _ m2)) (funext fun X => ?_))
  have t := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d).map_sub (Box.D (d.dd.e u') Φ) (Complex.I • Box.D (d.dd.e u) Φ)) X
  simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = d.T _ X - Complex.I * d.T _ X at t
  rw [t, _root_.PositivityTheory.SiegelWeilFormula.KK.vac_rel_k R g hΦ e hu hu' hr X, sub_self]
  rfl
theorem fock_le_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have e : (fun X => (∏ w ∈ Finset.univ, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w ∈ Finset.univ, evX (P w) (R.loc w X)) * _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X := funext fun X => by
    simp only [fP, _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, Finset.prod_mul_distrib]; ring
  rw [SetLike.mem_coe, e]
  exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_prod_k R P _ (_root_.PositivityTheory.SiegelWeilFormula.KK.vac_mem_k hT hF R hg)
theorem polyKFin_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k := by
  intro hT hF F E _ _ _ _ _ σ d R Φ hΦ hf
  obtain ⟨Φ', h', e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.fock_le_k hT hF R hf
  have : Φ = Φ' := (sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k h')) (by
    rw [show d.T (Φ - Φ') = _root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d (Φ - Φ') from rfl, map_sub]
    exact sub_eq_zero.2 e.symm))).symm ▸ rfl
  rw [this]
  exact _root_.PositivityTheory.SiegelWeilFormula.KK.kFin_of_mem_k h'
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isW_rat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) : w ∈ rat2 σ d.Y := by
  refine PositivityTheory.SiegelWeilFormula.kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
  rw [(hw : inFrame d.b w = _)]
  ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp
theorem thetaW_k : _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaW_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun ε w hw Φ hΦ => ?_, GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ⟩
  exact ⟨d.ok.dbl.weil.2.1.pres w Φ hΦ, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_rational_invariant d w (_root_.PositivityTheory.SiegelWeilFormula.TW.ThetaWPf.isW_rat_k d hw) Φ hΦ⟩
end PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
end
end
end

section



section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
namespace PositivityTheory.ThKF0
theorem thetaBasic_of_k (harch : _root_.PositivityTheory.ThKF0.ArchBd_k) : _root_.GlobalTheory.ThK.ThetaBasic_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hS := hP.weil.isUSplitting
  obtain ⟨l, hl, hlt⟩ := (GlobalTheory.T.theta_distribution_nonzero_admissible F (Fin n × Fin d)).2.1
  refine ⟨fun Φ hΦ => ⟨?_, ?_, _root_.PositivityTheory.ThKF0.norm_theta_le_mul_ht_pow_of_isPair harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ⟩, ?_⟩
  · refine (hS.cont l hl Φ hΦ).congr fun x => ?_
    simp only [theta]
    exact hlt _ (hS.pres _ _ hΦ)
  · intro γ hγ γ' hγ' g h
    simp only [theta]
    have e : om (γ * g, γ' * h) Φ = om (γ, γ') (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul]; rfl
    rw [e]
    exact _root_.PositivityTheory.ThKF0.thetaSum_rational_pair_invariant F E σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' _ (hS.pres _ _ hΦ)
  · intro φ hφ g h
    obtain ⟨T, hT⟩ := hS.adm (g, h) l hl φ hφ
    refine T.continuous.congr fun f => ?_
    simp only [theta]
    have hm : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) φ ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    rw [← hlt _ (hS.pres _ _ hm)]
    exact (hT f).symm
end PositivityTheory.ThKF0
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepW_exp (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : ∀ (ε : ℤˣ) (w₀ : d.G), d.IsW ε w₀ →
    ∃ (C : ℂ) (B : d.MF → d.MF), C ≠ 0 ∧ R.StepOK w w₀ (fun f u => C * ∫ v : Fin d.m → Fin d.n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) B := by
  intro ε w₀ hw
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  obtain ⟨C, μ', hC, -, hfact⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.intFact_k F E σ d R w ν hν
  have hs : (-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) (_root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero ε)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero (R.sg w))
  refine ⟨(C : ℂ), fun Ψ X => ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ', by exact_mod_cast hC.ne',
    fun f hf => KW.locFT_sw _ _ hs f hf, fun Ψ hΨ => ⟨?_, ?_⟩⟩
  · intro X Z hZ1 hZ2
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z₀ => ?_)
    simp only
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KW.gram_supp_cmp_k d w ⟨hZ1, hZ2⟩ Z₀.2, _root_.PositivityTheory.SiegelWeilFormula.KW.psi_zero_gram_k, mul_one]
  · intro f hf Φ hΦ hTΦ
    funext X
    rw [hT.2.2.1 F E σ d ν hν ε w₀ hw Φ hΦ X, hTΦ]
    let Ψ' : Mx F E d.m d.n → ℂ := fun Z =>
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)))) * Ψ Z
    have hΨ' : ∀ X' Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ' (X' + Z) = Ψ' X' := by
      intro X' Z hZ1 hZ2
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KW.rest_inv_k R w X' Z ⟨hZ1, hZ2⟩, hΨ X' Z hZ1 hZ2]
    have e : (fun Z => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * R.tens w f Ψ Z) =
        R.tens w (fun u => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) * f u) Ψ' := by
      funext Z
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Ψ']
      have h := _root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_right_k d ε X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z))
      rw [add_sub_cancel] at h
      rw [h]
      ring
    rw [e]
    refine (hfact (fun u => d.B.ψ (((ε : ℤ) : AF F) *
      d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) * f u) Ψ' hΨ').trans ?_
    have e2 : ∫ Z, Ψ' Z.1 ∂μ' = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ' := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w Z.2, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_zero_k, sub_zero]
    rw [e2]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KW.kernel_k R w ε X]
end RD
end PositivityTheory.SiegelWeilFormula
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
theorem hg_sch_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg' : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) : ∃ h : 𝓢(_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d, ℂ), ⇑h = _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.hg_sch_k R hνf hf hg'
theorem mem_fock_of_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) (H : ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∃ P : MvPolynomial (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℂ,
      ∀ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) :
    f ∈ R.fock := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.mem_fock_of_k R hνf hf H
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end
