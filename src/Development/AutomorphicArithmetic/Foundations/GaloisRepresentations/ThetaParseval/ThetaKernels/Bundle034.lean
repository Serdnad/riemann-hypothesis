module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.LRhoOm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle250
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle006
public import Development.WeilBound.ThetaLifts.FrameEstimates.SiegelAll
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bundle003
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem rho_smul'_k (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : ℂ) (φ : d.Fn) :
    d.dd.rho d.B.ψ w (c • φ) = c • d.dd.rho d.B.ψ w φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring
theorem T_smul'_k (c : ℂ) (φ : d.Fn) (X : Mx F E d.m d.n) : d.T (c • φ) X = c * d.T φ X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.KFP.rho_smul'_k, map_smul, smul_eq_mul]
theorem T_rho_sum'_k (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (Z Z' X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ + Z' * (incM F d.b.1.toCols₁)ᵀ) Φ) X =
      d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d (Z * (incM F d.b.1.toCols₂)ᵀ) (Z' * (incM F d.b.1.toCols₁)ᵀ))) *
        (d.B.ψ (d.tt (d.gram Z' (X + Z))) * d.T Φ (X + Z)) := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hrho : ∀ w, ∀ φ ∈ d.sch, d.dd.rho d.B.ψ w φ ∈ d.sch := fun w φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ hψ d.κ _ φ hφ
  set a := Z * (incM F d.b.1.toCols₂)ᵀ
  set b := Z' * (incM F d.b.1.toCols₁)ᵀ
  have h1 := Tpar.rho_rho (dd := d.dd) (ψ := d.B.ψ) a b Φ
  have h2 : d.dd.rho d.B.ψ (a + b) Φ =
      d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d a b)) • d.dd.rho d.B.ψ a (d.dd.rho d.B.ψ b Φ) := by
    have h3 := congrArg (fun x : d.Fn => d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d a b)) • x) h1
    change d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d a b)) • d.dd.rho d.B.ψ a (d.dd.rho d.B.ψ b Φ) = d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d a b)) • (d.B.ψ (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d a b) • d.dd.rho d.B.ψ (a + b) Φ) at h3
    rw [smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul] at h3
    exact h3.symm
  rw [h2, _root_.PositivityTheory.SiegelWeilFormula.KFP.T_smul'_k, (hH F E σ d _ (hrho b Φ hΦ) Z X).1, (hH F E σ d Φ hΦ Z' (X + Z)).2]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem om_mem_k {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ hΦ
theorem S_mem_k {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (h : UA σ d.A.J) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) : d.S h Φ ∈ d.sch :=
  d.ok.dbl.lin.pres h Φ hΦ
theorem thetaPt_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaPt_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ x h
  obtain ⟨-, hTPar, -, hTT, -⟩ := hT
  have hx := _root_.PositivityTheory.SiegelWeilFormula.Kdil.om_mem_k d x hΦ
  rw [(hTT F E σ d Φ hΦ).2 x h, ← ((hTT F E σ d _ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.S_mem_k d h hx)).1).tsum_eq]
  congr 1
  funext X
  exact (hTPar F E σ d _ hx).2.2 h (incM F X)
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil.Tb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev bA_k : Module.Basis (Fin 2) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) d.bs
abbrev Ix_k : Type := Fin d.m × Fin d.n × Fin 2
theorem tmul_eq_k (c : AF F) (k : Fin 2) : c ⊗ₜ[F] d.bs k = c • _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d k := by
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem cmb_eq_k (c : _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d → AF F) (i : Fin d.m) (j : Fin d.n) : d.cmb c i j = ∑ k, c (i, j, k) • _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.tmul_eq_k]
theorem cmb_crd_k (Y : Mx F E d.m d.n) : d.cmb (d.crd Y) = Y := by
  funext i j
  rw [_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cmb_eq_k]
  exact (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).sum_repr (Y i j)
theorem crd_cmb_k (c : _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d → AF F) : d.crd (d.cmb c) = c := by
  funext p
  obtain ⟨i, j, k⟩ := p
  show ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).repr (d.cmb c i j)) k = c (i, j, k)
  rw [_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cmb_eq_k]
  exact congrFun ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).repr_sum_self fun k => c (i, j, k)) k
def mh_k (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) : Matrix (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (AF F) :=
  fun p q => if p.2.1 = q.2.1 then (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).repr (M p.1 q.1 * _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d q.2.2) p.2.2 else 0
theorem crd_mul_k (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) (Y : Mx F E d.m d.n) :
    d.crd (M * Y) = _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d M *ᵥ d.crd Y := by
  funext p
  obtain ⟨i, j, k⟩ := p
  have hY : ∀ i', Y i' j = ∑ k', d.crd Y (i', j, k') • _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d k' := fun i' => ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).sum_repr (Y i' j)).symm
  show ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).repr ((M * Y) i j)) k = _
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun i' _ => by rw [hY i']]

  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k, ite_mul, zero_mul, Finset.sum_ite_eq,
  Finset.mem_univ, if_true, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
  Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd (Finset.mem_univ j) h)]
  simp only [if_true]
  exact Finset.sum_congr rfl fun k' _ => mul_comm _ _
theorem mulVec_ext_k {A B : Matrix (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (AF F)} (h : ∀ c, A *ᵥ c = B *ᵥ c) : A = B := by
  ext p q
  have := congrFun (h (Pi.single q 1)) p
  simpa [Matrix.mulVec_single_one] using this
theorem mh_mul_k (M N : Matrix (Fin d.m) (Fin d.m) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d (M * N) = _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d M * _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d N :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mulVec_ext_k d fun c => by
    conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_cmb_k d c]
    conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_cmb_k d c]
    rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k, ← Matrix.mulVec_mulVec, ← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k, Matrix.mul_assoc]
theorem mh_one_k : _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d 1 = 1 :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mulVec_ext_k d fun c => by
    conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_cmb_k d c]
    rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k, Matrix.one_mul, _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_cmb_k, Matrix.one_mulVec]
theorem continuous_mh_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k]
  split_ifs
  · have hc := (IsModuleTopology.continuous_of_linearMap ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).coord p.2.2)).comp
      ((continuous_id.matrix_elem p.1 q.1).mul (continuous_const (y := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d q.2.2)))
    exact hc
  · exact continuous_const
def mhU_k : GL (Fin d.m) (AE F E) →* GL (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (AF F) :=
  Units.map { toFun := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d, map_one' := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_one_k d, map_mul' := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_mul_k d }
theorem continuous_mhU_inv_k : Continuous fun h : UA σ d.A.J => _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mhU_k d ((h : GL (Fin d.m) (AE F E))⁻¹) := by
  rw [Units.continuous_iff]
  have h1 : Continuous fun h : UA σ d.A.J => ((h : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have h2 : Continuous fun h : UA σ d.A.J =>
      (((h : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  refine ⟨(_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.continuous_mh_k d).comp h2, ?_⟩
  simp only [← map_inv, inv_inv]
  exact (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.continuous_mh_k d).comp h1
def xi_k : Matrix (Fin d.m) (Fin d.n) E ≃ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d → F) where
  toFun X p := d.bs.repr (X p.1 p.2.1) p.2.2
  invFun c i j := ∑ k, c (i, j, k) • d.bs k
  left_inv X := by
    funext i j
    exact d.bs.sum_repr (X i j)
  right_inv c := by
    funext p
    obtain ⟨i, j, k⟩ := p
    exact congrFun (d.bs.repr_sum_self fun k => c (i, j, k)) k
theorem crd_incM_k (X : Matrix (Fin d.m) (Fin d.n) E) : d.crd (incM F X) = PositivityTheory.RgEis.ratV (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d X) := by
  funext p
  obtain ⟨i, j, k⟩ := p
  show ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).repr ((1 : AF F) ⊗ₜ[F] X i j)) k = algebraMap F (AF F) (d.bs.repr (X i j) k)
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp
theorem bound_cpt_k (Fn : Mx F E d.m d.n → ℂ) (hF : Fn ∈ d.schM) (Ω : Set (UA σ d.A.J)) (hΩ : IsCompact Ω) :
    ∃ u : (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d → F) → ℝ, Summable u ∧ ∀ h ∈ Ω, ∀ X, ‖Fn (mat h⁻¹ * incM F X)‖ ≤ u (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d X) := by
  have hG : (fun c => Fn (d.cmb c)) ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := F) (ι := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) := hF
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hG (hΩ.image (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.continuous_mhU_inv_k d))
  refine ⟨u, hu, fun h hh X => ?_⟩
  have e : Fn (mat h⁻¹ * incM F X) =
      Fn (d.cmb (((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mhU_k d ((h : GL (Fin d.m) (AE F E))⁻¹) : GL (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (AF F)) : Matrix (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (AF F)) *ᵥ
        PositivityTheory.RgEis.ratV (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d X))) := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_incM_k, ← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cmb_crd_k d (mat h⁻¹ * incM F X), _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k]
    rfl
  rw [e]
  exact hb _ ⟨h, hh, rfl⟩ _
theorem reindex_k (Fn : Mx F E d.m d.n → ℂ) (γ : UA σ d.A.J) (hγ : γ ∈ ratU σ d.A.J) :
    ∃ e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E, ∀ h X,
      Fn (mat (γ * h)⁻¹ * incM F (e X)) = Fn (mat h⁻¹ * incM F X) := by
  obtain ⟨G, hG⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hinc : ∀ A B : Matrix (Fin d.m) (Fin d.m) E, incM F (A * B) = incM F A * incM F B := fun A B => by
    simp only [incM]; exact Matrix.map_mul
  have hinc' : ∀ (A : Matrix (Fin d.m) (Fin d.m) E) (B : Matrix (Fin d.m) (Fin d.n) E), incM F (A * B) = incM F A * incM F B :=
    fun A B => by simp only [incM]; exact Matrix.map_mul
  have l1 : ∀ X : Matrix (Fin d.m) (Fin d.n) E, ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) * ((G : Matrix (Fin d.m) (Fin d.m) E) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have l2 : ∀ X : Matrix (Fin d.m) (Fin d.n) E, (G : Matrix (Fin d.m) (Fin d.m) E) * (((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  refine ⟨⟨fun X => (G : Matrix (Fin d.m) (Fin d.m) E) * X, fun X => ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) * X, l1, l2⟩,
    fun h X => ?_⟩
  congr 1
  have hm : mat (γ * h)⁻¹ = mat h⁻¹ * incM F ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) := by
    have : (((γ : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) =
        incM F ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) := by
      rw [← hG, ← map_inv]; rfl
    simp only [mat, mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    rw [this]
  simp only [Equiv.coe_fn_mk, hm]
  rw [Matrix.mul_assoc, ← hinc', l1]
theorem cpt_k (hS : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.ThK.Dbl.Cpt σ d.A.J := by
  have hC := _root_.GlobalTheory.ThK.Dbl.cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k (PositivityTheory.ThKEst.siegelAll_of hS)
    PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
  rcases d.ok.sign with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hC F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inl h1) d.ok.aniso
  · exact hC F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inr h1) d.ok.aniso
end PositivityTheory.SiegelWeilFormula.Kdil.Tb
namespace PositivityTheory.SiegelWeilFormula.Kdil
open Tb in
theorem thetaBdd_of_k (hS : GlobalTheory.Published.SiegelSetUnitary) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaBdd_k := by
  intro F E _ _ _ _ _ σ d Fn hF
  obtain ⟨Ω, hΩ, cov⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cpt_k d hS).cov
  obtain ⟨u, hu, hb⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bound_cpt_k d Fn hF Ω hΩ
  refine ⟨∑' ξ, u ξ, fun h => ?_⟩
  obtain ⟨γ, hγ, hγΩ⟩ := cov h
  obtain ⟨e, he⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.reindex_k d Fn γ hγ
  have key : (fun X => ‖Fn (mat h⁻¹ * incM F X)‖) = (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖) ∘ e := by
    funext X
    exact congrArg norm (he h X).symm
  have hs : Summable (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun Y => hb _ hγΩ Y) ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d).summable_iff.2 hu)
  refine ⟨?_, ?_⟩
  · rw [key]; exact e.summable_iff.2 hs
  · rw [key]
    show ∑' X, ‖Fn (mat (γ * h)⁻¹ * incM F (e X))‖ ≤ _
    rw [e.tsum_eq (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖)]
    calc ∑' Y, ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖ ≤ ∑' Y, u (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d Y) :=
          hs.tsum_le_tsum (fun Y => hb _ hγΩ Y) ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d).summable_iff.2 hu)
      _ = ∑' ξ, u ξ := (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d).tsum_eq u
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem gIdil_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hTP : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaPt_k) (hFP : FPSw) (hMC : MatCount)
    (hSD : _root_.PositivityTheory.SiegelWeilFormula.Kdil.SplitDom_k) (hTB : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaBdd_k) (hLF : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k) (hBD : BigDense) (hHM : HolMean)
    (hDC : DerCont) (hSO : StripOK) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k := by
  intro F E _ _ _ _ _ σ d R w Ψ hΨ φ hφ g X a ha
  obtain ⟨-, -, -, -, hTA⟩ := hT
  obtain ⟨hμ0, hμT, hTA'⟩ := hTA F E σ d
  obtain ⟨-, -, hGtop, -, -, -⟩ := hAux F E σ d
  obtain ⟨L, hL⟩ := hLE F E σ d R w
  obtain ⟨y₀, Ψ', hrep, hmaj⟩ := hSD F E σ d R w L hL Ψ hΨ g
  obtain ⟨Gf, hreal, hhol, hcont, hbd, hder⟩ := hLF F E σ d R w L hL X a ha
  obtain ⟨hUo, hUR, hUb⟩ := hSO d.n X
  have hcount := hMC E d.m d.n
  set U := strip X with hU
  have h0U : (0 : ℂ) ∈ U := by simpa using hUR 0
  set Fm : GR d.n → ℂ → UA σ d.A.J → Matrix (Fin d.m) (Fin d.n) E → ℂ := fun y z h Xr =>
    Gf (y₀ * y) z (R.loc w (mat h⁻¹ * incM F Xr)) * Ψ' (mat h⁻¹ * incM F Xr) with hFm
  set ν : Measure (UA σ d.A.J) := (d.μ.restrict d.D Set.univ)⁻¹ • d.μ.restrict d.D with hν
  have hav : ∀ f : UA σ d.A.J → ℂ, (⨍ h in d.D, f h ∂d.μ) = ∫ h, f h ∂ν := fun f => rfl
  have hc : (d.μ.restrict d.D Set.univ)⁻¹ ≠ ⊤ := by
    rw [ENNReal.inv_ne_top, Measure.restrict_apply_univ]; exact hμ0
  haveI : IsFiniteMeasure (d.μ.restrict d.D) := isFiniteMeasure_restrict.mpr hμT
  have hI : ∀ Φ ∈ d.sch, ∀ x, d.I Φ x =
      ∫ h, ∑' Xr : Matrix (Fin d.m) (Fin d.n) E, d.T (d.om x Φ) (mat h⁻¹ * incM F Xr) ∂ν := by
    intro Φ hΦ x
    rw [← hav]
    show (⨍ h in d.D, thetaSum F (d.om x (d.S h Φ)) ∂d.μ) = _
    simp_rw [hTP F E σ d Φ hΦ x]
  have hT1 : ∀ P y', d.T (d.om (g * R.ι w y') (φ P)) = R.tens w (L (y₀ * y') (fP P)) Ψ' := fun P y' =>
    hrep (φ P) (hφ P).1 (fP P) (hFP _ _ P) (hφ P).2 y'
  obtain ⟨hHc, hHd, hHr⟩ := hHM (GR d.n) (UA σ d.A.J) (Matrix (Fin d.m) (Fin d.n) E) ν U hUo hUb Fm
    (fun p h Xr => (hhol (y₀ * p) _).mul_const _)
    (fun h Xr => ((hcont (R.loc w (mat h⁻¹ * incM F Xr))).comp (f := fun q : GR d.n × ℂ => (y₀ * q.1, q.2))
      (by fun_prop) (fun q (hq : q ∈ Set.univ ×ˢ U) => ⟨trivial, hq.2⟩)).mul continuousOn_const)
    (by
      intro p t _
      have e : (fun h => ∑' k, Fm p t h k) = fun h => thetaSum F (d.om (g * R.ι w (p * a t)) (d.S h (φ 1))) := by
        funext h
        rw [hTP F E σ d (φ 1) (hφ 1).1, hT1 1 (p * a t)]
        simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hreal, mul_assoc]
      rw [e]
      exact ((hTA' (φ 1) (hφ 1).1).1 _).aestronglyMeasurable.smul_measure _)
    (by
      rintro ⟨p, z⟩ ⟨-, hz⟩
      obtain ⟨N, hN, C, δ, hδ, hCb⟩ := hbd (y₀ * p, z) ⟨trivial, hz⟩
      obtain ⟨K, hK⟩ := hTB F E σ d _ (hmaj δ hδ)
      refine ⟨(fun q : GR d.n × ℂ => (y₀ * q.1, q.2)) ⁻¹' N,
        (Continuous.continuousAt (by fun_prop)).preimage_mem_nhds hN,
        fun h Xr => |C| * ‖R.tens w (fun u => (Real.exp (-δ * sq u) : ℂ)) Ψ' (mat h⁻¹ * incM F Xr)‖,
        fun _ => |C| * K, fun h => (hK h).1.mul_left _, (integrable_const _).smul_measure hc, ?_, ?_⟩
      · intro h
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hK h).2 (abs_nonneg C)
      · intro q' hq' hq'U h Xr
        have hb1 := hCb (y₀ * q'.1, q'.2) hq' hq'U (R.loc w (mat h⁻¹ * incM F Xr))
        have he : 0 ≤ Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr))) := (Real.exp_pos _).le
        simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
        calc ‖Gf (y₀ * q'.1) q'.2 (R.loc w (mat h⁻¹ * incM F Xr))‖ * ‖Ψ' (mat h⁻¹ * incM F Xr)‖
            ≤ (C * Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr)))) * ‖Ψ' (mat h⁻¹ * incM F Xr)‖ :=
              mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
          _ ≤ (|C| * Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr)))) * ‖Ψ' (mat h⁻¹ * incM F Xr)‖ := by
              gcongr; exact le_abs_self C
          _ = _ := by ring)
  clear_value Fm
  refine ⟨U, fun y z => ∫ h, ∑' k, Fm y z h k ∂ν, hUo, hUR, hHc, fun y => ⟨hHd y, ?_, ?_⟩⟩
  · intro t
    beta_reduce
    rw [hI (φ 1) (hφ 1).1, hT1 1 (y * a t)]
    congr 1
    funext h
    congr 1
    funext Xr
    simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hreal, mul_assoc]
  · intro r
    have key : ∀ y', ((mR (y₀ * y')).toBlocks₂₂).det ≠ 0 →
        iteratedDeriv r (fun z => ∫ h, ∑' k, Fm y' z h k ∂ν) 0 =
          d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y') := by
      intro y' hy'
      rw [hHr y' 0 h0U r, hI _ (hφ _).1, hT1]
      congr 1
      funext h
      congr 1
      funext Xr
      simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
      rw [iteratedDeriv_mul_const' (fun z => Gf (y₀ * y') z (R.loc w (mat h⁻¹ * incM F Xr))) _ r]
      beta_reduce
      rw [hder (y₀ * y') hy' r]
    have hDC' := hDC (GR d.n) U hUo (fun y' z => ∫ h, ∑' k, Fm y' z h k ∂ν) hHc hHd r
    have hpair : Continuous fun y' : GR d.n => (y', (0 : ℂ)) := by fun_prop
    have hcL : Continuous fun y' => iteratedDeriv r (fun z => ∫ h, ∑' k, Fm y' z h k ∂ν) 0 :=
      hDC'.comp_continuous hpair (fun _ => ⟨trivial, h0U⟩)
    have hcR : Continuous fun y' => d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y') :=
      (hTA' _ (hφ _).1).2.1.comp (continuous_const.mul (R.cont w))
    have hden : Dense {y' : GR d.n | ((mR (y₀ * y')).toBlocks₂₂).det ≠ 0} :=
      (hBD d.n).preimage (isOpenMap_mul_left y₀)
    exact congrFun (hcL.ext_on hden hcR key) y
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
def YFrame_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ), n + 1 = d.n → 1 ≤ n →
  ∃ (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ), _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y ∧ IsFrame2 σ Y b ∧
    d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε
def JEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∃ j : G2 σ Y →* d.G, _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j
def KStd_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), IsFrame2 σ Y b → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j → IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j)
def HgtPull_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j → IsHgt (d.K.comap j) (d.a ∘ j)
def ModelEx_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  (∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∃ (κ : Type) (_ : Fintype κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ d.A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), IsDbl (σ := σ) (A := d.A) (Y := Y) d.B.ψ dd d.χ om S l ∧ _root_.PositivityTheory.SiegelWeilFormula.Ald.Res_k d h b j dd om l
theorem ldEx_of_leaves_k (h1 : _root_.PositivityTheory.SiegelWeilFormula.Ald.YFrame_k) (h2 : _root_.PositivityTheory.SiegelWeilFormula.Ald.JEx_k) (h3 : _root_.PositivityTheory.SiegelWeilFormula.Ald.KStd_k) (h4 : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k) (h5 : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k) : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.LDEx_k := by
  intro hT hA F E _ _ _ _ _ σ d hn
  have h : (d.n - 1) + 1 = d.n := by omega
  have hn1 : 1 ≤ d.n - 1 := by omega
  obtain ⟨Y, b, ε, hs, hb, e1, e2⟩ := h1 F E σ d (d.n - 1) h hn1
  obtain ⟨j, hj⟩ := h2 F E σ d (d.n - 1) h Y b ε e1 e2
  obtain ⟨κ, _, dd, om, S, l, hd, hr⟩ := h5 hT hA F E σ d (d.n - 1) h Y b j hn1 hs hb ⟨ε, e1, e2⟩ hj
  let L0 : _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum d :=
    { n := d.n - 1, Y := Y, κ := κ, dd := dd, om := om, S := S, l := l, b := b, K := d.K.comap j, a := fun x => d.a (j x),
      ok := ⟨d.ok.good, d.ok.hm, hn1, d.ok.aniso, hs, d.ok.hecke, d.ok.res, hd, hb, h3 F E σ d _ h Y b j hb hj,
        h4 F E σ d _ h Y b j hn1 hs hb hj, d.ok.haar, d.ok.dom⟩ }
  exact ⟨{ toLiftedSchrodingerDatum := L0, i₀ := i0 h, em := em0 h, inj := em0_injective h, rng := ne_last_iff_mem_range h, j := j, cont := hj.1,
             j_in := hj.2.1, j_out := hj.2.2, res := hr }⟩
end PositivityTheory.SiegelWeilFormula.Ald
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
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def eA_k : AE F E := (((R.ε : ℤ) : E) : E) |> inclR (F := F) (E := E) (AF F)
def elt_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) : d.G :=
  if h : ∃ x : d.G, inFrame d.b x = M then h.choose else 1
def uA_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)
def bMat_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 1 β 0 1
def sB_k (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R * cA σ (b j))))
def aB_k (δ : E) (a : AF F) : Matrix (Fin d.n) (Fin d.n) (AE F E) := Matrix.single L.i₀ L.i₀ (a • inclR (F := F) (E := E) (AF F) δ)
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
