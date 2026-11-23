module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinTDer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle027
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FrameBlockPairingSign
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle016
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FirstFrameHalfEqMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneSmulAdr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.ContinuousLoc
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Mathlib.Analysis.Matrix.MeasurableSpace
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
theorem cwA_add_k (w : InfinitePlace F) (X Y : Mx F E d.m d.n) : d.cw w (X + Y) = d.cw w X + d.cw w Y := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
theorem cwA_realAd_k (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    d.cw w (realAd F t • X) = (t : ℂ) • d.cw w X := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, GlobalTheory.RealScalar.piInf_realAd_smul]
theorem locA_add_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X Y : Mx F E d.m d.n) :
    R.loc w (X + Y) = R.loc w X + R.loc w Y := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, _root_.PositivityTheory.SiegelWeilFormula.KFP.cwA_add_k, Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _
theorem locA_realAd_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (t : ℝ) (X : Mx F E d.m d.n) :
    R.loc w (realAd F t • X) = (t : ℂ) • R.loc w X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, _root_.PositivityTheory.SiegelWeilFormula.KFP.cwA_realAd_k, Matrix.mul_smul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  rfl
def arcAF_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ :=
  fun i => if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im
theorem arcA_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X = (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R X) := rfl
theorem arc_add'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X Y : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (X + Y) = _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X + _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R Y := by
  have : _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R (X + Y) = _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R X + _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R Y := by
    funext i
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.locA_add_k, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, this, map_add (f := _)]
theorem arc_realAd'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (realAd F t • X) = t • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X := by
  have : _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R (realAd F t • X) = t • _root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k R X := by
    funext i
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcAF_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.locA_realAd_k, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arcA_eq_k, this, map_smul]
theorem crdA_add_k (X Y : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Y) k = d.crd X k + d.crd Y k := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
theorem sndA_crd_of_k (Z : Mx F E d.m d.n) (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd Z k).2 = 0 := by
  have h1 : finOne F • Z k.1 k.2.1 = 0 := by
    have := congrFun (congrFun hZ k.1) k.2.1
    simpa using this
  have h2 : finOne F * (Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2 = 0 := by
    have := congrArg (fun z => (Algebra.TensorProduct.basis (AF F) d.bs).repr z k.2.2) h1
    simpa only [map_smul, Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] using this
  have h3 : (1 : FiniteAdeleRing (𝓞 F) F) * ((Algebra.TensorProduct.basis (AF F) d.bs).repr (Z k.1 k.2.1) k.2.2).2 = 0 :=
    congrArg Prod.snd h2
  rw [one_mul] at h3
  exact h3
theorem fin_add_of'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d (X + Z) = _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X := by
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.crdA_add_k]
  show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.sndA_crd_of_k Z hZ k, add_zero]
theorem fin_realAd_smul'_k {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (t : ℝ) : finOne F • (realAd F t • Z) = 0 := by
  rw [smul_comm, hZ, smul_zero]
theorem gau_eq'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k R X = (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) := by
  have hn : ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2 = ∑ w, ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.equiv, if_true, if_false]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k, fP, evX, map_one, one_mul, gs]
  rw [hn, ← Complex.exp_sum, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem continuous_loc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : Continuous (fun X : Mx F E d.m d.n => R.loc w X) := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w (p := Fin d.m) (q := Fin d.n)
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  refine continuous_pi fun a => continuous_pi fun j => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply]
  exact continuous_star.comp (continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp h)))
theorem continuous_arc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k
  refine (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  have h : Continuous fun X : Mx F E d.m d.n => R.loc i.1 X i.2.1 i.2.2.1 :=
    (continuous_apply _).comp ((continuous_apply _).comp (_root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_loc_k R i.1))
  split_ifs
  · exact Complex.continuous_re.comp h
  · exact Complex.continuous_im.comp h
theorem continuous_fin_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k
  exact continuous_pi fun k => continuous_snd.comp ((continuous_apply k).comp (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_crd_k d))
theorem continuous_zOf_k : Continuous (fun u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ => _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k u) := by
  refine continuous_pi fun w => continuous_pi fun a => continuous_pi fun j => ?_
  have : (fun u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ => _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k u w a j) =
      fun u => Complex.equivRealProdCLM.symm (u (w, a, j, true), u (w, a, j, false)) := by
    funext u
    rfl
  rw [this]
  exact Complex.equivRealProdCLM.symm.continuous.comp ((continuous_apply _).prodMk (continuous_apply _))
theorem zOf_add_k (u v : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ) : _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (u + v) = _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k u + _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k v := by
  funext w a j
  apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k]
theorem jn_eq_cmb_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ cF : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin d.m × Fin d.n × Fin 2 → AF F), Continuous cF ∧
      (∀ p q, cF (p + q) = cF p + cF q) ∧ ∀ p, _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2 = d.cmb (cF p) := by
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  let cF : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin d.m × Fin d.n × Fin 2 → AF F) := fun p k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) k))
      (p.2 k) : AF F)
  refine ⟨cF, ?_, fun p q => ?_, fun p => ?_⟩
  · refine continuous_pi fun k => ?_
    have e : (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => cF p k) = fun p =>
        (Prod.mk ((GroundTheory.Global.homeomorphMixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) k))
          (p.2 k) : AF F) := by
      funext p
      simp only [cF]
      rw [homeo_symm_eq]
    rw [e]
    exact Continuous.prodMk ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply k).comp
      (L.symm.continuous.comp (_root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_zOf_k.comp ((EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).continuous.comp continuous_fst)))))
      ((continuous_apply k).comp continuous_snd)
  · funext k
    refine Prod.ext ?_ ?_
    · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ (p + q).1)) k) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) k) +
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ q.1)) k)
      rw [← map_add (f := _), Prod.fst_add, map_add (f := _), _root_.PositivityTheory.SiegelWeilFormula.KFPB.zOf_add_k, map_add (f := _)]
      rfl
    · rfl
  · refine (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R p.1 p.2).unique ⟨_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k R p.1 p.2, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R p.1 p.2⟩ ⟨?_, ?_⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k]
      intro w
      rw [← hL (cF p) w]
      have : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (cF p k).1) =
          L.symm (_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ p.1)) := by
        funext k
        exact RingEquiv.apply_symm_apply _ _
      rw [this, ContinuousLinearEquiv.apply_symm_apply]
    · funext k
      show (d.crd (d.cmb (cF p)) k).2 = p.2 k
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb'_k]
def jnpE_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d ≃ₜ+ Mx F E d.m d.n where
  toFun p := _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2
  invFun X := (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)
  left_inv p := Prod.ext (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k R p.1 p.2) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R p.1 p.2)
  right_inv X := _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_arc_fin_k R X
  map_add' p q := by
    obtain ⟨cF, -, hadd, heq⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFPB.jn_eq_cmb_k R
    show _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R (p + q).1 (p + q).2 = _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2 + _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R q.1 q.2
    rw [heq, heq, heq, hadd, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_add_k]
  continuous_toFun := by
    obtain ⟨cF, hc, -, heq⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFPB.jn_eq_cmb_k R
    have : (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) = fun p => d.cmb (cF p) := funext heq
    show Continuous fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2
    rw [this]
    exact (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_cmb_k d).comp hc
  continuous_invFun := (_root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_arc_k R).prodMk _root_.PositivityTheory.SiegelWeilFormula.KFPB.continuous_fin_k
end PositivityTheory.SiegelWeilFormula.KFPB
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
theorem T_add_k (Φ Ψ : d.Fn) (X : Mx F E d.m d.n) : d.T (Φ + Ψ) X = d.T Φ X + d.T Ψ X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, ← map_add (f := _)]
  congr 1
  funext z
  exact mul_add _ _ _
variable (d) in
abbrev firstFrameColumns : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := incM F d.b.1.toCols₁
theorem split_k (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    u = (u * (incM F (d.b⁻¹).1)ᵀ).toCols₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ + (u * (incM F (d.b⁻¹).1)ᵀ).toCols₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ := by
  have e : incM F d.b.1 = Matrix.fromCols (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d) (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns, _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns, ← Matrix.fromCols_toCols d.b.1]; ext i (j | j) <;> rfl
  have e1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← incM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one,
      Matrix.transpose_one]
  calc u = u * (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ := by rw [Matrix.mul_assoc, e1, Matrix.mul_one]
    _ = _ := by
      rw [e, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (u * (incM F (d.b⁻¹).1)ᵀ), Matrix.fromCols_mul_fromRows,
        Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
theorem firstColumns_eq_diag_mul : ∃ t : Matrix (Fin d.n) (Fin d.n) (AE F E), _root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d = _root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d * t := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  refine ⟨incM F t.1, ?_⟩
  have h2 : ∀ i j, d.b.1 i (Sum.inl j) = ∑ k, (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) i k * t.1 k j :=
    fun i j => congrFun₂ ht i j
  ext i j
  rw [Matrix.mul_apply]
  change inclR (AF F) (d.b.1 i (Sum.inl j)) = _

  rw [h2, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  congr 1
  rcases i with i | i <;>
  · change inclR (AF F) ((1 : Matrix (Fin d.n) (Fin d.n) E) i k) = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k
    by_cases h : i = k <;> simp [Matrix.one_apply, h]
def vacF_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, gs (2 * Real.pi) (R.loc w X)) * g fun k => (d.crd X k).2
theorem cw_add_smul_k (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (t : ℝ) :
    d.cw w (X + realAd F t • Z) = d.cw w X + (t : ℂ) • d.cw w Z := by
  ext i j
  show piInf (d.B.emb w) ((X + realAd F t • Z) i j) = piInf (d.B.emb w) (X i j) + (t : ℂ) * piInf (d.B.emb w) (Z i j)
  rw [Matrix.add_apply, Matrix.smul_apply, map_add (f := _), GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul]
theorem crd_add_smul_snd_k (X Z : Mx F E d.m d.n) (t : ℝ) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (X + realAd F t • Z) k).2 = (d.crd X k).2 := by
  have e : d.crd (X + realAd F t • Z) k = d.crd X k + realAd F t * d.crd Z k := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
  rw [e, snd_add_realAd]
def qL_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X Z : Mx F E d.m d.n) (t : ℝ) : ℝ :=
  ∑ w, ∑ a, ∑ i, ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2
theorem gs_loc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (t : ℝ) :
    gs (2 * Real.pi) (R.loc w (X + realAd F t • Z)) = Complex.exp ((-(2 * Real.pi * ∑ a, ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) : ℝ) : ℂ) := by
  simp only [gs, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, _root_.PositivityTheory.SiegelWeilFormula.KK.cw_add_smul_k, Matrix.mul_add, Matrix.mul_smul, Matrix.map_apply, norm_star, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_neg]
theorem vacF_line_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X Z : Mx F E d.m d.n) (t : ℝ) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g (X + realAd F t • Z) = Complex.exp ((-(2 * Real.pi) * _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z t : ℝ) : ℂ) * g fun k => (d.crd X k).2 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, _root_.PositivityTheory.SiegelWeilFormula.KK.crd_add_smul_snd_k, _root_.PositivityTheory.SiegelWeilFormula.KK.gs_loc_k]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.qL_k]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
theorem vacF_deriv_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X Z : Mx F E d.m d.n) :
    HasDerivAt (fun t : ℝ => _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g (X + realAd F t • Z))
      (((-(4 * Real.pi) * ∑ w, (Matrix.trace ((((R.fr w)⁻¹).1 * d.cw w X)ᴴ * (((R.fr w)⁻¹).1 * d.cw w Z))).re : ℝ) : ℂ) *
        _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X) 0 := by
  have hf : (fun t : ℝ => _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g (X + realAd F t • Z)) =
      fun t => Complex.exp ((-(2 * Real.pi) * _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z t : ℝ) : ℂ) * g fun k => (d.crd X k).2 :=
    funext (_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_line_k R g X Z)
  rw [hf]
  have hq : HasDerivAt (_root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z)
      (∑ w, ∑ a, ∑ i, 2 * (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re) 0 := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k
    refine HasDerivAt.fun_sum (A := fun w (t : ℝ) => ∑ a, ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun w _ => ?_
    refine HasDerivAt.fun_sum (A := fun a (t : ℝ) => ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun a _ => ?_
    exact HasDerivAt.fun_sum (A := fun i (t : ℝ) =>
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun i _ =>
      hasDerivAt_normSq _ _
  have he := ((hq.const_mul (-(2 * Real.pi))).ofReal_comp.cexp).mul_const (g fun k => (d.crd X k).2)
  refine he.congr_deriv ?_
  have e0 : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X = Complex.exp ((-(2 * Real.pi) * _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z 0 : ℝ) : ℂ) * g fun k => (d.crd X k).2 := by
    have := _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_line_k R g X Z 0
    rwa [realAd_zero, zero_smul, add_zero] at this
  rw [e0]
  have e2 : (∑ w, ∑ a, ∑ i, 2 * (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re) =
      2 * ∑ w, ∑ a, ∑ i, (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re := by
    simp only [Finset.mul_sum]
  simp only [trace_re, e2]
  push_cast
  ring
theorem frame_form_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * dbl (d.Y.J.map (d.B.emb w).1) * (d.b.1.map (d.B.emb w).1).map star = jE d.n R.ε := by
  have h := d.ok.good.cm
  have cst : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E, (x.map σ).map (d.B.emb w).1 =
      (x.map (d.B.emb w).1).map star := fun x => by
    ext i j; exact h.2.2.2 (d.B.emb w).1 (x i j)
  have hd : (dbl d.Y.J).map (d.B.emb w).1 = dbl (d.Y.J.map (d.B.emb w).1) := by
    ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks]
  have := congrArg (fun x => x.map (d.B.emb w).1) R.hε
  simp only [Matrix.map_mul, Matrix.transpose_map, cst, hd] at this
  rw [this]
  ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [jE, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, hij]
theorem map_mul_incM_T_k {p q r : Type} [Fintype q] (w : InfinitePlace F) (x : Matrix p q (AE F E)) (y : Matrix r q E) :
    (x * (incM F y)ᵀ).map (piInf (d.B.emb w)) = x.map (piInf (d.B.emb w)) * (y.map (d.B.emb w).1)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_map, map_incM']
theorem T_D_vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch)
    (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e u) Φ) X = (∑ w, Sw (d.A.J.map (d.B.emb w).1) ((R.fr w)⁻¹).1 (dbl (d.Y.J.map (d.B.emb w).1))
      (d.b.1.map (d.B.emb w).1) ((d.b⁻¹).1.map (d.B.emb w).1) (d.cw w X) (d.cw w u)) * _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X := by
  obtain ⟨tA, htA⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.firstColumns_eq_diag_mul (d := d)
  set W := u * (incM F (d.b⁻¹).1)ᵀ with hW
  have hWa : At (evI F) W := at_mul hu _
  have h1 : At (evI F) (W.toCols₁ * tAᵀ) := at_mul (at_toCols₁ hWa) _
  have h2 : At (evI F) W.toCols₂ := at_toCols₂ hWa
  have e1 : W.toCols₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ = (W.toCols₁ * tAᵀ) * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ := by
    rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
  have hs := _root_.PositivityTheory.SiegelWeilFormula.KK.split_k u
  rw [← hW, e1] at hs
  have hsplitD : Box.D (d.dd.e u) Φ = Box.D (d.dd.e ((W.toCols₁ * tAᵀ) * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ +
      Box.D (d.dd.e (W.toCols₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)) Φ := by
    conv_lhs => rw [hs]
    rw [map_add (f := _), Box.D_add_left]
  rw [hsplitD, _root_.PositivityTheory.SiegelWeilFormula.KK.T_add_k, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k hΦ h1, hT]
  have hder := _root_.PositivityTheory.SiegelWeilFormula.KK.hasDerivAt_translate_secondColumns hΦ h2 X
  rw [hT] at hder
  rw [(_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_deriv_k R g X W.toCols₂).unique hder |>.symm]
  have hmX : ∀ w, (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ := fun w => by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]; rfl
  have hmW : ∀ w, W.map (piInf (d.B.emb w)) = d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ := fun w => by
    rw [hW, _root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]; rfl
  have hmW1 : ∀ w, (W.toCols₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w)) =
      (d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₁ * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ := fun w => by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k, ← hmW]; rfl
  have hmW2 : ∀ w, d.cw w W.toCols₂ = (d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₂ := fun w => by
    rw [← hmW]; rfl
  have hm : _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d (W.toCols₁ * tAᵀ) X = ∑ w, -(2 * (T1 (d.A.J.map (d.B.emb w).1) (dbl (d.Y.J.map (d.B.emb w).1))
      (d.b.1.map (d.B.emb w).1) (d.cw w X) ((d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₁)).re) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, ← e1, _root_.PositivityTheory.SiegelWeilFormula.KK.trace_sp_k]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hmX w, hmW1 w]
    rfl
  rw [hm]
  simp only [hmW2, Sw, T2]
  rw [Finset.sum_mul]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
theorem vac_rel_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch)
    (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g) {u u' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (hu' : At (evI F) u') (hr : Box.Rel d.B.emb (fun _ => 1) (_root_.PositivityTheory.SiegelWeilFormula.KK.thA_k R) (_root_.PositivityTheory.SiegelWeilFormula.KK.thB_k d R.ε) u u') (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e u') Φ) X = Complex.I * d.T (Box.D (d.dd.e u) Φ) X := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_vac_k R g hΦ hT hu' X, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_vac_k R g hΦ hT hu X, ← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hfi : (R.fr w).1 * ((R.fr w)⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Sw_rel e2 hfi (_root_.PositivityTheory.SiegelWeilFormula.KK.frame_form_k R w) (R.hfr w) R.hζ (d.cw w X) (d.cw w u) (d.cw w u') (hr w)
end PositivityTheory.SiegelWeilFormula.KK
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
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem chi_adrU_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (τ : ℝ) :
    haveI := d.cm.1
    (d.χ (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : ℂ) = 1 := by
  haveI := d.cm.1
  haveI : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : StrongRankCondition (AF F) := commRing_strongRankCondition _
  have hfr : Module.finrank (AF F) (AE F E) = 2 := by
    rw [Module.finrank_baseChange]; exact d.cm.2.2.1
  have hmem : adrU w τ ∈ (Units.map (Algebra.norm (AF F) : AE F E →* AF F)).range := by
    refine ⟨Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w (τ / 2)), Units.ext ?_⟩
    show Algebra.norm (AF F) (algebraMap (AF F) (AE F E) (adr w (Real.exp (τ / 2)))) = adr w (Real.exp τ)
    rw [Algebra.norm_algebraMap, hfr, sq, adr_mul, ← Real.exp_add, add_halves]
  have := d.ok.res (adrU w τ)
  rw [if_pos (Subgroup.mem_sup_right hmem)] at this
  exact this
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def phz_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (f : d.G → ℂ) (s₁ z : ℂ) (x : d.G) : ℂ := ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x
abbrev Cs_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y)
def rep_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) : d.G := ((Quot.out q : rat2 σ d.Y) : d.G)
def FirstOrbit {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (γ : d.G) : Prop := ∀ i, inFrame d.b γ (Sum.inr i) (Sum.inl L.i₀) = 0
def kq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (T : nF σ d.Y d.b)
    (uM : (Fin L.n → AE F E) → d.G) (γ x : d.G) (p : (Fin L.n → AE F E) × nA σ d.Y d.b) : ℂ :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (γ * (nb p.2 * (uM p.1 * x))) *
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * p.2.1))))
def tm_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (γ x : d.G) : ℂ :=
  ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (fun g => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (γ * g)) T (uM u * x) ∂ν
def secondOrbitSection {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (x : d.G) : ℂ :=
  ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x
def first_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb' : nA σ L.Y L.b → G2 σ L.Y) (lam' : Measure (nA σ L.Y L.b))
    (𝓖' : Set (nA σ L.Y L.b)) (T' : nF σ L.Y L.b) (x : d.G) : ℂ :=
  fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
    ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1
end PositivityTheory.SiegelWeilFormula.Act
end
end
end
