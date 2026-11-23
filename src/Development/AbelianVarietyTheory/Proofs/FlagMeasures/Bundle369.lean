module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle287
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle361
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle154
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle144
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle122
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle133
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle350
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicFrameVectorPrimitiveInInnerLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle352
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle353
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.FixedConjMat

theorem fmat_iota (D : D7) (x : Formalism.L2.Theta.GA D (D.sp.Y 0)) :
    (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D x).2) =
      (Formalism.IndefR.Lev.finE (D.sp.Y 0) x).1 := by
  have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D x)).2
  have e : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D x) = x :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply x
  rw [hb]
  erw [e]
  ext i j
  exact GlobalTheory.RedFrame.tauF_gen (Formalism.IndefR.RationalEmbedding.inst D) _

theorem finE_val_eq (D : D7) (V : HSp D) (g : Formalism.L2.Theta.GA D V) :
    (Formalism.IndefR.Lev.finE V g).1 = (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).map (Formalism.IndefR.Lev.swapAE D) := rfl

theorem map_cast_swap (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) {m n : Type}
    (M : Matrix m n (ReciprocityTheory.Aut.AL D.host.E)) :
    (M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm).map (Formalism.IndefR.Lev.swapAE D) =
      M.map (GlobalTheory.FixedConj.adeleEquiv D hF) := by
  ext i j
  rfl

theorem map_mul_eq_one {k l R S : Type} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [CommRing R]
    [CommRing S] (f : R →+* S) {A : Matrix k l R} {B : Matrix l k R} (h : A * B = 1) :
    A.map f * B.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

theorem conj_map {k l R S : Type} [Fintype k] [Fintype l] [CommRing R] [CommRing S] (f : R →+* S)
    (T : Matrix k k S) (Ti : Matrix k k S) (B : Matrix k l R) (Y : Matrix l l R) (B' : Matrix l k R)
    (g : Matrix l l S) (hg : Y.map f = g) :
    T * (B * Y * B').map f * Ti = T * B.map f * g * (B'.map f * Ti) := by
  rw [Matrix.map_mul, Matrix.map_mul, hg]
  simp only [Matrix.mul_assoc]



theorem finE_conj_stdPsi (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r)
    (t : Formalism.L2.Theta.GA D (Yc D 0)) (hP : StdPsi hF PY) :
    ∃ (U : Matrix (Fin (Yc D 0).rank) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D))
      (U' : Matrix (Fin D.R.r) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧
      ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.IndefR.Lev.finE (Yc D 0) (MulAut.conj t (PY.ψ y))).1 =
        HMul.hMul (HMul.hMul U (((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r)
          (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF))) U' := by
  obtain ⟨⟨β, β', h1, h2, hβ⟩, -⟩ := hP
  have hbb := map_mul_eq_one (Formalism.IndefR.Lev.swapAE D) h1
  have hbb' := map_mul_eq_one (Formalism.IndefR.Lev.swapAE D) h2
  refine ⟨HMul.hMul (Formalism.IndefR.Lev.finE (Yc D 0) t).1 (β.map (Formalism.IndefR.Lev.swapAE D)),
    HMul.hMul (β'.map (Formalism.IndefR.Lev.swapAE D)) ((Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹).1, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β.map _), hbb, Matrix.one_mul, Units.mul_inv]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹).1), Units.inv_mul,
      Matrix.one_mul, hbb']
  · intro y
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
    have e1 := finE_val_eq D (Yc D 0) (PY.ψ y)
    have e3 := e1.trans (congrArg (fun M => M.map (Formalism.IndefR.Lev.swapAE D)) (hβ y))
    rw [e3]
    exact conj_map _ _ _ _ _ _ _ (map_cast_swap D hF _)

theorem fmat_iota_conj_stdPsi : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)), StdPsi hF PY → ∃ (U : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) (U' : Matrix (Fin D.R.r) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧ ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ y))).2) = U * ((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF) * U' := by
  intro D hF PY t hP
  obtain ⟨U, U', h1, h2, h3⟩ := finE_conj_stdPsi D hF PY t hP
  exact ⟨U, U', h1, h2, fun y => (fmat_iota D _).trans (h3 y)⟩

end GlobalTheory.FixedConjMat
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabFix

theorem mem_VT_of_sum_fixed : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf), IsRedHom X red → IsSec X red sec → ∀ (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) → ∀ f ∈ HHX X, ∑ᶠ γ, serCoef t γ • X.B.R ((1, sec γ) : X.B.I.GA) f = f → f ∈ VT X t := by
  intro D X red sec hred hsec t ht f hf hsum
  classical
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  let ρ : GlobalTheory.RowLev.Red X.B.I X.B.g (G0g D.nd) :=
    { toFun := red, map_mul := hred.2.1, ker := hred.2.2.2, surj := hred.2.2.1 }
  obtain ⟨hcoef, hcent⟩ := GlobalTheory.LabIdem.ES_single_coeff_central D t ht
  have hegA : egA X (ES {t}) = ρ.lift X.B.μf (ES {t}) := by
    funext x
    rw [egA]
    split_ifs with hx
    · rw [GlobalTheory.RowLev.Red.lift_of_mem ρ _ _ hx.1]
      congr 1
      exact GlobalTheory.coeff_goodAt_eq D X (ES {t}) hcent x (red x) (Classical.choose hx.2)
        (hred.1 x hx.1) (Classical.choose_spec hx.2)
    · have hnot : x ∉ X.B.I.Kset := fun h => hx ⟨h, red x, hred.1 x h⟩
      rw [GlobalTheory.RowLev.Red.lift_of_notMem ρ _ _ hnot]
  obtain ⟨h1R, hm, hn, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  obtain ⟨huniq, -, -, hprod, -⟩ := GlobalTheory.WeakConv.rightConv_unique_add_smul_mul_comm X.B.I X.B.μf X.B.fund X.B.R
    X.B.fund_spec X.B.R_spec
  obtain ⟨hQ, -, -, -, -, hinfl, -, -, -⟩ := GlobalTheory.InflBasic.inflation_basic X.B.I X.B.g (G0g D.nd) ρ X.B.μf hg
  letI : Fintype (G0g D.nd) := Fintype.ofFinite _
  obtain ⟨hlint, hlloc, -⟩ := hinfl (ES {t})
  obtain ⟨Ta, hTa⟩ := (GlobalTheory.AutInst_exists_isRConvF_and_isRConv X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R
    X.B.R_spec).1 _ hlint
  have he := X.B.e_adm
  have hecont : Continuous X.B.e := he.1.continuous
  have hReRe : X.B.Re.comp X.B.Re = X.B.Re := by
    have h := hprod _ _ _ _ hecont hecont X.B.Re_spec X.B.Re_spec
    rw [he.2.1] at h
    exact huniq _ _ _ h X.B.Re_spec
  have hRT : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X {t}) (X.B.Re.comp Ta) := by
    unfold eT
    rw [hegA]
    exact hprod _ _ _ _ hecont hlloc.continuous X.B.Re_spec hTa
  have hReT : ReT X {t} = X.B.Re.comp Ta := by
    have hex : ∃ T, X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X {t}) T := ⟨_, hRT⟩
    unfold ReT
    rw [dite_eq_left hex]
    exact huniq _ _ _ (Classical.choose_spec hex) hRT
  obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hf
  have hRef : X.B.Re f = f := by
    rw [← hz]
    show X.B.Re (X.B.Re (X.Rph z)) = X.B.Re (X.Rph z)
    rw [← ContinuousLinearMap.comp_apply X.B.Re X.B.Re, hReRe]
  have p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1 := h1R
  have pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b) := by
    intro a b
    rw [ContinuousLinearMap.mul_def, ← hm]
    simp
  have pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖ := fun g v => hn _ v
  have hone : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
    refine ⟨(Formalism.UG.stabGL X.B.I.Lf).one_mem, fun y _ => ⟨0, X.B.I.Lf.zero_mem, ?_⟩⟩
    have : X.B.I.fmat 1 = 1 := rfl
    simp [this]
  haveI : SecondCountableTopology X.B.I.Gf := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints X.B.I
  have hfix : ∀ k ∈ X.B.I.Kg X.B.g, X.B.R (1, k) f = f := by
    intro k hk
    have h := GlobalTheory.IdemProj.op_fixed X.B.μf (fun g => X.B.R (1, g)) p1 pm pn X.B.e X.B.Re X.B.Re_spec.2 k
      (fun x => by simpa using he.2.2.2.2.2.1 x k hk 1 hone)
    rw [← hRef, ← ContinuousLinearMap.comp_apply]
    exact DFunLike.congr_fun h f
  have hTaf : Ta f = f := by
    apply ext_inner_left ℂ
    intro v
    rw [hTa.2, GlobalTheory.LevelIdem.integral_lift ρ X.B.μf hg (ES {t}) sec hsec (fun x => ⟪v, X.B.R (1, x) f⟫_ℂ) ?_]
    · conv_rhs => rw [← hsum]
      rw [finsum_eq_sum_of_fintype, inner_sum]
      simp only [inner_smul_right, hcoef]
    · intro x k hk
      show ⟪v, X.B.R (1, x * k) f⟫_ℂ = ⟪v, X.B.R (1, x) f⟫_ℂ
      rw [show ((1 : X.B.I.Ginf), x * k) = ((1, x) : X.B.I.GA) * (1, k) by simp, hm,
        ContinuousLinearMap.comp_apply, hfix k hk]
  refine Submodule.mem_inf.2 ⟨hf, ?_⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  show ReT X {t} f = f
  rw [hReT, ContinuousLinearMap.comp_apply, hTaf, hRef]

end GlobalTheory.LabFix
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthogonal_hyperbolicFrame_anisotropic_mem_span_transported : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → (VS D).hT (X.zu u) y = 0 → ∃ d : Fin (D.R.N 0) → D.host.E, Fintype.linearCombination D.host.E (qFr wt) d = y := by
  first | exact @GlobalTheory.St.orth_mem_span_qFr | exact GlobalTheory.St.orth_mem_span_qFr | (intros; apply GlobalTheory.St.orth_mem_span_qFr <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.St

theorem col_mul_eq_mulVec {A : Type} [CommRing A] {n ι κ : Type} [Fintype n] [Fintype ι]
    (M : Matrix n ι A) (B : Matrix ι κ A) (c : κ) :
    M *ᵥ (fun i => B i c) = fun i => (M * B) i c := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem rational_unitary_extend_by_identity : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  intro D X u wt hw y₀ hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hz, hG', hblk⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hw
  have hU := (GlobalTheory.unitary_stabiliser_orthogonal_summand X.B.I.E (starRingEnd X.B.I.E) _ _ _ X.B.I.J
    ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) G' Q Qi hQQi hQiQ hblk hG').1 y₀ hy
  set M := Q * Matrix.fromBlocks y₀ 0 0 (1 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E) * Qi with hM
  have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.2 X.B.I.J_det
  have hdet : IsUnit M.det := by
    refine Matrix.isUnit_det_of_left_inverse (B := X.B.I.J⁻¹ * ((M.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J)) ?_
    rw [Matrix.mul_assoc, hU, Matrix.nonsing_inv_mul _ hJu]
  have hMu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hdet
  have hMQ : M * Q = Q * Matrix.fromBlocks y₀ 0 0 1 := by
    rw [hM, Matrix.mul_assoc, hQiQ, Matrix.mul_one]
    rfl
  refine ⟨hMu.unit, ?_, ?_, ?_⟩
  · show Formalism.UG.cT (starRingEnd X.B.I.E) (hMu.unit : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J * (hMu.unit : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J
    rw [IsUnit.unit_spec]
    exact hU
  · intro x hx
    rw [IsUnit.unit_spec]
    have key : ∀ b, M *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b) := by
      intro b
      rw [col_mul_eq_mulVec, hMQ]
      funext i
      erw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz'
    · have := key (Sum.inl a)
      have e : (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := funext fun i => he a i
      rwa [e] at this
    · have := key (Sum.inr (Sum.inl a))
      have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := funext fun i => hf a i
      rwa [e] at this
    · rw [Set.mem_singleton_iff] at hz'
      subst hz'
      have := key (Sum.inr (Sum.inr ()))
      have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext fun i => hz i
      rwa [e] at this
  · intro j
    rw [IsUnit.unit_spec]
    have e : ∀ j, X.crd (qFr wt j) = fun i => Q i (Sum.inl j) := fun j => funext fun i => (hq j i).symm
    rw [e j, col_mul_eq_mulVec, hMQ]
    funext r
    simp only [e, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    erw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.St
end
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St



theorem unitary_fix_acts_on_complement_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  intro D X u wt hw γ₀ hγ hfix
  obtain ⟨Q, Qi, G', h1, h2, hq, he, hf, hz, hG', hD⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hw
  have hU : ((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (starRingEnd X.B.I.E))ᵀ * X.B.I.J *
      (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hγ
  have hcol : ∀ b, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ (fun i => Q i (Sum.inr b)) =
      fun i => Q i (Sum.inr b) := by
    intro b
    rcases b with a | a | ⟨⟩
    · have e : (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := funext (he a)
      rw [e]; exact hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
    · have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := funext (hf a)
      rw [e]; exact hfix _ (Or.inl (Or.inr ⟨a, rfl⟩))
    · have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext hz
      rw [e]; exact hfix _ (Or.inr rfl)
  obtain ⟨y, hy, hγQ⟩ := (GlobalTheory.unitary_stabiliser_orthogonal_summand X.B.I.E (starRingEnd X.B.I.E) _ _ _
    X.B.I.J _ G' Q Qi h1 h2 hD hG').2 _ hU hcol
  refine ⟨y, hy, fun j => ?_⟩
  have hQ : (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Q = Q * (Matrix.fromBlocks y (0 : Matrix (Fin (D.R.N 0)) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E) (0 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin (D.R.N 0)) X.B.I.E) (1 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E)) := by
    rw [hγQ, Matrix.mul_assoc _ Qi Q, h2, Matrix.mul_one]
  funext i
  have e := congrFun (congrFun hQ i) (Sum.inl j)
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type] at e
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
    Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hq] at e
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [e]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.St
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.St



theorem sTil_eq_atInf_of_rational : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ (s : X.B.I.Ginf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), (∀ v, uMat (s v) = (X.B.I.P v)⁻¹ * γ₀.map (X.B.I.φ v) * X.B.I.P v) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → sTil X wt s = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) := by
  intro D X u wt hW s γ₀ y₀ hs hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hQq, -, -, -, hG', hblk⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW
  funext τ
  set v := X.pl.symm τ with hv
  set φ := X.B.I.φ v with hφ
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hGdef

  have hgram : gramQ X wt v = G.map φ := by
    ext a b
    have h1 := congrFun (congrFun hblk (Sum.inl a)) (Sum.inl b)
    rw [Matrix.fromBlocks_apply₁₁] at h1
    rw [Matrix.map_apply, ← h1]
    simp only [gramQ, Matrix.of_apply, rvV]
    have := PI.ScPiFrameW.hJ_rv X.B.I v (X.crd (qFr wt a)) (X.crd (qFr wt b))
    refine this.trans ?_
    congr 1
    simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hQq, Finset.sum_mul]
    rw [Finset.sum_comm]

  have hdetG : G.det ≠ 0 := by
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.mpr X.B.I.J_det
    have hJinv : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJu
    have hR : Matrix.fromBlocks G 0 0 G' *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      rw [← hblk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J, hJinv, Matrix.one_mul,
        ← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hd := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fromBlocks_zero₂₁] at hd
    exact left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hd)
  have hdetQ : IsUnit (gramQ X wt v).det := by
    have hm : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
    rw [hgram, hm, isUnit_iff_ne_zero, map_ne_zero]; exact hdetG

  have hvec : ∀ x, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v (γ₀ *ᵥ x) := by
    intro x
    have hu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)
    have hinv : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    rw [hs v]
    simp only [rv]
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ (X.B.I.P v), hinv, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext k

    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, φ]
  have hlin : ∀ b, rv X.B.I v (γ₀ *ᵥ X.crd (qFr wt b)) = ∑ i, φ (y₀ i b) • rvV X v (qFr wt i) := by
    intro b
    rw [hy b]
    simp only [rvV, rv]
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext k

    simp [Finset.sum_apply, map_sum, map_mul, φ]
  have hM : (Matrix.of fun a b => hJ (X.B.I.ε v) (rvV X v (qFr wt a))
      (uMat (s v) *ᵥ rvV X v (qFr wt b))) = gramQ X wt v * y₀.map φ := by
    ext a b
    rw [Matrix.of_apply, show rvV X v (qFr wt b) = rv X.B.I v (X.crd (qFr wt b)) from rfl, hvec, hlin,
      Matrix.mul_apply]
    simp only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, gramQ,
      Matrix.of_apply, Matrix.map_apply, smul_eq_mul, rvV]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hfin : y₀.map φ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) τ := by
    ext a b
    simp only [Formalism.L2.Forms.atInf, Matrix.map_apply, φ, X.φ_eq, hv, Equiv.apply_symm_apply]
    rfl
  show (gramQ X wt v)⁻¹ * _ = _
  rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetQ, Matrix.one_mul, hfin]

end GlobalTheory.St
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.anisotropicFrameVector_primitive_in_innerLattice : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∀ c : D.host.E, c • G.fl.z ∈ Lsub Λ G → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  first | exact @GlobalTheory.FramePrim.coef_integral | exact GlobalTheory.FramePrim.coef_integral | (intros; apply GlobalTheory.FramePrim.coef_integral <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_isometriesFixingBothFrames_stabilizing_lattice : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  first | exact @GlobalTheory.StabFin.stab_finite | exact GlobalTheory.StabFin.stab_finite | (intros; apply GlobalTheory.StabFin.stab_finite <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fixedFlag_frameVector_mem_rowLattice : ∀ (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D), IsRowLat D F0 Λ → ∀ a, frame (lf D F0) a ∈ Λ := by
  first | exact @GlobalTheory.Unfold.RowFrame.frame_mem | exact GlobalTheory.Unfold.RowFrame.frame_mem | (intros; apply GlobalTheory.Unfold.RowFrame.frame_mem <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.split_and_smul_completedLattice_le_at_level_prime : ∀ (D : D7) (Z : LocDat D) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ sg : Loc.SplitG (Z.M (below D P)).L, (Z.M (below D P)).split = some sg ∧ ∀ (Λ : LV D) (v : Vp D (below D P)), v ∈ (locH Z (below D P)).smulLat (algebraMap (D.s.atP (below D P)).Fp (D.s.atP (below D P)).Ep (sg.q : (D.s.atP (below D P)).Fp)) (lattice₂ D Z.M (below D P) Λ) → v ∈ lattice₂ D Z.M (below D P) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  first | exact @GlobalTheory.LocCong.qsmul_latP_le_gS | exact GlobalTheory.LocCong.qsmul_latP_le_gS | (intros; apply GlobalTheory.LocCong.qsmul_latP_le_gS <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_right_change_moves_flag_complement : ∀ (D : D7) (T' : D.host.E) (F' : LFlag (D.sp.Y 0) D.R.rS T') (γ₁ γ₂ m n' : GV D), γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → n' ∈ NRat F' → γ₂ = m * γ₁ * n' → ∀ x' ∈ orth (VS D) (Xsp (mapLF γ₁ F')), m x' - (γ₂ * γ₁⁻¹) x' ∈ Xsp (mapLF γ₂ F') := by
  first | exact @GlobalTheory.UnipRight.unip_right | exact GlobalTheory.UnipRight.unip_right | (intros; apply GlobalTheory.UnipRight.unip_right <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.baseFrameLattice_invariant_under_adapted_translate : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ s : TauC Y u u') (Λ₀ : LV D) (a a' n n' : GV D), TG F F' t₀ Λ₀ → a ∈ Aut0 (lf D (X.Fu u)) t₀.lam → a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam' → n ∈ NLam t₀.lam (lf D (X.Fu u)) → n' ∈ NLam t₀.lam' (lf D (X.Fu u')) → s.lam = t₀.lam → s.lin = n * (a * t₀.lin * a'⁻¹) * n' → TG F F' s Λ₀ := by
  first | exact @GlobalTheory.Unfold.tg_translate | exact GlobalTheory.Unfold.tg_translate | (intros; apply GlobalTheory.Unfold.tg_translate <;> assumption)
end
