module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle538
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle573
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AutConjTranslatesDetCharacterMarkings
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section




namespace GlobalTheory.HeisRatRead

open GlobalTheory.FinTranslate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7}

theorem ratW_sub_realPt_inf (S T : HSp D) (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ).map (infPart D) = 0 := by
  ext i j
  change infPart D (incA D (ℓ i j) - pairA D.host.F 1 0 ⊗ₜ[D.host.F] ℓ i j) = 0
  rw [map_sub]
  change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ ℓ i j) -
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 1 0 ⊗ₜ ℓ i j) = 0
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one]
  exact sub_eq_zero.2 rfl

theorem realPt_sub (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T (X - Y) = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T Y := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt, Matrix.of_apply, Matrix.sub_apply, TensorProduct.tmul_sub]

theorem actO_inf (S T : HSp D) (h : GA D T) {w : WO S T} (hw : w.map (infPart D) = 0) :
    (actO S T 1 h w).map (infPart D) = 0 := by
  have hw' : ∀ k l, infPart D (w k l) = 0 := fun k l => congrFun (congrFun hw k) l
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold actO

  simp only [Matrix.mul_apply, map_sum, map_mul, hw', mul_zero, zero_mul, Finset.sum_const_zero]

theorem actO_add (S T : HSp D) (h : GA D T) (u v : WO S T) :
    actO S T 1 h (u + v) = actO S T 1 h u + actO S T 1 h v := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

end GlobalTheory.HeisRatRead

namespace GlobalTheory.HeisRatRead

open GlobalTheory.FinTranslate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem heis_translate_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∀ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
    w.map (infPart D) = 0 → heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i →
    x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w →
    ∀ X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      R.ωP i A.μ0 (1, g) (heisO R.ψ (Vc D i) (Wc D i) x (R.vacP i)) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
        R.ψ (-(symplOH (Vc D i) (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) +
            symplOH (Vc D i) (Wc D i) (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (actO (Vc D i) (Wc D i) 1 g w))) *
          R.ωP i A.μ0 (1, g) (R.vacP i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) := by
  intro D G _ _ Pl0 T0 A T _ R hL hF hT i g x hx ℓ w hw hρw hxe X
  have hW := hT.ωP i A.μ0
  have hv := hT.vP i A.μ0
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hv.1.2.theta
  set F := R.ωP i A.μ0 (1, g) (R.vacP i) with hFdef
  have hFθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) F := hW.om_pres _ _ hf
  set lf := ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ with hlf
  have hlf0 : lf.map (infPart D) = 0 := ratW_sub_realPt_inf (Vc D i) (Wc D i) ℓ
  set gw := actO (Vc D i) (Wc D i) 1 g w with hgw
  have hgw0 : gw.map (infPart D) = 0 := actO_inf (Vc D i) (Wc D i) g hw
  have hgx : actO (Vc D i) (Wc D i) 1 g x = lf + gw := by
    rw [hxe, actO_add, ← GlobalTheory.HeckeVacuum.act_mul, mul_inv_cancel, GlobalTheory.HeckeVacuum.act_one]
  have hFw : heisO R.ψ (Vc D i) (Wc D i) gw F = F := by
    have := hW.om_heis 1 g w (R.vacP i) hf
    rw [hρw] at this
    exact this.symm
  set P := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X
  set z := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)
  have hP0 : P.map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) X
  have hz0 : z.map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) (X - ℓ)
  have hl0 : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ).map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) ℓ
  have hzF : F (z + gw) = F z := by
    have := congrFun hFw z
    simp only [heisO, symplOH_real_fin hgw0 hz0, AddChar.map_zero_eq_one, one_mul] at this
    exact this
  have hpt : P + (lf + gw) = ratW (Wc D i) (Vc D i) ℓ + (z + gw) := by
    simp only [z, P, hlf, realPt_sub]
    abel
  have hratW : ratW (Wc D i) (Vc D i) ℓ = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ + lf := by
    rw [hlf]; abel
  rw [hW.om_heis 1 g x (R.vacP i) hf, ← hFdef]
  show R.ψ (symplOH (Vc D i) (Wc D i) P (actO (Vc D i) (Wc D i) 1 g x)) * F (P + actO (Vc D i) (Wc D i) 1 g x) = _
  rw [hgx, hpt, hFθ.quasi, hzF, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  rw [hratW, symplOH_add_right, symplOH_add_left, symplOH_add_right, symplOH_add_right,
    symplOH_real_fin hlf0 hP0, symplOH_real_fin hgw0 hP0, symplOH_real_fin hgw0 hl0, symplOH_fin_real hlf0 hz0]
  ring

end GlobalTheory.HeisRatRead
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.FockConjNeg

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem dRho_cj_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (S T : HSp D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO (GlobalTheory.Grid.neg S) T → ℂ) :
    dRho (heisO ψ S T) θ τ z (cj id g) = cj id (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ z g) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id g) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) g x) 0)
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id g) x) =
      fun t => star (heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) g x) := by
    funext t
    rw [GlobalTheory.CjNeg.heis_negS' hψ]
    rfl
  rw [e, deriv.star]
  rfl

theorem cplxO_neg_left {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ)
    (u : Matrix (Fin m) (Fin n) ℂ) : cplxO (-sS) sT u = -cplxO sS sT u := by
  simp [cplxO, Matrix.mul_neg, smul_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem aPlus_cj_neg {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {g : WO (GlobalTheory.Grid.neg S) T → ℂ} (hg : IsThetaFunO ψ (GlobalTheory.Grid.neg S) T g) (τ : D.what₂.Tau)
    (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    cj id (aPlus (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ (cplxO (-sS) sT) u g) =
      aPlus (heisO ψ S T) θ τ (cplxO sS sT) u (cj id g) := by
  have hn := GlobalTheory.FockAdjoint.dRho_neg' hψ hθ hg τ (cplxO sS sT u)
  unfold aPlus crea
  rw [cplxO_neg_left, hn, dRho_cj_neg hψ, dRho_cj_neg hψ]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, map_mul, map_sub, map_neg,
    map_inv₀, Complex.conj_ofReal, Complex.conj_I]
  ring

end GlobalTheory.FockConjNeg

namespace GlobalTheory.FockConjNeg

variable {D : D7}

theorem fock_true_eq_ptF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (P : GlobalTheory.Grid.Pol S T) :
    GlobalTheory.Grid.fock ψ θ true S T f P = ptF ψ θ (frSgn true (Fr.ofModel S.M)) (Fr.ofModel T.M) f P := by
  have hc : (frSgn true (Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS true S :=
    funext fun τ => cart_frSgn true (Fr.ofModel S.M) τ
  unfold ptF
  rw [hc]
  rfl

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem cj_ptF_neg {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {V W : HSp D} (A : Fr V) (B : Fr W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ (GlobalTheory.Grid.neg V) W f)
    (P : PolF D W.rank V.rank) :
    cj id (ptF ψ θ (frSgn true A) B f P) = ptF ψ θ A B (cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  have hcf : IsThetaFunO ψ V W (cj id f) := GlobalTheory.CjNeg.theta_negS' hψ hf
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, ← mul_one (MvPolynomial.C a), ← mul_one (MvPolynomial.C (starRingEnd ℂ a)),
      GlobalTheory.FockAdjoint.ptF_C, GlobalTheory.FockAdjoint.ptF_one, GlobalTheory.FockAdjoint.ptF_C, GlobalTheory.FockAdjoint.ptF_one]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  | add p q hp hq =>
    rw [map_add (f := _), GlobalTheory.FockAdjoint.ptF_add, GlobalTheory.FockAdjoint.ptF_add, ← hp, ← hq]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  | mul_X p v hp =>
    rw [map_mul, MvPolynomial.map_X, mul_comm, GlobalTheory.FockAdjoint.ptF_X_mul hψ hθ (frSgn true A) B hf, mul_comm,
      GlobalTheory.FockAdjoint.ptF_X_mul hψ hθ A B hcf, ← hp, cart_frSgn]
    exact aPlus_cj_neg hψ hθ (GlobalTheory.FockAdjoint.ptF_theta hψ hθ (frSgn true A) B hf p) v.1 _ _ _

theorem fock_neg_cj : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f → ∀ P : GlobalTheory.Grid.Pol S T, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.Grid.fock ψ θ true S T f P) = GlobalTheory.Chain.ptOf ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  intro D S T ψ θ f hψ hθ hf P
  rw [fock_true_eq_ptF, cj_ptF_neg hψ hθ _ _ hf]
  rfl

end GlobalTheory.FockConjNeg
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

private theorem selfDual_full {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

private theorem det_int {D : D7} {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsFullLattice D.host.E L) (g : GA D V)
    (h : ∀ y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)),
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E))) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hL.toIsLattice.fg hL.span_eq_top h

private theorem unram_detAt {D : D7} {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsFullLattice D.host.E L) {g : GA D V}
    (h : ∀ y, y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)))
    {e : AE D} (he : e * e = e) {ε : AF D.host.F} (hs : algebraMap (AF D.host.F) (AE D) ε * e = e)
    {χ : (AE D)ˣ →* Circle} (hχ : GlobalTheory.WeilParts.UnramAt ε χ) : χ (GlobalTheory.VecInv.detAt e he V g) = 1 := by
  refine hχ _ ?_ (GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g fun y hy => (h y).1 hy)) ?_
  · change _ * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
    linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * hs
  · rw [← MonoidHom.map_inv]
    exact GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g⁻¹ (GlobalTheory.LocalLatStab.inv_keeps V _ g h))


theorem splitVacuumFixed : ∀ D : D7, SplitVacuumFixed D := by
  intro D ψ S T χS χT om ΛS ΛT hW hS hT v hv uS uT f hf hvac k hk k' hk'
  obtain ⟨e, he, hb⟩ := hv
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hb' : e + cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := hb
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have s1 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * e = e := by
    rw [← hb']; linear_combination he.1 + he.2.1
  have s2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * cA D e = cA D e := by
    rw [← hb']; linear_combination he'.1 + he.2.1
  have sk := suppPl_emb S v k
  have sk' := suppPl_emb T v k'
  have kS := emb_keeps_latHat S hS.1.fg v hk
  have kT := emb_keeps_latHat T hT.1.fg v hk'
  have key := GlobalTheory.VacStabFixed.om_split_halves hW hS hT he (fun i j => by rw [hb']; exact sk i j)
    (fun i j => by rw [hb']; exact sk' i j)
    (fun u hu => ⟨GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (fun y hy => (kS y).1 hy) (fun y hy => (kT y).1 hy) u hu,
      GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (GlobalTheory.LocalLatStab.inv_keeps S _ _ kS)
        (GlobalTheory.LocalLatStab.inv_keeps T _ _ kT) u hu⟩)
    (GlobalTheory.VecInv.isDetAt_detAt e he.1 S _) (GlobalTheory.VecInv.isDetAt_detAt e he.1 T _) hf
    (fun u hu hh => hvac.2 e he u (GlobalTheory.VacStabFixed.half_mem_place hε s1 hu hh) hh)
    (fun u hu hh => hvac.2 _ he' u (GlobalTheory.VacStabFixed.half_mem_place hε s2 hu hh) hh)
  rwa [splitFacO, unram_detAt (selfDual_full S ΛS hS) kS he.1 s1 uT, unram_detAt (selfDual_full T ΛT hT) kT he.1 s1 uS,
    inv_one, mul_one, Circle.coe_one, one_smul] at key

end GlobalTheory.PlaceTensor

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ModulUnit

open GlobalTheory.ChiGrid

theorem exists_int_mem_modul {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ P.S0) : ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
  have hne : ∀ v' ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal := by
    intro v' hv'
    by_contra hc
    push_neg at hc
    have hle : v'.asIdeal ≤ v.asIdeal := fun t ht => hc t ht
    have heq : v'.asIdeal = v.asIdeal := v'.isMaximal.eq_of_le v.isPrime.ne_top hle
    have : v' = v := HeightOneSpectrum.ext heq
    exact hv (this ▸ hv')
  choose! f hf using hne
  refine ⟨∏ v' ∈ P.S0, f v' ^ P.depth sc v', ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨v', hv', h⟩
    exact (hf v' hv').2 (v.isPrime.mem_of_pow_mem _ h)
  · rw [map_prod, Places.modul]
    refine Ideal.prod_mem_prod fun v' hv' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have e : ((P.w v').under (𝓞 D.host.F)).asIdeal = v'.asIdeal := by rw [P.under_w hv']
    have h1 : f v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := e ▸ (hf v' hv').1
    exact h1

end GlobalTheory.ModulUnit

theorem GlobalTheory.ModulUnit.idV_modul_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v := by
  intro D T L P sc v hv
  obtain ⟨t, ht, htm⟩ := GlobalTheory.ModulUnit.exists_int_mem_modul P sc v hv
  apply le_antisymm
  · exact GlobalTheory.SeeSaw.idV_mono FractionalIdeal.coeIdeal_le_one v
  · rw [GlobalTheory.SeeSaw.idV, AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hαv, a, ha, rfl⟩
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [GlobalTheory.IdVGen.tmul_eq ht α]
    obtain ⟨h1, h2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht hα hαv
    refine AddSubgroup.subset_closure ⟨_, h1, h2, _, ?_, rfl⟩
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t * o, Ideal.mul_mem_right _ _ htm, by rw [map_mul]; rfl⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem vec_isThetaFunO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (S.Z.vec d) := by
  intro D T L sc G W U S t p hp d hd
  have hIn : p.InRange D.R.m := by
    have hn := hp.nodes
    cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega
  exact GlobalTheory.LastVertexInv.vec_theta S hp hIn d hd

end GlobalTheory.TopZeroInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.polarisationTwist_lattice_selfDual_same_stabilisers : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ i : ℕ, IsSelfDualC V (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) ∧ (∀ v, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) ∧ ∀ 𝔪 : Ideal (𝓞 D.host.E), congLev D.sp.cm V.gram (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) 𝔪 = congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual | exact GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual | (intros; apply GlobalTheory.ScaleSelfDual.scaleLat_twist_selfDual <;> assumption)
end
