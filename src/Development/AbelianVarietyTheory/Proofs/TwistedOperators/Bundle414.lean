module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDepthPaysEveryLoss
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientDecayKFiniteSecondVector
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle381
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LipschitzBoundRealUnipotentAction
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle384
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gridDepth_pays_every_loss : DepthPays := by
  first | exact @GlobalTheory.SepPer.depth_pays | exact GlobalTheory.SepPer.depth_pays | (intros; apply GlobalTheory.SepPer.depth_pays <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem _root_.GlobalTheory.T.hasDerivAt_levelIndicatorCoefficientTest_oneParam : ∀ (D : D7), GlobalTheory.Published.HarishChandraModules → ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ) (τ : D.what₂.Tau), b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → ∀ X ∈ lieAt V τ, ∀ x : GA D V, HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 := by
  first | exact @GlobalTheory.TermDeriv.hasDerivAt_coef_oneP | exact GlobalTheory.TermDeriv.hasDerivAt_coef_oneP | (intros; apply GlobalTheory.TermDeriv.hasDerivAt_coef_oneP <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coefficientDecay_kFinite_second_vector : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (v : M.H τ) (N : ℕ), v ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → DecayAt M τ v v N → ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, DecayAt M τ v a N := by
  first | exact @GlobalTheory.KFinDecay.decayAt_of_kFin | exact GlobalTheory.KFinDecay.decayAt_of_kFin | (intros; apply GlobalTheory.KFinDecay.decayAt_of_kFin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicPointRationalLattice_unitaryModelIso_eq : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA), latAt fr.Λ (Formalism.IndefR.Eqv.UI.brg fr x) = GlobalTheory.Count.lamX (Formalism.IndefR.Eqv.UI.instV fr) x := by
  first | exact @GlobalTheory.LatDict.latAt_brg | exact GlobalTheory.LatDict.latAt_brg | (intros; apply GlobalTheory.LatDict.latAt_brg <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalVectorNorm_adelicPoint_twoModels_eq : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (w : Fin V.rank → D.host.E), ∏ v, Real.sqrt (∑ i, ‖(Formalism.MainNotions.S.uMat (x.1 v)⁻¹ *ᵥ (((Formalism.IndefR.Eqv.UI.instV fr).P v)⁻¹ *ᵥ fun j => (Formalism.IndefR.Eqv.UI.instV fr).φ v (w j))) i‖ ^ 2) = ∏ τ, nrm θ A (Formalism.IndefR.Eqv.UI.brg fr x) τ w := by
  first | exact @GlobalTheory.NormDict.norm_dict | exact GlobalTheory.NormDict.norm_dict | (intros; apply GlobalTheory.NormDict.norm_dict <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_instanceFrames_of_diagonalFrame_selfDual : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  first | exact @GlobalTheory.frames_of_diagonalising_frame | exact GlobalTheory.frames_of_diagonalising_frame | (intros; apply GlobalTheory.frames_of_diagonalising_frame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lipschitz_bound_real_unipotent_action : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (φ : GA D V → ℂ) (c : ℝ), 0 ≤ c → Lip θ A φ c → ∀ (u : (Formalism.IndefR.Eqv.UI.instV fr).Ginf) (Av Z : InfinitePlace D.host.F → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ v, Formalism.REAL.inG (fr.ε v) (Av v) ∧ Formalism.REAL.inG (fr.ε v) (Z v)) → (∀ v, Formalism.MainNotions.S.uMat (u v) = NormedSpace.exp (Av v) * NormedSpace.exp (Z v)) → ∀ y : GA D V, ‖φ (y * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) - φ y‖ ≤ c * ∑ v, (Real.sqrt (Formalism.REAL.hs (Av v)) + Real.sqrt (Formalism.REAL.hs (Z v))) := by
  first | exact @GlobalTheory.RealMove.lip_move_real | exact GlobalTheory.RealMove.lip_move_real | (intros; apply GlobalTheory.RealMove.lip_move_real <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.unitaryAdelicHeight_wittEmbedding_le_const_mul : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀, height S (d.emb0 g) ≤ C * height S₀ g := by
  first | exact @GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le | exact GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le | (intros; apply GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.SplitVac

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplO_eq_halves (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem heisO_add_fix {f : WO S T → ℂ} {w w' : WO S T} (h : heisO ψ S T w f = f) (h' : heisO ψ S T w' f = f)
    (hc : ψ (symplOH S T w w') = 1) : heisO ψ S T (w + w') f = f := by
  have e := GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) w w' f
  rw [h', h, hc, one_smul] at e
  exact e.symm

theorem psi_four {t : AF D.host.F} (h : ψ (t + t) = 1) : ψ ((t + t) + (t + t)) = 1 := by
  rw [AddChar.map_add_eq_mul, h, one_mul]

theorem psi_symplO_two {x y : WO S T} (h : ψ (symplO S T x y) = 1) : ψ (symplO S T x (2 • y)) = 1 := by
  rw [symplO_eq_halves] at h ⊢
  rw [two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_right]
  exact psi_four h

theorem psi_symplOH_two {x y : WO S T} (h : ψ (symplO S T x y) = 1) : ψ (symplOH S T (2 • x) (2 • y)) = 1 := by
  rw [symplO_eq_halves] at h
  rw [two_nsmul, two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]
  exact psi_four h

variable {m n k : ℕ} {e : AE D}

theorem isHalf_add' {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := fun i j => by
  rw [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_mul_right' {x : Mx D m n} (hx : IsHalf e x) (M : Mx D n k) : IsHalf e (x * M) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hx i]

theorem isHalf_mul_left' (M : Mx D k m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (M * x) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx l j]

theorem symplOH_half (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplOH S T x y = 0 := by
  have h0 : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hx d a, ← hy c b, map_mul]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) * he
  unfold symplOH symplO
  rw [h0, mul_zero, map_zero, mul_zero]

end GlobalTheory.AscFin.SplitVac

namespace GlobalTheory.AscFin.SplitVac

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {dV : HypDec V V₀ ρ} {dW : HypDec W W₀ σ}
  {p : Pieces V₀ W W₀ ρ σ} {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ} {Γ : AddSubgroup (WO V W)} {Φ : WO V W → ℂ}

theorem fix_two (hp : p.Is dV dW x ψ) (hs : Splits dV dW p x y ψ Γ) (hΦ : Φ ∈ cls dV dW p x y ψ) (u : WO V W) (hu : u ∈ Γ) :
    heisO ψ V W (2 • u) Φ = Φ := by
  obtain ⟨hθ, hA1, hA2, hB1, hB2, hvac⟩ := hΦ
  obtain ⟨a, ha, a', ha', ξ, hξ, η, hη, w, hw, rfl, hx', hy'⟩ := hs.comp u hu
  have e1 : 2 • (dV.extX W a + dV.extY W a' + dV.ext0 W (dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w)) =
      dV.extX W (2 • a) + (dV.extY W (2 • a') + (dV.ext0 W (dW.incX V₀ (2 • ξ)) +
        (dV.ext0 W (dW.incY V₀ (2 • η)) + dV.ext0 W (dW.inc0 V₀ (2 • w))))) := by
    simp only [map_nsmul, map_add (f := _), nsmul_add]
    abel
  show heisO ψ V W _ Φ = Φ
  rw [e1]
  have fX : heisO ψ V W (dV.extX W (2 • a)) Φ = Φ := hA1 _ (nsmul_mem ha 2)
  have fY : heisO ψ V W (dV.extY W (2 • a')) Φ = Φ := by
    rw [hA2 _ (nsmul_mem ha' 2), map_nsmul, psi_symplO_two hx', one_smul]
  have fP : heisO ψ V W (dV.ext0 W (dW.incX V₀ (2 • ξ))) Φ = Φ := by
    rw [hB1 _ (nsmul_mem hξ 2), map_nsmul, psi_symplO_two hy', one_smul]
  have fQ : heisO ψ V W (dV.ext0 W (dW.incY V₀ (2 • η))) Φ = Φ := hB2 _ (nsmul_mem hη 2)
  have fR : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ (2 • w))) Φ = Φ := by
    have h := hvac.1 _ (AddSubgroup.mem_map_of_mem ((dV.ext0 W).comp (dW.inc0 V₀)) hw)
    rw [AddMonoidHom.comp_apply, ← map_nsmul, ← map_nsmul] at h
    exact h
  have cAB : ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1 := (hp.dualA a (hp.a₁.fin a ha)).1 ha a' ha'
  have cXY : ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1 := (hp.dualB ξ (hp.b₁.fin ξ hξ)).1 hξ η hη
  refine heisO_add_fix fX (heisO_add_fix fY (heisO_add_fix fP (heisO_add_fix fQ fR ?_) ?_) ?_) ?_
  · rw [HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic, HypDec.wittDecomp_sympl_inclDual_inclAnisotropic, AddChar.map_zero_eq_one]
  · rw [GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic, HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic,
      HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, add_zero, map_nsmul, map_nsmul]
    exact psi_symplOH_two cXY
  · simp only [GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.wittDecomp_sympl_extDual_extAnisotropic, add_zero, AddChar.map_zero_eq_one]
  · rw [GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
      HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, add_zero, add_zero, add_zero,
      map_nsmul, map_nsmul]
    exact psi_symplOH_two cAB

theorem fix_half (hs : Splits dV dW p x y ψ Γ) (hΦ : Φ ∈ cls dV dW p x y ψ) (e : AE D) (he : IsSplitIdem D e) (u : WO V W)
    (hu : u ∈ Γ) (hh : IsHalf e u) : heisO ψ V W u Φ = Φ := by
  obtain ⟨hθ, hA1, hA2, hB1, hB2, hvac⟩ := hΦ
  obtain ⟨a, ha, a', ha', ξ, hξ, η, hη, w, hw, rfl, hx', hy'⟩ := hs.comp u hu
  have he0 : e * cA D e = 0 := he.2.1
  have e1 : dV.extX W a + dV.extY W a' + dV.ext0 W (dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w) =
      dV.extX W a + (dV.extY W a' + (dV.ext0 W (dW.incX V₀ ξ) +
      (dV.ext0 W (dW.incY V₀ η) + dV.ext0 W (dW.inc0 V₀ w)))) := by
    rw [map_add (f := _), map_add (f := _)]
    abel
  obtain ⟨z, hz⟩ : ∃ z, dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w = z := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, dV.extX W a + dV.extY W a' + dV.ext0 W z = U := ⟨_, rfl⟩
  rw [hz, hU] at hh
  have hUa : U * dV.jX = a := by
    rw [← hU]
    simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc,
      HypDec.pX_jX, HypDec.pY_jX, HypDec.p0_jX, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hUa' : U * dV.jY = a' := by
    rw [← hU]
    simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc,
      HypDec.pX_jY, HypDec.pY_jY, HypDec.p0_jY, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
  have hUz : U * dV.j0 = z := by
    rw [← hU]
    simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc,
      HypDec.pX_j0, HypDec.pY_j0, HypDec.p0_j0, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
  have hzξ : dW.pX * z = ξ := by
    rw [← hz]
    simp only [HypDec.incX_apply, HypDec.incY_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc,
      HypDec.pX_jX, HypDec.pX_jY, HypDec.pX_j0, Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hzη : dW.pY * z = η := by
    rw [← hz]
    simp only [HypDec.incX_apply, HypDec.incY_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc,
      HypDec.pY_jX, HypDec.pY_jY, HypDec.pY_j0, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  have hzw : dW.p0 * z = w := by
    rw [← hz]
    simp only [HypDec.incX_apply, HypDec.incY_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc,
      HypDec.p0_jX, HypDec.p0_jY, HypDec.p0_j0, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  have hzh : IsHalf e z := hUz ▸ isHalf_mul_right' hh _
  have hX : IsHalf e (dV.extX W a) := by
    rw [HypDec.extX_apply, ← hUa]; exact isHalf_mul_right' (isHalf_mul_right' hh _) _
  have hY : IsHalf e (dV.extY W a') := by
    rw [HypDec.extY_apply, ← hUa']; exact isHalf_mul_right' (isHalf_mul_right' hh _) _
  have hP : IsHalf e (dV.ext0 W (dW.incX V₀ ξ)) := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, ← hzξ]
    exact isHalf_mul_right' (isHalf_mul_left' _ (isHalf_mul_left' _ hzh)) _
  have hQ : IsHalf e (dV.ext0 W (dW.incY V₀ η)) := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, ← hzη]
    exact isHalf_mul_right' (isHalf_mul_left' _ (isHalf_mul_left' _ hzh)) _
  have hR : IsHalf e (dV.ext0 W (dW.inc0 V₀ w)) := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, ← hzw]
    exact isHalf_mul_right' (isHalf_mul_left' dW.j0 (isHalf_mul_left' dW.p0 hzh)) dV.p0
  have fX : heisO ψ V W (dV.extX W a) Φ = Φ := hA1 _ ha
  have fY : heisO ψ V W (dV.extY W a') Φ = Φ := by rw [hA2 _ ha', hx', one_smul]
  have fP : heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) Φ = Φ := by rw [hB1 _ hξ, hy', one_smul]
  have fQ : heisO ψ V W (dV.ext0 W (dW.incY V₀ η)) Φ = Φ := hB2 _ hη
  have fR : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Φ = Φ := by
    have h := hvac.2 e he ((dV.ext0 W).comp (dW.inc0 V₀) w) (AddSubgroup.mem_map_of_mem ((dV.ext0 W).comp (dW.inc0 V₀)) hw)
      (by rw [AddMonoidHom.comp_apply]; exact hR)
    rw [AddMonoidHom.comp_apply] at h
    exact h
  have z0 : ∀ {s t : WO V W}, IsHalf e s → IsHalf e t → ψ (symplOH V W s t) = 1 := fun hs ht => by
    rw [symplOH_half he0 hs ht, AddChar.map_zero_eq_one]
  show heisO ψ V W _ Φ = Φ
  rw [e1]
  exact heisO_add_fix fX (heisO_add_fix fY (heisO_add_fix fP (heisO_add_fix fQ fR (z0 hQ hR))
    (z0 hP (isHalf_add' hQ hR))) (z0 hY (isHalf_add' hP (isHalf_add' hQ hR))))
    (z0 hX (isHalf_add' hY (isHalf_add' hP (isHalf_add' hQ hR))))

theorem cls_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ)
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ)
    (Γ : AddSubgroup (WO V W)), p.Is dV dW x ψ → Splits dV dW p x y ψ Γ → ∀ Φ ∈ cls dV dW p x y ψ, VacG ψ V W Γ Φ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hs _ hΦ =>
    ⟨hΦ.1, fun u hu => fix_two hp hs hΦ u hu, fun e he u hu hh => fix_half hs hΦ e he u hu hh⟩

end GlobalTheory.AscFin.SplitVac
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

noncomputable section

namespace GlobalTheory.IdLatDual

variable {D : D7}

def hp (S : HSp D) (x y : Fin S.rank → D.host.E) : D.host.E :=
  ∑ i, ∑ j, star (x i) * S.gram i j * y j

def IsO (z : D.host.E) : Prop := ∃ b : 𝓞 D.host.E, (b : D.host.E) = z

lemma isO_zero : IsO (0 : D.host.E) := ⟨0, by simp⟩
lemma isO_add {z w : D.host.E} (hz : IsO z) (hw : IsO w) : IsO (z + w) := by
  obtain ⟨b, rfl⟩ := hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b + c, by push_cast; rfl⟩
lemma isO_mul {z w : D.host.E} (hz : IsO z) (hw : IsO w) : IsO (z * w) := by
  obtain ⟨b, rfl⟩ := hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b * c, by push_cast; rfl⟩
lemma isO_coe (a : 𝓞 D.host.E) : IsO (a : D.host.E) := ⟨a, rfl⟩
lemma isO_star (a : 𝓞 D.host.E) : IsO (star (a : D.host.E)) := by
  refine ⟨⟨star (a : D.host.E), ?_⟩, rfl⟩
  exact (RingOfIntegers.isIntegral_coe a).map (starRingEnd D.host.E).toIntAlgHom
lemma isO_of_mem_one {z : D.host.E} (h : z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) : IsO z := by
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨b, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hb⟩

lemma osmul {n : ℕ} (a : 𝓞 D.host.E) (x : Fin n → D.host.E) : a • x = (a : D.host.E) • x := by
  ext i; simp [Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap]

variable (S : HSp D)

lemma hp_add_left (x x' y) : hp S (x + x') y = hp S x y + hp S x' y := by
  simp only [hp, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]
lemma hp_add_right (x y y') : hp S x (y + y') = hp S x y + hp S x y' := by
  simp only [hp, Pi.add_apply, mul_add, Finset.sum_add_distrib]
lemma hp_zero_left (y) : hp S 0 y = 0 := by simp [hp]
lemma hp_zero_right (x) : hp S x 0 = 0 := by simp [hp]
lemma hp_smul_left (s : D.host.E) (x y) : hp S (s • x) y = star s * hp S x y := by
  simp only [hp, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
lemma hp_smul_right (t : D.host.E) (x y) : hp S x (t • y) = t * hp S x y := by
  simp only [hp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.IdLatDual

open GlobalTheory.IdLatDual in
lemma GlobalTheory.IdLatDual.idLat_fg {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hΛ : Λ.FG)
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : (idLat I Λ).FG := by
  obtain ⟨a, ha, hint⟩ := I.isFractional
  let f : (Fin n → D.host.E) →ₗ[𝓞 D.host.E] (Fin n → D.host.E) := LinearMap.lsmul (𝓞 D.host.E) (Fin n → D.host.E) a
  have hle : (idLat I Λ).map f ≤ Λ := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, hr⟩ := hint s hs
    show a • (s • y) ∈ Λ
    rw [← smul_assoc, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ hy
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hinj : Function.Injective f := by
    intro x x' h
    have h' : a • x = a • x' := h
    rw [osmul, osmul] at h'
    have : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
    exact smul_right_injective _ this h'
  have hfg : ((idLat I Λ).map f).FG := Submodule.FG.of_le hΛ hle
  exact Submodule.fg_of_fg_map_injective f hinj hfg


open GlobalTheory.IdLatDual in
theorem GlobalTheory.idLat_isSelfDualC : ∀ {D : D7} (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (I I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), IsSelfDualC S Λ → I * I' = 1 →
    (∀ x : D.host.E, x ∈ I' ↔ star x ∈ I) → IsSelfDualC S (idLat I Λ) := by
  intro D S Λ I I' hΛ hII' hconj
  obtain ⟨hlat, hdual⟩ := hΛ
  have intL : ∀ x ∈ Λ, ∀ y ∈ Λ, IsO (hp S x y) := fun x hx y hy => (hdual y).1 hy x hx
  have gen : ∀ s ∈ I, ∀ y ∈ Λ, s • y ∈ idLat I Λ := fun s hs y hy =>
    Submodule.subset_span ⟨s, hs, y, hy, rfl⟩
  have one_mem : (1 : D.host.E) ∈ I * I' := by rw [hII']; exact FractionalIdeal.one_mem_one _

  have hspan : ∀ y ∈ Λ, y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E)) := by
    intro y hy
    have key : ∀ z ∈ I * I', z • y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E)) := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi c _ => ?_) (fun a b ha hb => ?_)
      · rw [mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (gen i hi y hy))
      · rw [add_smul]; exact Submodule.add_mem _ ha hb
    simpa using key 1 one_mem
  have hfg : (idLat I Λ).FG := idLat_fg Λ hlat.fg I
  refine ⟨Submodule.IsLattice.of_fg D.host.E hfg, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  ·
    have stepA : ∀ s ∈ I, ∀ x₀ ∈ Λ, ∀ y ∈ idLat I Λ, IsO (hp S (s • x₀) y) := by
      intro s hs x₀ hx₀ y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨t, ht, y₀, hy₀, rfl⟩ := hz
        rw [hp_smul_left, hp_smul_right, ← mul_assoc]
        refine isO_mul (isO_of_mem_one ?_) (intL x₀ hx₀ y₀ hy₀)
        rw [← hII', mul_comm I]
        exact FractionalIdeal.mul_mem_mul ((hconj _).2 (by rwa [star_star])) ht
      | zero => rw [hp_zero_right]; exact isO_zero
      | add a b _ _ ha hb => rw [hp_add_right]; exact isO_add ha hb
      | smul c z _ hz => rw [osmul, hp_smul_right]; exact isO_mul (isO_coe c) hz
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, hs, x₀, hx₀, rfl⟩ := hz
      obtain ⟨b, hb⟩ := stepA s hs x₀ hx₀ y hy
      exact ⟨b, hb⟩
    | zero => exact ⟨0, by rw [← hp, hp_zero_left]; simp⟩
    | add a b _ _ ha hb =>
      have h : IsO (hp S a y + hp S b y) := isO_add ha hb
      rw [← hp_add_left] at h
      exact h
    | smul c z _ hz =>
      obtain ⟨u, hu⟩ := isO_mul (isO_star c) hz
      exact ⟨u, by rw [← hp, osmul, hp_smul_left]; exact hu⟩
  · have hint : ∀ x ∈ idLat I Λ, IsO (hp S x y) := fun x hx => hy x hx
    have key : ∀ z ∈ I * I', z • y ∈ idLat I Λ := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi c hc => ?_) (fun a b ha hb => ?_)
      · rw [mul_smul]
        refine gen i hi _ ((hdual _).2 fun x' hx' => ?_)
        have hsc : star c ∈ I := (hconj c).1 hc
        obtain ⟨b, hb⟩ := hint _ (gen _ hsc x' hx')
        refine ⟨b, ?_⟩
        rw [hb]
        show hp S (star c • x') y = hp S x' (c • y)
        rw [hp_smul_left, hp_smul_right, star_star]
      · rw [add_smul]; exact Submodule.add_mem _ ha hb
    simpa using key 1 one_mem
end
end
