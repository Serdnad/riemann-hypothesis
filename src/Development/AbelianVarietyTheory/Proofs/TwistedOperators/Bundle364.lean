module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Mathlib.RingTheory.PicardGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle346
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KapXLine

variable {D : D7}

theorem kapX_mul (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g h : GA D X) :
    kapX X e hJ (g * h) = kapX X e hJ g * kapX X e hJ h := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X (g * h)) =
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X g) *
      Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X h)
  rw [map_mul, map_mul]

theorem kapX_one (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : kapX X e hJ 1 = 1 := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X 1) = 1
  rw [map_one, map_one]

theorem continuous_kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : Continuous (kapX X e hJ) := by
  have h1 : Continuous (matHom X) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp h1).matrix_reindex e e
  · exact (Units.continuous_coe_inv.comp h1).matrix_reindex e e

theorem smul_eq_zero_of_finTens {u : AF D.host.F} (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0) {z : AE D}
    (hz : GlobalTheory.LFun.finTens D.host.F D.host.E z = 0) : u • z = 0 := by
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective (hu.trans (map_zero _).symm)
  refine GlobalTheory.LFun.tens_ext ?_ ?_
  · rw [Algebra.smul_def, map_mul, map_zero]
    change (u.1 ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = 0
    rw [hu1, TensorProduct.zero_tmul, zero_mul]
  · rw [Algebra.smul_def, map_mul, map_zero, hz, mul_zero]

theorem kapX_mem_UAt (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) {g : GA D X} (hg : g ∈ GinfC X) :
    kapX X e hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have hf : finHom X g = 1 := hg
  have hent : ∀ a b, GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.mt X g a b) =
      (1 : Matrix (Fin X.rank) (Fin X.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    have := congrArg (fun k : GL (Fin X.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf
    exact this
  ext i j
  rw [mat_kapX]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, reindex_apply, submatrix_apply]
  apply smul_eq_zero_of_finTens hu
  rw [map_sub, hent, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : e.symm i ≠ e.symm j := fun k => h (e.symm.injective k)
    simp [h, h']

end GlobalTheory.KapXLine

open GlobalTheory.KapXLine in
theorem GlobalTheory.KapXLine.exists_line : ∀ (D : D7) (θ : InfFam D) (X : HSp D) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ),
    IsInfFam θ → Y ∈ lieAt X τ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ),
    ∃ γ ∈ Lines D.sp.cm.sig Wd, ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  intro D θ X τ Y hθ hY d e Wd hJ
  let γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J :=
    { toFun := fun t => kapX X e hJ (oneP θ X τ Y (Multiplicative.toAdd t))
      map_one' := by
        show kapX X e hJ (oneP θ X τ Y 0) = 1
        rw [GlobalTheory.Mem.Lift.oneP_zero hθ, kapX_one]
      map_mul' := fun s t => by
        show kapX X e hJ (oneP θ X τ Y (Multiplicative.toAdd s + Multiplicative.toAdd t)) = _
        rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, kapX_mul] }
  refine ⟨γ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · exact (continuous_kapX X e hJ).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_toAdd)
  · exact kapX_mem_UAt X e Wd hJ (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY _).1

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.FinHeightBound

open GlobalTheory.AdelicU

variable {D : D7}

def cst (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : NNReal :=
  max 1 (Finset.univ.sup fun k : Fin (Module.finrank D.host.F D.host.E) =>
    absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)))

theorem one_le_cst (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : 1 ≤ cst D v := le_max_left _ _

theorem compFin_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AF D.host.F ⊗[D.host.F] D.host.E) :
    compFin D.host.F D.host.E v y =
      Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    simp only [compFin, evFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.comp_apply, AlgHom.id_apply]

theorem sum_finCoord (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
    (Module.finBasis D.host.F D.host.E)).sum_repr y]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem absFin_map_le (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    absFin D.host.F v (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) y) ≤
      cst D v * Finset.univ.sup fun k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k)‖₊ := by
  conv_lhs => rw [← sum_finCoord y]

  rw [map_sum]
  refine absFin_sum_le _ v _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e1 : evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) =
      (evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k) ⊗ₜ[D.host.F] (1 : D.host.E)) *
        ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e1]
  refine (absFin_mul_le _ v _ _).trans ?_
  rw [absFin_tmul_one, mul_comm]
  refine mul_le_mul' ?_ ?_
  · exact le_max_of_le_right (Finset.le_sup (f := fun k : Fin (Module.finrank D.host.F D.host.E) =>
      absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k))) (Finset.mem_univ k))
  · exact Finset.le_sup (f := fun k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k)‖₊) (Finset.mem_univ k)

theorem absFin_le (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AF D.host.F ⊗[D.host.F] D.host.E) :
    absFin D.host.F v (compFin D.host.F D.host.E v y) ≤ cst D v * Finset.univ.sup fun k =>
      ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) k)‖₊ := by
  rw [compFin_eq]
  exact absFin_map_le v _

end GlobalTheory.SquareAgree.FinHeightBound

namespace GlobalTheory.SquareAgree.FinHeightBound

open GlobalTheory.AdelicU

variable {D : D7}

theorem coordNorm_le_finNorm (X : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : GA D X) (a b : Fin X.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) :
    ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (finMat D.sp.cm.sig X.gram h a b) k)‖₊ ≤
      GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm X v h := by
  have := Finset.le_sup (f := fun p : Fin X.rank × Fin X.rank × Fin (Module.finrank D.host.F D.host.E) =>
    ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (finMat D.sp.cm.sig X.gram h p.1 p.2.1) p.2.2)‖₊)
    (Finset.mem_univ (a, b, k))
  dsimp only at this
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm
  exact this

theorem normFin_reindex_le (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : GA D X) :
    normFin D.host.F v ((reindex e e (Formalism.L2.Theta.mt X h)).map (compFin D.host.F D.host.E v)) ≤
      cst D v * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm X v h := by
  refine (normFin_le_iff D.host.F v).2 fun i j => ?_
  rw [Matrix.map_apply, reindex_apply, Matrix.submatrix_apply]
  have hfm : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (Formalism.L2.Theta.mt X h (e.symm i) (e.symm j)) = finMat D.sp.cm.sig X.gram h (e.symm i) (e.symm j) := rfl
  have h1 := absFin_le v (Formalism.L2.Theta.mt X h (e.symm i) (e.symm j))
  rw [hfm] at h1
  have h2 := Finset.sup_le (s := Finset.univ) fun k _ => coordNorm_le_finNorm X v h (e.symm i) (e.symm j) k
  exact h1.trans (mul_le_mul' le_rfl h2)

theorem kapX_inv (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) : (kapX X e hJ h).1⁻¹ = (kapX X e hJ h⁻¹).1 := by
  show (Units.map _ (Formalism.L2.Theta.matHom X h))⁻¹ = Units.map _ (Formalism.L2.Theta.matHom X h⁻¹)
  rw [map_inv, map_inv]

theorem coe_bc_kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ((Formalism.UG.bc (compFin D.host.F D.host.E v) (kapX X e hJ h).1 : GL (Fin d) _) : Matrix (Fin d) (Fin d) _) =
      (reindex e e (Formalism.L2.Theta.mt X h)).map (compFin D.host.F D.host.E v) := by
  rw [← mat_kapX X e hJ h]
  rfl

theorem htFin_kapX_le (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤
      cst D v * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h := by
  have h1 := normFin_reindex_le X e v h
  have h2 := normFin_reindex_le X e v h⁻¹
  unfold htFin htOf GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt
  rw [← map_inv, kapX_inv, coe_bc_kapX, coe_bc_kapX]
  refine max_le ?_ (max_le ?_ ?_)
  · exact (one_le_cst D v).trans (le_mul_of_one_le_right' (le_max_left _ _))
  · exact h1.trans (mul_le_mul' le_rfl (le_max_of_le_right (le_max_left _ _)))
  · exact h2.trans (mul_le_mul' le_rfl (le_max_of_le_right (le_max_right _ _)))

theorem cst_mulSupport_finite (D : D7) : Function.HasFiniteMulSupport (cst D) := by
  have h : ∀ k : Fin (Module.finrank D.host.F D.host.E), ∀ᶠ v in Filter.cofinite,
      absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) ≤ 1 := by
    intro k
    refine (eventually_absFin_le_one D.host.F
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k))).mono fun v hv => ?_
    have e1 : compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) =
        (1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) := by
      simp only [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one,
        AlgHom.id_apply]
    rwa [e1] at hv
  refine (Filter.eventually_cofinite.1 (Filter.eventually_all.2 h)).subset fun v hv hv' => hv ?_
  exact max_eq_left (Finset.sup_le fun k _ => hv' k)

end GlobalTheory.SquareAgree.FinHeightBound

namespace GlobalTheory.SquareAgree

open GlobalTheory.AdelicU GlobalTheory.SquareAgree.FinHeightBound

theorem finprod_htFin_kapX_le : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal,
    ∀ h : GA D X, ∏ᶠ v, GlobalTheory.AdelicU.htFin D.host.F v
      (Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤
      C * ∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h := by
  intro D X d e J hJ
  refine ⟨∏ᶠ v, cst D v, fun h => ?_⟩
  have hc := cst_mulSupport_finite D
  have hf : Function.HasFiniteMulSupport fun v => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h :=
    GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite X h
  rw [← finprod_mul_distrib hc hf]
  refine finprod_le_finprod₀ (finite_mulSupport_htFin D.host.F (kapX X e hJ h).1) (fun _ => bot_le) ?_
    (fun v => htFin_kapX_le X e hJ h v)
  exact (hc.union hf).subset (Function.mulSupport_mul _ _)

end GlobalTheory.SquareAgree
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.LineAtPlace

variable {D : D7}

theorem emb_eq_or_conj (e₁ e₂ : D.host.E →+* ℂ)
    (h : ∀ a : D.host.F, e₁ (algebraMap D.host.F D.host.E a) = e₂ (algebraMap D.host.F D.host.E a)) :
    (∀ x, e₂ x = e₁ x) ∨ ∀ x, e₂ x = starRingEnd ℂ (e₁ x) := by
  have hconj : ∀ a : D.host.E, e₁ (star a) = starRingEnd ℂ (e₁ a) := D.sp.cm.cmUnram.2.1 e₁
  have hb := Eqv.star_alphaE D
  have hdec : ∀ y : D.host.E, ∃ p q : D.host.F,
      y = algebraMap D.host.F D.host.E p + algebraMap D.host.F D.host.E q * Eqv.alphaE D := by
    intro y
    refine ⟨(Eqv.basE D).repr y 0, (Eqv.basE D).repr y 1, ?_⟩
    conv_lhs => rw [← (Eqv.basE D).sum_repr y]
    rw [Fin.sum_univ_two, Eqv.basE_zero, Eqv.basE_one, Algebra.smul_def, Algebra.smul_def, mul_one]
  have hb2 : e₂ (Eqv.alphaE D) ^ 2 = e₁ (Eqv.alphaE D) ^ 2 := by
    have h1 : star (Eqv.alphaE D ^ 2) = Eqv.alphaE D ^ 2 := by rw [star_pow, hb]; ring
    obtain ⟨t, ht⟩ := (D.sp.cm.fixed _).1 h1
    rw [← map_pow, ← map_pow, ← ht, h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hb2 with hc | hc
  · left
    intro y
    obtain ⟨p, q, rfl⟩ := hdec y
    rw [map_add (f := _), map_add (f := _), map_mul, map_mul, hc, h, h]
  · right
    intro y
    obtain ⟨p, q, rfl⟩ := hdec y
    rw [← hconj, star_add, star_mul, Eqv.star_algebraMapF, Eqv.star_algebraMapF, hb, map_add (f := _), map_add (f := _), map_mul, map_mul,
      map_neg, hc, h, h]
    ring

theorem exists_piInf (τ : D.what₂.Tau) (p : GlobalTheory.AdelicU.EmbOver D.host.E (Eqv.plW D τ)) :
    ∃ c : ℂ →+* ℂ, Continuous c ∧ (∀ (t : ℝ) z, c (t • z) = t • c z) ∧
      ∀ y : AE D, Eqv.psiT D τ y = c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p y) := by
  have key : ∀ c : ℂ →+* ℂ, (∀ t : ℝ, c t = t) → (∀ x, tauE D τ x = c (p.1 x)) →
      ∀ y : AE D, Eqv.psiT D τ y = c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p y) := by
    intro c hc hx y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
    | tmul a x =>
      have l1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p (a ⊗ₜ[D.host.F] x) = Eqv.gW D (Eqv.plW D τ) (fstA D.host.F a) * p.1 x :=
        GlobalTheory.AdelicU.infEmb_tmul p _ x
      have l2 : Eqv.psiT D τ (a ⊗ₜ[D.host.F] x) = Eqv.gW D (Eqv.plW D τ) (fstA D.host.F a) * tauE D τ x :=
        Eqv.thetaC_tmul D τ _ x
      rw [l1, l2, map_mul, hx, Eqv.gW_real, hc]
  rcases emb_eq_or_conj p.1 (tauE D τ) (fun a => RingHom.congr_fun (p.2.trans (Eqv.plW_embedding D τ)) a) with h | h
  · exact ⟨RingHom.id ℂ, continuous_id, fun _ _ => rfl, key _ (fun _ => rfl) h⟩
  · exact ⟨starRingEnd ℂ, Complex.continuous_conj, fun t z => by simp, key _ Complex.conj_ofReal h⟩

theorem kapX_surj (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : ∃ h, kapX X e hJ h = k := by
  subst hJ
  have h1 : (k.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • reindex e e X.gramᵀ) * (k.1.1).map (cA D) =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • reindex e e X.gramᵀ) := k.2
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h1
  have hx : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have h2 := congrArg (fun Y => ((incA D D.host.xi0⁻¹ • Y)ᵀ).submatrix e e) h1
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hx, map_one, one_smul, transpose_mul,
    transpose_transpose, ← Matrix.mul_assoc] at h2
  rw [← submatrix_mul_equiv _ _ _ e, ← submatrix_mul_equiv _ _ _ e] at h2
  have e1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ))ᵀ.submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  rw [e1] at h2
  refine ⟨⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom k.1, h2⟩, Subtype.ext (Units.ext ?_)⟩
  show reindex e e (reindex e.symm e.symm k.1.1) = k.1.1
  simp


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem lie_of_exp {n : ℕ} (Y H : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ * H * NormedSpace.exp (t • Y) = H) : Yᴴ * H + H * Y = 0 := by
  have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Yᴴ (0 : ℝ)).mul_const H).fun_mul
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ))
  have h2 : (fun t : ℝ => NormedSpace.exp (t • Yᴴ) * H * NormedSpace.exp (t • Y)) = fun _ => H := by
    funext t
    have e : t • Yᴴ = (t • Y)ᴴ := by rw [Matrix.conjTranspose_smul, star_trivial]
    rw [e, Matrix.exp_conjTranspose]
    exact h t
  have h3 := (h1.congr_of_eventuallyEq (f₁ := fun _ => H)
    (Filter.Eventually.of_forall fun t => (congrFun h2 t).symm)).unique (hasDerivAt_const _ _)
  simpa using h3


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_map {n d : ℕ} (e : Fin n ≃ Fin d) (c : ℂ →+* ℂ) (hc : Continuous c) (Z : Matrix (Fin d) (Fin d) ℂ) :
    ((NormedSpace.exp Z).map c).submatrix e e = NormedSpace.exp ((Z.map c).submatrix e e) :=
  NormedSpace.map_exp ((Matrix.reindexAlgEquiv ℂ ℂ e.symm).toRingHom.comp c.mapMatrix)
    ((continuous_id.matrix_map hc).matrix_submatrix e e) Z

end GlobalTheory.LineAtPlace

open GlobalTheory.LineAtPlace in
theorem GlobalTheory.LineAtPlace.exists_oneP : ∀ (D : D7) (θ : InfFam D) (X : HSp D), IsInfFam θ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ)
    (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) (w : InfinitePlace D.host.F)
    (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J),
    γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd →
    (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w)) =
      NormedSpace.exp (t • Z)) →
    (∀ (t : ℝ) (w' : InfinitePlace D.host.F), w' ≠ w →
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w')) = 1) →
    ∃ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ), Y ∈ lieAt X τ ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  intro D θ X hθ d e Wd hJ emb w Z γ hγ hw ho
  obtain rfl := Eqv.eq_thetaC D hθ
  obtain ⟨τ, rfl⟩ : ∃ τ, Eqv.plW D τ = w := ⟨_, Eqv.plW_symm D w⟩
  choose h hh using fun t : ℝ => kapX_surj X e hJ (γ (Multiplicative.ofAdd t))
  have hm : ∀ t, Eqv.matA D X (h t) = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).submatrix e e := by
    intro t
    rw [← hh t]
    show _ = (reindex e e (Eqv.matA D X (h t))).submatrix e e
    simp
  obtain ⟨c, hc, hcs, hp⟩ := exists_piInf τ (emb _)
  have h1 : ∀ t : ℝ, infMat D.sp.cm.sig X.gram (Eqv.thetaC D τ) (h t) =
      NormedSpace.exp (t • (Z.map c).submatrix e e) := by
    intro t
    have e1 : t • (Z.map c).submatrix e e = ((t • Z).map c).submatrix e e := by
      ext i j
      exact (hcs t _).symm
    rw [Eqv.infMat_thetaC, hm, e1, ← exp_map e c hc, ← hw]
    ext i j
    exact hp _
  have hu : ∀ t : ℝ, (NormedSpace.exp (t • (Z.map c).submatrix e e))ᴴ * gramAt D X τ *
      NormedSpace.exp (t • (Z.map c).submatrix e e) = gramAt D X τ := by
    intro t
    rw [← h1]
    exact Eqv.infMat_unitary' D X (h t) τ
  refine ⟨τ, (Z.map c).submatrix e e, lie_of_exp _ _ hu, fun t => ?_⟩
  rw [← hh t, oneP, Eqv.atTau_eq D X τ _ (hu t)]
  congr 1
  apply Eqv.matA_inj D X
  rw [Eqv.matA_atH]
  refine Eqv.matA_of_isAtTau D X ⟨(Eqv.mem_GinfC D X _).2 ?_, h1 t, fun ρ hρ => ?_⟩
  · ext i j
    have k1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) (e i) (e j) - (1 : Matrix _ _ (AE D)) (e i) (e j)) :=
      fun u hu => congrFun (congrFun (hγ.2 _ u hu) (e i)) (e j)
    have k2 := GlobalTheory.ConjInfExp.finPart_eq_one
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) (e i) (e j) - (1 : Matrix _ _ (AE D)) (e i) (e j) + 1)
      (by rwa [add_sub_cancel_right])
    rw [RingHom.map_add (f := _), RingHom.map_one, add_eq_right, RingHom.map_sub, sub_eq_zero] at k2
    rw [Matrix.map_apply, hm, submatrix_apply, k2]
    by_cases k : i = j
    · subst k; simp
    · simp [Matrix.one_apply_ne k, Matrix.one_apply_ne (e.injective.ne k)]
  · obtain ⟨c', -, -, hp'⟩ := exists_piInf ρ (emb _)
    have k1 : Eqv.plW D ρ ≠ Eqv.plW D τ := fun k => hρ (by rw [← Eqv.symm_plW D ρ, k, Eqv.symm_plW])
    rw [Eqv.infMat_thetaC, hm]
    ext i j
    have k2 := congrFun (congrFun (ho t _ k1) (e i)) (e j)
    rw [Matrix.map_apply] at k2
    rw [Matrix.map_apply, submatrix_apply, hp', k2]
    by_cases k : i = j
    · subst k; simp
    · simp [Matrix.one_apply_ne k, Matrix.one_apply_ne (e.injective.ne k)]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaFunction_prod_conj_eq_of_heisenbergFixed : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := by
  first | exact @GlobalTheory.ThetaFixedProd.prod_eq_of_fixed | exact GlobalTheory.ThetaFixedProd.prod_eq_of_fixed | (intros; apply GlobalTheory.ThetaFixedProd.prod_eq_of_fixed <;> assumption)
end
