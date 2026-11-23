module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle010
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
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

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}


open Classical in
def atT {m : ℕ} (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) (M : Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  fun i j => σ (Pi.single τ (M i j))

theorem compAt_atT {m : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (M : Matrix (Fin m) (Fin n) ℂ) : compAt θ τ (atT σ τ M) = M := by
  classical
  ext i j
  simp only [compAt, atT, Matrix.map_apply, h.comp, Pi.single_eq_same]

theorem compAt_atT_ne {m : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {τ τ' : D.what₂.Tau}
    (hne : τ' ≠ τ) (M : Matrix (Fin m) (Fin n) ℂ) : compAt θ τ' (atT σ τ M) = 0 := by
  classical
  ext i j
  simp only [compAt, atT, Matrix.map_apply, h.comp, Matrix.zero_apply]
  exact Pi.single_eq_of_ne hne _

theorem finPart_atT {m : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) : finPart D (atT σ τ M i j) = 0 := h.fin _

theorem compAt_zero {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) : compAt θ τ (0 : Mx D m n) = 0 := by
  ext i j; simp [compAt]

def intW (D : D7) (m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) where
  carrier := {a | ∀ i j, a i j ∈ intAE D}
  add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
  zero_mem' := fun _ _ => (intAE D).zero_mem
  neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j)


open Classical in
def g0 (D : D7) (m n : ℕ) : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
  if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ intW D m n) = 0 then (1 : ℂ) else 0

theorem gaussian_mem_schwartz_bruhat (D : D7) (m n : ℕ) : g0 D m n ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  classical
  have hWe : (intW D m n : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (intW D m n : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (intW D m n : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  exact GlobalTheory.SchwartzBruhatTensor.coset_mem_SB (intW D m n) hWo hWc 0

theorem gaussian_at_zero_eq_one (D : D7) (m n : ℕ) : g0 D m n 0 = 1 := by
  classical
  simp only [g0]
  rw [if_pos]
  exact (QuotientAddGroup.eq_zero_iff (N := intW D m n) (0 : Matrix (Fin m) (Fin n) _)).2 (intW D m n).zero_mem

def psi0 (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : Mx D V.rank n → ℂ := fun x =>
  evalPoly (1 : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (fun τ => compAt θ τ x) *
    gAway V l s τ (fun τ => compAt θ τ x) * g0 D V.rank n (fun i j => finPart D (x i j))

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : psi0 θ V n l s τ ∈ awayA θ V n l s τ :=
  Submodule.subset_span ⟨1, g0 D V.rank n, gaussian_mem_schwartz_bruhat D V.rank n, fun v hv => by simp at hv, rfl⟩

theorem gAway_of {V : HSp D} (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (hz : ∀ τ', τ' ≠ τ → z τ' = 0) : gAway V l s τ z = 1 := by
  classical
  simp only [gAway]
  rw [Finset.sum_eq_zero]
  · simp
  · intro τ' h'
    rw [hz τ' (Finset.mem_filter.1 h').2]
    simp

theorem gaussian_vacuum_archimedean_point {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D)
    (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    (M : Matrix (Fin V.rank) (Fin n) ℂ) : psi0 θ V n l s τ (atT σ τ M) = 1 := by
  have e1 : (fun i j => finPart D (atT σ τ M i j)) = (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    funext i j; exact finPart_atT h τ M i j
  simp only [psi0, evalPoly, map_one, one_mul, e1, gaussian_at_zero_eq_one, mul_one]
  exact gAway_of l s τ _ fun τ' h' => compAt_atT_ne h h' M

theorem cmTraceAdditiveCharacter_zero (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : psi0 θ V n l s τ 0 = 1 := by
  have e1 : (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    funext i j; simp
  simp only [psi0, evalPoly, map_one, one_mul, e1, gaussian_at_zero_eq_one, mul_one]
  exact gAway_of l s τ _ fun τ' _ => compAt_zero θ τ'

theorem tens_cancel {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D)
    (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsUnit fr.det) {f f' : (Fin V.rank → Fin n → ℂ) → ℂ}
    (e : tens θ τ fr f (psi0 θ V n l s τ) = tens θ τ fr f' (psi0 θ V n l s τ)) : f = f' := by
  funext u
  let U : Matrix (Fin V.rank) (Fin n) ℂ := u
  have := congrFun e (atT σ τ (fr * U))
  simp only [tens, compAt_atT h, gaussian_vacuum_archimedean_point h, mul_one] at this
  have e2 : fr⁻¹ * (fr * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr, Matrix.one_mul]
  rw [e2] at this
  exact this

theorem tens_zero {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ)
    (Ψ : Mx D m n → ℂ) : tens θ τ fr f Ψ 0 = f 0 * Ψ 0 := by
  simp only [tens, compAt_zero, Matrix.mul_zero]
  rfl

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ} {Ψ : Mx D m n → ℂ}
    {P : PX m n} (hm : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : (phiS θ τ fr c Ψ P).1 = tens θ τ fr (fP c P) Ψ := by
  simp only [phiS, dif_pos hm]

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end

section

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcBH

open DCalcH

variable {m n : ℕ}

theorem norm_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) (a : Fin m) (j : Fin n) :
    ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
  simp only [DCalcH.vS, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def nS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : ℝ := ∑ a, ∑ j, ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2

theorem gs_vS (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    gs c (vS u X s) = Complex.exp (((-(c * nS u X s)) : ℝ) : ℂ) := by
  simp only [gs, nS, norm_vS, Complex.ofReal_neg]

theorem nS_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (nS u X) (∑ a, ∑ j, 2 * X j * ‖vS u X s a j‖ ^ 2) s := by
  have h : ∀ a j, HasDerivAt (fun s => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2)
      (2 * X j * ‖vS u X s a j‖ ^ 2) s := by
    intro a j
    rw [norm_vS]
    have h1 : HasDerivAt (fun s : ℝ => s * X j) (X j) s := by
      simpa using (hasDerivAt_id s).mul_const (X j)
    refine (((h1.exp).pow 2).const_mul (‖u a j‖ ^ 2)).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have h3 := HasDerivAt.sum (u := Finset.univ) fun a _ => HasDerivAt.sum (u := Finset.univ) fun j _ => h a j
  have e : nS u X = ∑ a, ∑ j, fun s : ℝ => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
    ext y
    simp [nS, Finset.sum_apply]
  rw [e]
  exact h3

theorem gs_hasDeriv (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => gs c (vS u X s))
      (gs c (vS u X s) * (-(2 * c : ℂ) * ∑ a, ∑ j, (X j : ℂ) * ((‖vS u X s a j‖ ^ 2 : ℝ) : ℂ))) s := by
  simp_rw [gs_vS]
  have h := ((nS_hasDeriv u X s).const_mul c).neg.ofReal_comp.cexp
  refine h.congr_deriv ?_
  congr 1
  push_cast
  rw [neg_mul]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def fF (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) : ℂ :=
  ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * fP c P (vS u X s)

theorem fF_hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fF c X P u) (fF c X (dil c X P) u s) s := by
  have he : HasDerivAt (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ))
      ((((m : ℝ) * ∑ j, X j : ℝ) : ℂ) * ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) s := by
    have := hasDerivAt_expX ((m : ℝ) * ∑ j, X j) s
    simp only [mul_assoc] at this ⊢
    exact this
  have h := he.mul ((eval_hasDeriv P u X s).mul (gs_hasDeriv c u X s))
  unfold fF fP
  have efun : (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s))) =
      fun s => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s)) := rfl
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [evX_dil]
  push_cast
  ring

theorem fF_iter (c : ℝ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (r : ℕ) :
    iteratedDeriv r (fF c X 1 u) = fF c X ((dil c X ^ r) 1) u := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [(fF_hasDeriv c X ((dil c X ^ r) 1) u s).deriv, pow_succ', Module.End.mul_apply]

end DCalcBH

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem cnt_add {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at h
  exact h

theorem sigOK_of (hlt : WittLBlt) (heq : WittLBeq) : SigOK := by
  intro D n V s hr hs
  by_contra hne
  push Not at hne
  choose ε fr hfr hng using hne
  obtain ⟨h1, h2, h3⟩ := hr
  have hb : ∀ τ, V.rank - n ≤ cnt (ε τ) true ∧ V.rank - n ≤ cnt (ε τ) false := by
    intro τ
    have hc := cnt_add (ε τ)
    unfold GoodSig at hng
    have := hng τ
    push Not at this
    obtain ⟨a, b, c, d⟩ := this
    constructor <;> omega
  have hS : SigAtLeast D V (V.rank - n) := fun τ =>
    ⟨ε τ, fr τ, (hfr τ).1, (hfr τ).2.1, (hb τ).1, (hb τ).2⟩
  have hw : V.rank - n ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
    rcases Nat.lt_or_ge (2 * (V.rank - n)) V.rank with h | h
    · exact hlt D V _ h hS
    · exact heq D V _ (by omega) hS
  omega

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open EmbP
open Formalism.IndefR.Eqv (psiT thetaC eq_thetaC)

variable {D : D7} {n : ℕ}

theorem reidx_mul (a b : M2 n) : reidx (a * b) = reidx a * reidx b := by
  simp only [reidx, Matrix.submatrix_mul_equiv]

theorem reidx_one : reidx (1 : M2 n) = 1 := Matrix.submatrix_one_equiv _

theorem reidx_conjTranspose (a : M2 n) : reidx aᴴ = (reidx a)ᴴ := by
  simp only [reidx, Matrix.conjTranspose_submatrix]

theorem continuous_reidx : Continuous (fun a : M2 n => reidx a) :=
  continuous_id.matrix_submatrix _ _

theorem Jst_map (τ : D.what₂.Tau) : (Jst D n).map (tauE D τ) = reidx (JJ n) := by
  ext i j
  simp only [Jst, blk4, reidx, JJ, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem mR_mul_inv (a : GR n) : mR a * mR a⁻¹ = 1 := by
  rw [← mR_mul, mul_inv_cancel, mR_one]

theorem mR_inv_mul (a : GR n) : mR a⁻¹ * mR a = 1 := by
  rw [← mR_mul, inv_mul_cancel, mR_one]

theorem reidx_unitary (τ : D.what₂.Tau) (y : GR n) :
    (reidx (mR y))ᴴ * (Jst D n).map (tauE D τ) * reidx (mR y) = (Jst D n).map (tauE D τ) := by
  have h : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  rw [Jst_map, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, h]

def iotaF (τ : D.what₂.Tau) (y : GR n) : G D n :=
  (⟨⟨atMN D τ (reidx (mR y)), atMN D τ (reidx (mR y⁻¹)),
      by rw [← atMN_mul, ← reidx_mul, mR_mul_inv, reidx_one, atMN_one],
      by rw [← atMN_mul, ← reidx_mul, mR_inv_mul, reidx_one, atMN_one]⟩,
    atMN_unitary D τ (Jst D n) _ (reidx_unitary τ y)⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

def iota (τ : D.what₂.Tau) : GR n →* G D n where
  toFun := iotaF τ
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show atMN D τ (reidx (mR 1)) = 1
    rw [mR_one, reidx_one, atMN_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    show atMN D τ (reidx (mR (a * b))) = atMN D τ (reidx (mR a)) * atMN D τ (reidx (mR b))
    rw [mR_mul, reidx_mul, atMN_mul]

theorem continuous_iota (τ : D.what₂.Tau) : Continuous (iota (D := D) (n := n) τ) := by
  have hm : Continuous fun y : GR n => mR y := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun y : GR n => mR y⁻¹ := hm.comp continuous_inv
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_atMN D τ).comp (continuous_reidx.comp hm)
  · exact (continuous_atMN D τ).comp (continuous_reidx.comp hmi)

theorem sEmb : SEmb := by
  intro D n θ τ hθ
  obtain rfl := eq_thetaC D hθ
  refine ⟨iota τ, continuous_iota τ, fun y => ⟨?_, fun τ' hτ' => ?_, ?_⟩⟩
  · have e := psi_atMN D τ τ (reidx (mR y))
    rw [if_pos rfl] at e
    exact e
  · have e := psi_atMN D τ τ' (reidx (mR y))
    rw [if_neg hτ'] at e
    exact e
  · exact fin_atMN D τ (reidx (mR y))

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def DX (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (Φ : Mx D V.rank n → ℂ)
    (x : Mx D V.rank n) : ℂ :=
  deriv (fun t : ℝ => Φ (HMul.hMul (mt V (atTau θ V τ (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹))) x)) 0

def LieComm : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ Ψ ∈ awayA θ V n l s τ,
    ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUe ε X → ∀ (P : PX V.rank n) (g : G D n) (x : Mx D V.rank n),
      (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X P))).1 x = DX θ V τ fr X (ω g (phiS θ τ fr (cLoc l τ) Ψ P)).1 x

def DerivOne : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUe ε X → ∀ Θ Θ' : schwartzA θ V.rank n,
      (∀ x, Θ'.1 x = DX θ V τ fr X Θ.1 x) → thetaInt ω ν Θ' 1 = 0

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct SchwartzMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

variable {D : D7} {n : ℕ}

theorem evalPoly_congr {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (τ : D.what₂.Tau)
    (hp : ∀ v ∈ p.vars, v.1 ≠ τ) (z z' : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (h : ∀ τ', τ' ≠ τ → z τ' = z' τ') :
    evalPoly p z = evalPoly p z' := by
  unfold evalPoly
  change MvPolynomial.eval₂ (RingHom.id ℂ) _ p = MvPolynomial.eval₂ (RingHom.id ℂ) _ p
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  have hv : i ∈ p.vars := (MvPolynomial.mem_vars_iff_mem_support i).2 ⟨c, (MvPolynomial.mem_support_iff).2 hc, hi⟩
  have e := h i.1 (hp i hv)
  simp only [e]

theorem gAway_congr (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (z z' : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (h : ∀ τ', τ' ≠ τ → z τ' = z' τ') :
    gAway V l s τ z = gAway V l s τ z' := by
  classical
  unfold gAway
  congr 2
  refine Finset.sum_congr rfl (fun τ' hτ' => ?_)
  rw [h τ' (Finset.mem_filter.1 hτ').2]

theorem dep (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ) (x x' : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D)) :
    Ψ x = Ψ x' := by
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, _, hp, rfl⟩ := hφ
    simp only
    have hf' : (fun i j => finPart D (x i j)) = (fun i j => finPart D (x' i j)) := hf
    rw [evalPoly_congr p τ hp _ _ hx, gAway_congr V l s τ _ _ hx, hf']
  | zero => rfl
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]
  | smul c a _ ha => simp only [Pi.smul_apply, ha]

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end
