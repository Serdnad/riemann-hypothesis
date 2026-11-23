module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle498
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle484
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle485
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle486
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

@[expose] public section

section

noncomputable section

open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocalHypotheses

section Generic

variable {G : Type} [Group G] [TopologicalSpace G]

def LocConds (θ : G →* G) (K : Subgroup G) (d : G) (f : G → ℂ) : Prop :=
  (∀ x ∈ twCent θ d, ∀ y ∈ twCent θ d, x * y = y * x) ∧
  (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0) ∧
  {q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) |
    ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k)) ≠ 0}.Finite ∧
  (∀ y : G, twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent θ d) ∧
    (twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent θ d)) ≠ 0)

def UnitConds (θ : G →* G) (K : Subgroup G) (d : G) (f : G → ℂ) : Prop :=
  f = (K : Set G).indicator 1 ∧ d ∈ K ∧ cptPart (twCent θ d) ≤ K ∧
    ∀ y, y⁻¹ * d * θ y ∈ K → ∃ t ∈ twCent θ d, ∃ k ∈ K, y = t * k

end Generic

section Split

variable {H : Type} [Group H]

def swTw (σ : H →* H) : H × H →* H × H :=
  (MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom

theorem mem_twCent_swTw (σ : H →* H) (hσ : ∀ g, σ (σ g) = g) (d d' : H) (g : H × H) :
    g ∈ twCent (swTw σ) (d, d') ↔
      g.1 ∈ twCent (MonoidHom.id H) (d * σ d') ∧ g.2 = d' * σ g.1 * d'⁻¹ := by
  obtain ⟨g₁, g₂⟩ := g
  show (g₁, g₂) * (d, d') = (d, d') * (σ g₂, σ g₁) ↔ g₁ * (d * σ d') = d * σ d' * g₁ ∧ g₂ = d' * σ g₁ * d'⁻¹
  simp only [Prod.mk_mul_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have e : g₂ = d' * σ g₁ * d'⁻¹ := by rw [← h₂]; group
    refine ⟨?_, e⟩
    rw [← mul_assoc, h₁, e]
    simp only [map_mul, map_inv, hσ]
    group
  · rintro ⟨h₁, rfl⟩
    refine ⟨?_, by group⟩
    simp only [map_mul, map_inv, hσ]
    have : g₁ * d = d * σ d' * g₁ * (σ d')⁻¹ := by
      rw [← h₁]; group
    rw [this]; group

end Split

section Place

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E]

def sgP (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w :=
  (thetaGL a (RingHom.id _)).prodMap (thetaGL b (RingHom.id _))

def ratW (n : ℕ) (w : Pl E) : GL (Fin n) E →* GLw n w := GeneralLinearGroup.map (algebraMap E (w.adicCompletion E))

end Place

end GlobalTheory.CompanionTheory.LocalHypotheses

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.cuspidal_is_generic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π := by
  first | exact @GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal | exact GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal | (intros; apply GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.finite_dim_coefficients_finite_determining : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W), ∃ S : Finset K, ∀ c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent | exact GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent | (intros; apply GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD

theorem _root_.GlobalTheory.T.cuspidal_satake_almost_all : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : Multiset ℂˣ, (CG.mk π).HasSat w B := by
  first | exact @GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat | exact GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat | (intros; apply GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn GlobalTheory.CompanionTheory.ThTot
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.Orb
variable {D : D7}

def fro {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem fro_nonneg {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : 0 ≤ fro A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem fro_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin b) (Fin c) ℂ) :
    fro (A * B) ≤ fro A * fro B := by
  have key : ∀ i j, ‖(A * B) i j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := by
      rw [Matrix.mul_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖A i k‖) (fun k => ‖B k j‖)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  unfold fro
  calc ∑ i, ∑ j, ‖(A * B) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ k, ∑ j, ‖B k j‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]

theorem norm_entry_sq_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (i : Fin a) (j : Fin b) :
    ‖A i j‖ ^ 2 ≤ fro A := by
  unfold fro
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖ ^ 2) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)

theorem continuous_fro {a b : ℕ} : Continuous (fro : Matrix (Fin a) (Fin b) ℂ → ℝ) := by
  unfold fro
  fun_prop

theorem trace_conjTranspose_mul_self {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) :
    Matrix.trace (Aᴴ * A) = ((fro A : ℝ) : ℂ) := by
  unfold fro
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul']
  rfl

def nrm {m : ℕ} {n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ τ, |l τ| * fro (z τ)

theorem nrm_nonneg {m n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : 0 ≤ nrm l z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (fro_nonneg _)

theorem entry_le_nrm {m n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (τ) (i j) :
    |l τ| * ‖z τ i j‖ ^ 2 ≤ nrm l z := by
  refine le_trans (mul_le_mul_of_nonneg_left (norm_entry_sq_le _ i j) (abs_nonneg _)) ?_
  exact Finset.single_le_sum (f := fun τ => |l τ| * fro (z τ)) (fun _ _ => mul_nonneg (abs_nonneg _) (fro_nonneg _)) (Finset.mem_univ τ)

theorem norm_le_exp {w : ℂ} {d : ℝ} (hd : 0 < d) : ‖w‖ ≤ (1 / Real.sqrt d) * Real.exp (d * ‖w‖ ^ 2) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have h1 : Real.sqrt d * ‖w‖ ≤ Real.exp (d * ‖w‖ ^ 2) := by
    have h2 : d * ‖w‖ ^ 2 + 1 ≤ Real.exp (d * ‖w‖ ^ 2) := Real.add_one_le_exp _
    have h3 : (Real.sqrt d * ‖w‖) ^ 2 = d * ‖w‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hd.le]
    nlinarith [sq_nonneg (Real.sqrt d * ‖w‖ - 1)]
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hs]
  linarith [mul_comm (Real.sqrt d) ‖w‖]

theorem evalPoly_bound {m n : ℕ} (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    ∀ e : ℝ, 0 < e → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ,
      ‖evalPoly q z‖ ≤ C * Real.exp (e * nrm l z) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    intro e he
    refine ⟨‖a‖, norm_nonneg _, fun z => ?_⟩
    simp only [evalPoly, MvPolynomial.eval_C]
    have : 1 ≤ Real.exp (e * nrm l z) := Real.one_le_exp (mul_nonneg he.le (nrm_nonneg _ _))
    nlinarith [norm_nonneg a]
  | add p q hp hq =>
    intro e he
    obtain ⟨C₁, h₁, b₁⟩ := hp e he
    obtain ⟨C₂, h₂, b₂⟩ := hq e he
    refine ⟨C₁ + C₂, add_nonneg h₁ h₂, fun z => ?_⟩
    have : evalPoly (p + q) z = evalPoly p z + evalPoly q z := by simp [evalPoly]
    rw [this, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (b₁ z) (b₂ z))
  | mul_X p k hp =>
    intro e he
    obtain ⟨C₁, h₁, b₁⟩ := hp (e / 2) (by positivity)
    obtain ⟨τ, i, j, b⟩ := k
    have hlt : 0 < |l τ| := abs_pos.2 (hl τ)
    set d : ℝ := e / 2 * |l τ| with hd
    have hd0 : 0 < d := by positivity
    refine ⟨C₁ * (1 / Real.sqrt d), by positivity, fun z => ?_⟩
    have hm : evalPoly (p * MvPolynomial.X (τ, i, j, b)) z = evalPoly p z *
        (if b then conj (z τ i j) else z τ i j) := by simp [evalPoly]
    have hx : ‖(if b then conj (z τ i j) else z τ i j)‖ = ‖z τ i j‖ := by
      split_ifs <;> simp
    rw [hm, norm_mul, hx]
    have h1 := norm_le_exp (w := z τ i j) hd0
    have h2 : Real.exp (d * ‖z τ i j‖ ^ 2) ≤ Real.exp (e / 2 * nrm l z) := by
      apply Real.exp_le_exp.2
      have := entry_le_nrm l z τ i j
      rw [hd, mul_assoc]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : ‖z τ i j‖ ≤ (1 / Real.sqrt d) * Real.exp (e / 2 * nrm l z) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    calc ‖evalPoly p z‖ * ‖z τ i j‖
        ≤ (C₁ * Real.exp (e / 2 * nrm l z)) * ((1 / Real.sqrt d) * Real.exp (e / 2 * nrm l z)) :=
          mul_le_mul (b₁ z) h3 (norm_nonneg _) (by positivity)
      _ = C₁ * (1 / Real.sqrt d) * Real.exp (e * nrm l z) := by
          have : Real.exp (e * nrm l z) = Real.exp (e / 2 * nrm l z) * Real.exp (e / 2 * nrm l z) := by
            rw [← Real.exp_add]; ring_nf
          rw [this]; ring

end GlobalTheory.CompanionTheory.ThTot.Orb

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.countable_matrices_and_cosets : ∀ (D : D7) (a b : ℕ), Countable (Matrix (Fin a) (Fin b) D.host.E) ∧ Countable (GlobalTheory.Eis.Cosets (P D b) (GF D b)) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.countable_mat_cosets | exact GlobalTheory.CompanionTheory.FJE.countable_mat_cosets | (intros; apply GlobalTheory.CompanionTheory.FJE.countable_mat_cosets <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.parabolic_unipotent_levi_factor : ∀ (D : D7) (p : ℕ) (q : G D p), q ∈ P D p → ∀ a : GL (Fin p) (AE D), blkA (mat q) = a.1 →
  ∃ (g₁ g₂ : G D p) (b : Mx D p p), q = g₁ * g₂ ∧ mat g₁ = blk4 1 b 0 1 ∧ mat g₂ = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi | exact GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi | (intros; apply GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.orbit_integral_invariant_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₀ : Measure (Fin n → Fin M → R ⊗[F] E), (∀ h : HA R σ J, m₀.map (actW R σ J h) = m₀) → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ g g' : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = actW R σ (hypOne J) g' (e0 _ M) → stageInt R σ J b lam m₀ φ g = stageInt R σ J b lam m₀ φ g' := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv.stageInt_eq_of_e0 | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv.stageInt_eq_of_e0 | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv.stageInt_eq_of_e0 <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.capelli_operators_commute : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u v : ℂ), Commute (capR r s τ u) (capR r s τ v) ∧ Commute (capR r s τ u) (capS r s τ v) ∧ Commute (capS r s τ u) (capS r s τ v) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute | exact GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute | (intros; apply GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem _root_.GlobalTheory.T.multicone_point_descends_to_subvariety : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (z : (Σ k, Bk n k) → ℂ), z ∈ mcPts (ptIdeal (i (genericPoint X))) →
    ∃ y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀, IsUnder (PtsOver.map i rfl _ y) z := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.UnderSub.exists_cxPt_of_mem_mcPts | exact GlobalTheory.CompanionTheory.MPDict.UnderSub.exists_cxPt_of_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.MPDict.UnderSub.exists_cxPt_of_mem_mcPts <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

theorem _root_.GlobalTheory.T.arithmetic_variety_point_dimension : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) → Geo.IsArithVar (ptIdeal x) d := by
  exact @GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal
end

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

theorem _root_.GlobalTheory.T.hermitian_line_bundle_smooth : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → Geo.IsSmoothHerm A := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep | exact GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep <;> assumption)
end
