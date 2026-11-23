module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle602
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle442
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqZeroOfFourierCoefficientsVanish
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle018
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.CompanionTheory.HermPoisson

theorem hermCocompact (D : D7) (r : ℕ) :
    ∃ K : Set (hermA D r), IsCompact K ∧ ∀ x, ∃ l ∈ ratHerm D r, x - l ∈ K := by
  obtain ⟨-, K, hK, hKx⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := r)
  refine ⟨K, hK, fun x => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hKx x
  refine ⟨-γ, neg_mem hγ, ?_⟩
  rwa [sub_neg_eq_add, add_comm]




theorem hermFourierZero (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (lam : Measure (hermA D r)) (hH : lam.IsAddHaarMeasure) (𝓖 : Set (hermA D r))
    (h𝓖 : IsAddFundamentalDomain (ratHerm D r) 𝓖 lam) (φ : hermA D r → ℂ) (hφ : Continuous φ)
    (hper : ∀ x, ∀ l ∈ ratHerm D r, φ (x + l) = φ x)
    (hco : ∀ β : HermE D r,
      ∫ b in 𝓖, φ b * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) ∂lam = 0) :
    ∀ x, φ x = 0 := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) :=
    (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  haveI : Countable D.host.E := GlobalTheory.CompanionTheory.FourierComplete.countable_numberField D.host.E
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  have hmem : ∀ q : ratHerm D r, q.1.1 ∈ ratMx D r r := fun q => AddSubgroup.mem_comap.1 q.2
  haveI : Countable (ratHerm D r) := by
    choose g hg using fun q : ratHerm D r => mem_ratMx.1 (hmem q)
    exact Function.Injective.countable (f := g) fun a b h =>
      Subtype.ext (Subtype.ext (by rw [← hg a, ← hg b, h]))
  haveI := hH
  obtain ⟨K, hK, hc⟩ := hermCocompact D r
  intro x
  refine GlobalTheory.CompanionTheory.FourierComplete.eq_zero_of_coeffs_vanish (ratHerm D r) lam h𝓖 hK hc (T := ratHerm D r)
    (fun t b => chi ψ t.1.1 b) (fun t => continuous_chi hψ t.1.1) ?_ ?_ ?_ ?_ ?_ φ hφ hper ?_ x
  · intro t y l hl
    show chi ψ t.1.1 (y + l) = chi ψ t.1.1 y
    rw [chi_add_right, chi_rat hψ (hmem t) ⟨l, hl⟩, mul_one]
  · intro y
    exact chi_zero_left ψ y
  · intro s t y
    exact chi_add_left ψ s.1.1 t.1.1 y
  · intro t y
    show star (chi ψ t.1.1 y) = chi ψ (-t.1.1) y
    rw [chi_neg_left]
    exact star_psi' hψ _
  · intro a b hab
    refine rat_of_chi hψ (-a + b) fun t => ?_
    have h1 : chi ψ t.1.1 a * chi ψ t.1.1 (-a) = 1 := by
      rw [← chi_add_right, add_neg_cancel, chi_zero_right]
    rw [chi_add_right, ← hab t, mul_comm]
    exact h1
  · intro t
    obtain ⟨β, hβ⟩ := (ofHermE_bijective (D := D) (r := r)).2 t
    have h1 : ∀ b : hermA D r, chi ψ (-t).1.1 b =
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) := fun b => by
      show chi ψ (-t.1.1) b = _
      rw [chi_neg_left, ← hβ, ofHermE_val]
    simp only [h1]
    exact hco β

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}




theorem eval_aeval_subst {σ τ' : Type} (x : τ' → ℂ) (f : σ → MvPolynomial τ' ℂ) (p : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval f p) = MvPolynomial.eval (fun v => MvPolynomial.eval x (f v)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.eval_X]

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
  have hWe : ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  convert GlobalTheory.SchwartzBruhatTensor.coset_mem_SB (intW D m n) hWo hWc 0 using 1
  funext a
  unfold g0
  exact if_congr Iff.rfl rfl rfl

theorem gaussian_at_zero_eq_one (D : D7) (m n : ℕ) : g0 D m n 0 = 1 := by
  unfold g0
  split_ifs with h
  · rfl
  · exact (h ((QuotientAddGroup.eq_zero_iff (N := intW D m n) (0 : Matrix (Fin m) (Fin n) _)).2 (intW D m n).zero_mem)).elim

def psi0 (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : Mx D V.rank n → ℂ :=
  fun x => gAway V l s τ (fun τ => compAt θ τ x) * g0 D V.rank n (fun i j => finPart D (x i j))

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : psi0 θ V n l s τ ∈ awayA θ V n l s τ := by
  refine Submodule.subset_span ⟨1, g0 D V.rank n, gaussian_mem_schwartz_bruhat D V.rank n, ?_, ?_⟩
  · intro v hv
    simp at hv
  · funext x
    simp [psi0, evalPoly]

def xL (θ : InfFam D) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) : Mx D m n := lineAt θ τ Z 1

theorem compAt_xL {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) :
    (fun τ' => compAt θ τ' (xL θ τ Z)) = GlobalTheory.FockAnnKill.dirAt τ Z := by
  have h := GlobalTheory.FockAnnKill.compAt_add_lineAt hθ (0 : Mx D m n) τ Z 1
  simp only [zero_add] at h
  rw [xL, h]
  funext τ'
  have h0 : compAt θ τ' (0 : Mx D m n) = 0 := by
    ext i j
    simp [compAt]
  simp [h0]

theorem finPart_xL {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) :
    (fun i j => finPart D ((xL θ τ Z) i j)) = 0 := by
  have h := GlobalTheory.FockAnnKill.finPart_add_lineAt hθ (0 : Mx D m n) τ Z 1
  simp only [zero_add] at h
  rw [xL, h]
  funext i j
  simp

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section

noncomputable section

open scoped Matrix ComplexConjugate SchwartzMap ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

theorem diag_eq {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    (Mᴴ * A * M) j j = star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j) := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, Matrix.conjTranspose_apply, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

theorem tr_re_nonneg {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef) (M : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ (trace (Mᴴ * A * M)).re ∧ (M ≠ 0 → 0 < (trace (Mᴴ * A * M)).re) := by
  have hsum : (trace (Mᴴ * A * M)).re = ∑ j, (star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j)).re := by
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.diag_apply, diag_eq]
  have hnn : ∀ j, 0 ≤ (star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j)).re := by
    intro j
    by_cases hv : (fun a => M a j) = 0
    · rw [hv]
      simp
    · exact (hA.re_dotProduct_pos hv).le
  refine ⟨hsum ▸ Finset.sum_nonneg (fun j _ => hnn j), fun hM => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, (fun a => M a j) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hM
    ext a j
    exact congrFun (hc j) a
  rw [hsum]
  exact Finset.sum_pos' (fun j _ => hnn j) ⟨j, Finset.mem_univ _, hA.re_dotProduct_pos hj⟩

theorem tr_re_symm {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (M N : Matrix (Fin m) (Fin n) ℂ) :
    (trace (Mᴴ * A * N)).re = (trace (Nᴴ * A * M)).re := by
  have h : (Mᴴ * A * N)ᴴ = Nᴴ * A * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq,
      Matrix.mul_assoc]
  rw [← h, Matrix.trace_conjTranspose]
  simp

theorem tr_im_zero {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (M : Matrix (Fin m) (Fin n) ℂ) :
    trace (Mᴴ * A * M) = ((trace (Mᴴ * A * M)).re : ℂ) := by
  have h : star (trace (Mᴴ * A * M)) = trace (Mᴴ * A * M) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  have him : (trace (Mᴴ * A * M)).im = 0 := by
    have := congrArg Complex.im h
    simp at this
    linarith
  apply Complex.ext <;> simp [him]

section
variable {T : Type} [Fintype T] [DecidableEq T] {m n : ℕ} (τ : T)

def qf (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) (b b' : Bsp τ m n) : ℝ :=
  ∑ t : {τ' : T // τ' ≠ τ}, w t.1 * (trace ((of (b t))ᴴ * A t.1 * of (b' t))).re

def Qf (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) : LinearMap.BilinForm ℝ (Bsp τ m n) :=
  LinearMap.mk₂ ℝ (fun b b' => 2 * qf τ A w b b')
    (fun b₁ b₂ b' => by
      simp only [qf, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      congr 1
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.conjTranspose_add]
      rfl)
    (fun r b b' => by
      simp only [qf, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : (of ((r • b) t))ᴴ = (r : ℂ) • (of (b t))ᴴ := by
        rw [show of ((r • b) t) = (r : ℂ) • of (b t) from by ext i j; simp [Complex.real_smul]]
        rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
      rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring)
    (fun b b₁ b₂ => by
      simp only [qf, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      congr 1
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.mul_add]
      rfl)
    (fun r b b' => by
      simp only [qf, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : of ((r • b') t) = (r : ℂ) • of (b' t) := by ext i j; simp [Complex.real_smul]
      rw [this, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring)

theorem Qf_apply (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) (b b' : Bsp τ m n) :
    Qf τ A w b b' = 2 * qf τ A w b b' := rfl

theorem Qf_symm (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).IsHermitian) (w : T → ℝ)
    (b b' : Bsp τ m n) : Qf τ A w b b' = Qf τ A w b' b := by
  rw [Qf_apply, Qf_apply]
  congr 1
  unfold qf
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [tr_re_symm (hA t.1 t.2)]

theorem Qf_pos (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).PosDef) (w : T → ℝ)
    (hw : ∀ t, t ≠ τ → 0 < w t) (b : Bsp τ m n) (hb : b ≠ 0) : 0 < Qf τ A w b b := by
  rw [Qf_apply]
  have hnn : ∀ t : {τ' : T // τ' ≠ τ}, 0 ≤ w t.1 * (trace ((of (b t))ᴴ * A t.1 * of (b t))).re :=
    fun t => mul_nonneg (hw t.1 t.2).le (tr_re_nonneg (hA t.1 t.2) _).1
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hb (funext hc)
  have hof : of (b t) ≠ 0 := by
    intro h0
    apply ht
    funext i j
    exact congrFun (congrFun h0 i) j
  have hpos : 0 < qf τ A w b b :=
    Finset.sum_pos' (fun t _ => hnn t)
      ⟨t, Finset.mem_univ _, mul_pos (hw t.1 t.2) ((tr_re_nonneg (hA t.1 t.2) _).2 hof)⟩
  linarith

theorem exists_gauss (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).PosDef) (w : T → ℝ)
    (hw : ∀ t, t ≠ τ → 0 < w t) :
    ∃ G : 𝓢(Bsp τ m n, ℂ), ∀ b, G b = Complex.exp (-(Real.pi : ℂ) * ((2 * qf τ A w b b : ℝ) : ℂ)) := by
  obtain ⟨G, hG⟩ := GlobalTheory.ThK.EvAt0.GaussForm.exists_schwartz_gauss_form (Qf τ A w)
    (Qf_symm τ A (fun t ht => (hA t ht).isHermitian) w) (fun b hb => Qf_pos τ A hA w hw b hb)
  refine ⟨G, fun b => ?_⟩
  rw [(hG b).1, Qf_apply]

end

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end
