module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle003
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle010
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle017
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle008
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomLem8

theorem ev_col {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι ℂ) (hH : Γᴴ = Γ)
    (h2 : Γ * Γ = 1) (R : BranchingSupport.Rep k r) (x : ι → R.H) (e : ι) :
    ev Γ R (fun c => Γ c e) x = x e := by
  unfold ev
  rw [Finset.sum_comm]
  have key : ∀ j, ∑ i, (star (Γ i e) * Γ i j) = if e = j then 1 else 0 := by
    intro j
    have h := congrFun (congrFun h2 e) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (Γ i e) = Γ e i := by
      have := congrFun (congrFun hH e) i
      rwa [Matrix.conjTranspose_apply] at this
    rw [this]
  simp_rw [← Finset.sum_smul, key]
  simp

theorem transpose_unitary {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι ℂ) (hH : Γᴴ = Γ)
    (h2 : Γ * Γ = 1) : Γᵀ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have : (Γᵀ)ᴴ = Γᵀ := by
    rw [show (Γᵀ)ᴴ = (Γᴴ)ᵀ from rfl, hH]
  rw [this, ← Matrix.transpose_mul, h2, Matrix.transpose_one]

theorem div_step (b t : ℝ) (ht : 0 ≤ t) (L : ℝ≥0∞)
    (h : ENNReal.ofReal (b * t * t) ≤ L * ENNReal.ofReal t) : ENNReal.ofReal (b * t) ≤ L := by
  rcases ht.eq_or_lt with h0 | h0
  · simp [← h0]
  · rw [ENNReal.ofReal_mul' ht] at h
    exact (ENNReal.mul_le_mul_iff_left (by simpa using h0) ENNReal.ofReal_ne_top).1 h

theorem moment_lemma_pieri : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ENNReal.ofReal (‖β I‖ ^ 2 * ‖y‖ ^ 2) ≤ ∫⁻ x, ENNReal.ofReal ((∑ i, ‖(ρ (Matrix.of x)⁻¹ *ᵥ om) i‖ ^ 2) * ‖BI I ((RI I).σ (Matrix.of x) y)‖ ^ 2) ∂νq := by
  intro hy k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ z π u μW μN μG νq om Bm BI β hR hRI hinj hρ hT
    hS hB hBI hβ I hI y hy'
  have hK : PI.KFinSmooth := hy.1.2.2.1
  obtain ⟨hadj, -, hev, hnorm, -⟩ :=
    GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hρ hT
  obtain ⟨hae, hcont, -, hmB⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hR hS
  obtain ⟨-, -, -, hmI⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (hRI I) hS
  have hf := hmI (BI I) hI.1 y hy'
  have hH := hρ.1
  have h2 := hρ.2.1
  have hc := hρ.2.2.2.2.2.1
  have hph : ∀ e, AEStronglyMeasurable
      (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ fun c => Γ c e) om) νq := by
    intro e
    refine hcont ℂ (fun g => Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ fun c => Γ c e) om) ?_
    simp only [Formalism.QuantumDeterminants.herm, dotProduct, Matrix.mulVec]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
    refine continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ?_
    exact continuousOn_finsetSum _ fun l _ => (hc j l).mul continuousOn_const
  have hstep : ∀ e, ENNReal.ofReal (‖β I‖ ^ 2 * ‖io I e y‖ ^ 2) ≤
      ∫⁻ x, ENNReal.ofReal (‖Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ fun c => Γ c e) om‖ ^ 2 *
        ‖BI I ((RI I).σ (Matrix.of x) y)‖ ^ 2) ∂νq := by
    intro e
    have hw : io I e y ∈ R.sm := (hT.raw.io_sm I e).mem y hy'
    have hpair := GlobalTheory.T.tensor_moment_transfer hy k r ι κ ρ Γ d R RI io pr ε mu muI Wp z π u μW μN μG νq om Bm BI β hR hRI hinj
      hT.raw hS hB.1 hBI hβ I hI y hy' (fun c => Γ c e) (io I e y) hw
    have hcs := GlobalTheory.T.norm_sq_integral_inner_weight_le (Formalism.QuantumDeterminants.Mt k r) Wp νq _ _ _ hf (hmB Bm hB.1 _ hw) (hph e)
    rw [hpair] at hcs
    have hiso := hB.2 _ hw
    have hg : ∫⁻ x, ENNReal.ofReal (‖Bm (R.σ (Matrix.of x) (io I e y))‖ ^ 2) ∂νq =
        ENNReal.ofReal (‖io I e y‖ ^ 2) := by
      rw [← hiso]
      unfold PI.BesselPeriodGGP.l2SG
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl
    rw [hg] at hcs
    have h1 := hadj I y hy' (tm R (fun c => Γ c e) (io I e y)) (fun c => R.smSub.smul_mem _ hw)
    rw [hev, ev_col Γ hH h2] at h1
    have h3 : ‖⟪y, ∑ c, pr I c (tm R (fun c => Γ c e) (io I e y) c)⟫_ℂ‖ = ‖io I e y‖ ^ 2 := by
      rw [norm_inner_symm]
      have h4 := congrArg norm h1
      have hep : ‖(ep I : ℂ)‖ = 1 := by
        rcases hT.ep_sq I with h | h <;> simp [h]
      rw [norm_mul, hep, one_mul, inner_self_eq_norm_sq_to_K] at h4
      rw [← h4]
      simp
    rw [norm_mul, h3] at hcs
    refine div_step _ _ (by positivity) _ ?_
    convert hcs using 2
    ring
  have hsum : ENNReal.ofReal (‖β I‖ ^ 2 * ‖y‖ ^ 2) ≤ ∑ e, ENNReal.ofReal (‖β I‖ ^ 2 * ‖io I e y‖ ^ 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity), ← Finset.mul_sum]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hnorm I y hy') (by positivity))
  refine hsum.trans ((Finset.sum_le_sum fun e _ => hstep e).trans (le_of_eq ?_))
  rw [← lintegral_finsetSum']
  · refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity), ← Finset.sum_mul]
    have := GlobalTheory.T.sum_norm_sq_herm_translates_orthonormal k r ι ρ Γ Γᵀ d om hρ (transpose_unitary Γ hH h2) _ hx
    rw [← this]
    rfl
  · intro e _
    exact (((hph e).norm.aemeasurable.pow_const 2).mul (hf.norm.aemeasurable.pow_const 2)).ennreal_ofReal

end GlobalTheory.MomLem8
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.bessel_integral_equivariant_of_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (g * m) w) v = Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  first | exact @GlobalTheory.BesselEquiv.be_equivariant | exact GlobalTheory.BesselEquiv.be_equivariant | (intros; apply GlobalTheory.BesselEquiv.be_equivariant <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.bessel_gap_pairing : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (w + w') v = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w' v ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (a • w) v = a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, ∀ v' ∈ R.TK, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (v + v') = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v' ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (a • v) = star a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v := by
  first | exact @GlobalTheory.besselIntegral_sesquilinear | exact GlobalTheory.besselIntegral_sesquilinear | (intros; apply GlobalTheory.besselIntegral_sesquilinear <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.coefficient_psi_pairing_eq_iterated_integral : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ ξ : Wp, ((‖be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ‖ ^ 2 : ℝ) : ℂ) = ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, (∫ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r, ⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star ⟪v, R.σ (Matrix.of q.1 * Matrix.of q.2 * (Matrix.of p.1 * Matrix.of p.2)) w⟫_ℂ * (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of q.2) * ⟪π (Matrix.of q.1)⁻¹ ξ, ξ⟫_ℂ) ∂(μW.prod μN)) ∂(μW.prod μN) := by
  first | exact @GlobalTheory.bessel_norm_sq_double_integral | exact GlobalTheory.bessel_norm_sq_double_integral | (intros; apply GlobalTheory.bessel_norm_sq_double_integral <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPieri

theorem gg_mul {k r : ℕ} {a b : Mx k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem one_gg (k r : ℕ) : (1 : Mx k r) ∈ GG k r := by
  show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem one_N (k r : ℕ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
  ⟨one_gg k r, fun _ _ _ => Matrix.one_apply, fun _ _ _ _ _ => Matrix.one_apply⟩

theorem one_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z :=
  ⟨one_gg k r, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩

theorem herm_iso {ι : Type} [Fintype ι] [DecidableEq ι] {Γ A : Matrix ι ι ℂ} (hA : Aᴴ * Γ * A = Γ) (x y : ι → ℂ) :
    Formalism.QuantumDeterminants.herm Γ (A *ᵥ x) (A *ᵥ y) = Formalism.QuantumDeterminants.herm Γ x y := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

theorem coef_inv {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ}
    {d : ℕ} (hρ : IsFRep ρ Γ d) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {om om' : ι → ℂ}
    (h1 : ∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) (h2 : ∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om')
    {γ : Mx k r} (hγ : γ ∈ GG k r) (p : B.SS k r) (hp : D.inSS p) :
    Formalism.QuantumDeterminants.herm Γ (ρ (B.sgs p γ) *ᵥ om') om = Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  obtain ⟨-, -, -, hmul, hiso, -⟩ := hρ
  have hi := PI.MirrorSection₂.uw_inv hh
  have ni := PI.MirrorSection₂.n_inv hn
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GG k r := gg_mul hi.1 ni.1
  have e1 := h1 _ ⟨_, hi, _, ni, rfl⟩
  have e2 : ρ (Matrix.of p.2.1) *ᵥ om' = om' := h2 _ ⟨_, hh', 1, one_N k r, (Matrix.mul_one _).symm⟩
  have e3 : ρ (Matrix.of p.2.2) *ᵥ om' = om' := h2 _ ⟨1, one_UW k r _, _, hn', (Matrix.one_mul _).symm⟩
  unfold B.sgs
  rw [hmul _ (gg_mul (gg_mul ha hγ) hn'.1) _ hh'.1, hmul _ (gg_mul ha hγ) _ hn'.1, hmul _ ha _ hγ,
    ← mulVec_mulVec, e2, ← mulVec_mulVec, e3, ← mulVec_mulVec]
  conv_lhs => rw [← e1]
  exact herm_iso (hiso _ ha) _ _

theorem pieri_bessel : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) (FI : κ → Mx k r → (Wq →L[ℂ] Wp)) (sI τ : κ → ℂ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → (∀ I, (RI I).IsDG ε (muI I) ∧ Formalism.QuantumDeterminants.GapAtLeast ε (muI I) h) → GapOK k r h → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om') → (∀ I, IsBeL (RI I) D.z D.π D.μW D.μN (lI I) ∧ IsBeL (RI I) D.z' D.π' D.μW' D.μN (lI' I)) → IsCoef R l l' F s → (∀ I, ((¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) ∧ τ I = 0) ∨ (IsCoef (RI I) (lI I) (lI' I) (FI I) (sI I) ∧ sI I ≠ 0 ∧ ∃ κ₀ κ₁ : ℂ, (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) ∧ τ I = (ep I : ℂ) * κ₁ * star κ₀ * s / sI I)) → ∀ γ ∈ JF.Om k r D.z D.z', Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om • B.JF D F γ = ∑ I, τ I • B.JF D (FI I) γ := by
  intro H k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI h Wp _ _ _ _ Wq _ _ _ _ D om om' l l' lI lI' F s FI sI τ
    hR _ hRI hgap hρ hT h1 h2 hBe hF hτ γ hγ
  have hγG : γ ∈ GG k r := hγ.1
  obtain ⟨Ft, st, hFt, hsum, hz, hst⟩ := GlobalTheory.T.tensor_weighted_bessel_sum H.1.2.2.1 k r ι κ ρ Γ d R RI io pr ep ε mu muI Wp Wq om om'
    l l' lI lI' F s hR (fun I => (hRI I).1) hρ hT hF
  obtain ⟨hloc, hfac, hfin, -⟩ := GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum k r Wp Wq D γ hγG
  have hOO := fun I => GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul H k r ε (muI I) h (RI I) Wp Wq D (lI I) (lI' I) (hRI I).1 (hRI I).2 hgap
    (hBe I).1 (hBe I).2
  choose OO hOO using hOO
  rw [← hfac (fun g => Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om) F (fun p hp => coef_inv hρ D h1 h2 hγG p hp),
    (hloc _ (fun g => ∑ I, Ft I g) hsum).1, hfin κ Ft (fun I => (hOO I _ _ (hFt I) γ hγ).1)]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [(hOO I _ _ (hFt I) γ hγ).2]
  rcases hτ I with ⟨hn, h0⟩ | ⟨hc, hs, κ₀, κ₁, a0, a1, ht⟩
  · rw [hz I hn, h0, zero_smul, zero_smul]
  · rw [(hOO I _ _ hc γ hγ).2, hst I κ₀ κ₁ a0 a1, ht, smul_smul, div_mul_cancel₀ _ hs]

end GlobalTheory.BesselPieri
end Gp91
end
