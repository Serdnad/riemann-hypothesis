module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardPreimageHom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle070
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle067
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle133
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.Bundle001
import GroundTheory.PAdicHodge.ACrisBdRGalois
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle497
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Mathlib.RingTheory.Flat.TorsionFree
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG GlobalTheory.CompanionTheory.RealCount.InjHw

namespace GlobalTheory.CompanionTheory.RealCountG.WtInt

variable {n : ℕ}

theorem expU_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    expU X hX (s + t) = expU X hX s * expU X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl X).smul_left _).smul_right _

theorem expU_two_pi (a : Fin n) (hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I)) :
    expU (Matrix.single a a Complex.I) hX (2 * Real.pi) = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ)) = 1
  have e : (((2 * Real.pi : ℝ) : ℂ)) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
      diagonal (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hc : i = a
      · subst hc
        simp
      · simp [Matrix.single_apply, hc, Ne.symm hc]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
        if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
  rw [e, Matrix.exp_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext c
  have hh : NormedSpace.exp (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) c =
      if c = a then Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) else 1 := by
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  rw [hh]
  have h2 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    push_cast
    exact Complex.exp_two_pi_mul_I
  rw [h2]
  simp

theorem eigen_int (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H)
    (hd : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H,
      HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0)
    (a : Fin n) (r : ℝ) {v : H} (hv : v ≠ 0) (hr : G a a v = (r : ℂ) • v) : ∃ m : ℤ, r = m := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  set X : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a Complex.I with hXdef
  set φ : ℝ → H := fun s => ρ (expU X hX s) v with hφ
  have hd0 : HasDerivAt φ ((Complex.I * r) • v) 0 := by
    have := hd X (expU X hX) hX (fun _ => rfl) v
    have e := sum_single (Kf := G) v a a Complex.I
    rw [← hXdef] at e
    rw [e, hr, smul_smul] at this
    exact this
  have hstep : ∀ s, HasDerivAt φ ((Complex.I * r) • φ s) s := by
    intro s
    let L : H →L[ℝ] H := (ρ (expU X hX s)).restrictScalars ℝ
    have hL : ∀ y, L y = ρ (expU X hX s) y := fun _ => rfl
    have h1 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hd0
    have h2 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) (s - s) := by
      rwa [sub_self]
    have h3 := h2.comp_sub_const s s
    have e : (fun t => L (φ (t - s))) = φ := by
      funext t
      have : expU X hX t = expU X hX s * expU X hX (t - s) := by
        rw [← expU_add]
        congr 1
        ring
      simp only [hL, hφ, this, map_mul, ContinuousLinearMap.mul_apply]
    rw [e] at h3
    have e2 : L ((Complex.I * r) • v) = (Complex.I * r) • φ s := by
      rw [hL, map_smul]
    rwa [e2] at h3
  set ψ : ℝ → H := fun s => Complex.exp ((s : ℂ) * (-(Complex.I * r))) • φ s with hψ
  have hψd : ∀ s, HasDerivAt ψ 0 s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(Complex.I * r))) (-(Complex.I * r)) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (-(Complex.I * (r : ℂ)))
    have h2 := h1.cexp
    have h3 := h2.smul (hstep s)
    have : Complex.exp ((s : ℂ) * (-(Complex.I * r))) • (Complex.I * r) • φ s +
        (Complex.exp ((s : ℂ) * (-(Complex.I * r))) * -(Complex.I * r)) • φ s = 0 := by
      rw [smul_smul, ← add_smul]
      simp
    rw [this] at h3
    exact h3
  have hconst : ψ (2 * Real.pi) = ψ 0 :=
    is_const_of_deriv_eq_zero (fun s => (hψd s).differentiableAt) (fun s => (hψd s).deriv) _ _
  have h0 : φ 0 = v := by
    have : expU X hX 0 = 1 := by
      apply Subtype.ext
      show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
      simp
    simp [hφ, this]
  have h2π : φ (2 * Real.pi) = v := by
    show ρ (expU X hX (2 * Real.pi)) v = v
    rw [show expU X hX (2 * Real.pi) = 1 from expU_two_pi a hX, map_one]
    rfl
  have hE : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v = v := by
    have b : ψ 0 = v := by simp [hψ, h0]
    have a' : ψ (2 * Real.pi) = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v := by
      show Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • φ (2 * Real.pi) = _
      rw [h2π]
    rw [← a', hconst, b]
  have hE1 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) = 1 := by
    have : (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) - 1) • v = 0 := by
      rw [sub_smul, hE, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hv
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hE1
  refine ⟨-m, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h5 : (r : ℂ) = ((-m : ℤ) : ℂ) := by
    push_cast at hm ⊢
    have h6 : (2 * (Real.pi : ℂ) * Complex.I) * ((r : ℂ) + m) = 0 := by
      linear_combination -hm
    have h7 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have := (mul_eq_zero.1 h6).resolve_left h7
    linear_combination this
  exact_mod_cast h5

theorem weight_integral : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (μ : Fin n → ℝ) (v : H), v ≠ 0 → Formalism.REAL.IsWeight G μ v → ∃ ν : Fin n → ℤ, μ = wtR ν := by
  intro n H _ _ _ ρ G hd μ v hv hw
  choose ν hν using fun a => eigen_int H ρ G hd a (μ a) hv (hw a)
  exact ⟨ν, funext hν⟩

end GlobalTheory.CompanionTheory.RealCountG.WtInt
end
end

section

noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD GlobalTheory.ThetaPull GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.DualSm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem map_invT {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  apply Units.ext
  ext i j
  change p ((g⁻¹).val j i) = (GeneralLinearGroup.map p g)⁻¹.val j i
  rw [← map_inv]
  rfl

theorem invA_infGL (y : GL (Fin a) (Cinf E)) :
    invA E a (infGL E a y) = infGL E a (invT a (Cinf E) y) :=
  ga_ext (by rw [invA, map_invT, pInf_infGL, pInf_infGL])
    (by rw [invA, map_invT, pFin_infGL, pFin_infGL, map_one])


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
def trL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᵀ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }


omit [_root_.NumberField.IsTotallyComplex E] in
theorem toL_invT (y : GL (Fin a) (Cinf E)) : toL (invT a (Cinf E) y).val = trL (invL (toL y.val)) := by
  change toL ((y⁻¹).val)ᵀ = toL (Matrix.of (toL (Matrix.of (toL y.val))⁻¹))ᵀ
  rw [Matrix.coe_units_inv]
  rfl

theorem chart_dual (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => star (φ (invA E a g))) g x = star (chart φ (invA E a g) (trL (invL x))) ∧
      trL (invL x) ∈ invSet E a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_invT, chart_val, chart_val, map_mul, invA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

theorem conj_invA_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) :
    (fun g => star (φ (invA E a g))) ∈ Sm E a := fun g =>
  (Complex.conjCLE.contDiff.comp_contDiffOn ((hφ (invA E a g)).comp
    (fun x hx => (trL.contDiff.contDiffAt.comp x (invL_smooth.1 x hx)).contDiffWithinAt)
    fun _ hx => (chart_dual φ g hx).2)).congr fun _ hx => (chart_dual φ g hx).1

end GlobalTheory.CompanionTheory.DualSm

end
end

section

noncomputable section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.LocalDens Filter Topology Polynomial

namespace GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries

variable {R : Type} [CommRing R]

theorem densAt_succ {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T) (b : ℕ) :
    densAt σ ϖ S T (0 + b + 1) = densAt σ ϖ S T (0 + b + 1 + 1) := by
  obtain ⟨hTc, hdet⟩ := hT
  obtain ⟨c, hc⟩ : ∃ c, c * T.det = ϖ ^ 0 := by
    obtain ⟨w, hw⟩ := hdet.exists_left_inv
    exact ⟨w, by simpa using hw⟩
  have hσ := hU.fix_ϖ
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => finite_lev (by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hU.card]
    exact pow_ne_zero _ (by have := hU.one_lt; omega)) k
  have h1 : T * (c • T.adjugate) = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc]
  have h2 : cT σ (c • T.adjugate) * T = ϖ ^ 0 • (1 : Matrix (Fin n) (Fin n) R) := by
    have := congrArg (cT σ) h1
    rw [cT_mul, hTc, cT_smul σ (ϖ ^ 0), cT_one, map_pow, hσ] at this
    exact this
  obtain ⟨t, ht⟩ : ∃ t, t + σ t = 1 := by
    obtain ⟨u, hu, -⟩ := hU.basis
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h3 : (u - σ u) * σ w = -1 := by
      have := congrArg σ hw
      simp only [map_mul, map_sub, hU.inv, map_one] at this
      linear_combination -this
    have h4 : σ w = -w := by linear_combination (-σ w) * hw + w * h3
    refine ⟨u * w, ?_⟩
    rw [map_mul, h4]
    linear_combination hw
  refine dens_step hfin hU.inv hσ S T _ hS.1 hTc (fun h hh hk => ?_)
  rw [red_eq_iff] at hk
  choose C hC using hk
  have hhT : h = T + ϖ ^ (0 + b + 1) • Matrix.of C := by
    ext i j
    have := hC i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hCh : cT σ (Matrix.of C) = Matrix.of C := by
    ext i j
    have e1 := congrFun (congrFun (hh) i) j
    have e2 := congrArg σ (hC j i)
    have e3 := congrFun (congrFun hTc i) j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at e1 e3
    simp only [map_sub, map_mul, map_pow, hσ, e1, e3] at e2
    have := (hU.reg.pow (0 + b + 1)) (a₁ := σ (C j i)) (a₂ := C i j) (by
      simp only [smul_eq_mul]
      rw [← e2, hC i j])
    simpa [cT] using this
  obtain ⟨g, h', hgh, hhg, hg⟩ := _root_.GlobalTheory.CompanionTheory.LocalDens.twist hσ ht hCh 0 b h1 h2
  rw [← hhT] at hg
  rw [solCount_eq, ← sol_congr σ ϖ S _ hg, ← solCount_eq]
  exact solCount_congr hσ S T g h' _ hgh hhg

theorem densAt_eq_densAt_one_of_isUnimod {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    (k : ℕ) (hk : 1 ≤ k) : densAt σ ϖ S T k = densAt σ ϖ S T 1 := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    obtain ⟨b, rfl⟩ : ∃ b, k = 0 + b + 1 := ⟨k - 1, by omega⟩
    rw [← densAt_succ hU S T hS hT b, ih]

theorem densAt_eq_of_isDens {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hU : IsUnrQuad R σ ϖ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : IsUnimod σ S) (hT : IsUnimod σ T)
    {α : ℝ} (hα : IsDens σ ϖ S T α) (k : ℕ) (hk : 1 ≤ k) : densAt σ ϖ S T k = α := by
  have h1 : Tendsto (densAt σ ϖ S T) atTop (𝓝 (densAt σ ϖ S T 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (densAt_eq_densAt_one_of_isUnimod hU S T hS hT j hj).symm
  rw [densAt_eq_densAt_one_of_isUnimod hU S T hS hT k hk]
  exact tendsto_nhds_unique h1 hα

theorem isUnimod_one (σ : R →+* R) (m : ℕ) : IsUnimod σ (1 : Matrix (Fin m) (Fin m) R) :=
  ⟨cT_one σ, by simp⟩

theorem unrPoly : PositivityTheory.PfSWUS.Loc.UnrFormula → PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := by
  intro hF R _ σ ϖ q ε hR ψ hψ n T hT k hk t
  classical
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => finite_lev (by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hR.card]
    exact pow_ne_zero _ (by have := hR.one_lt; omega)) k
  letI : ∀ k, Fintype (R ⧸ lev ϖ k) := fun k => Fintype.ofFinite _
  haveI : Finite (Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :=
    inferInstanceAs (Finite (Fin n → Fin n → R ⧸ lev ϖ k))
  haveI : Finite (hermMod σ ϖ n k) := Subtype.finite
  letI : Fintype (hermMod σ ϖ n k) := Fintype.ofFinite _
  have hq1 : 1 < q := hR.one_lt
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hε : (ε : ℂ) ^ 2 = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hnε : ‖(ε : ℂ)‖ = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  let P : ℂ[X] := ∑ B : hermMod σ ϖ n k,
    C (ψ k (Matrix.trace (red ϖ k T * B.1))) * X ^ Nat.log (q ^ 2) (nuAt ϖ B.1)
  let Q : ℂ[X] := ∏ i : Fin n, (1 - X * C (((ε : ℂ) * q) ^ (i : ℕ)))
  have hP : ∀ x : ℂ, P.eval x = ∑' B : hermMod σ ϖ n k,
      ψ k (Matrix.trace (red ϖ k T * B.1)) * x ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    intro x
    rw [tsum_fintype]
    simp [P, Polynomial.eval_finsetSum]
  have hQ : ∀ x : ℂ, Q.eval x = ∏ i : Fin n, (1 - x * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    intro x
    simp [Q, Polynomial.eval_prod]
  have hval : ∀ m, n ≤ m → P.eval (((ε : ℂ) / q) ^ m) = Q.eval (((ε : ℂ) / q) ^ m) := by
    intro m hm
    have hS := isUnimod_one σ m
    have hs : siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ (1 : Matrix (Fin m) (Fin m) R) T k : ℝ) : ℂ) :=
      GlobalTheory.CompanionTheory.SiegLoc.level_identity R σ ϖ q ε hR ψ hψ m n k 1 T hS.1 hT.1
        (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod R σ ϖ q ε hR ψ hψ n k)
        (fun B hB => GlobalTheory.CompanionTheory.SiegLoc.gauss_full hR hψ hε k 1 hS B hB)
    have hc : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m := by
      rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [hP, hQ]
    unfold siegAt at hs
    rw [hc] at hs
    rw [hs, densAt_eq_of_isDens hR 1 T hS hT (hF R σ ϖ q ε hR m n hm 1 T hS hT) k hk]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ m := by have := i.2; omega
    have e1 : ((ε : ℂ) / q) ^ m = ((ε : ℂ) / q) ^ (m - (i : ℕ)) * ((ε : ℂ) / q) ^ (i : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    have e2 : ((ε : ℂ) / q) ^ (i : ℕ) * ((ε : ℂ) * q) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]
      have : (ε : ℂ) / q * ((ε : ℂ) * q) = 1 := by
        field_simp
        simpa using hε
      rw [this, one_pow]
    rw [e1, mul_assoc, e2, mul_one]
  have hinj : Function.Injective (fun j : ℕ => ((ε : ℂ) / q) ^ (n + j)) := by
    intro a b hab
    have h1 : ‖((ε : ℂ) / q) ^ (n + a)‖ = ‖((ε : ℂ) / q) ^ (n + b)‖ := congrArg norm hab
    have hnorm : ‖(ε : ℂ) / q‖ = (q : ℝ)⁻¹ := by
      rw [norm_div, hnε]
      simp
    rw [norm_pow, norm_pow, hnorm] at h1
    have hq0 : (0 : ℝ) < (q : ℝ)⁻¹ := by
      have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      positivity
    have hq2 : (q : ℝ)⁻¹ ≠ 1 := by
      have : (1 : ℝ) < q := by exact_mod_cast hq1
      exact (inv_lt_one_of_one_lt₀ this).ne
    have := pow_right_injective₀ hq0 hq2 h1
    omega
  have hPQ : P = Q := Polynomial.eq_of_infinite_eval_eq P Q
    (Set.infinite_of_injective_forall_mem hinj fun j => hval (n + j) (by omega))
  have := congrArg (Polynomial.eval t) hPQ
  rw [hP, hQ] at this
  exact this

end GlobalTheory.CompanionTheory.SiegLoc.UnimodSeries

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FlatW

theorem eq_zero_of_pow_mul_eq_zero {l : ℕ} [Fact l.Prime] (m : ℕ) {x : Acris l}
    (h : (l : Acris l) ^ m * x = 0) : x = 0 := by
  induction m with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply ACris.eq_zero_of_p_mul_eq_zero (K := ℂ_[l]) (p := l)
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem flat_AW {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) :
    Module.Flat (WittVector l r.k) (CrystallineSemistableComparison.Pb.AW r) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro a ha
  obtain ⟨⟨y, hy0⟩, hy⟩ := (Submodule.mem_torsion_iff _).1 ha
  have hne : y ≠ 0 := nonZeroDivisors.ne_zero hy0
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' y hne
  have hu : IsUnit (r.w (b : WittVector l r.k)) := b.isUnit.map r.w
  have key : ∀ x : Acris l, r.w y * x = 0 → x = 0 := by
    intro x h
    rw [e, map_mul, map_pow, map_natCast] at h
    apply eq_zero_of_pow_mul_eq_zero m
    apply hu.mul_right_eq_zero.1
    linear_combination h
  exact (Submodule.mem_bot _).2 (key a hy)

end GlobalTheory.CompanionTheory.FlatW
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

theorem _root_.GlobalTheory.T.flat_thickening_quotient : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (n : ℕ) (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))), FlatT T → FlatT (qT hn T) := by
  first | exact @GlobalTheory.CompanionTheory.FlatThick.flatT_qT | exact GlobalTheory.CompanionTheory.FlatThick.flatT_qT | (intros; apply GlobalTheory.CompanionTheory.FlatThick.flatT_qT <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

theorem _root_.GlobalTheory.T.witt_level_morphism_cover_compat : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (n : ℕ) (c : WittVector l k) (m : QMor (sW l (B.schFn q) ρ n) (sW l (B.schFn q) ρ (n + 1)) (IdF.span _ c)) (hG : ∀ (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory), stF q ρ n 𝒱 (m.G.obj ⟨T.obj, T.property.1⟩).obj), (∀ S : Finset U.ι, S.Nonempty → ∀ j, Function.Bijective (((subQ m (stF q ρ n {⨅ α ∈ S, U.U α}) (stF q ρ (n + 1) {⨅ α ∈ S, U.U α}) (fun _ h => h.1) (hG _)).o (IdF.span _ c) (fun _ => le_rfl)).pull j)) → ∀ j, Function.Bijective (((subQ m (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1) (hG _)).o (IdF.span _ c) (fun _ => le_rfl)).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.FlatCoverGlue.glue | exact GlobalTheory.CompanionTheory.FlatCoverGlue.glue | (intros; apply GlobalTheory.CompanionTheory.FlatCoverGlue.glue <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

theorem _root_.GlobalTheory.T.witt_site_restrict_bijective : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resV q ρ m 𝒱).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.FlatZar.resV_bij | exact GlobalTheory.CompanionTheory.FlatZar.resV_bij | (intros; apply GlobalTheory.CompanionTheory.FlatZar.resV_bij <;> assumption)
end
