module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle005
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntTens
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle010
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.USideA
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement

@[expose] public section

section

noncomputable section

namespace Formalism.L2.KerInert.OrthonormalJets

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem smulLat_star {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (h : star γ * γ = 1)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    SDLat.smulLat (star γ) (SDLat.smulLat γ M) = M := by
  ext x
  rw [PullbackComparison.mem_smulLat]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (PullbackComparison.mem_smulLat γ M y).1 hy
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    exact hz
  · intro hx
    refine ⟨γ.mulVec x, (PullbackComparison.mem_smulLat γ M _).2 ⟨x, hx, rfl⟩, ?_⟩
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem locBasis_push {N N' r : ℕ} (p : ℕ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (h1 : γ * star γ = 1) (h2 : star γ * γ = 1)
    (h3 : γ' * star γ' = 1) (h4 : star γ' * γ' = 1) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : LocBasis D p (YYl D M M') b) :
    LocBasis D p (YYl D (SDLat.smulLat γ M) (SDLat.smulLat γ' M')) (fun i => γ' * b i * star γ) := by
  have hb' : LocBasis D p (YYl D (SDLat.smulLat (star γ) (SDLat.smulLat γ M))
      (SDLat.smulLat (star γ') (SDLat.smulLat γ' M'))) b := by
    rw [smulLat_star γ h2, smulLat_star γ' h4]
    exact hb
  have := PullbackComparison.locBasis_pull p (star γ) (star γ') (by rw [star_star]; exact h2) (by rw [star_star]; exact h1)
    (by rw [star_star]; exact h4) (by rw [star_star]; exact h3) (SDLat.smulLat γ M) (SDLat.smulLat γ' M') b hb'
  simpa only [star_star] using this

theorem ortho_push {N N' r : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (h2 : star γ * γ = 1) (h4 : star γ' * γ' = 1)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : Orthonormal D b) :
    Orthonormal D (fun i => γ' * b i * star γ) := by
  have := PullbackComparison.ortho_pull (star γ) (star γ') (by rw [star_star]; exact h2) (by rw [star_star]; exact h4) b hb
  simpa only [star_star] using this

end Formalism.L2.KerInert.OrthonormalJets

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker OrthonormalJets

theorem orthBasisExists_of (hG : GlobONB) (hW : WeakApprox) : OrthBasisExists := by
  intro D p _ hp5 hin N N' L L' hA
  obtain ⟨n, rfl⟩ := hA.1
  obtain ⟨n', rfl⟩ := hA.2.1
  have hQ : Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  let lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p] :=
    (IsAlgClosed.lift (R := ℚ) (S := Formalism.MainNotions.TaylorLogMetric.Qbar) (M := ℂ_[p])).toRingHom
  obtain ⟨r, b, hloc, hon, -⟩ := hG D p hp5 hin lam
  have hlocN := IntTens.locBasis_bB (IntTens.eTwo n') (IntTens.eTwo n) p b hloc
  have honN := IntTens.orth_bB (IntTens.eTwo n') (IntTens.eTwo n) b hon
  obtain ⟨γ, γ', M, M', -, hM, hM', rfl, rfl⟩ := hW D p hp5 hin _ _ L L' hA
  have hlocM := (pairing_fact D ⊥ 0 p _ _ _ M _ M' hM hM').1 _ _ hlocN
  letI := D.host.cmStar
  have h1 : (γ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) * star (γ : Matrix _ _ D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 γ.2
  have h2 : star (γ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) * (γ : Matrix _ _ D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 γ.2
  have h3 : (γ' : Matrix (Fin (n' + n')) (Fin (n' + n')) D.host.E) * star (γ' : Matrix _ _ D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 γ'.2
  have h4 : star (γ' : Matrix (Fin (n' + n')) (Fin (n' + n')) D.host.E) * (γ' : Matrix _ _ D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 γ'.2
  exact ⟨_, _, locBasis_push p _ _ h1 h2 h3 h4 M M' _ hlocM, ortho_push _ _ h2 h4 _ honN⟩

end Formalism.L2.KerInert
end
end

section

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

theorem eFac_ne_zero {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    Y.eS j La * (Y.eT j La')⁻¹ ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_) <;>
  · refine Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ ?_
    have hs := X.G.P.setting v
    haveI := hs.frac_alt
    have h1 : ((p : ℕ) : X.G.P.W v) ≠ 0 := hs.p_unif.ne_zero
    have h2 : ((p : ℕ) : X.G.P.Qq v) ≠ 0 := by
      rw [← map_natCast (algebraMap (X.G.P.W v) (X.G.P.Qq v))]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr h1
    rw [← map_natCast (X.G.P.ι v)]
    exact (map_ne_zero _).mpr h2

theorem series_compatibility_of : TieSerOf := by
  intro p _ X Y j La _ c' L' _
  unfold srOf
  rw [smul_smul, inv_mul_cancel₀ (eFac_ne_zero Y j La (c', L')), one_smul]

end Formalism.L2.KerInert.SecondKernelSeries
end
end

section

noncomputable section

namespace Formalism.L2.KerInert

namespace JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Good

variable {p : ℕ} [Fact p.Prime] {σ ι : Type*}

variable (δ : ι → MvPowerSeries σ ℂ_[p] →+ MvPowerSeries σ ℂ_[p])

def Wd (l : List ι) (G : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  l.foldr (fun j H => δ j H) G

def Good (G : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ l : List ι, IsIntP (MvPowerSeries.constantCoeff (Wd δ l G))

variable {δ}

end Good

section Ring

variable {p : ℕ} [Fact p.Prime]

end Ring

section Deriv

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

end Deriv

section Chain

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Chain

section Lin

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem test_vector_mem_schwartz_bruhat (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map D.host.φ₀.toRatAlgHom

theorem isPadicIntegral_lamC_K (c : 𝓞 D.host.K) : IsIntP (lamC lam (D.host.φ₀ ((c : D.host.K) : D.host.E))) := by
  have hI : IsIntegral ℤ ((c : D.host.K) : D.host.E) :=
    map_isIntegral_int (algebraMap D.host.K D.host.E) (NumberField.RingOfIntegers.isIntegral_coe c)
  unfold lamC
  rw [dite_eq_left (test_vector_mem_schwartz_bruhat _)]
  exact RestC.norm_le_one_of_int (map_isIntegral_int (lam.comp (D.host.φ₀.codRestrict Qbar test_vector_mem_schwartz_bruhat)) hI)

variable (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

end Lin

section Core

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end Core

section Log

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {p : ℕ} [Fact p.Prime]

end Log

end JetIntegrality

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

end Formalism.L2.KerInert
end
end

section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

namespace ParameterChangeLemmas

open IntegralOrthonormalChange

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_inVar_eq_zero {σ : Type*} (i : σ) (f : PowerSeries ℂ_[p]) (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) f hf

theorem integral_subst_single_variable {σ : Type*} (i : σ) (f : PowerSeries ℂ_[p]) (hf : ∀ n, IsIntP (PowerSeries.coeff n f)) :
    IntegralMv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) := by
  intro n
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · exact hf _
  · show ‖(0 : ℂ_[p])‖ ≤ 1
    simp

theorem integral_prod {σ ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ ℂ_[p])
    (hf : ∀ i ∈ s, IntegralMv (f i)) : IntegralMv (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f IntegralMv (fun a b ha hb => IntegralOrthonormalChange.integral_mul ha hb) ?_ hf
  intro n
  show ‖MvPowerSeries.coeff n (1 : MvPowerSeries σ ℂ_[p])‖ ≤ 1
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem subst_single_var {σ τ : Type*} (S : σ → MvPowerSeries τ ℂ_[p]) (hS : MvPowerSeries.HasSubst S)
    (f : PowerSeries ℂ_[p]) (i : σ) :
    MvPowerSeries.subst S (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) =
      PowerSeries.subst (S i) f := by
  have hX : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p])) :=
    (PowerSeries.HasSubst.X i).const
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hX hS, PowerSeries.subst]
  congr 1
  funext _
  exact MvPowerSeries.subst_X hS i

theorem subst_inv {σ : Type*} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries ℂ_[p]) : PowerSeries.subst a f⁻¹ = (PowerSeries.subst a f)⁻¹ := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  by_cases hf : PowerSeries.constantCoeff f = 0
  · have h1 : f⁻¹ = 0 := PowerSeries.inv_eq_zero.mpr hf
    have h2 : MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero ha f hf
    rw [h1, MvPowerSeries.inv_eq_zero.mpr h2, ← PowerSeries.coe_substAlgHom hs, map_zero]
  · have hm : PowerSeries.subst a f * PowerSeries.subst a f⁻¹ = 1 := by
      rw [← PowerSeries.subst_mul hs, PowerSeries.mul_inv_cancel f hf, ← PowerSeries.coe_substAlgHom hs, map_one]
    have hc : MvPowerSeries.constantCoeff (PowerSeries.subst a f) ≠ 0 := by
      intro h0
      have := congrArg MvPowerSeries.constantCoeff hm
      rw [map_mul, h0, zero_mul, map_one] at this
      exact zero_ne_one this
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one hc, mul_comm, hm]

private theorem exists_integral_subst_inverse_of_unit_linear (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0)
    (hI : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) (h1 : ‖PowerSeries.coeff 1 h‖ = 1) :
    ∃ g : PowerSeries ℂ_[p], PowerSeries.constantCoeff g = 0 ∧ (∀ n, ‖PowerSeries.coeff n g‖ ≤ 1) ∧
      ‖PowerSeries.coeff 1 g‖ = 1 ∧ PowerSeries.subst h g = PowerSeries.X := by
  set u := PowerSeries.coeff 1 h with hudef
  have hu0 : u ≠ 0 := by
    intro hu
    rw [hu, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨h', hh'⟩ : PowerSeries.X ∣ h := PowerSeries.X_dvd_iff.mpr h0
  have hcc : PowerSeries.constantCoeff h' = u := by
    rw [hudef, hh', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hpow : ∀ m k, PowerSeries.coeff k (h ^ m) =
      if m ≤ k then PowerSeries.coeff (k - m) (h' ^ m) else 0 := by
    intro m k
    rw [hh', mul_pow, PowerSeries.coeff_X_pow_mul']
  have hlow : ∀ m k, k < m → PowerSeries.coeff k (h ^ m) = 0 := by
    intro m k hk
    rw [hpow, ite_eq_right (by omega)]
  have hdiag : ∀ m, PowerSeries.coeff m (h ^ m) = u ^ m := by
    intro m
    rw [hpow, ite_eq_left le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hcc]
  let b : ℕ → ℂ_[p] := Nat.strongRec fun n rec =>
    (u ^ n)⁻¹ * PowerSeries.coeff n
      (PowerSeries.X - ∑ m : Fin n, PowerSeries.C (rec m m.isLt) * h ^ (m : ℕ))
  have hb : ∀ n, b n = (u ^ n)⁻¹ * PowerSeries.coeff n
      (PowerSeries.X - ∑ m ∈ Finset.range n, PowerSeries.C (b m) * h ^ m) := by
    intro n
    rw [← Fin.sum_univ_eq_sum_range (fun m => PowerSeries.C (b m) * h ^ m) n]
    exact Nat.strongRec_eq _ n
  have hcoeffP : ∀ N k, PowerSeries.coeff k (∑ m ∈ Finset.range N, PowerSeries.C (b m) * h ^ m) =
      ∑ m ∈ Finset.range N, b m * PowerSeries.coeff k (h ^ m) := by
    intro N k

    simp only [map_sum, PowerSeries.coeff_C_mul]
  have hA : ∀ N, ∀ k < N, PowerSeries.coeff k
      (PowerSeries.X - ∑ m ∈ Finset.range N, PowerSeries.C (b m) * h ^ m) = 0 := by
    intro N
    induction N with
    | zero => intro k hk; omega
    | succ N ih =>
      intro k hk
      rw [Finset.sum_range_succ, ← sub_sub, map_sub]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · rw [ih k hk, PowerSeries.coeff_C_mul, hlow N k hk, mul_zero, sub_zero]
      · subst hk
        rw [PowerSeries.coeff_C_mul, hdiag, hb k, mul_comm ((u ^ k)⁻¹) _, mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero k hu0), mul_one, sub_self]
  have hb0 : b 0 = 0 := by
    rw [hb 0]
    simp
  have hb1 : b 1 = u⁻¹ := by
    rw [hb 1]
    simp [hb0]
  have hH : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hhI : Formalism.L2.Th1.C.IntPS (IntegralOrthonormalChange.intRing p) h := fun n => hI n
  have hpowI : ∀ m, Formalism.L2.Th1.C.IntPS (IntegralOrthonormalChange.intRing p) (h ^ m) := by
    intro m
    induction m with
    | zero => simpa using Formalism.L2.Th1.C.USideA.intPS_C (R := IntegralOrthonormalChange.intRing p) (one_mem _)
    | succ m ihm => rw [pow_succ]; exact Formalism.L2.Th1.C.USideA.intPS_mul ihm hhI
  have hint : ∀ n, b n ∈ IntegralOrthonormalChange.intRing p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rw [hb n]
      refine Subring.mul_mem _ ?_ ?_
      · show ‖(u ^ n)⁻¹‖ ≤ 1
        rw [norm_inv, norm_pow, h1, one_pow, inv_one]
      · exact Formalism.L2.Th1.C.USideA.intPS_sub Formalism.L2.Th1.C.USideA.intPS_X
          (Formalism.L2.Th1.C.USideA.intPS_sum _ fun m hm =>
            Formalism.L2.Th1.C.USideA.intPS_mul
              (Formalism.L2.Th1.C.USideA.intPS_C (ih m (Finset.mem_range.mp hm))) (hpowI m)) n
  refine ⟨PowerSeries.mk b, ?_, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hb0]
  · intro n
    rw [PowerSeries.coeff_mk]
    exact hint n
  · rw [PowerSeries.coeff_mk, hb1, norm_inv, h1, inv_one]
  · ext k
    rw [PowerSeries.coeff_subst' hH]
    simp only [PowerSeries.coeff_mk, smul_eq_mul]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (k + 1)) ?_]
    · have := hA (k + 1) k (Nat.lt_succ_self k)
      rw [map_sub, hcoeffP, sub_eq_zero] at this
      exact this.symm
    · intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hdk
      exact hd (by rw [hlow d k (by omega), mul_zero])

theorem exists_inv (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0)
    (hI : ∀ n, IsIntP (PowerSeries.coeff n h)) (h1 : ‖PowerSeries.coeff 1 h‖ = 1) :
    ∃ g : PowerSeries ℂ_[p], PowerSeries.constantCoeff g = 0 ∧ (∀ n, IsIntP (PowerSeries.coeff n g)) ∧
      h.subst g = PowerSeries.X := by
  obtain ⟨g, g0, gI, g1, hg⟩ := exists_integral_subst_inverse_of_unit_linear h h0 hI h1
  obtain ⟨k, k0, -, -, hk⟩ := exists_integral_subst_inverse_of_unit_linear g g0 gI g1
  have hG : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' g0
  have hH : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hkh : k = h := by
    have e1 : PowerSeries.subst h (PowerSeries.subst g k) = h := by
      rw [hk, PowerSeries.subst_X hH]
    rw [PowerSeries.subst_comp_subst_apply hG hH, hg, PowerSeries.X_subst] at e1
    exact e1
  refine ⟨g, g0, gI, ?_⟩
  rw [← hkh]
  exact hk

end ParameterChangeLemmas

open ParameterChangeLemmas IntegralOrthonormalChange

end Formalism.L2.KerInert
end
end
