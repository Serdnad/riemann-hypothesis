module

public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteContinuousCocyclesLocalGaloisRep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle060
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle001
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem thinSize_dominates : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x0 ≤ L.sc.x → (100 : ℝ) ≤ L.sc.w'' D.R.n ∧ 100 * (L.etaSz + L.Sc + D.R.t + 2) ≤ L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' := by
  intro eps _
  refine ⟨10000, fun D L P _ hx => ?_⟩
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (7 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m; exact_mod_cast (by omega : 7 ≤ D.R.t)
  have hn1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have hxn : 1 ≤ L.sc.x * D.R.n := by nlinarith
  have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := div_le_self hb'.le hxn
  have hte := P.t_le_eta
  have h1 := P.teta
  rw [le_div_iff₀ hx0] at h1
  have hS := L.Sc_pos
  have hsq : (100 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hlog : (1 : ℝ) ≤ Real.log L.sc.x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hk : (200 : ℝ) ≤ D.R.k := by
    refine le_trans ?_ P.k_ge_mx
    have a : (200 : ℝ) ≤ (D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) := by nlinarith
    nlinarith
  have h2 : 200 * L.Sc ≤ L.sc.w'' D.R.n :=
    le_trans (mul_le_mul_of_nonneg_right hk hS.le) P.kS_le
  have h3 : 7 * L.etaSz ≤ (D.R.t : ℝ) * L.etaSz := mul_le_mul_of_nonneg_right ht (by linarith)
  have h4 : 7 * L.etaSz * 10000 ≤ L.sc.w'' D.R.n :=
    le_trans (mul_le_mul h3 hx (by norm_num) (by linarith)) h1
  exact ⟨by linarith, by linarith, hw1⟩

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.Ggeo

theorem bT_add_div_le_three_halves : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 4 ≤ L.sc.x →
    ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b' := by
  intro D L P hx t
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hb' : 0 < L.sc.b' := by
    unfold Formalism.BasicNotions.Scale.b' Formalism.BasicNotions.Scale.a Formalism.BasicNotions.Scale.b Formalism.BasicNotions.Scale.X'
    positivity
  have hbT := P.bT_le t
  have hrho := P.rho_le
  unfold Formalism.BasicNotions.LevelStarExponents.rhoP at hrho
  have hLaG : 0 < L.LaG := by
    have h1 := P.S_le
    have h2 := L.Sc_pos
    by_contra hneg
    have hneg' : L.LaG ≤ 0 := le_of_not_gt hneg
    have h3 : L.LaG * L.sc.b' / (D.R.k : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg' hb'.le) (Nat.cast_nonneg _)
    linarith
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / (D.R.k : ℝ) := by
    have := P.Crho_pos
    positivity
  set T := Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) with hT
  have hT4 : 4 * T ≤ L.sc.x ^ (-2 : ℝ) := by
    have h4 : 4 * Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) = 4 * T := by
      rw [hT]
      ring
    linarith
  have hbT' : (L.bT t : ℝ) ≤ L.sc.b' + T * L.sc.b' := by
    have h5 : Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) = T * L.sc.b' := by
      rw [hT]
      ring
    linarith
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 / 16 := by
    calc L.sc.x ^ (-2 : ℝ) = (L.sc.x ^ 2)⁻¹ := by rw [Real.rpow_neg hx0.le, Real.rpow_two]
      _ ≤ (16 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).mpr (by nlinarith)
      _ = 1 / 16 := by norm_num
  have hTb : T * L.sc.b' ≤ L.sc.b' / 64 := by
    have h6 : T ≤ 1 / 64 := by linarith
    nlinarith
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  linarith

end GlobalTheory.Ggeo
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem scale_log_mul_b'_le_b : ∀ eps C A : ℝ, 0 < eps → 0 ≤ C → 0 ≤ A → ∃ x0 : ℝ, ∀ s : Scale,
    s.eps = eps → x0 ≤ s.x → C * (A * Real.log s.x + 1) * s.b' ≤ s.b := by
  intro eps C A heps hC hA
  have hK : 0 ≤ C * (A + 1) := by positivity
  have hev : ∀ᶠ t in Filter.atTop, t ^ ⌈6 / eps⌉₊ * Real.exp (-t) ≤ 1 / (C * (A + 1) + 1) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero ⌈6 / eps⌉₊).eventually
      (ge_mem_nhds (by positivity))
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max T0 1 ^ (3 / eps), fun s hse hx => ?_⟩
  have hx1 : 1 < s.x := s.one_lt_alt
  have hx0 : 0 ≤ s.x := by linarith
  have hT1 : 0 ≤ max T0 1 := le_trans zero_le_one (le_max_right _ _)
  have ht : max T0 1 ≤ s.x ^ (eps / 3) := by
    calc max T0 1 = (max T0 1 ^ (3 / eps)) ^ (eps / 3) := by
          rw [← Real.rpow_mul hT1]
          rw [show 3 / eps * (eps / 3) = 1 by field_simp, Real.rpow_one]
      _ ≤ s.x ^ (eps / 3) := Real.rpow_le_rpow (by positivity) hx (by positivity)
  have ht1 : 1 ≤ s.x ^ (eps / 3) := le_trans (le_max_right _ _) ht
  have hxsq : s.x ^ 2 ≤ (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ := by
    have e : s.x ^ 2 = (s.x ^ (eps / 3)) ^ (6 / eps) := by
      rw [← Real.rpow_mul hx0, show eps / 3 * (6 / eps) = ((2 : ℕ) : ℝ) by field_simp; norm_num,
        Real.rpow_natCast]
    rw [e, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (Nat.le_ceil _)
  have hu := hT0 _ (le_trans (le_max_left _ _) ht)
  rw [le_div_iff₀ (by positivity)] at hu
  have hu0 : 0 ≤ (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ * Real.exp (-(s.x ^ (eps / 3))) := by positivity
  have he := Real.exp_pos (s.x ^ (eps / 3))
  have e1 : (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ =
      (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ * Real.exp (-(s.x ^ (eps / 3))) * Real.exp (s.x ^ (eps / 3)) := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hlog : A * Real.log s.x + 1 ≤ (A + 1) * s.x := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < s.x)
    nlinarith
  have main : C * (A * Real.log s.x + 1) * s.x ≤ Real.exp (s.x ^ (eps / 3)) := by
    calc C * (A * Real.log s.x + 1) * s.x ≤ C * ((A + 1) * s.x) * s.x := by gcongr
      _ = C * (A + 1) * s.x ^ 2 := by ring
      _ ≤ C * (A + 1) * (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ := by gcongr
      _ ≤ Real.exp (s.x ^ (eps / 3)) := by
          rw [e1]
          nlinarith [mul_le_mul_of_nonneg_right hu he.le, mul_nonneg hu0 he.le]
  have hb : 0 ≤ s.b := (Real.exp_pos _).le
  have hb' : s.b' = s.x * s.b / Real.exp (s.x ^ (eps / 3)) := by
    simp only [Scale.b', Scale.a, Scale.X', hse]
  rw [hb']
  calc C * (A * Real.log s.x + 1) * (s.x * s.b / Real.exp (s.x ^ (eps / 3)))
      = C * (A * Real.log s.x + 1) * s.x / Real.exp (s.x ^ (eps / 3)) * s.b := by ring
    _ ≤ 1 * s.b := by
        gcongr
        rw [div_le_one he]
        exact main
    _ = s.b := one_mul _

end GlobalTheory
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeLarge

theorem lt_prime : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), l.Prime → l ≠ 2 →
    jacobiSym (-(D.host.d : ℤ)) l ≠ 1 → L.sc.x ^ (L.sc.ez / 5) < l := by
  intro D L l hl h2 hj
  by_contra hlt
  push_neg at hlt
  have hle : l ≤ D.host.splitBound := le_trans (Nat.le_floor hlt) L.split_tie
  exact hj (D.host.split_small l hl h2 hle)

end GlobalTheory.InertPrimeLarge
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistedDualLoc

theorem continuous_T2O (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    Continuous (T2O D.nd i ρ π) := by
  have h1 : Continuous fun g : GE D.nd => ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) :=
    D.nd.chi_cont i 1
  have h2 : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
    GlobalTheory.LocalInv.eps_cont D.nd i
  have h3 : Continuous fun g : GE D.nd => ((ρ π g⁻¹ : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := hρ.comp continuous_inv
  refine continuous_matrix fun a b => ?_
  have h : ∀ g : GE D.nd, T2O D.nd i ρ π g a b =
      ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) * (((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) *
        ((ρ π g⁻¹ : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) b a) := by
    intro g
    simp [T2O, WpO, rhoO, twistM, dualM]
  simp only [h]
  exact h2.mul (h1.mul (h3.matrix_elem b a))

theorem continuous_and_integral : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → Continuous (fun g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g) ∧ ∀ g a b, ‖((mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g a b : ↥LL'.1) : Om (D.nd.l i))‖ ≤ 1 := by
  intro D i w hw LL' h ρ π hρ
  have hc := GlobalTheory.WordJumpsCompare.continuous_loc D i w hw (T2O D.nd i ρ π) (continuous_T2O D i ρ π hρ)
  refine ⟨continuous_matrix fun a b => ?_, fun g a b => ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp (hc.matrix_elem a b)) _
  · exact GlobalTheory.LocalH1Finiteness.norm_toLL_le (D.nbr i w hw) _

end GlobalTheory.TwistedDualLoc
end
end

section

namespace GlobalTheory.IndependentInfimum

open Module

theorem le_of_indep {K V X : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : X → Submodule K V) (hW : iSupIndep W) (hUW : ∀ x, U x ≤ W x)
    (hU : ⨆ x, U x = ⊤) (x : X) : W x ≤ U x := by
  classical
  intro w hw
  have htop : w ∈ ⨆ y, U y := by rw [hU]; exact Submodule.mem_top
  have hsplit : (⨆ y, U y) = U x ⊔ ⨆ (y) (_ : y ≠ x), U y := by
    apply le_antisymm
    · refine iSup_le fun y => ?_
      by_cases hy : y = x
      · subst hy
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le y hy le_rfl)
    · exact sup_le (le_iSup U x) (iSup₂_le fun y _ => le_iSup U y)
  rw [hsplit] at htop
  obtain ⟨u, hu, w', hw', hsum⟩ := Submodule.mem_sup.1 htop
  have hw'W : w' ∈ ⨆ (y) (_ : y ≠ x), W y :=
    (iSup₂_mono fun y _ => hUW y) hw'
  have hdiff : w - u ∈ W x := W x |>.sub_mem hw (hUW x hu)
  have heq : w - u = w' := by rw [← hsum]; abel
  have hdis := (hW x).le_bot (Submodule.mem_inf.2 ⟨hdiff, heq ▸ hw'W⟩)
  rw [Submodule.mem_bot, sub_eq_zero] at hdis
  rw [hdis]
  exact hu

theorem mem_iInf_of_apply {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : I → Module.End K V) (x : I → K) (v : V) (hv : ∀ i, A i v = x i • v) :
    v ∈ ⨅ i, (A i).maxGenEigenspace (x i) := Submodule.mem_iInf _ |>.2 fun i =>
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 (hv i))

theorem main {E I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hE : ⨆ (c : C), Ec c = LinearMap.range e)
    (hl : ∀ (c : C), ∀ w ∈ Ec c, ∀ (i : I), (h i : E → E) w = lab c i • w) :
    (Formalism.L2.Col.PairComm fun (i : I) ↦ h i * e) ∧ ∀ (Q : (I → ℂ) → Prop), ¬Q (0 : I → ℂ) →
      Formalism.L2.Col.eigSum (fun (i : I) ↦ h i * e) Q = ⨆ (c : C), ⨆ (_ : Q (lab c)), Ec c := by
  classical
  have hee : ∀ v, e (e v) = e v := fun v => by
    have := congrArg (fun f : Module.End ℂ E => f v) he
    simpa using this
  have hfix : ∀ c, ∀ w ∈ Ec c, e w = w := by
    intro c w hw
    have : w ∈ LinearMap.range e := hE ▸ Submodule.mem_iSup_of_mem c hw
    obtain ⟨u, rfl⟩ := this
    exact hee u
  have hA : ∀ c, ∀ w ∈ Ec c, ∀ i, (h i * e) w = lab c i • w := by
    intro c w hw i
    rw [Module.End.mul_apply, hfix c w hw, hl c w hw]
  have hcomm : ∀ i j, Commute (h i * e) (h j * e) := by
    intro i j
    have key : ∀ w ∈ ⨆ c, Ec c, (h i * e) ((h j * e) w) = (h j * e) ((h i * e) w) := by
      intro w hw
      induction hw using Submodule.iSup_induction' with
      | mem c w hw =>
        rw [hA c w hw j, hA c w hw i, map_smul, map_smul, hA c w hw j, hA c w hw i, smul_comm]
      | zero => simp
      | add a b _ _ ha hb => simp only [map_add (f := _), ha, hb]
    ext v
    have hv : e v ∈ ⨆ c, Ec c := by rw [hE]; exact ⟨v, rfl⟩
    have := key _ hv
    simpa [Module.End.mul_apply, hee] using this
  refine ⟨hcomm, fun Q hQ => ?_⟩
  have hind : iSupIndep fun x : I → ℂ => ⨅ i, (h i * e).maxGenEigenspace (x i) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun i => h i * e)
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  let U : (I → ℂ) → Submodule ℂ E := fun x =>
    (⨆ (c : C) (_ : lab c = x), Ec c) ⊔ ⨆ (_ : x = 0), LinearMap.ker e
  have hUW : ∀ x, U x ≤ ⨅ i, (h i * e).maxGenEigenspace (x i) := by
    intro x
    refine sup_le (iSup₂_le fun c hc w hw => ?_) (iSup_le fun hx w hw => ?_)
    · exact mem_iInf_of_apply (fun i => h i * e) x w fun i => hc ▸ hA c w hw i
    · refine mem_iInf_of_apply (fun i => h i * e) x w fun i => ?_
      rw [LinearMap.mem_ker] at hw
      simp [hx, Module.End.mul_apply, hw]
  have hU : ⨆ x, U x = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : LinearMap.range e ≤ ⨆ x, U x := by
      rw [← hE]
      exact iSup_le fun c => le_iSup_of_le (lab c)
        (le_sup_of_le_left (le_iSup₂_of_le (f := fun c' (_ : lab c' = lab c) => Ec c') c rfl le_rfl))
    have h2 : LinearMap.ker e ≤ ⨆ x, U x :=
      le_iSup_of_le 0 (le_sup_of_le_right
        (le_iSup_of_le (f := fun _ : (0 : I → ℂ) = 0 => LinearMap.ker e) rfl le_rfl))
    have h3 : v - e v ∈ LinearMap.ker e := by simp [LinearMap.mem_ker, hee]
    have := Submodule.add_mem _ (h1 ⟨v, rfl⟩) (h2 h3)
    simpa using this
  unfold Formalism.L2.Col.eigSum Formalism.L2.Col.eigAt
  apply le_antisymm
  · refine iSup₂_le fun x hx => (le_of_indep U _ hind hUW hU x).trans ?_
    refine sup_le (iSup₂_le fun c hc => ?_) (iSup_le fun h0 => absurd (h0 ▸ hx) hQ)
    exact le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c (hc ▸ hx) le_rfl
  · refine iSup₂_le fun c hc => ?_
    refine le_iSup₂_of_le
      (f := fun (x : I → ℂ) (_ : Q x) => ⨅ i, (h i * e).maxGenEigenspace (x i)) (lab c) hc ?_
    intro w hw
    exact mem_iInf_of_apply (fun i => h i * e) (lab c) w (hA c w hw)

end GlobalTheory.IndependentInfimum
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem eig_descends : ∀ (D : D7) (M : Formalism.L2.MtFam D) (B : Formalism.L2.NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (y : D.what₂.Mt μ j), y ≠ 0 → (∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ Formalism.AUTREP.IsUnif D.host.E s.v ϖ ∧ (∀ (c : ℂ) (f f' : Formalism.AUTREP.GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f + Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f') ∧ Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → ∃ e : B.V j w, e ≠ 0 ∧ ∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → B.hK j w v k e = κ v k • e := by
  intro D M B j w μ h1 h2 hμ φ hφ κ y hy hgen
  subst hμ
  classical
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  let bC := Module.Basis.mk hjb.1 hjb.2.ge
  have hb := B.iV_basis j w b
  let bV := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ a, bC a = D.what₂.jMt (D.what₂.muTw w) j (b a) := fun a => by simp [bC]
  have hbV : ∀ a, bV a = B.iV j w (b a) := fun a => by simp [bV]
  have rC : ∀ x r, bC.repr (D.what₂.jMt (D.what₂.muTw w) j x) r = D.what₂.embLL (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 x r
  have rV : ∀ x r, bV.repr (B.iV j w x) r = B.ec j w (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport (B.ec j w) (B.iV j w) b hb.1 hb.2 x r
  let A : PlE D.host → ℕ → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) D.what₂.LL :=
    fun v k => LinearMap.toMatrix b b (B.hL j w v k)
  let G := {p : PlE D.host × ℕ // Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) p.1 p.2}
  let Mg : G → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) (FractionRing (B.Oc j w)) :=
    fun g => (A g.1.1 g.1.2).map (B.ec j w) - κ g.1.1 g.1.2 • 1
  have hd : (⇑(bC.repr y)) ≠ 0 := by
    intro h
    apply hy
    have h' : bC.repr y = 0 := Finsupp.coe_eq_zero.1 h
    exact bC.repr.injective (h'.trans (map_zero _).symm)
  have hC : ∀ g : G, Matrix.mulVec ((Mg g).map φ) (⇑(bC.repr y)) = 0 := by
    rintro ⟨⟨v, k⟩, hvk⟩
    obtain ⟨s, ϖ, hc, hu, hadd, heig⟩ := hgen v k hvk
    set Mw := M (D.what₂.muTw w) j h1 h2 with hMw
    let tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j) :=
      bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))
    have htN0 : Formalism.L2.NG.tN Mw.J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
      have := hadd 1 0 0
      rw [one_smul, add_zero, one_smul] at this
      simpa using this
    let Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) :=
      { toFun := fun y => Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y)
        map_add' := fun y y' => by
          have := hadd 1 (Mw.real y) (Mw.real y')
          rw [one_smul, one_smul] at this
          simp only [map_add (f := _)]
          exact this
        map_smul' := fun c y => by
          have := hadd c (Mw.real y) 0
          rw [add_zero, htN0, add_zero] at this
          simp only [map_smul, RingHom.id_apply]
          exact this }
    have hagree : ∀ x, Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real x) = Mw.real (tC x) := by
      have hLt : Lt = Mw.real.comp tC := bC.ext fun a => by
        have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) a
        show Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real (bC a)) =
          Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC a))
        rw [e, hbC a]
        exact (B.hL_def j w h1 h2 v k s ϖ hvk hc hu (b a)).symm
      intro x
      exact LinearMap.congr_fun hLt x
    have hty : tC y = φ (κ v k) • y := by
      apply Mw.real_inj
      rw [← hagree, heig, map_smul]
    have hmat : LinearMap.toMatrix bC bC tC = (A v k).map D.what₂.embLL := by
      ext r c
      rw [LinearMap.toMatrix_apply, Matrix.map_apply]
      have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) c
      show bC.repr ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC c)) r = _
      rw [e, rC]
      simp only [A, LinearMap.toMatrix_apply]
    have hMg : (Mg ⟨(v, k), hvk⟩).map φ = (A v k).map D.what₂.embLL - φ (κ v k) • 1 := by
      ext r c
      simp only [Mg, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [hφ]
    rw [hMg, Matrix.sub_mulVec, ← hmat, LinearMap.toMatrix_mulVec_repr, hty, Matrix.smul_mulVec,
      Matrix.one_mulVec, map_smul, Finsupp.coe_smul, sub_self]
  obtain ⟨c, hc0, hcM⟩ := GlobalTheory.PtLocalEig.descent φ Mg (⇑(bC.repr y)) hd hC
  refine ⟨bV.equivFun.symm c, ?_, fun v k hvk => ?_⟩
  · intro h
    apply hc0
    have := congrArg bV.equivFun h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  · apply bV.equivFun.injective
    have hmat : LinearMap.toMatrix bV bV (B.hK j w v k) = (A v k).map (B.ec j w) := by
      ext r c'
      rw [LinearMap.toMatrix_apply, Matrix.map_apply, hbV, B.hK_def, rV]
      simp only [A, LinearMap.toMatrix_apply]
    have hM := hcM ⟨(v, k), hvk⟩
    simp only [Mg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hM
    have hr := LinearMap.toMatrix_mulVec_repr bV bV (B.hK j w v k) (bV.equivFun.symm c)
    rw [hmat] at hr
    rw [map_smul, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply, ← hr, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply, hM]

end GlobalTheory.PtLocalEig
end
end
