module

import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesTelescope
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle018
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle008
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

namespace StokesStep

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_multicone : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem ptsIntegral_congr_g (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  apply _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.StokesTelescope.ptsIntegral_congr_g <;> assumption

theorem isConeTangent_lift {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X)
    (j : Fin R.A.n) {y : Fin e → ℂ}
    (hy : y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) (w : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (R.lift x ((R.A.chart j).symm y))
      (fderiv ℂ (fun y' => R.lift x ((R.A.chart j).symm y')) y w) := by
  set τ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y') with hτdef
  have hO : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :=
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  have hτ : AnalyticAt ℂ τ y := analyticAt_pi_iff.mpr fun p => R.holo x p j y hy
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have h0 : (fun y' => eval (τ y') F) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hO.mem_nhds hy] with y' hy'
    exact (R.mem x _ hy'.2).2 f hf
  have hD := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (τ y)).comp y hτ.differentiableAt.hasFDerivAt
  have hD0 : HasFDerivAt (fun y' => eval (τ y') F) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq h0
  have h1 := congrArg (fun L => L w) (hD.unique hD0)
  simpa [smul_eq_mul, mul_comm] using h1

theorem isPsh_potOf {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {A : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hA : IsSemipositiveH P A) : IsPsh R.A (potOf R A) := by
  intro x j y hy w
  have hy' : y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x := hy
  set τ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y') with hτdef
  have hτ : AnalyticAt ℂ τ y := analyticAt_pi_iff.mpr fun p => R.holo x p j y hy'
  have hz : τ y ∈ mcPts P := R.mem x _ hy'.2
  have hS : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ y) :=
    isOpen_multicone.mem_nhds hz.1
  have hφ : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (τ y) :=
    ((hA.1.contDiffAt hS).of_le (WithTop.coe_le_coe.mpr le_top)).log (A.pos _ hz.1).ne'
  have hc : (potOf R A).φ x ∘ (R.A.chart j).symm = (fun z => Real.log (A.h z)) ∘ τ := rfl
  rw [hc, ReciprocityTheory.AnForm.levi_comp w hτ hφ]
  exact hA.2 _ hz _ (isConeTangent_lift R x j hy' w)

end StokesStep


open StokesStep in
theorem StokesStep.proof (hE : ResExistsStatement) : StokesStep.Statement := by
  intro K _ ι _ P n i A A' hP ha hA hA' hi
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  set C := A'.tensor A.inv with hCdef
  have hC0 : C.a = 0 := by
    change A'.a + (-A.a) = 0
    rw [ha, add_neg_cancel]
  have hCs : IsSmoothHerm C := hA'.1.mul (isSmoothHerm_inv hA.1)
  have hlogC : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      Real.log (C.h z) = Real.log (A'.h z) - Real.log (A.h z) := by
    intro z hz
    show Real.log (A'.h z * (A.h z)⁻¹) = _
    rw [Real.log_mul (A'.pos z hz).ne' (inv_ne_zero (A.pos z hz).ne'), Real.log_inv]
    ring
  let L : ℕ → Fin (m + 1) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun l j => if j.val < l then A' else A
  have hpot : ∀ l, stokesMixPot A A' (m + 1) l = pot (L l) := by
    intro l
    funext j z
    simp only [stokesMixPot, pot, L]
    split_ifs <;> rfl
  have hLsp : ∀ l j, IsSemipositiveH P (L l j) := fun l j => by
    simp only [L]
    split_ifs
    exacts [hA', hA]
  have hL : ∀ l j, IsSmoothHerm (L l j) := fun l j => (hLsp l j).1
  have hs := isSectionOn_inv_one hP.2.1.1 hC0
  set v : R.X → ℝ := fun x => Real.log (C.h (R.lift x x)) with hvdef
  have key : ∀ l, ptsIntegral P (stokesMixPot A A' (m + 1) l)
      (fun z => Real.log (A'.h z) - Real.log (A.h z)) = mInt R.A (fun j => potOf R (L l j)) v := by
    intro l
    rw [ptsIntegral_congr_g P _ (g' := logNorm C.inv 1) fun z hz => by
      rw [logNorm_inv_one, hlogC z hz.1], hpot,
      ptsIntegral_eq_mInt' hE resBridge R hP (hL l) (isSmoothHerm_inv hCs) hs]
    congr 1
    funext x
    exact logNorm_inv_one C _
  rw [key, key]

  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 ⟨i, hi⟩ with hσ
  rw [← mIntSymm R.A (fun j => potOf R (L (i + 1) j)) σ v,
    ← mIntSymm R.A (fun j => potOf R (L i j)) σ v]
  set T : Fin m → LocPot R.X := fun k => potOf R (L i (σ k.succ)) with hT
  have hne : ∀ j : Fin (m + 1), j ≠ ⟨i, hi⟩ → L (i + 1) j = L i j := by
    intro j hj
    have hj' : j.val ≠ i := fun h => hj (Fin.ext h)
    simp only [L]
    by_cases h : j.val < i
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hσs : ∀ k : Fin m, σ k.succ ≠ ⟨i, hi⟩ := by
    intro k hk
    rw [hσ, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hk
    exact Fin.succ_ne_zero k hk
  have e1 : (fun j => potOf R (L (i + 1) j)) ∘ σ = Fin.cons (potOf R A') T := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [σ, L]
    · simp only [Function.comp_apply, Fin.cons_succ, T]
      rw [hne _ (hσs k)]
  have e0 : (fun j => potOf R (L i j)) ∘ σ = Fin.cons (potOf R A) T := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [σ, L]
    · simp only [Function.comp_apply, Fin.cons_succ, T]
  rw [e1, e0]

  have hv : R.A.Smooth v := smooth_diag R hCs hC0
  have hgerm : mInt R.A (Fin.cons (potOf R A') T) v =
      mInt R.A (Fin.cons (potOf R A + LocPot.ofFun v) T) v := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr R.A (locDens_cons_congr R.A T fun j y hy => ?_) fun _ => rfl
    set x0 := (R.A.chart j).symm y
    filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)).mem_nhds
      ⟨hy, R.mem_U x0⟩] with y' hy'
    have hmc := (R.mem x0 _ hy'.2).1
    show Real.log (A'.h (R.lift x0 _)) = Real.log (A.h (R.lift x0 _)) + v _
    rw [hvdef]
    simp only
    rw [← h_eq_of_sameOrbit hC0 (R.compat x0 _ _ ⟨hy'.2, R.mem_U _⟩), hlogC _ hmc]
    ring
  have hpA : IsPotential R.A (potOf R A) := isPotential_potOf R hA.1
  have hpv : IsPotential R.A (LocPot.ofFun v) := isPotential_ofFun R.A v hv
  have hTp : ∀ k, IsPotential R.A (T k) := fun k => isPotential_potOf R (hL i _)
  have hTpsh : ∀ k, IsPsh R.A (T k) := fun k => isPsh_potOf R (hLsp i _)
  have hcons : ∀ Q, IsPotential R.A Q → ∀ k, IsPotential R.A ((Fin.cons Q T : Fin (m + 1) → LocPot R.X) k) :=
    fun Q hQ k => by
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hQ
      · simpa using hTp k
  have hvc : Continuous v := PLC.continuous_of_smooth R.A hv
  have hadd := mIntAdd R.A (potOf R A) (LocPot.ofFun v) T hpA hpv hTp v
    (mIntegrableCont R.A _ (hcons _ hpA) v hvc) (mIntegrableCont R.A _ (hcons _ hpv) v hvc)
  have hneg := byPartsNonpos R.A v hv T hTp hTpsh
  rw [hgerm, hadd]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem ComponentSetting.wSt_torusSmul (X : ComponentSetting D O Lt) (B p q : ℕ) (t t' : ℝ) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    X.wSt B p q t t' (torusSmul c z) = X.wSt B p q t t' z := by
  have ha : (X.MUq B p q t').a = (X.NbarQ B p q t).a := by
    simp only [ComponentSetting.MUq, MUc, ComponentSetting.NbarQ, smoothRepConj_a, smoothRep_a]
    rfl
  have hpos : 0 < ∏ k, ‖c k‖ ^ (X.NbarQ B p q t).a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  have e : torusSmul c z = fun x => c x.1 * z x := rfl
  have h1 := (X.MUq B p q t').smul c z hc
  have h2 := (X.NbarQ B p q t).smul c z hc
  rw [ha] at h1
  unfold ComponentSetting.wSt
  rw [e, h1, h2, Real.log_mul hpos.ne' ((X.MUq B p q t').pos z hz.1).ne',
    Real.log_mul hpos.ne' ((X.NbarQ B p q t).pos z hz.1).ne']
  ring

theorem StokesLimitTp.proof (hLim : TpIntegrandLimit.Statement) (hAbove : RegAboveWeight.Statement)
    (hU : TpCuspIntegrable.Statement) (hConv : PtsBddConv.Statement) (hMono : PtsMonoSemipos.Statement) :
    StokesLimitTp.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hp hpq
  have hq : 1 ≤ q := hp.trans hpq
  have hr : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨t₁, ht₁, hL⟩ := hLim II Ψ K ι Ω E D O Lt X B p q hq
  obtain ⟨t₃, ht₃, N₂, hN₂, hA⟩ := hAbove II Ψ K ι Ω E D O Lt X
  refine ⟨min t₁ t₃, lt_min ht₁ ht₃, fun t ht0 ht hsp => ?_⟩
  obtain ⟨N₁, C, s₀, hs₀, hN₁, hbd, hpt⟩ := hL t ht0 (ht.trans (min_le_left _ _))
  obtain ⟨hint, hlim⟩ := hConv K ι (mCoordIdeal D.y) D.n (X.NbarQ B p q t) q (X.wSt B p q t)
    (fun z => cuspCorr X.H X.Cd z - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z))) N₁ C s₀
    D.arith hsp.1 hr hN₁ hs₀
    (fun s hs hs' => ⟨(hbd s hs hs').1, (hbd s hs hs').2, fun c hc z hz => X.wSt_torusSmul B p q t s c hc z hz⟩) hpt
  refine ⟨hlim, ?_⟩
  refine hMono K ι (mCoordIdeal D.y) D.n (X.NbarQ B p q t) q _ (fun z => X.Cd.cuspWeight z / 2) N₂ D.arith hsp hr
    hN₂ (fun z hz hzN => ?_) hint (hU II Ψ K ι Ω E D O Lt X B p q t hsp.1)
  have h := hA t ht0 (ht.trans (min_le_right _ _)) z hz hzN
  show phMu X.H z + X.Cd.cuspWeight z / 2 - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z)) ≤
    X.Cd.cuspWeight z / 2
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem ComponentSetting.mixN_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
    (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) : X.mixN B (D.n + 1) t = arLimFun X.H X.S B t := by
  unfold ComponentSetting.mixN arLimFun
  congr 1
  funext j
  simp [j.is_lt]

theorem StokesLimitTTop.proof (hE : TopNMixedExpand.Statement) (hM : TopNMixedLimit.Statement) :
    StokesLimitTTop.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hAr hp hpq
  have hlim : ∀ k ∈ Finset.range (D.n + 2), ∃ L : ℝ, Tendsto (X.mixN B k) (𝓝[>] 0) (𝓝 L) := by
    intro k hk
    rcases Nat.lt_or_ge k (D.n + 1) with h | h
    · exact hM II Ψ K ι Ω E D O Lt X B hII hAr k (Nat.lt_succ_iff.1 h)
    · have hk' : k = D.n + 1 := le_antisymm (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) h
      subst hk'
      obtain ⟨L, hL⟩ := hAr
      exact ⟨L, hL.congr fun t => (X.mixN_top B t).symm⟩
  choose! L hL using hlim
  refine ⟨∑ k ∈ Finset.range (D.n + 2), ((D.n + 1).choose k : ℝ) * ((p : ℝ) / q) ^ (D.n + 1 - k) * L k, ?_⟩
  refine Tendsto.congr' ((hE II Ψ K ι Ω E D O Lt X B p q hII hp hpq).mono fun t ht => ht.symm) ?_
  exact tendsto_finsetSum _ fun k hk => (hL k hk).const_mul _

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem StokesLimitT.proof (hG : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement)
    (hNs : NbarSemipos.Statement) (hTop : StokesLimitTTop.Statement) (hVb : StokesLimitTVb.Statement) :
    StokesLimitT.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hAr hp hpq
  refine ⟨tendsto_nhds_limUnder (hTop II Ψ K ι Ω E D O Lt X B p q hII hAr hp hpq),
    tendsto_nhds_limUnder (hVb II Ψ K ι Ω E D O Lt X B p q hp hpq), ?_⟩
  obtain ⟨t₁, ht₁, hN⟩ := hNs II Ψ K ι Ω E D O Lt X B p q hp hpq

  have ha : ∀ t : ℝ, (X.NbarQ B p q t).a = (X.NbarQ B p q t₁).a := by
    intro t
    simp only [ComponentSetting.NbarQ, smoothRep_a]
    rfl
  have hconst : ∀ᶠ t in 𝓝[>] (0 : ℝ), X.degN B p q t₁ = X.degN B p q t := by
    filter_upwards [Ioc_mem_nhdsGT ht₁] with t ht
    unfold ComponentSetting.degN
    rw [hG K ι Ω D.y D.n _ D.arith (hN t ht.1 ht.2).1, hG K ι Ω D.y D.n _ D.arith (hN t₁ ht₁ le_rfl).1, ha t]
  exact tendsto_nhds_limUnder ⟨_, tendsto_const_nhds.congr' hconst⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem NbarSemipos.proof (h : NbarChartSemipos.Statement) : NbarSemipos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hp _
  obtain ⟨c, hc, hX⟩ := h II Ψ K ι Ω E D O Lt X
  have hpc : 0 < (p : ℝ) * c := mul_pos (by exact_mod_cast hp) hc
  have hlim : Tendsto (fun t => (q : ℝ) * (4 * X.S.Cη * X.S.e1 t)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (X.S_tied.e1_tendsto_zero.const_mul (4 * X.S.Cη)).const_mul (q : ℝ)
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t) := by
    filter_upwards [X.S.eventually_chartLevi X.S_tied, hlim.eventually (eventually_le_nhds hpc)] with t ht hq
    exact hX B p q t _ ht.1 ht.2 hq
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hall
  exact ⟨u, hu, fun t ht0 ht1 => hsub ⟨ht0, ht1⟩⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem OmNVbInt.proof (hT : TpCuspIntegrable.Statement) (hS : NbarSmooth.Statement) : OmNVbInt.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q _ _
  filter_upwards [X.S.eventually_chartLevi X.S_tied] with t ht
  exact hT II Ψ K ι Ω E D O Lt X B p q t (hS II Ψ K ι Ω E D O Lt X B p q t ht.1)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace StokesLimitEps

open Matrix

theorem coeff_tendsto {N : ℕ} (c : ℕ → ℝ → ℝ) (f : ℕ → ℝ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ), f q t = ∑ i ∈ Finset.range N, c i t * (1 / (q : ℝ)) ^ i)
    (hg : ∀ q : ℕ, 1 ≤ q → Tendsto (f q) (𝓝[>] 0) (𝓝 (g q))) :
    ∃ ℓ : ℕ → ℝ, (∀ i < N, Tendsto (c i) (𝓝[>] 0) (𝓝 (ℓ i))) ∧
      ∀ q : ℕ, 1 ≤ q → g q = ∑ i ∈ Finset.range N, ℓ i * (1 / (q : ℝ)) ^ i := by

  let x : Fin N → ℝ := fun j => 1 / (((j : ℕ) + 1 : ℕ) : ℝ)
  have hinj : Function.Injective x := by
    intro j k h
    simp only [x, one_div, _root_.inv_inj, Nat.cast_inj] at h
    exact Fin.ext (by omega)
  have hdet : IsUnit (Matrix.vandermonde x).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
    exact hinj
  let F : ℝ → Fin N → ℝ := fun t j => f ((j : ℕ) + 1) t

  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (fun i : Fin N => c i t) = (Matrix.vandermonde x)⁻¹ *ᵥ F t := by
    filter_upwards [Filter.eventually_all.2 fun j : Fin N => hf ((j : ℕ) + 1) (by omega)] with t ht
    have hval : F t = Matrix.vandermonde x *ᵥ fun i : Fin N => c i t := by
      funext j
      simp only [F, ht j, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, x]
      rw [← Fin.sum_univ_eq_sum_range (fun i => c i t * (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) ^ i)]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hval, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hF : Tendsto F (𝓝[>] 0) (𝓝 fun j : Fin N => g ((j : ℕ) + 1)) :=
    tendsto_pi_nhds.2 fun j => hg _ (by omega)
  have hC : Tendsto (fun t => fun i : Fin N => c i t) (𝓝[>] 0)
      (𝓝 ((Matrix.vandermonde x)⁻¹ *ᵥ fun j : Fin N => g ((j : ℕ) + 1))) :=
    (((continuous_const.matrix_mulVec continuous_id).tendsto _).comp hF).congr' (hev.mono fun t ht => ht.symm)
  let ℓ : ℕ → ℝ := fun i => if h : i < N then
    ((Matrix.vandermonde x)⁻¹ *ᵥ fun j : Fin N => g ((j : ℕ) + 1)) ⟨i, h⟩ else 0
  have hℓ : ∀ i < N, Tendsto (c i) (𝓝[>] 0) (𝓝 (ℓ i)) := by
    intro i hi
    simpa only [ℓ, dif_pos hi] using tendsto_pi_nhds.1 hC ⟨i, hi⟩
  refine ⟨ℓ, hℓ, fun q hq => tendsto_nhds_unique (hg q hq) ?_⟩
  refine Tendsto.congr' ((hf q hq).mono fun t ht => ht.symm) ?_
  exact tendsto_finsetSum _ fun i hi => (hℓ i (Finset.mem_range.1 hi)).mul_const _

theorem tendsto_const_coeff {N : ℕ} (ℓ : ℕ → ℝ) (hN : 1 ≤ N) :
    Tendsto (fun m : ℕ => ∑ i ∈ Finset.range N, ℓ i * (1 / ((m + 1 : ℕ) : ℝ)) ^ i) atTop (𝓝 (ℓ 0)) := by
  have h0 : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hs := tendsto_finsetSum (Finset.range N) fun i _ => (h0.pow i).const_mul (ℓ i)
  have e : ∑ i ∈ Finset.range N, ℓ i * (0 : ℝ) ^ i = ℓ 0 := by
    rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [zero_pow hb])
      (fun h => absurd (Finset.mem_range.2 hN) h)]
    simp
  rwa [e] at hs

end StokesLimitEps

theorem StokesLimitEps.proof (hT : StokesLimitT.Statement) (hTop : TopNPoly.Statement)
    (hOm : OmNPoly.Statement) (hMu : MuMeasureLimit.Statement) : StokesLimitEps.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII hAr
  have hTq := fun q (hq : 1 ≤ q) => hT II Ψ K ι Ω E D O Lt X B 1 q hII hAr le_rfl hq
  obtain ⟨c, hc0, hc⟩ := hTop II Ψ K ι Ω E D O Lt X B hII hAr
  obtain ⟨v, d, hv0, hd0, hvd⟩ := hOm II Ψ K ι Ω E D O Lt X B hII hAr
  obtain ⟨hmuV, hmuD⟩ := hMu II Ψ K ι Ω E D O Lt X B hII hAr
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto c (fun q => X.topN B 1 q) (X.topNLim B 1) hc
      fun q hq => (hTq q hq).1
    have h0 : ℓ 0 = arLim X.H X.S B := by
      obtain ⟨L, hL⟩ := hAr
      have e1 : arLim X.H X.S B = L := by unfold arLim; exact hL.limUnder_eq
      have h := hℓ 0 (by omega)
      rw [hc0] at h
      rw [e1]; exact tendsto_nhds_unique h hL
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 2) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto v (fun q => X.Vb B 1 q) (X.VbLim B 1)
      (fun q hq => (hvd q hq).mono fun t h => h.1) fun q hq => (hTq q hq).2.1
    have h0 : ℓ 0 = meanU X.H X.Cd * degMu X.H / 2 := by
      have h := hℓ 0 (by omega)
      rw [hv0] at h
      exact tendsto_nhds_unique h hmuV
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 1) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto d (fun q => X.degN B 1 q) (X.degNLim B 1)
      (fun q hq => (hvd q hq).mono fun t h => h.2) fun q hq => (hTq q hq).2.2
    have h0 : ℓ 0 = degMu X.H := by
      have h := hℓ 0 (by omega)
      rw [hd0] at h
      exact tendsto_nhds_unique h hmuD
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 1) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
