module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueJointTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle563
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle566
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle568
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle569
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HarmLine

theorem loc_jointTop : ∀ {σ : Type} [DecidableEq σ] {k l N : ℕ} (z : Fin k × Fin N → σ) (y : Fin l × Fin N → σ) (κ : Fin N → ℂ) (α : Fin k → ℂ) (β : Fin l → ℂ) (G P : MvPolynomial σ ℂ), G ≠ 0 → (∀ v ∈ G.vars, (∀ u, z u ≠ v) ∧ ∀ u, y u ≠ v) → GlobalTheory.CompactHarm.JointTop z y κ α β (G * P) → GlobalTheory.CompactHarm.JointTop z y κ α β P := by
  intro σ _ k l N z y κ α β G P hG hGv hJ
  have hd : ∀ u, u ∉ G.vars → ∀ Q : MvPolynomial σ ℂ,
      MvPolynomial.pderiv u (G * Q) = G * MvPolynomial.pderiv u Q := by
    intro u hu Q
    rw [Derivation.leibniz, MvPolynomial.pderiv_eq_zero_of_notMem_vars hu, smul_zero, add_zero, smul_eq_mul]
  have hz : ∀ c Q, MvPolynomial.pderiv (z c) (G * Q) = G * MvPolynomial.pderiv (z c) Q :=
    fun c Q => hd _ (fun h => (hGv _ h).1 c rfl) Q
  have hy : ∀ c Q, MvPolynomial.pderiv (y c) (G * Q) = G * MvPolynomial.pderiv (y c) Q :=
    fun c Q => hd _ (fun h => (hGv _ h).2 c rfl) Q
  have hmix : ∀ i j, GlobalTheory.Capelli.mixedOp ℂ z y i j (G * P) = G * GlobalTheory.Capelli.mixedOp ℂ z y i j P := by
    intro i j
    rw [GlobalTheory.Capelli.mixedOp_apply, GlobalTheory.Capelli.mixedOp_apply, mul_sub, Finset.mul_sum, Finset.mul_sum]
    simp only [hz, hy]
    exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => by ring) (Finset.sum_congr rfl fun _ _ => by ring)
  have hrz : ∀ c c', GlobalTheory.Capelli.rowOp ℂ z c c' (G * P) = G * GlobalTheory.Capelli.rowOp ℂ z c c' P := by
    intro c c'
    simp only [GlobalTheory.Capelli.rowOp_apply, hz, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hry : ∀ c c', GlobalTheory.Capelli.rowOp ℂ y c c' (G * P) = G * GlobalTheory.Capelli.rowOp ℂ y c c' P := by
    intro c c'
    simp only [GlobalTheory.Capelli.rowOp_apply, hy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hJ
  refine ⟨fun i j hij => ?_, fun i => ?_, fun c c' h => ?_, fun c => ?_, fun d d' h => ?_, fun d => ?_,
    fun c d => ?_⟩
  · have := h1 i j hij
    rw [hmix] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h2 i
    rw [hmix, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h3 c c' h
    rw [hrz] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h4 c
    rw [hrz, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h5 d d' h
    rw [hry] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h6 d
    rw [hry, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h7 c d
    simp only [hy, hz, ← Finset.mul_sum] at this
    exact (mul_eq_zero.1 this).resolve_left hG

theorem joint_line : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P P' : PolF D m n), P ≠ 0 → GlobalTheory.LowestKType.IsHarm w P → GlobalTheory.LowestKType.IsHarm w P' → GlobalTheory.LowestKType.IsNHw w lam P → GlobalTheory.LowestKType.IsNHw w lam P' → GlobalTheory.LowestKType.IsKHw w P → GlobalTheory.LowestKType.IsKHw w P' → ∃ c : ℂ, P' = c • P := by
  intro D n m w lam P P' hP0 hH hH' hN hN' hK hK'
  classical
  set κ : D.what₂.Tau → Fin n → ℂ := fun τ a => lam τ a - (m : ℂ) / 2 + ((m - w.p τ : ℕ) : ℂ) with hκ
  have hJ := GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType D n m w lam P hH hN hK
  have hJ' := GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType D n m w lam P' hH' hN' hK'
  have hU : ∀ τ : D.what₂.Tau, ∃ Q₀ : MvPolynomial (Fin m × Fin n) ℂ, ∀ α β f,
      GlobalTheory.CompactHarm.JointTop (GlobalTheory.HarmLine.zR m n (w.p τ)) (GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β f →
        ∃ r : ℂ, f = r • Q₀ := fun τ =>
    GlobalTheory.T.jointHighestWeightHarmonic_multiplicity_one_covering _ _ (GlobalTheory.HarmLine.zR_inj m n (w.p τ)) (GlobalTheory.HarmLine.yR_inj m n (w.p τ))
      (GlobalTheory.HarmLine.zR_ne_yR m n (w.p τ)) (GlobalTheory.HarmLine.zR_yR_cover m n (w.p τ)) (κ τ)
  choose Q₀ hQ₀ using hU
  let Q : D.what₂.Tau → PolF D m n := fun τ => MvPolynomial.rename (Prod.mk τ) (Q₀ τ)
  have hfac : ∀ (τ : D.what₂.Tau) (P : PolF D m n) α β,
      GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ))
        (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β P →
      ∃ R : PolF D m n, P = Q τ * R ∧ ∀ v ∈ R.vars, v.1 ≠ τ := by
    intro τ P α β h
    obtain ⟨s, f, g, hPs, hf, hg⟩ := GlobalTheory.T.isJointHighestWeightHarmonic_slice_outer_variables (Prod.mk τ) (fun a b h => (Prod.mk.inj h).2) _ _ _ _ _ P h
    choose! r hr using fun i (hi : i ∈ s) => hQ₀ τ α β (f i) (hf i hi)
    refine ⟨∑ i ∈ s, r i • g i, ?_, ?_⟩
    · rw [hPs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hr i hi, map_smul, smul_mul_assoc, mul_smul_comm]
    · intro v hv hvτ
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_sum_subset _ _ hv)
      have hvi' : v ∈ (g i).vars := by
        rw [MvPolynomial.smul_eq_C_mul] at hvi
        have := MvPolynomial.vars_mul (MvPolynomial.C (r i)) (g i) hvi
        simpa using this
      exact hg i hi v hvi' ⟨v.2, by rw [← hvτ]⟩
  have hQne : ∀ τ, Q τ ≠ 0 := by
    intro τ h0
    obtain ⟨α, β, hτ⟩ := hJ τ
    obtain ⟨R, hR, -⟩ := hfac τ P α β hτ
    exact hP0 (by rw [hR, h0, zero_mul])
  have hE : ∀ s : Finset D.what₂.Tau, ∀ P : PolF D m n,
      (∀ τ ∈ s, ∃ α β, GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ))
        (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β P) →
      ∃ R : PolF D m n, P = (∏ τ ∈ s, Q τ) * R ∧ ∀ v ∈ R.vars, v.1 ∉ s := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro P _; exact ⟨P, by simp, by simp⟩
    | insert τ₀ s hτ₀ ih =>
      intro P hPs
      obtain ⟨R, hPR, hRv⟩ := ih P (fun τ hτ => hPs τ (Finset.mem_insert_of_mem hτ))
      obtain ⟨α, β, hJ0⟩ := hPs τ₀ (Finset.mem_insert_self _ _)
      have hG0 : (∏ τ ∈ s, Q τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hQne τ
      have hGv : ∀ v ∈ (∏ τ ∈ s, Q τ).vars, v.1 ∈ s := by
        intro v hv
        obtain ⟨τ, hτ, hv'⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hv)
        have := MvPolynomial.vars_rename (Prod.mk τ) (Q₀ τ) hv'
        obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 this
        exact hτ
      have hJR := loc_jointTop _ _ _ α β _ R hG0 (fun v hv =>
        ⟨fun u h => hτ₀ (by have := hGv v hv; rw [← h] at this; simpa using this),
         fun u h => hτ₀ (by have := hGv v hv; rw [← h] at this; simpa using this)⟩) (hPR ▸ hJ0)
      obtain ⟨R', hRR', hR'v⟩ := hfac τ₀ R α β hJR
      refine ⟨R', by rw [hPR, hRR', Finset.prod_insert hτ₀]; ring, ?_⟩
      intro v hv
      rw [Finset.mem_insert, not_or]
      refine ⟨fun h => hR'v v hv h, hRv v ?_⟩
      have hR'0 : R' ≠ 0 := by rintro rfl; simp at hv
      rw [hRR', MvPolynomial.mem_vars_iff_degreeOf_ne_zero, MvPolynomial.degreeOf_mul_eq (hQne τ₀) hR'0]
      rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hv
      omega
  obtain ⟨R, hR, hRv⟩ := hE Finset.univ P (fun τ _ => hJ τ)
  obtain ⟨R', hR', hR'v⟩ := hE Finset.univ P' (fun τ _ => hJ' τ)
  have hc : ∀ R : PolF D m n, (∀ v ∈ R.vars, v.1 ∉ (Finset.univ : Finset D.what₂.Tau)) →
      R = MvPolynomial.C (R.coeff 0) := fun R h =>
    MvPolynomial.vars_eq_empty_iff_eq_C.1
      (Finset.eq_empty_of_forall_notMem fun v hv => h v hv (Finset.mem_univ _))
  rw [hc R hRv] at hR
  rw [hc R' hR'v] at hR'
  have hc0 : R.coeff 0 ≠ 0 := by
    intro h0; apply hP0; rw [hR, h0]; simp
  refine ⟨R'.coeff 0 / R.coeff 0, ?_⟩
  rw [hR', hR, MvPolynomial.smul_eq_C_mul, ← mul_assoc, mul_comm (MvPolynomial.C _) (∏ τ, Q τ), mul_assoc,
    ← MvPolynomial.C_mul, div_mul_cancel₀ _ hc0]

end GlobalTheory.HarmLine

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.PlaceTranslate

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by simp [Formalism.L2.Theta.mt]

theorem mt_one' (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mul_mt_eq {S T : HSp D} {e : AE D} {g : GA D S} (hg : ∀ i j, e * (mt S g - 1) i j = 0) {u : WO S T}
    (hu : IsHalf e u) : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g) = u := by
  have hM : ∀ k j, e * mt S g k j = e * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by
    intro k j
    have h := hg k j
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero] at h
    exact h
  ext i j
  rw [Matrix.mul_apply]
  conv_rhs => rw [← Matrix.mul_one (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc u i k * mt S g k j = (e * u i k) * mt S g k j := by rw [hu i k]
    _ = u i k * (e * mt S g k j) := by ring
    _ = u i k * (e * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j) := by rw [hM k j]
    _ = (e * u i k) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by ring
    _ = u i k * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := by rw [hu i k]

theorem actO_fix {S T : HSp D} {e : AE D} {g : GA D S} (hg : ∀ i j, e * (mt S g - 1) i j = 0) {u : WO S T}
    (hu : IsHalf e u) : actO S T g 1 u = u ∧ actO S T g⁻¹ 1 u = u := by
  have h1 := mul_mt_eq (T := T) hg hu
  have h2 : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) = u := by
    conv_lhs => rw [← h1]
    rw [Matrix.mul_assoc, ← mt_mul', mul_inv_cancel, mt_one', Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · simp only [actO, mt_one', Matrix.one_mul]; exact h2
  · simp only [actO, mt_one', Matrix.one_mul, inv_inv]; exact h1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem avgW_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (f g : WO (Vc D i) (Wc D i) → ℂ) :
    avgW R i t PP a tr ε κ (f + g) = avgW R i t PP a tr ε κ f + avgW R i t PP a tr ε κ g := by
  simp only [avgW, map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem avgW_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (c : ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) :
    avgW R i t PP a tr ε κ (c • f) = c • avgW R i t PP a tr ε κ f := by
  simp only [avgW, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => smul_comm _ _ _

theorem avgW_zero (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) : avgW R i t PP a tr ε κ 0 = 0 := by
  simp only [avgW, map_zero, smul_zero, Finset.sum_const_zero]

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D) (u : WO S T') : heisO ψ S T' u 0 = 0 := by
  funext w; simp [heisO]

theorem locSpan_pres : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP →
    ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)),
    v ∈ Sb → ∀ (ε : AF D.host.F) (a : AE D), IsPlaceIdem D v ε → a + cA D a = algebraMap (AF D.host.F) (AE D) ε →
    ∀ f : WO (Vc D i) (Wc D i) → ℂ, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f →
    ∀ f' ∈ locSpan R.ψ (Vc D i) (Wc D i) a f,
      TypeIn R i t (dropPl Sb v) f' ∧ CleanIn R i t (dropPl Sb v) f' ∧ LikeOff R i t Sb f' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t Sb v hv ε a hε hae f hT hC hL f' hf'
  set E' := algebraMap (AF D.host.F) (AE D) ε with hE'
  have hW := hω i t
  have hψ := hW.std
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := hT.1
  have hvd : v ∉ dropPl Sb v := by
    classical
    unfold dropPl
    simp
  have hsub : ∀ w, w ∈ dropPl Sb v → w ∈ Sb := by
    classical
    intro w hw
    unfold dropPl at hw
    exact Finset.mem_of_mem_erase hw

  have hsupp : ∀ κ : GA D (Vc D i), SuppIn (dropPl Sb v) (Vc D i) κ →
      SuppIn Sb (Vc D i) κ ∧ ∀ i' j', E' * (mt (Vc D i) κ - 1) i' j' = 0 := by
    intro κ hκ
    exact ⟨⟨hκ.1, fun w hw => hκ.2 w fun h => hw (hsub w h)⟩, hκ.2 v hvd ε hε⟩
  have hcE : cA D E' = E' := by
    rw [← hae, map_add (f := _), GlobalTheory.DualPairCheck.cA_cA, add_comm]

  let P : (WO (Vc D i) (Wc D i) → ℂ) → Prop := fun φ =>
    TypeIn R i t (dropPl Sb v) φ ∧ CleanIn R i t (dropPl Sb v) φ ∧ LikeOff R i t Sb φ
  have hgen : ∀ u : WO (Vc D i) (Wc D i), IsHalf E' u → P (heisO R.ψ (Vc D i) (Wc D i) u f) := by
    intro u hu
    have hthu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hth u
    refine ⟨⟨hthu, fun κ hκ hκs => ?_⟩, ?_, ⟨hthu, ?_⟩⟩
    · obtain ⟨hκS, hκv⟩ := hsupp κ hκs
      rw [hW.om_heis κ 1 u f hth, (actO_fix hκv hu).1, hT.2 κ hκ hκS, GlobalTheory.SplitScalar.heisO_smul]
    · intro PP a' ha' tr e he hex κ hκ hκs
      have hex' : ∃ w ∈ Sb, Over PP.1 w := by
        obtain ⟨w, hw, hO⟩ := hex; exact ⟨w, hsub w hw, hO⟩
      have hκs' : ∀ g, mirC R i PP a' tr e g ≠ 0 → SuppIn Sb (Vc D i) (κ g) := fun g hg => (hsupp _ (hκs g hg)).1
      have key : avgW R i t PP a' tr e κ (heisO R.ψ (Vc D i) (Wc D i) u f) =
          heisO R.ψ (Vc D i) (Wc D i) u (avgW R i t PP a' tr e κ f) := by
        simp only [avgW]
        rw [GlobalTheory.SplitScalar.heisO_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        by_cases hc : mirC R i PP a' tr e g = 0
        · rw [hc, zero_mul, zero_smul, zero_smul, heisO_zero']
        · rw [hW.om_heis (κ g)⁻¹ 1 u f hth, (actO_fix (hsupp _ (hκs g hc)).2 hu).2, GlobalTheory.SplitScalar.heisO_smul]
      rw [key, hC PP a' ha' tr e he hex' κ hκ hκs', heisO_zero']
    · intro c hc h0
      have hcomm : ∀ w ∈ c.support, heisO R.ψ (Vc D i) (Wc D i) w (heisO R.ψ (Vc D i) (Wc D i) u f) =
          heisO R.ψ (Vc D i) (Wc D i) u (heisO R.ψ (Vc D i) (Wc D i) w f) := by
        intro w hw
        have hw0 : E' • w = 0 := by
          ext i' j'; exact (hc w hw).2 v hv ε hε i' j'
        have hs : symplO (Vc D i) (Wc D i) w u = 0 := by
          have hu' : E' • u = u := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hu
          rw [← hu', ← hcE, ← GlobalTheory.SplitScalar.symplO_smul, hw0, GlobalTheory.SplitScalar.symplO_zero_left]
        rw [GlobalTheory.SplitScalar.heisO_comm, hs, AddChar.map_zero_eq_one, one_smul]
      have e1 : (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w (heisO R.ψ (Vc D i) (Wc D i) u f)) =
          heisO R.ψ (Vc D i) (Wc D i) u (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w f) := by
        unfold Finsupp.sum
        rw [GlobalTheory.SplitScalar.heisO_sum]
        refine Finset.sum_congr rfl fun w hw => ?_
        dsimp only
        rw [hcomm w hw, GlobalTheory.SplitScalar.heisO_smul]
      rw [e1, hL.2 c hc h0, heisO_zero']
  have h0 : P 0 := by
    have hz : IsThetaFunO R.ψ (Vc D i) (Wc D i) 0 := by simpa using theta_smul (0 : ℂ) hth
    refine ⟨⟨hz, fun κ _ _ => by rw [map_zero, smul_zero]⟩, fun _ _ _ _ _ _ _ _ _ _ => avgW_zero _ _ _ _ _ _ _ _,
      ⟨hz, fun c _ _ => ?_⟩⟩
    simp [heisO_zero']
  have hadd : ∀ φ₁ φ₂, P φ₁ → P φ₂ → P (φ₁ + φ₂) := by
    rintro φ₁ φ₂ ⟨⟨t1, T1⟩, C1, ⟨l1, L1⟩⟩ ⟨⟨t2, T2⟩, C2, ⟨l2, L2⟩⟩
    refine ⟨⟨theta_add t1 t2, fun κ hκ hκs => ?_⟩, fun PP a' ha' tr e he hex κ hκ hκs => ?_,
      ⟨theta_add l1 l2, fun c hc h0 => ?_⟩⟩
    · rw [map_add (f := _), T1 κ hκ hκs, T2 κ hκ hκs, smul_add]
    · rw [avgW_add, C1 PP a' ha' tr e he hex κ hκ hκs, C2 PP a' ha' tr e he hex κ hκ hκs, add_zero]
    · simp only [heisO_add', smul_add]
      rw [Finsupp.sum_add, L1 c hc h0, L2 c hc h0, add_zero]
  have hsmul : ∀ (r : ℂ) φ, P φ → P (r • φ) := by
    rintro r φ ⟨⟨t1, T1⟩, C1, ⟨l1, L1⟩⟩
    refine ⟨⟨theta_smul r t1, fun κ hκ hκs => ?_⟩, fun PP a' ha' tr e he hex κ hκ hκs => ?_,
      ⟨theta_smul r l1, fun c hc h0 => ?_⟩⟩
    · rw [map_smul, T1 κ hκ hκs, smul_comm]
    · rw [avgW_smul, C1 PP a' ha' tr e he hex κ hκ hκs, smul_zero]
    · have e1 : (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w (r • φ)) =
          r • (c.sum fun w z => z • heisO R.ψ (Vc D i) (Wc D i) w φ) := by
        rw [Finsupp.smul_sum]
        refine Finsupp.sum_congr fun w _ => ?_
        rw [GlobalTheory.SplitScalar.heisO_smul, smul_comm]
      rw [e1, L1 c hc h0, smul_zero]
  refine Submodule.span_induction (p := fun φ _ => P φ) ?_ h0 (fun x y _ _ hx hy => hadd x y hx hy)
    (fun r x _ hx => hsmul r x hx) hf'
  rintro φ ⟨u, hu, rfl⟩
  rw [hae] at hu
  exact hgen u hu

end GlobalTheory.DownLift.PlaceTranslate

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.HodgeAt

variable {l : ℕ} [Fact l.Prime]

def emb (P : LocPrime l) (σ : GQ l) (L : FinExt l) : ↥L.1 →ₐ[ℚ_[l]] P.R.BdR :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp (σ.toAlgHom.comp L.1.val)

def phiS (P : LocPrime l) (σ : GQ l) (L : FinExt l) : ↥L.1 ⊗[ℚ_[l]] P.R.BdR →ₐ[ℚ_[l]] P.R.BdR :=
  Algebra.TensorProduct.lift (emb P σ L) (AlgHom.id ℚ_[l] P.R.BdR) (fun _ _ => Commute.all _ _)

def PhiS (P : LocPrime l) (σ : GQ l) (L : FinExt l) (a : ℕ) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    Fin a → P.R.BdR :=
  fun i => phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1) x)

variable (P : LocPrime l) (σ : GQ l) (L : FinExt l) (a : ℕ)

theorem emb_apply (c : ↥L.1) : emb P σ L c = algebraMap (Om l) P.R.BdR (σ (c : Om l)) := rfl

theorem phiS_tmul (c : ↥L.1) (b : P.R.BdR) :
    phiS P σ L (c ⊗ₜ b) = algebraMap (Om l) P.R.BdR (σ (c : Om l)) * b := by
  simp [phiS, emb]

theorem PhiS_tmul (v : Fin a → ↥L.1) (b : P.R.BdR) :
    PhiS P σ L a (v ⊗ₜ b) = fun i => algebraMap (Om l) P.R.BdR (σ (v i : Om l)) * b := by
  funext i
  simp [PhiS, phiS_tmul]

theorem PhiS_add (x y : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (x + y) = PhiS P σ L a x + PhiS P σ L a y := by
  funext i
  simp [PhiS]

theorem PhiS_zero : PhiS P σ L a 0 = 0 := by
  funext i
  simp [PhiS]

theorem PhiS_sum {ι : Type} (s : Finset ι) (x : ι → (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (∑ i ∈ s, x i) = ∑ i ∈ s, PhiS P σ L a (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PhiS_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, PhiS_add, ih]

theorem PhiS_sm (r : ↥L.1 ⊗[ℚ_[l]] P.R.BdR) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) r x) = fun i => phiS P σ L r * PhiS P σ L a x i := by
  funext i
  simp only [PhiS]
  rw [GlobalTheory.DRFil.ext_sm, GlobalTheory.DRFil.sm_self, map_mul]

theorem PhiS_mulR (b : P.R.BdR) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) b x) = fun i => b * PhiS P σ L a x i := by
  rw [← GlobalTheory.DRFil.sm_one_tmul, PhiS_sm, phiS_tmul]
  funext i
  simp

end GlobalTheory.HodgeAt
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1), let ρ : Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) := ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r'); Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = Module.finrank ℚ_[l] ↥K.1 * m → (∀ (σ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), σ x ∈ LL.1) → ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) → ∀ (K' : FinExt l), K.1 ≤ K'.1 → LL.1 ≤ K'.1 → ∃ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ), (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) ρ τ' a) ∧ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  first | (exact @GlobalTheory.HTBasis.htc_basis) | (exact GlobalTheory.HTBasis.htc_basis) | (intros; apply GlobalTheory.HTBasis.htc_basis  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_cyclotomic_period_local_prime : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (n : ℕ), 0 < n → ∃ x : P.R.B, IsUnit x ∧ (⇑P.φB)^[n] x = (l : P.R.B) * x ∧ P.ιB x ∈ (P.PD K).Fil 1 ∧ P.ιB x ∉ (P.PD K).Fil 2 ∧ ∀ j : ℕ, 0 < j → j < n → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1 := by
  first | exact @GlobalTheory.LTPeriod.main | exact GlobalTheory.LTPeriod.main | (intros; apply GlobalTheory.LTPeriod.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

theorem _root_.GlobalTheory.T.isCrys_character_of_crystalline_vectors : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) := by
  first | exact @GlobalTheory.LetterCrys.isCrys_of_letters | exact GlobalTheory.LetterCrys.isCrys_of_letters | (intros; apply GlobalTheory.LetterCrys.isCrys_of_letters <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ), Continuous (fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g ∈ IK K, μ g = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = 0 then 1 else 0 := by
  first | exact @GlobalTheory.UnramifiedChar.isCrys_and_multV_eq | exact GlobalTheory.UnramifiedChar.isCrys_and_multV_eq | (intros; apply GlobalTheory.UnramifiedChar.isCrys_and_multV_eq <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

theorem _root_.GlobalTheory.T.crystalline_character_jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  first | exact @GlobalTheory.Per.CharJumps.jumps_of_exact_degree | exact GlobalTheory.Per.CharJumps.jumps_of_exact_degree | (intros; apply GlobalTheory.Per.CharJumps.jumps_of_exact_degree <;> assumption)
end
