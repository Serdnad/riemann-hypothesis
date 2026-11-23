module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfCoordSB

theorem eventually_pow_nsmul_mem {K M : Type} [NormedField K] [AddCommGroup M] [Module K M] [TopologicalSpace M]
    [ContinuousSMul K M] {p : ℕ} (hp : ‖(p : K)‖ < 1) {C U : Set M} (hC : IsCompact C) (hU : U ∈ 𝓝 (0 : M)) :
    ∀ᶠ n in Filter.atTop, ∀ x ∈ C, p ^ n • x ∈ U := by
  have hsmul : ∀ᶠ c in 𝓝 (0 : K), ∀ x ∈ C, c • x ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun y _ => ?_
    have ht : Filter.Tendsto (fun z : K × M => z.1 • z.2) (𝓝 ((0 : K), y)) (𝓝 (0 : M)) := (continuous_smul (M := K) (X := M)).tendsto' _ _ (by simp)
    exact ht hU
  have hpow : Filter.Tendsto (fun n : ℕ => (p : K) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp
  filter_upwards [hpow.eventually hsmul] with n hn x hx
  have hx' := hn x hx
  rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hx'

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  apply GlobalTheory.PartialIntegral.eventually_invariant <;> assumption

variable {D : D7} {m n : ℕ} {a : AE D}

theorem isHalf_add {x y : Mx D m n} (hx : IsHalf a x) (hy : IsHalf a y) : IsHalf a (x + y) := by
  unfold IsHalf at hx hy ⊢
  intro i j
  rw [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_sub {x y : Mx D m n} (hx : IsHalf a x) (hy : IsHalf a y) : IsHalf a (x - y) := by
  unfold IsHalf at hx hy ⊢
  intro i j
  rw [Matrix.sub_apply, mul_sub, hx i j, hy i j]

theorem isHalf_nsmul {x : Mx D m n} (hx : IsHalf a x) (k : ℕ) : IsHalf a (k • x) := by
  induction k with
  | zero =>
    unfold IsHalf
    intro i j
    simp
  | succ k ih =>
    rw [succ_nsmul]
    exact isHalf_add ih hx

theorem isSBHalf_iff_pull : ∀ (D : D7) (S T : HSp D) (v : FinPl D) (m n : ℕ) (a : AE D) (Λ : AddSubgroup (WO S T)) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a Λ κ → (∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsSBHalf a Λ (pull a κ Φ)) ∧ ∀ Ψ, IsSBHalf a Λ Ψ → ∃ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), Ψ = pull a κ Φ := by
  intro D S T v m n a Λ κ hκ
  unfold IsCoord at hκ
  obtain ⟨hadd, hbij, hopen, hcpt⟩ := hκ
  have h0 : κ 0 = 0 := by simpa using hadd 0 0
  have hns : ∀ (k : ℕ) (t : WO S T), κ (k • t) = k • κ t := by
    intro k t
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [succ_nsmul, succ_nsmul, hadd, ih]
  have hz : IsHalf a (0 : WO S T) := by
    unfold IsHalf
    intro i j
    simp
  have hO0 : κ '' {t | t ∈ Λ ∧ IsHalf a t} ∈ 𝓝 (0 : Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
    hopen.mem_nhds ⟨0, ⟨Λ.zero_mem, hz⟩, h0⟩
  refine ⟨fun Φ hΦ => ?_, fun Ψ hΨ => ?_⟩
  ·
    obtain ⟨p, hp0, hp⟩ : ∃ p : ℕ, 0 < p ∧ ‖(p : Fv D.host.F v)‖ < 1 := by
      refine ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero ?_, ?_⟩
      · rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact v.ne_bot
      · have h := (NumberField.FinitePlace.norm_lt_one_iff_mem D.host.F v
          ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.F)).mpr (Ideal.absNorm_mem v.asIdeal)
        simpa using h
    have hΦ' : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
    obtain ⟨h1, h2⟩ := hΦ'
    have hU := eventually_invariant h1 h2
    have E1 := eventually_pow_nsmul_mem hp hcpt hU
    have E2 := eventually_pow_nsmul_mem hp h2 hO0
    obtain ⟨N, hN1, hN2⟩ := (E1.and E2).exists
    unfold IsSBHalf
    refine ⟨fun t ht => ?_, p ^ N, pow_pos hp0 N, fun u hu hhu t => ?_, fun t ht => ?_⟩
    · by_contra hh
      exact ht (by simp [pull, hh])
    · by_cases htH : IsHalf a t
      · have h' : IsHalf a (t + (p ^ N) • u) := isHalf_add htH (isHalf_nsmul hhu _)
        have hm : ∀ x, Φ (x + (p ^ N) • κ u) = Φ x := hN1 (κ u) ⟨u, ⟨hu, hhu⟩, rfl⟩
        simp only [pull, if_pos htH, if_pos h']
        rw [hadd, hns]
        exact hm (κ t)
      · have h' : ¬ IsHalf a (t + (p ^ N) • u) := by
          intro hc
          apply htH
          have hc' := isHalf_sub hc (isHalf_nsmul hhu (p ^ N))
          simpa using hc'
        simp only [pull, if_neg htH, if_neg h']
    · have htH : IsHalf a t := by
        by_contra hh
        exact ht (by simp [pull, hh])
      have hΦt : Φ (κ t) ≠ 0 := by simpa [pull, htH] using ht
      obtain ⟨s, ⟨hsΛ, hsH⟩, hs⟩ := hN2 (κ t) (subset_tsupport Φ hΦt)
      have hk : IsHalf a ((p ^ N) • t) := isHalf_nsmul htH _
      have hst : s = (p ^ N) • t := hbij.injOn hsH hk (by rw [hs, hns])
      rw [← hst]
      exact hsΛ
  · unfold IsSBHalf at hΨ
    obtain ⟨hsupp, k, hk0, hinv, hΛ⟩ := hΨ

    obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin m) (Fin n) (Fv D.host.F v) → WO S T,
        ∀ x, IsHalf a (g x) ∧ κ (g x) = x :=
      ⟨Function.invFunOn κ {t | IsHalf a t}, fun x =>
        ⟨Function.invFunOn_mem (hbij.surjOn (Set.mem_univ x)), Function.invFunOn_eq (hbij.surjOn (Set.mem_univ x))⟩⟩
    have hgk : ∀ t, IsHalf a t → g (κ t) = t := fun t ht => hbij.injOn (hg _).1 ht (hg _).2
    have : CharZero (Fv D.host.F v) :=
      charZero_of_injective_algebraMap (R := D.host.F) (algebraMap D.host.F (Fv D.host.F v)).injective
    have hkF : ((k : ℕ) : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
    refine ⟨fun x => Ψ (g x), ?_, ?_⟩
    · show IsLocallyConstant (fun x => Ψ (g x)) ∧ HasCompactSupport (fun x => Ψ (g x))
      refine ⟨?_, ?_⟩
      · rw [IsLocallyConstant.iff_eventually_eq]
        intro x
        have hW : (fun z : Matrix (Fin m) (Fin n) (Fv D.host.F v) => (k : Fv D.host.F v) • z) ''
            (κ '' {t | t ∈ Λ ∧ IsHalf a t}) ∈ 𝓝 (0 : Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
          (isOpenMap_smul₀ hkF _ hopen).mem_nhds ⟨0, ⟨0, ⟨Λ.zero_mem, hz⟩, h0⟩, smul_zero _⟩
        have hc : Filter.Tendsto (fun y : Matrix (Fin m) (Fin n) (Fv D.host.F v) => y - x) (𝓝 x) (𝓝 0) :=
          (show Continuous fun y : Matrix (Fin m) (Fin n) (Fv D.host.F v) => y - x from
            continuous_id.sub continuous_const).tendsto' _ _ (by simp)
        filter_upwards [hc.eventually_mem hW] with y hy
        obtain ⟨w, ⟨u, ⟨huΛ, huH⟩, rfl⟩, hw0⟩ := hy
        have hw : (k : Fv D.host.F v) • κ u = y - x := hw0
        have hy' : y = x + κ (k • u) := by
          rw [hns, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v), hw]
          abel
        have hgy : g y = g x + k • u := by
          rw [hy']
          apply hbij.injOn (hg _).1 (isHalf_add (hg x).1 (isHalf_nsmul huH k))
          rw [(hg _).2, hadd, (hg x).2]
        show Ψ (g y) = Ψ (g x)
        rw [hgy]
        exact hinv u huΛ huH (g x)
      · refine HasCompactSupport.intro
          (K := (fun z : Matrix (Fin m) (Fin n) (Fv D.host.F v) => (k : Fv D.host.F v)⁻¹ • z) ''
            (κ '' {t | t ∈ Λ ∧ IsHalf a t}))
          (hcpt.image (continuous_const_smul _)) ?_
        intro x hx
        by_contra hne
        apply hx
        have hm := hΛ (g x) hne
        have hmem : κ (k • g x) ∈ κ '' {t | t ∈ Λ ∧ IsHalf a t} := ⟨_, ⟨hm, isHalf_nsmul (hg x).1 k⟩, rfl⟩
        rw [hns, (hg x).2, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v)] at hmem
        exact ⟨_, hmem, inv_smul_smul₀ hkF x⟩
    · funext t
      by_cases ht : IsHalf a t
      · simp only [pull, if_pos ht]
        rw [hgk t ht]
      · simp only [pull, if_neg ht]
        by_contra hne
        exact ht (hsupp t hne)

end GlobalTheory.HalfCoordSB

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal TensorProduct

namespace GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def term (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E) : ℂ :=
  res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G) 0

def phase (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) : ℂ :=
  ψ (symplO V W (isoPart V W C' (Matrix.map y (incA D))) (isoPart V W C κ))

def pairQ (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) : Matrix (Fin r) (Fin W.rank) D.host.E :=
  D.host.xi0 • (adj D y * W.gram)

def ratPair (W : HSp D) {r : ℕ} (y x : Matrix (Fin W.rank) (Fin r) D.host.E) : ℝ :=
  ((Algebra.trace ℚ D.host.E (Matrix.trace (pairQ W y * x)) : ℚ) : ℝ)

def dirAt (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin r) ℂ) : Matrix (Fin W.rank) (Fin V.rank) ℂ :=
  z * (adj D C * V.gram).map (tauE D τ)

def derAlong (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E) (G : WO V W → ℂ) : WO V W → ℂ :=
  ∑ τ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G

def finLift {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  x.map fun e => (pairA D.host.F 0 1 : AF D.host.F) ⊗ₜ[D.host.F] e

end GlobalTheory.MixedTerm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerForm

variable {D : D7}

def ad {m n : ℕ} (A : Mx D m n) : Mx D n m := Formalism.UG.cT (cA D) A

theorem ad_mul {l m n : ℕ} (A : Mx D l m) (B : Mx D m n) :
    ad (HMul.hMul A B : Mx D l n) = HMul.hMul (ad B) (ad A) := by
  unfold ad Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cA_incA_sig (e : D.host.E) : cA D (incA D e) = incA D (D.sp.cm.sig e) := by
  simp only [cA, sigR, incA, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]

theorem ad_map {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) :
    ad (A.map (incA D) : Mx D m n) = (adj D A).map (incA D) := by
  unfold ad adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, cA_incA_sig]
  rfl

theorem adj_mul {l m n : ℕ} (A : Matrix (Fin l) (Fin m) D.host.E) (B : Matrix (Fin m) (Fin n) D.host.E) :
    adj D (A * B) = adj D B * adj D A := by
  unfold adj Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem adj_adj {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D (adj D A) = A := by
  unfold adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  exact star_star (A i j)

theorem adj_gram (V : HSp D) : adj D V.gram = V.gram := by
  unfold adj Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  exact GlobalTheory.LatVac.gram_star V j i

theorem adj_gram_inv (V : HSp D) : adj D V.gram⁻¹ = V.gram⁻¹ := by
  have hu := GlobalTheory.LatVac.gram_det_isUnit V
  symm
  apply Matrix.inv_eq_left_inv
  calc adj D V.gram⁻¹ * V.gram = adj D V.gram⁻¹ * adj D V.gram := by rw [adj_gram]
    _ = adj D (V.gram * V.gram⁻¹) := (adj_mul _ _).symm
    _ = 1 := by
      rw [Matrix.mul_nonsing_inv (h := hu)]
      unfold adj Formalism.UG.cT
      simp

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹.map (incA D) * ad y) * T.gram.map (incA D) * x) := by
  unfold hO
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ad, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  unfold hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_mul_mul (V W : HSp D) {m n : ℕ} (y₁ : Mx D W.rank m) (y₂ : Mx D W.rank n)
    (P₁ : Matrix (Fin m) (Fin V.rank) D.host.E) (P₂ : Matrix (Fin n) (Fin V.rank) D.host.E) :
    hO V W (HMul.hMul y₁ (P₁.map (incA D))) (HMul.hMul y₂ (P₂.map (incA D))) =
      Matrix.trace (ad y₂ * W.gram.map (incA D) * y₁ * (P₁ * V.gram⁻¹ * adj D P₂).map (incA D)) := by
  rw [hO_eq_trace, ad_mul, ad_map, Matrix.map_mul, Matrix.map_mul]
  have key := Matrix.trace_mul_comm (V.gram⁻¹.map (incA D) * (adj D P₂).map (incA D))
    (ad y₂ * W.gram.map (incA D) * y₁ * P₁.map (incA D))
  simpa only [Matrix.mul_assoc] using key

theorem adj_zero {m n : ℕ} : adj D (0 : Matrix (Fin m) (Fin n) D.host.E) = 0 := by
  unfold adj Formalism.UG.cT
  simp

section Split

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}

theorem coef_iso_iso (hs : IsIsoSplit V V' C B) :
    adj D C * V.gram * V.gram⁻¹ * adj D (adj D C * V.gram) = 0 := by
  have hC : adj D C * V.gram * C = 0 := hs.frame.2.2
  rw [adj_mul, adj_adj, adj_gram, Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V),
    ← Matrix.mul_assoc]
  exact hC

theorem coef_iso_mid (hs : IsIsoSplit V V' C B) :
    adj D C * V.gram * V.gram⁻¹ * adj D (V'.gram⁻¹ * adj D B * V.gram) = 0 := by
  rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_gram_inv,
    Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V), ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hs.orth, Matrix.zero_mul]

theorem coef_mid_iso (hs : IsIsoSplit V V' C B) :
    V'.gram⁻¹ * adj D B * V.gram * V.gram⁻¹ * adj D (adj D C * V.gram) = 0 := by
  have hBC : adj D B * (V.gram * C) = 0 := by
    have h := congrArg (adj D) hs.orth
    rwa [adj_mul, adj_mul, adj_adj, adj_gram, adj_zero] at h
  rw [adj_mul, adj_adj, adj_gram, Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V),
    Matrix.mul_assoc, hBC, Matrix.mul_zero]

theorem coef_mid_mid (hs : IsIsoSplit V V' C B) :
    V'.gram⁻¹ * adj D B * V.gram * V.gram⁻¹ * adj D (V'.gram⁻¹ * adj D B * V.gram) = V'.gram⁻¹ := by
  rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_gram_inv,
    Matrix.mul_nonsing_inv_cancel_right (h := GlobalTheory.LatVac.gram_det_isUnit V)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (adj D B), ← Matrix.mul_assoc (adj D B * V.gram), hs.isom,
    Matrix.mul_nonsing_inv (h := GlobalTheory.LatVac.gram_det_isUnit V'), Matrix.mul_one]

theorem trace_swap {m n : ℕ} (Z : Mx D m m) (A : Mx D m n) (Y : Mx D n n) (X : Mx D n m) :
    Matrix.trace (Z * A * Y * X) = Matrix.trace (A * Y * X * Z) := by
  have key := Matrix.trace_mul_comm Z (A * Y * X)
  simpa only [Matrix.mul_assoc] using key

theorem hO_isoPart_add_midPart (hs : IsIsoSplit V V' C B) (y y' : Mx D W.rank r) (x x' : WO V' W) :
    hO V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = hO V' W x x' := by
  rw [hO_add_left, hO_add_right, hO_add_right]
  unfold isoPart midPart
  rw [hO_mul_mul, hO_mul_mul, hO_mul_mul, hO_mul_mul, coef_iso_iso hs, coef_iso_mid hs, coef_mid_iso hs,
    coef_mid_mid hs]
  simp only [Matrix.map_zero, map_zero, Matrix.mul_zero, Matrix.trace_zero, zero_add]
  rw [hO_eq_trace, trace_swap]

end Split

theorem symplOH_isoPart_add_midPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (y y' : Mx D W.rank r) (x x' : WO V' W),
    symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x' := by
  intro D V V' W r C B hs y y' x x'
  unfold symplOH symplO
  rw [hO_isoPart_add_midPart hs]

end GlobalTheory.TowerForm

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

theorem exists_leftInv_frame_kill_emb : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 ∧ K * B = 0 := by
  intro D V V' r C B hs
  have hadj : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), adj D X = Xᴴ := fun X => rfl
  have hG : V.gramᴴ = V.gram := by
    ext i j; simp [Matrix.conjTranspose_apply, GlobalTheory.LatVac.gram_star]
  have hBC : adj D B * V.gram * C = 0 := by
    have h := congrArg Matrix.conjTranspose hs.orth
    rw [hadj] at h ⊢
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f := C.mulVecLin.coprod B.mulVecLin
  have hf : ∀ c b, f (c, b) = C *ᵥ c + B *ᵥ b := fun c b => rfl
  have hker : LinearMap.ker f = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun ⟨c, b⟩ h => ?_
    rw [hf] at h
    have h1 := congrArg ((adj D B * V.gram).mulVec) h
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBC, hs.isom, Matrix.zero_mulVec,
      zero_add, Matrix.mulVec_zero] at h1
    have hb : b = 0 := Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (GlobalTheory.LatVac.gram_det_isUnit V')) (by rw [h1, Matrix.mulVec_zero])
    subst hb
    rw [Matrix.mulVec_zero, add_zero] at h
    have hc : c = 0 := Matrix.mulVec_injective_iff.2 hs.frame.2.1 (by rw [h, Matrix.mulVec_zero])
    subst hc
    rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  have key : ∀ c b, g (C *ᵥ c + B *ᵥ b) = (c, b) := fun c b => by
    rw [← hf]; exact LinearMap.congr_fun hg (c, b)
  have k1 : ∀ c, g (C *ᵥ c) = (c, 0) := fun c => by simpa using key c 0
  have k2 : ∀ b, g (B *ᵥ b) = (0, b) := fun b => by simpa using key 0 b
  refine ⟨LinearMap.toMatrix' (LinearMap.fst _ _ _ ∘ₗ g), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp [Matrix.toLin'_mul, Matrix.toLin'_apply, k1]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp [Matrix.toLin'_mul, Matrix.toLin'_apply, k2]

end GlobalTheory.HalfAverage

end
end

section

open Classical


theorem _root_.GlobalTheory.T.lowerZeroUpperBlockIndicator_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
  ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  first | exact @GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card | exact GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card | (intros; apply GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.dense_range_finite_vectors_discrete_series : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (D : DSRep T), Nontrivial D.HK.V → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → Dense (Set.range D.ι) := by
  first | exact @GlobalTheory.AnalyticDense.dense_range_of_factorial_bound | exact GlobalTheory.AnalyticDense.dense_range_of_factorial_bound | (intros; apply GlobalTheory.AnalyticDense.dense_range_of_factorial_bound <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.exists_isometry_intertwiner_of_derived_action : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (D : DSRep T) (πU : URep T) (E : D.HK.V →ₗ[ℂ] πU.H), Dense (Set.range D.ι) → (∀ y, ‖E y‖ = ‖D.ι y‖) → (∀ Y ∈ upq p q, ∀ y, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E y)) (E (D.HK.act Y y)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ j : D.U.H →ₗᵢ[ℂ] πU.H, (∀ y, j (D.ι y) = E y) ∧ ∀ g x, j (D.U.π g x) = πU.π g (j x) := by
  first | exact @GlobalTheory.FockTensor.exists_isometry_intertwiner_of_derived | exact GlobalTheory.FockTensor.exists_isometry_intertwiner_of_derived | (intros; apply GlobalTheory.FockTensor.exists_isometry_intertwiner_of_derived <;> assumption)
end
