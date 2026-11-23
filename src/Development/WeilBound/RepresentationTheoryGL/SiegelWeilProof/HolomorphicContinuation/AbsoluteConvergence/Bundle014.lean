module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RepKerP
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle009
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

theorem groupPart : GroupPart := by
  intro n X a ha
  exact ⟨dil_mul ha, dil_zero ha, dil_up ha, cont_dil ha, fun y hy s => up_mul hy (dil_up ha s), cell_dec,
    fun g b hg h => conj_cell ha g b hg h, fun y hy s => cell_mul ha y hy s, dense_cell,
    fun p q e h => weight_factor_dilation ha p q e h⟩

end PositivityTheory.Rg.Sw.AbsSt.DF
end

section

noncomputable section

open MeasureTheory Matrix Set Topology

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem cpt_unitary (n : ℕ) : IsCompact (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hsub : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ⊆
      Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) 1)) := by
    intro U hU i _ j _
    simpa using entry_norm_bound_of_unitary hU i j
  refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset ?_ hsub
  have hset : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
      {A | star A * A = 1 ∧ A * star A = 1} := by
    ext A
    exact Iff.rfl
  rw [hset]
  have h1 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => star A * A := by fun_prop
  have h2 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A * star A := by fun_prop
  exact (isClosed_eq h1 continuous_const).inter (isClosed_eq h2 continuous_const)

instance cptU (n : ℕ) : CompactSpace (unitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (cpt_unitary n)

variable {n : ℕ}

def kE (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : GR n := Classical.choose ((hK n).1 a.1 b.1 a.2 b.2)

theorem kE_mem (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : kE hK a b ∈ KR n :=
  (Classical.choose_spec ((hK n).1 a.1 b.1 a.2 b.2)).1

theorem mR_kE (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : mR (kE hK a b) = kM a.1 b.1 :=
  (Classical.choose_spec ((hK n).1 a.1 b.1 a.2 b.2)).2

theorem mR_inj {g h : GR n} (e : mR g = mR h) : g = h := Subtype.ext (Units.ext e)

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem kE_mul (hK : KIso) (a b a' b' : unitaryGroup (Fin n) ℂ) :
    kE hK a b * kE hK a' b' = kE hK (a * a') (b * b') := by
  apply mR_inj
  rw [mR_mul, mR_kE, mR_kE, mR_kE, (hK n).2.1]
  rfl

theorem mR_inv_kE (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : mR (kE hK a b)⁻¹ = kM (a⁻¹ : unitaryGroup (Fin n) ℂ).1 (b⁻¹ : unitaryGroup (Fin n) ℂ).1 := by
  have h1 : kE hK a b * kE hK a⁻¹ b⁻¹ = 1 := by
    rw [kE_mul, mul_inv_cancel, mul_inv_cancel]
    apply mR_inj
    rw [mR_kE]
    exact (hK n).2.2.1
  have h2 : (kE hK a b)⁻¹ = kE hK a⁻¹ b⁻¹ := (eq_inv_of_mul_eq_one_right h1).symm
  rw [h2, mR_kE]

theorem continuous_mR : Continuous (fun g : GR n => mR g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_kM : Continuous (fun ab : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => kM ab.1 ab.2) := by
  unfold kM
  refine Continuous.matrix_fromBlocks ?_ ?_ ?_ ?_ <;> fun_prop

theorem continuous_kE (hK : KIso) (a : unitaryGroup (Fin n) ℂ) : Continuous (fun b : unitaryGroup (Fin n) ℂ => kE hK a b) := by
  refine continuous_induced_rng.2 ((Units.continuous_iff).2 ⟨?_, ?_⟩)
  · exact (continuous_kM.comp (continuous_const.prodMk continuous_subtype_val)).congr
      fun b => (mR_kE hK a b).symm
  · exact (continuous_kM.comp (continuous_const.prodMk
      (continuous_subtype_val.comp continuous_inv))).congr fun b => (mR_inv_kE hK a b).symm

theorem continuous_second_cayley_block_map : Continuous (fun M : M2 n => u2 M) := by
  have h21 : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))
  have h22 : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))
  unfold u2
  exact ((h21.const_smul Complex.I).neg).add h22

theorem lower_left_block_mul {X Y : M2 n} (hX : X.toBlocks₂₁ = 0) (hY : Y.toBlocks₂₁ = 0) : (X * Y).toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks X, ← fromBlocks_toBlocks Y, fromBlocks_multiply, toBlocks_fromBlocks₂₁, hX, hY]
  simp

theorem projOp_of (hK : KIso) (hR : RepKer) (hI : Iwa) (hM : Mult) : ProjOp := by
  intro m n ε c t p q e sL ρ hL _ _ W hW hWinv
  letI : MeasurableSpace (unitaryGroup (Fin n) ℂ) := borel _
  haveI : BorelSpace (unitaryGroup (Fin n) ℂ) := ⟨rfl⟩
  let μ : Measure (unitaryGroup (Fin n) ℂ) := Measure.haar
  let L : PX m n →ₗ[ℂ] (unitaryGroup (Fin n) ℂ → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun c : unitaryGroup (Fin n) ℂ => kE hK 1 c) ∘ₗ sL
  have hLapp : ∀ (P : PX m n) (c : unitaryGroup (Fin n) ℂ), L P c = sL P (kE hK 1 c) :=
    fun _ _ => rfl
  have hVfin : FiniteDimensional ℂ (W.map L) := inferInstance
  have hupK : ∀ a : unitaryGroup (Fin n) ℂ, toBlocks₂₁ (mR (kE hK a a)) = 0 := by
    intro a
    rw [mR_kE]
    exact (hK n).2.2.2.2.1 a.1
  have hVcont : ∀ φ ∈ W.map L, Continuous φ := by
    rintro φ ⟨P, -, rfl⟩
    show Continuous fun c => sL P (kE hK 1 c)
    exact (hL.cont P).comp (continuous_kE hK 1)
  have hVinv : ∀ φ ∈ W.map L, ∀ a : unitaryGroup (Fin n) ℂ,
      (fun x : unitaryGroup (Fin n) ℂ => φ (a * x)) ∈ W.map L := by
    rintro φ ⟨P, hP, rfl⟩ a
    refine ⟨F0 p q e (kE hK a a) • ρ (kE hK a⁻¹ 1) P,
      W.smul_mem _ (hWinv _ (kE_mem hK a⁻¹ 1) P hP), ?_⟩
    funext x
    have hx : kE hK 1 (a * x) = kE hK a a * (kE hK 1 x * kE hK a⁻¹ 1) := by
      rw [kE_mul, kE_mul]
      simp
    show sL (F0 p q e (kE hK a a) • ρ (kE hK a⁻¹ 1) P) (kE hK 1 x) = sL P (kE hK 1 (a * x))
    rw [hx, hL.law _ _ _ (hupK a), hL.kact _ _ _ (kE_mem hK a⁻¹ 1), map_smul,
      Pi.smul_apply, smul_eq_mul]
  obtain ⟨κ0, hκ0c, hκ0img, hκ0fix⟩ := hR (unitaryGroup (Fin n) ℂ) μ (W.map L) hVfin hVcont hVinv
  have hu2mem : ∀ k : KR n, u2 (mR (k : GR n)) ∈ unitaryGroup (Fin n) ℂ :=
    fun k => ((hK n).2.2.2.2.2 (k : GR n) k.2).2.1
  let κ : KR n → ℂ := fun k => κ0 ⟨u2 (mR (k : GR n)), hu2mem k⟩
  let eK : unitaryGroup (Fin n) ℂ → KR n := fun v => ⟨kE hK 1 v, kE_mem hK 1 v⟩
  have heK : Continuous eK := (continuous_kE hK 1).subtype_mk _
  have hκe : ∀ v, κ (eK v) = κ0 v := by
    intro v
    show κ0 _ = κ0 v
    congr 1
    apply Subtype.ext
    show u2 (mR (kE hK 1 v)) = v.1
    rw [mR_kE]
    exact ((hK n).2.2.2.1 1 v.1).2
  have hκc : Continuous κ :=
    hκ0c.comp ((continuous_second_cayley_block_map.comp (continuous_mR.comp continuous_subtype_val)).subtype_mk _)
  have hint : ∀ g : KR n → ℂ, Continuous g →
      ∫ k, κ k * g k ∂(μ.map eK) = ∫ v, κ0 v * g (eK v) ∂μ := by
    intro g hg
    have hm : Continuous fun k => κ k * g k := hκc.mul hg
    rw [integral_map (f := fun k => κ k * g k) heK.measurable.aemeasurable hm.aestronglyMeasurable]
    simp only [hκe]
  have hdec : ∀ y : GR n, ∃ (p' : GR n) (c : unitaryGroup (Fin n) ℂ),
      toBlocks₂₁ (mR p') = 0 ∧ y = p' * kE hK 1 c := by
    intro y
    obtain ⟨p0, k0, hp0, hk0, rfl⟩ := hI n y
    obtain ⟨ha, hb, hk⟩ := (hK n).2.2.2.2.2 k0 hk0
    have hk0e : k0 = kE hK ⟨_, ha⟩ ⟨_, hb⟩ := mR_inj (by rw [mR_kE]; exact hk)
    refine ⟨p0 * kE hK ⟨_, ha⟩ ⟨_, ha⟩, (⟨_, ha⟩ : unitaryGroup (Fin n) ℂ)⁻¹ * ⟨_, hb⟩, ?_, ?_⟩
    · rw [mR_mul]
      exact lower_left_block_mul hp0 (hupK _)
    · rw [mul_assoc, kE_mul]
      simp only [mul_one, mul_inv_cancel_left]
      exact congrArg (p0 * ·) hk0e
  refine ⟨μ.map eK, κ, inferInstance, hκc, ?_, ?_⟩
  · intro Q hQ y
    obtain ⟨p', c, hp', rfl⟩ := hdec y
    rw [hint (fun k : KR n => sL Q (p' * kE hK 1 c * (k : GR n)))
      ((hL.cont Q).comp (continuous_const.mul continuous_subtype_val))]
    have h1 : ∀ v, κ0 v * sL Q (p' * kE hK 1 c * ((eK v : KR n) : GR n)) =
        F0 p q e p' * (κ0 v * L Q (c * v)) := by
      intro v
      show κ0 v * sL Q (p' * kE hK 1 c * kE hK 1 v) = F0 p q e p' * (κ0 v * sL Q (kE hK 1 (c * v)))
      rw [mul_assoc, kE_mul, one_mul, hL.law _ _ _ hp']
      ring
    simp only [h1]
    rw [integral_const_mul, hκ0fix (L Q) ⟨Q, hQ, rfl⟩ c, hL.law _ _ _ hp', hLapp]
  · intro w f hf hfeq
    obtain ⟨Q, hQ, hQeq⟩ := hκ0img (fun c => f (kE hK 1 c)) (hf.comp (continuous_kE hK 1))
    refine ⟨Q, hQ, fun y => ?_⟩
    obtain ⟨p', c, hp', rfl⟩ := hdec y
    rw [hint (fun k : KR n => f (p' * kE hK 1 c * (k : GR n)))
      (hf.comp (continuous_const.mul continuous_subtype_val))]
    have h2 : ∀ v, κ0 v * f (p' * kE hK 1 c * ((eK v : KR n) : GR n)) =
        ((hLoc p' : ℂ) ^ w * F0 p q e p') * (κ0 v * f (kE hK 1 (c * v))) := by
      intro v
      show κ0 v * f (p' * kE hK 1 c * kE hK 1 v) = _
      rw [mul_assoc, kE_mul, one_mul, hfeq _ _ hp']
      ring
    simp only [h2]
    have hc := congrFun hQeq c
    rw [integral_const_mul, ← hc, hLapp, hL.law _ _ _ hp',
      ((hM n p q e).1 p' (kE hK 1 c) (kE_mem hK 1 c)).2]
    ring

theorem projOp (hI : Iwa) (hM : Mult) : ProjOp := projOp_of kIso repKer hI hM

end PositivityTheory.Rg.Sw.AbsSt.Proj
end
end

section

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ}
  {sL : PX m n →ₗ[ℂ] (GR n → ℂ)} {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ}
  {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

def invSub (Γ : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {F | Continuous F ∧ ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g}
  add_mem' := fun {F F'} hF hF' => ⟨hF.1.add hF'.1, fun γ hγ g => by simp [hF.2 γ hγ g, hF'.2 γ hγ g]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  smul_mem' := fun a F hF => ⟨hF.1.const_smul a, fun γ hγ g => by simp [hF.2 γ hγ g]⟩

theorem lam_zero (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) : l 0 = 0 := by
  obtain ⟨C, -, hC⟩ := hG.Λbd l hl
  have h0 := hC 0 0 continuous_const (fun _ _ _ => rfl) (fun x _ => by simp)
  exact norm_le_zero_iff.mp h0

theorem lam_smul (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) (a : ℂ) (F : G → ℂ)
    (hF : Continuous F) (hFi : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) : l (fun g => a * F g) = a * l F := by
  have h := hG.Λadd l hl a F 0 hF continuous_const hFi (fun _ _ _ => rfl)
  rw [lam_zero hG l hl, add_zero, add_zero] at h
  have hfun : (fun g => a * F g) = a • F := by
    funext g
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact h

theorem lam_local (hBH : BanachHol) (hFL : FactorL) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G → ℂ} {σ : ℝ} (hUo : IsOpen U) (hUr : GlobalTheory.Cont.IsRightDomain U)
    (hs : s₀ ∈ U) (hd : d ≠ 0) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ))
    (hEinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g)
    (hEr : ∀ z : ℂ, σ < z.re → ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) g)
    (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H s₀ ∧ H s₀ = l (I 1) ∧ ∀ᶠ z in 𝓝[≠] s₀, l (E z) = d.eval z * H z := by
  obtain ⟨C, hCc, hCb⟩ := hG.Λbd l hl
  obtain ⟨L, hL⟩ := hFL G (invSub Γ) l C hCc (fun F hF => hF.1)
    (fun a F hF F' hF' => hG.Λadd l hl a F F' hF.1 hF'.1 hF.2 hF'.2)
    (fun F hF M hM => hCb F M hF.1 hF.2 hM)
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hEcont : ∀ z ∈ U, Continuous (E z) := by
    intro z hzU
    exact hEc.comp_continuous (continuous_const.prodMk continuous_id) (fun g => ⟨hzU, mem_univ g⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := hBH C U (fun z x => E z x) hUo
    (hEc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩))
    (fun x => hEh x)
  have hfeq : ∀ z ∈ U, l (E z) = L (Φ z) := by
    intro z hzU
    have hmem : E z ∈ invSub Γ := ⟨hEcont z hzU, hEinv z hzU⟩
    rw [hL (E z) hmem (hEcont z hzU)]
    congr 1
    ext x
    rw [hΦ z hzU x]
    rfl
  have hfan : AnalyticOnNhd ℂ (fun z => l (E z)) U :=
    ((L.differentiable.comp_differentiableOn hΦd).congr hfeq).analyticOnNhd hUo
  obtain ⟨H, hHext, hHan, hHval⟩ := hG.Λval l hl
  refine ⟨H, hHan, hHval, ?_⟩
  have hext1 : GlobalTheory.Cont.IsExtAt (fun z => l (E z)) s₀ (fun z => l (E z)) :=
    (GlobalTheory.Cont.IsHolExt.isMerExt ⟨hUr, hfan, ⟨0, fun _ _ => rfl⟩⟩).isExtAt hs
  have hpoly : GlobalTheory.Cont.IsExtAt (fun z => d.eval z) s₀ (fun z => d.eval z) :=
    (GlobalTheory.Cont.IsHolExt.isMerExt ⟨hUr, fun z _ => (Polynomial.differentiable d).analyticAt z,
      ⟨0, fun _ _ => rfl⟩⟩).isExtAt hs
  have hmul := hpoly.mul hHext
  have hright : GlobalTheory.Cont.EqRight (fun z => l (E z))
      (fun s => d.eval s * l (GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (s - s₀) * sec 1 x))) := by
    obtain ⟨σ₁, hσ₁⟩ := hUr.1
    refine ⟨max σ σ₁, fun z hzr => ?_⟩
    have hzr' : max σ σ₁ < z.re := hzr
    have hz1 : σ < z.re := lt_of_le_of_lt (le_max_left _ _) hzr'
    have hzU : z ∈ U := hσ₁ (show σ₁ < z.re from lt_of_le_of_lt (le_max_right _ _) hzr')
    show l (E z) = d.eval z * l (GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z))
    obtain ⟨cs, hcsdef⟩ : ∃ cs, cs = GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) := ⟨_, rfl⟩
    rw [← hcsdef]
    have hE : ∀ g, E z g = d.eval z * cs g := by
      intro g
      rw [hEr z hz1 g, hcsdef]
    by_cases hd0 : d.eval z = 0
    · have hE0 : E z = 0 := funext fun g => by rw [hE g, hd0, zero_mul]; rfl
      rw [hE0, lam_zero hG l hl, hd0, zero_mul]
    · have hcs : cs = fun g => (d.eval z)⁻¹ * E z g := by
        funext g
        rw [hE g, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
      have hcsc : Continuous cs := by
        rw [hcs]
        exact continuous_const.mul (hEcont z hzU)
      have hcsi : ∀ γ ∈ Γ, ∀ g, cs (γ * g) = cs g := by
        intro γ hγ g
        rw [hcs]
        simp only
        rw [hEinv z hzU γ hγ g]
      have hEf : E z = fun g => d.eval z * cs g := funext hE
      rw [hEf, lam_smul hG l hl _ cs hcsc hcsi]
  exact (hext1.congr hright).eventuallyEq hmul

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem coV : CoV := by
  intro m n A hA F
  let Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' Aᵀ).restrictScalars ℝ
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a => Li.comp (LinearMap.proj a)
  have hL : ∀ y, L y = mulR A y := by
    intro y; funext a j
    simp [L, Li, mulR, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hdetLi : LinearMap.det Li = Complex.normSq A.det := by
    simp only [Li]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Matrix.det_transpose]
  have hdet : LinearMap.det L = Complex.normSq A.det ^ m := by
    simp only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hD : 0 < Complex.normSq A.det ^ m := pow_pos (Complex.normSq_pos.2 hA) _
  have hne : LinearMap.det L ≠ 0 := by rw [hdet]; exact hD.ne'
  let Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.equivOfDetNeZero L hne
  have hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = mulR A y := fun y => hL y
  have hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume := by
    have : (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L := by funext y; rfl
    rw [this]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne
  have h1 : ∫ y, F (mulR A y) = ((Complex.normSq A.det ^ m)⁻¹ : ℝ) * ∫ x, F x := by
    have := integral_map_equiv e F (μ := volume)
    simp only [he] at this
    rw [← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.2 hD)]
    simp [Complex.real_smul]
  rw [h1, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end
