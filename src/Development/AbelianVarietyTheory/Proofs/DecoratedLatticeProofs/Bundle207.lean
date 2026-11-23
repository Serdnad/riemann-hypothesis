module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle184
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_tprod_ne_zero_of_cc {D : D7} {c : Com D} {s : PiLocalization₂ D} (z : s.CC c) (hz : z ≠ 0) :
    ∃ v : s.M.Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply hz
  apply Subtype.ext
  show (z : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := ℂ) (s := fun τ => s.M.sm τ))
  rintro w ⟨v, rfl⟩
  simp [hne v]

theorem ip_unique {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD ipD' : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip ip' : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (h' : IsMet c s ipD' ip')
    (z : s.CC c) (hz : z ≠ 0) (x y : s.CC c) : ip x y = ip' x y := by
  obtain ⟨v, hv⟩ := exists_tprod_ne_zero_of_cc z hz
  have d : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) =
      ipD' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) := by rw [h.pure, h'.pure]
  have dne : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    intro h0
    have := h.posD _ hv
    rw [h0] at this
    simp at this
  have e1 := h.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  have e2 := h'.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  rw [e1, ← d] at e2
  exact mul_right_cancel₀ dne e2

theorem thetaChain_upward_induction_fixed_metric {D : D7} (hMet : MetEx D) (hSU : StepUp D) (hgap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) {c : Com D} (hc : c.Is)
    {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {ipD₀ ip₀} (h₀ : IsMet c s₀ ipD₀ ip₀) {u : s₀.CC c} {B : GlobalTheory.LFun.Fam D.host.E}
    (hu : IsPar u B) (hL : ∀ k < D.R.m, LNe c (c.chT (k + 1)) (chainPar c B k)) {k : ℕ} {s : PiLocalization₂ D}
    {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (hR : Reach c s₀ k s Θ) : k ≤ D.R.m → s.Is c k ∧
      ∀ ipD ip, IsMet c s ipD ip → ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k) := by
  induction hR with
  | zero =>
    intro _
    refine ⟨hs₀, fun ipD ip h => ⟨u, fun y => ?_, hu⟩⟩
    exact ip_unique h h₀ u hu.1 y u
  | @step k s Θ _ s' hs' p hp ih =>
    intro hk
    obtain ⟨hsk, ih⟩ := ih (by omega)
    refine ⟨hs', fun ipD' ip' h' => ?_⟩
    obtain ⟨ipD, ip, hm⟩ := hMet c hc k (by omega) s hsk
    obtain ⟨x, hx, hxp⟩ := ih ipD ip hm
    obtain ⟨x', hx', hx'p⟩ := hSU hgap c hc k (by omega) s s' hsk hs' p hp ipD ip ipD' ip' hm h' x (chainPar c B k) hxp
      (hL k (by omega))
    refine ⟨x', fun y => ?_, ?_⟩
    · rw [hx', hx]
      rfl
    · rw [chainPar_succ]
      exact hx'p

theorem reach_is {D : D7} {c : Com D} {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c}
    (hR : Reach c s₀ k s Θ) : s.Is c k := by
  cases hR with
  | zero => exact hs₀
  | step _ hs' _ _ => exact hs'

theorem chainUp_of : ∀ D : D7, MetEx D → ParBoundW D → ChainLW D → StepUp D → ChainUp D := by
  intro D hMet hPB hCL hSU hgap c hc s₀ hs₀ k hk s Θ hR
  refine ⟨reach_is hs₀ hR, fun ipD₀ ip₀ ipD ip h₀ h u B hu => ?_⟩
  have hb := hPB c hc 0 (Nat.zero_le _) s₀ hs₀ u B hu
  have hr : s₀.V.rank = D.R.r := by rw [hs₀.rank]; simp [Formalism.BasicNotions.Ranks.rankY]
  rw [hr] at hb
  exact (thetaChain_upward_induction_fixed_metric hMet hSU hgap hc hs₀ h₀ hu (fun k hk => hCL c hc B hb k hk) hR hk).2 ipD ip h

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ChainOnto.ParClosed

variable {D : D7}

theorem chS_succ (c : Com D) (k : ℕ) : c.chS (k + 1) = c.μ (k + 1) * c.eps (k + 1) := by
  unfold Com.chS Com.eps Lift.chrStep
  split_ifs <;> simp

theorem chT_succ (c : Com D) (k : ℕ) : c.chT (k + 1) = c.μ (k + 1) * c.eps k := by
  unfold Com.chT Com.eps Lift.chrStep
  rcases Nat.even_or_odd k with hk | hk
  · have h1 : Odd (k + 1) := hk.add_one
    have h2 : ¬ Odd k := Nat.not_odd_iff_even.2 hk
    simp [h1, h2]
  · have h1 : ¬ Odd (k + 1) := Nat.not_odd_iff_even.2 hk.add_one
    simp [h1, hk]

theorem eps_succ (c : Com D) (k : ℕ) :
    c.chS (k + 1) * (c.chT (k + 1))⁻¹ * c.eps k = c.eps (k + 1) := by
  rw [chS_succ, chT_succ]
  exact by
    have h : ∀ a b e : (AE D)ˣ →* Circle, a * b * (a * e)⁻¹ * e = b := fun a b e => by
      rw [_root_.mul_inv_rev, mul_comm e⁻¹ a⁻¹, mul_comm a b]
      simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one]
    exact h _ _ _

abbrev vf (χ : (AE D)ˣ →* Circle) : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := GlobalTheory.LFun.val (F := D.host.F) χ

theorem vf_mul (χ ψ : (AE D)ˣ →* Circle) : vf (χ * ψ) = vf χ * vf ψ := by
  funext w; simp [vf]

theorem twist_sum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → GlobalTheory.LFun.Fam K)
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) : GlobalTheory.LFun.twist (∑ i ∈ s, f i) z = ∑ i ∈ s, GlobalTheory.LFun.twist (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => funext w; simp [GlobalTheory.LFun.twist]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LFun.twist_add, ih]

theorem stepPar_eq (χS χT : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) :
    stepPar χS χT t B = GlobalTheory.LFun.twist B (vf (χS * χT⁻¹)) + GlobalTheory.LFun.segFam (vf χS) t := by
  funext w; simp [stepPar, GlobalTheory.LFun.twist, GlobalTheory.LFun.segFam, vf]

theorem chainPar_closed (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B k = GlobalTheory.LFun.twist (B + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (vf (c.μ i)) D.R.t) (vf (c.eps k)) := by
  induction k with
  | zero =>
    have h1 : vf (1 : (AE D)ˣ →* Circle) = 1 := funext fun w => GlobalTheory.LFun.val_one (F := D.host.F) w
    simp [chainPar, Com.eps, h1]
  | succ k ih =>
    rw [chainPar_succ, ih, stepPar_eq, GlobalTheory.LFun.twist_twist, ← vf_mul, eps_succ, Finset.sum_Icc_succ_top (by omega),
      ← add_assoc, GlobalTheory.LFun.twist_add (B + _), GlobalTheory.LFun.twist_segFam, ← vf_mul, chS_succ, mul_comm (c.eps (k + 1))]

theorem twist_vf (μ e : (AE D)ˣ →* Circle) : (vf (μ * e))⁻¹ * vf e = (vf μ)⁻¹ := by
  funext w; simp [vf, mul_comm]

theorem vf_quot (μ ν : (AE D)ˣ →* Circle) : (vf ν)⁻¹ * vf μ = vf (μ * ν⁻¹) := by
  funext w; simp [vf, mul_comm]

end GlobalTheory.ChainOnto.ParClosed


open GlobalTheory.ChainOnto.ParClosed in
theorem GlobalTheory.ChainOnto.chainPar_twist_chT : ∀ (D : D7) (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ),
    GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ =
      GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ +
        ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t := by
  intro D c B k
  change GlobalTheory.LFun.twist (chainPar c B k) (vf (c.chT (k + 1)))⁻¹ =
    GlobalTheory.LFun.twist B (vf (c.μ (k + 1)))⁻¹ + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (vf (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t
  rw [chainPar_closed, GlobalTheory.LFun.twist_twist, chT_succ, twist_vf, GlobalTheory.LFun.twist_add, twist_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.LFun.twist_segFam, vf_quot]

end
end

section

noncomputable section

namespace GlobalTheory.ChainOnto

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

section Move

variable {G : Type} [Group G] {K : Subgroup G}

theorem mem_doubleCoset_inv_iff {a g : G} :
    g⁻¹ ∈ DoubleCoset.doubleCoset a (K : Set G) K ↔ g ∈ DoubleCoset.doubleCoset a⁻¹ (K : Set G) K := by
  simp only [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, K.inv_mem hh, ?_⟩
    have hg : g = (h * a * k)⁻¹ := by rw [← e, inv_inv]
    rw [hg]
    group
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, K.inv_mem hh, ?_⟩
    rw [e]
    group

theorem dosetInd_comp_inv (a : G) : (fun g => dosetInd ℂ K a g⁻¹) = dosetInd ℂ K a⁻¹ := by
  funext g
  simp only [dosetInd]
  by_cases h : g ∈ DoubleCoset.doubleCoset a⁻¹ (K : Set G) K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mem_doubleCoset_inv_iff.mpr h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (mem_doubleCoset_inv_iff.mp h'))]

theorem out_mem_doubleCoset_iff (a : G) (c : G ⧸ K) :
    c.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ↔ ∃ k ∈ K, c = ((k * a : G) : G ⧸ K) := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨h, hh, ?_⟩
    have hc : ((c.out : G) : G ⧸ K) = c := QuotientGroup.out_eq' c
    rw [← hc, e, QuotientGroup.eq]
    have hx : (h * a * k)⁻¹ * (h * a) = k⁻¹ := by group
    rw [hx]
    exact K.inv_mem hk
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (k * a)
    exact ⟨k, hk, h, h.2, hh⟩

private theorem finite_left_cosets_of_isCommensurated (hK : IsCommensurated K) (a : G) :
    {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)}.Finite := by
  have h := hK a
  set H := K.map (MulAut.conj a).toMonoidHom with hH
  have hfin : Finite (K ⧸ H.subgroupOf K) := by
    unfold Subgroup.relIndex at h
    exact Subgroup.index_ne_zero_iff_finite.mp h
  apply (Set.finite_range (fun q : K ⧸ H.subgroupOf K => ((((q.out : K) : G) * a : G) : G ⧸ K))).subset
  rintro c ⟨k, hk, rfl⟩
  obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf K) (⟨k, hk⟩ : K)
  refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
  simp only
  rw [hh', QuotientGroup.eq]
  have hm : ((h' : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp h'.2
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hm
  have hy' : ((h' : K) : G) = a * y * a⁻¹ := by
    rw [← hyeq]
    simp [MulAut.conj_apply]
  have hx : ((((⟨k, hk⟩ : K) * (h' : K) : K) : G) * a)⁻¹ * (k * a) = y⁻¹ := by
    rw [Subgroup.coe_mul, hy']
    simp only [Subgroup.coe_mk]
    group
  rw [hx]
  exact K.inv_mem hy

theorem finsum_dosetInd_out (hK : IsCommensurated K) (a : G) :
    ∑ᶠ c : G ⧸ K, dosetInd ℂ K a c.out = (Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} : ℂ) := by
  classical
  set S := {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} with hSdef
  have hS : S.Finite := finite_left_cosets_of_isCommensurated hK a
  have hind : ∀ c : G ⧸ K, dosetInd ℂ K a c.out = S.indicator (fun _ => (1 : ℂ)) c := by
    intro c
    simp only [dosetInd, Set.indicator_apply, out_mem_doubleCoset_iff, hSdef, Set.mem_setOf_eq, Pi.one_apply]
  rw [finsum_congr hind, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hcard : Nat.card S = hS.toFinset.card := Nat.card_eq_card_finite_toFinset hS
  exact_mod_cast hcard.symm

private theorem apply_eq_of_mem_fixed {G V : Type} [Group G] {K : Subgroup G} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {v : V} (hv : v ∈ fixed ρ K) {k : G} (hk : k ∈ K) : ρ k v = v := by
  have h : ∀ h : K, ρ h v = ((1 : K →* ℂˣ) h : ℂ) • v := hv
  simpa using h ⟨k, hk⟩

private theorem invariant_pairing_doubleCoset_eq {G U X X' : Type} [Group G] {K : Subgroup G} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X')
    (hb : ∀ g u y, b (π g u) (ρ g y) = b u y) {u : U} (hu : u ∈ fixed π K) {y : X} (hy : y ∈ fixed ρ K)
    {a w : G} (hw : w ∈ DoubleCoset.doubleCoset a (K : Set G) K) : b (π w u) y = b (π a u) y := by
  obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hw
  have hu' : π k' u = u := apply_eq_of_mem_fixed π hu hk'
  have hy' : ρ k⁻¹ y = y := apply_eq_of_mem_fixed ρ hy (K.inv_mem hk)
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hu']
  calc b (π k (π a u)) y = b (π k (π a u)) (ρ k (ρ k⁻¹ y)) := by rw [Representation.self_inv_apply]
    _ = b (π a u) (ρ k⁻¹ y) := hb k _ _
    _ = b (π a u) y := by rw [hy']

private theorem pairing_heckeVec_dosetInd_eq_card_smul {G U X X' : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X')
    (hb : ∀ g u y, b (π g u) (ρ g y) = b u y) {u : U} (hu : u ∈ fixed π K) {y : X} (hy : y ∈ fixed ρ K)
    (r : ℂ) (a : G) :
    b (heckeVec π K (r • dosetInd ℂ K a) u) y =
      (r * (Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} : ℂ)) • b (π a u) y := by
  classical
  have hS := finite_left_cosets_of_isCommensurated hK a
  have hind : ∀ c : G ⧸ K, c ∉ {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} → dosetInd ℂ K a c.out = 0 := by
    intro c hc
    simp only [dosetInd]
    exact Set.indicator_of_notMem (fun h => hc ((out_mem_doubleCoset_iff a c).mp h)) _
  rw [← LinearMap.flip_apply b (heckeVec π K (r • dosetInd ℂ K a) u) y]
  unfold heckeVec
  have hsupp : (Function.support fun c : G ⧸ K => (r • dosetInd ℂ K a) c.out • π c.out u).Finite := by
    apply hS.subset
    intro c hc
    by_contra hcS
    apply hc
    simp [hind c hcS]
  rw [map_finsum _ hsupp]
  have hterm : ∀ c : G ⧸ K, (b.flip y) ((r • dosetInd ℂ K a) c.out • π c.out u) =
      (r * dosetInd ℂ K a c.out) • b (π a u) y := by
    intro c
    rw [map_smul, LinearMap.flip_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hc : c ∈ {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)}
    · rw [invariant_pairing_doubleCoset_eq π ρ b hb hu hy ((out_mem_doubleCoset_iff a c).mpr hc)]
    · simp [hind c hc]
  rw [finsum_congr hterm, ← finsum_smul, ← mul_finsum, finsum_dosetInd_out hK a]

private theorem comp_inv_mem_hecke {G : Type} [Group G] {K : Subgroup G} {ψ : G → ℂ} (hψ : ψ ∈ Hecke ℂ K) :
    (fun g => ψ g⁻¹) ∈ Hecke ℂ K := by
  classical
  have h : IsBiInv K ψ ∧ FinDosetSupp K ψ := hψ
  obtain ⟨hbi, S, hS⟩ := h
  show IsBiInv K (fun g => ψ g⁻¹) ∧ FinDosetSupp K (fun g => ψ g⁻¹)
  refine ⟨fun a b g => ?_, S.image (fun s => s⁻¹), fun g hg => ?_⟩
  · have e := hbi b⁻¹ a⁻¹ g⁻¹
    simp only [Subgroup.coe_inv] at e
    simp only
    rw [← e]
    congr 1
    group
  · obtain ⟨s, hs, a, b, e⟩ := hS g⁻¹ hg
    refine ⟨s⁻¹, Finset.mem_image_of_mem _ hs, b⁻¹, a⁻¹, ?_⟩
    have hg' : g = (↑a * s * ↑b)⁻¹ := by rw [← e, inv_inv]
    rw [hg', Subgroup.coe_inv, Subgroup.coe_inv]
    group

end Move

theorem heckeVec_move : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → CosetSym K →
    ∀ (U X X' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X'),
    (∀ g u y, b (π g u) (ρ g y) = b u y) → ∀ f ∈ fixed π K, ∀ x ∈ fixed ρ K, ∀ φ ∈ Hecke ℂ K,
    (fun g => φ g⁻¹) ∈ Hecke ℂ K ∧ b (heckeVec π K φ f) x = b f (heckeVec ρ K (fun g => φ g⁻¹) x) := by
  intro G _ K hK hsym U X X' _ _ _ _ _ _ π ρ b hb f hf x hx φ hφ
  refine ⟨comp_inv_mem_hecke hφ, ?_⟩
  refine hecke_induction (p := fun ψ => b (heckeVec π K ψ f) x = b f (heckeVec ρ K (fun g => ψ g⁻¹) x))
    ?_ ?_ ?_ hφ
  · simp [heckeVec]
  · intro ψ hψ ψ' hψ' e e'
    have hsum : (fun g => (ψ + ψ') g⁻¹) = (fun g => ψ g⁻¹) + (fun g => ψ' g⁻¹) := rfl
    rw [heckeVec_add hK π hψ hψ' f, hsum, heckeVec_add hK ρ (comp_inv_mem_hecke hψ) (comp_inv_mem_hecke hψ') x,
      map_add, LinearMap.add_apply, map_add, e, e']
  · intro r a
    have hc : (fun g => (r • dosetInd ℂ K a) g⁻¹) = r • dosetInd ℂ K a⁻¹ := by
      funext g
      rw [Pi.smul_apply, Pi.smul_apply, ← dosetInd_comp_inv a]
    have hb' : ∀ g y u, b.flip (ρ g y) (π g u) = b.flip y u := fun g y u => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply, hb]
    rw [hc, pairing_heckeVec_dosetInd_eq_card_smul hK π ρ b hb hf hx r a, ← LinearMap.flip_apply b f (heckeVec ρ K (r • dosetInd ℂ K a⁻¹) x),
      pairing_heckeVec_dosetInd_eq_card_smul hK ρ π b.flip hb' hx hf r a⁻¹, LinearMap.flip_apply, hsym a]
    congr 1
    rw [← hb a f (ρ a⁻¹ x), Representation.self_inv_apply]

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.InertSym

theorem cosets_eq {G : Type} [Group G] (K : Subgroup G) {g g' : G} {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (e : g' = a * g * b) (c : G ⧸ K) :
    (∃ k ∈ K, c = ((k * g' : G) : G ⧸ K)) ↔ (∃ k ∈ K, c = ((k * g : G) : G ⧸ K)) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a, mul_mem hk ha, ?_⟩
    rw [e, show k * (a * g * b) = (k * a * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, mul_mem hk (inv_mem ha), ?_⟩
    rw [e, show k * a⁻¹ * (a * g * b) = (k * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]

theorem cosetSym_of_inv {G : Type} [Group G] (K : Subgroup G)
    (h : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, g⁻¹ = a * g * b) : CosetSym K := by
  intro g
  obtain ⟨a, ha, b, hb, e⟩ := h g
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun c => cosets_eq K ha hb e c)).symm

theorem inv_mem_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) (g : GU σ n) :
    ∃ a ∈ KU σ n, ∃ b ∈ KU σ n, g⁻¹ = a * g * b := by
  have hint : ∀ i j, Formalism.UG.antiJ L n i j ∈ Formalism.UG.intL L := by
    intro i j; unfold Formalism.UG.antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := Formalism.UG.P.cartan_exists_glint (Formalism.UG.intL L) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := (GlobalTheory.UnitarySwap.inv_mem_doubleCoset_and_comm).1 L ϖ σ q n J hU hJ (by
    intro i j
    rw [hJe]
    simp only [Formalism.UG.antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (g : GL (Fin n) L) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩

end GlobalTheory.ChainOnto.InertSym

namespace GlobalTheory.ChainOnto

theorem inert_cosetSym_heckeEven : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ n : ℕ, IsCommensurated (KU σ n) ∧ CosetSym (KU σ n) ∧ ∀ φ ∈ Hecke ℂ (KU σ n), ∀ g, φ g⁻¹ = φ g := by
  intro L _ _ _ ϖ σ q hU n
  refine ⟨Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n, InertSym.cosetSym_of_inv _ (InertSym.inv_mem_KU hU n), ?_⟩
  intro φ hφ g
  obtain ⟨a, ha, b, hb, e⟩ := InertSym.inv_mem_KU hU n g
  rw [e]
  exact hφ.1 ⟨a, ha⟩ ⟨b, hb⟩ g

end GlobalTheory.ChainOnto

end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → SumAgree Ch sel mu cst σ₀ P ι s W ν := by
  first | exact @GlobalTheory.TwSumAgree.sumAgree | exact GlobalTheory.TwSumAgree.sumAgree | (intros; apply GlobalTheory.TwSumAgree.sumAgree <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.theta_kernel_moderate_growth_both_variables : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → GlobalTheory.Grow.ModGrowth₂ S T fun g h => thetaKO om g h f := by
  first | exact @GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ | exact GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ | (intros; apply GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ <;> assumption)
end
