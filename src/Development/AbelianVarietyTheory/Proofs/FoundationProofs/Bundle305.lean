module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle283
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTaylorThetaTranslate
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.IopSum

theorem act_inv_act {D : D7} {N N' : ℕ} (u : GA D N × GA D N') (ζ : XA D N N') :
    actA D N N' u⁻¹ (actA D N N' u ζ) = ζ := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem act_act_inv {D : D7} {N N' : ℕ} (u : GA D N × GA D N') (ζ : XA D N N') :
    actA D N N' u (actA D N N' u⁻¹ ζ) = ζ := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem mem_map_act {D : D7} {N N' : ℕ} (A : Submodule (𝓞 D.host.E) (XA D N N')) (u : GA D N × GA D N') (ζ : XA D N N') :
    ζ ∈ A.map (actA D N N' u) ↔ actA D N N' u⁻¹ ζ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [act_inv_act]
  · intro h
    exact ⟨_, h, act_act_inv u ζ⟩

theorem mem_moved {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} (g : GA D N) (g' : GA D N') (ζ : XA D N N') :
    ζ ∈ (latA D cc N N').map (actA D N N' (g, g')) ↔
      ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
        ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  rw [mem_map_act, Prod.inv_mk, actA_apply, mem_latA, Subgroup.coe_inv, Subgroup.coe_inv, inv_inv]

theorem pt_sub {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z z' : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z - z') = pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ z' := by
  funext τ i j
  simp [pt, embV, tor0, mul_sub]

theorem sd_of_moves {D : D7} {N : ℕ} (g : GA D N) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  have : L = Lt g := Submodule.ext fun x => (h x).trans ((hLt g).1 x).symm
  rw [this]
  exact (hLt g).2

end GlobalTheory.FinWeil.IopSum

namespace GlobalTheory.FinWeil

open IopSum

theorem iop_eq_sumOp : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → SelfDual γ ((latA D cc N N').map (actA D N N' (g, g'))) → ∀ F : TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') F → Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') F = ((Real.sqrt (idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) : ℝ))⁻¹ : ℂ) • ((sumOp WA (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := by
  intro D hG cc δ hC N N' w γ WA hM g g' L₁ L₁' hL hL' hSD F hF
  obtain ⟨hlat1, -, hlat3, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hG cc δ hC N N'
  have hidx := (GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hG cc δ hC N N' g g').1
  have hidx' := (GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hG cc δ hC N N' g⁻¹ g'⁻¹).1
  have hA := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hC.1.1 N N' g g' L₁ L₁' hL hL'
  have hB := GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hC.1.1 N N' g g' L₁ L₁' hL hL'
  have hW := (GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨L₁, L₁', sd_of_moves g hL, sd_of_moves g' hL', rfl⟩)).2.1
  simp only [← mem_moved] at hA hB
  set A := latA D cc N N' with hAdef
  set B := A.map (actA D N N' (g, g')) with hBdef
  set La₂ := La D (tor0 D cc δ) L₁ L₁' with hLa₂
  set La₁ := La0 D (tor0 D cc δ) N N' with hLa₁

  have hm : ∀ a ∈ A, idx A (A.map (actA D N N' (g⁻¹, g'⁻¹))) • a ∈ B := by
    intro a ha
    rw [hBdef, mem_map_act, map_nsmul, Prod.inv_mk]
    exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup
      (K := (A.map (actA D N N' (g⁻¹, g'⁻¹))).toAddSubgroup) ⟨a, ha, rfl⟩
  choose z hz hzB using fun q : La₂ ⧸ La₁.addSubgroupOf La₂ => hA _ (Quotient.out q).2
  have hsub : ∀ x y : Matrix (Fin N') (Fin N) D.host.E, x.map (inc D) - y.map (inc D) ∈ A ↔
      pt D (tor0 D cc δ) δ x - pt D (tor0 D cc δ) δ y ∈ La₁ := by
    intro x y
    rw [← Matrix.map_sub _ (map_sub (inc D)), hlat1, pt_sub]
  have huniq : ∀ q q', (z q).map (inc D) - (z q').map (inc D) ∈ A → q = q' := by
    intro q q' h
    rw [hsub, ← hz, ← hz] at h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', eq_comm, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using h
  have htr : ∀ b ∈ B, ∃! q, b - (z q).map (inc D) ∈ A := by
    intro b hb
    obtain ⟨y, a, ha, hy⟩ := hlat3 b _ (Nat.pos_of_ne_zero hidx')
    have hyB : y.map (inc D) ∈ B := hy ▸ B.add_mem hb (hm a ha)
    have hex : b - (z (QuotientAddGroup.mk ⟨_, hB y hyB⟩)).map (inc D) ∈ A := by
      have h1 : y.map (inc D) - (z (QuotientAddGroup.mk ⟨_, hB y hyB⟩)).map (inc D) ∈ A := by
        rw [hsub, ← hz]
        have h2 := QuotientAddGroup.out_eq' (QuotientAddGroup.mk ⟨_, hB y hyB⟩ : La₂ ⧸ La₁.addSubgroupOf La₂)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h2
        simpa [neg_add_eq_sub] using h2
      have h3 := A.sub_mem h1 (nsmul_mem ha (idx A (A.map (actA D N N' (g⁻¹, g'⁻¹)))))
      rw [hy] at h3
      convert h3 using 1
      abel
    refine ⟨QuotientAddGroup.mk ⟨_, hB y hyB⟩, ?_, ?_⟩
    · exact hex
    · intro q hq
      refine huniq _ _ ?_
      have := A.sub_mem hex hq
      rwa [sub_sub_sub_cancel_left] at this
  haveI : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hidx
  haveI : Finite (La₂ ⧸ La₁.addSubgroupOf La₂) := by
    refine Finite.of_injective (fun q => (QuotientAddGroup.mk ⟨_, hzB q⟩ :
      B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)) fun q q' h => ?_
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    refine (huniq q' q ?_).symm
    simpa [neg_add_eq_sub] using h
  haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
  obtain ⟨h1, h2⟩ := (GlobalTheory.FinWeil.sumOp_transversal hM.1 A B hSD).1 F hF _ (fun q => (z q).map (inc D)) hzB htr
  rw [h1, h2]
  funext v
  rw [Iop, finsum_eq_sum_of_fintype, AddSubgroup.index, Nat.card_eq_fintype_card, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hM.2.2.2.1, ← hz, hW _ (Quotient.out q).2]

end GlobalTheory.FinWeil
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.LatSelfDual

theorem ee_neg_eq_one_iff (t : ℝ) : ee (-t) = 1 ↔ ∃ m : ℤ, t = m := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [mul_comm (n : ℂ)] at hn
    have h3 := mul_left_cancel₀ h2 hn
    have h4 : (-t : ℝ) = (n : ℝ) := by exact_mod_cast h3
    push_cast
    linarith
  · rintro ⟨m, rfl⟩
    refine ⟨-m, ?_⟩
    push_cast
    ring

theorem gamA_add_left {D : D7} {ψ : AE D → ℂ} (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y) {N N' : ℕ} (ζ η ξ : XA D N N') :
    gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ := by
  simp only [gamA, ← hψ, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem gamA_add_right {D : D7} {ψ : AE D → ℂ} (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y) {N N' : ℕ} (ζ η ξ : XA D N N') :
    gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ := by
  simp only [gamA, ← hψ, Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem gamA_rat {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {ψ : AE D → ℂ} (hψ : ∀ a, ψ (inc D a) = psi0 D cc δ a)
    {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    gamA ψ (z.map (inc D)) (y.map (inc D)) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) := by
  rw [← hψ]

  simp only [gamA, Matrix.map_apply, map_sum, map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]

theorem latA_selfDual (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) (ψ : AE D → ℂ)
    (hψ : IsPsi D cc δ ψ) (N N' : ℕ) : SelfDual (gamA ψ) (latA D cc N N') := by
  obtain ⟨hadd, -, hrat, -, m₀, hm₀, h₀⟩ := hψ
  obtain ⟨l1, l2, l3, -, ⟨m₁, hm₁, h₁⟩, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hG cc δ hC N N'
  obtain ⟨w, -, hw⟩ := GlobalTheory.T.theta_point_additive_form D hG cc δ hC
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, hL, h1, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
    exact h1 ▸ (hL 1).2
  obtain ⟨-, -, t1, t2, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (La0 D (tor0 D cc δ) N N')
    (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩)
  have key : ∀ z y : Matrix (Fin N') (Fin N) D.host.E, gamA ψ (z.map (inc D)) (y.map (inc D)) = 1 ↔
      ∃ m : ℤ, (Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im = m := fun z y => by
    rw [gamA_rat hrat, ← (hw N N' z y).1, ee_neg_eq_one_iff]
  have hM : 0 < m₀ * m₁ * m₁ := by positivity
  have hs : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N',
      (∑ i, ∑ j, ((m₁ : AE D) * ζ i j) * sgA D ((m₁ : AE D) * η i j)) ∈ OhE D := fun ζ hζ η hη =>
    sum_mem fun i _ => sum_mem fun j _ => mul_mem (h₁ _ (hζ i j)) (Formalism.UG.P.csDual_sig_mem _ (h₁ _ (hη i j)))
  have dl : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ((m₀ * m₁ * m₁) • ζ) η = 1 := fun ζ hζ η hη => by
    rw [← h₀ _ (hs ζ hζ η hη), gamA]
    congr 1
    simp only [Finset.mul_sum, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have dr : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ζ ((m₀ * m₁ * m₁) • η) = 1 := fun ζ hζ η hη => by
    rw [← h₀ _ (hs ζ hζ η hη), gamA]
    congr 1
    simp only [Finset.mul_sum, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have iso : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ζ η = 1 := fun ζ hζ η hη => by
    obtain ⟨z, a, ha, hz⟩ := l3 ζ _ hM
    obtain ⟨y, b, hb, hy⟩ := l3 η _ hM
    have hzm : z.map (inc D) ∈ latA D cc N N' := hz ▸ add_mem hζ (nsmul_mem ha _)
    have hym : y.map (inc D) ∈ latA D cc N N' := hy ▸ add_mem hη (nsmul_mem hb _)
    have h := (key z y).2 (t1 _ ((l1 z).1 hzm) _ ((l1 y).1 hym))
    rwa [hz, gamA_add_left hadd, dl a ha _ hym, mul_one, hy, gamA_add_right hadd, dr ζ hζ b hb, mul_one] at h
  refine fun ζ => ⟨iso ζ, fun h => ?_⟩
  obtain ⟨z, a, ha, hz⟩ := l3 ζ 1 one_pos
  rw [one_smul] at hz
  have hzm : z.map (inc D) ∈ latA D cc N N' := by
    refine (l1 z).2 (t2 _ fun x hx => ?_)
    obtain ⟨y, rfl⟩ := l2 x hx
    have hym := (l1 y).2 hx
    rw [← key, hz, gamA_add_left hadd, h _ hym, iso a ha _ hym, mul_one]
  have : ζ = z.map (inc D) - a := by rw [hz, add_sub_cancel_right]
  rw [this]
  exact sub_mem hzm ha

end GlobalTheory.FinWeil.LatSelfDual
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TorsionTranslate

theorem ee_mem_Qbar (x : ℝ) (n : ℕ) (hn : 0 < n) (k : ℤ) (h₀ : (n : ℝ) * x = k) : ee x ∈ Qbar := by
  have h : (n : ℂ) * x = k := by exact_mod_cast h₀
  have h1 : ee x ^ n = 1 := by
    unfold ee
    rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k, ← h]
    congr 1
    ring
  refine (mem_algebraicClosure_iff).2 ?_
  refine IsAlgebraic.of_pow hn ?_
  rw [h1]
  exact isAlgebraic_one

theorem Hf_nsmul (D : D7) (T : Tor D) {N N' : ℕ} (m m' : ℕ) (x y : VC D N N') :
    Hf D T (m • x) (m' • y) = (m * m' : ℕ) * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left, Hf_conj D T (m' • y) x, ← Nat.cast_smul_eq_nsmul ℂ,
    Hf_smul_left, Hf_conj D T y x]
  simp [mul_assoc]

theorem translate_mem : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ F ∈ Tr D (tor0 D cc δ) b, ∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → U D (tor0 D cc δ) t F ∈ Tr D (tor0 D cc δ) b := by
  intro D cc δ hC N N' r b hb F hF t m hm ht
  have hint := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N'
    (LaB D (tor0 D cc δ) b) (Or.inl ⟨r, b, hb, rfl⟩)).2.2.1
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨s, ⟨m', hm', hs⟩, rfl⟩ := hG
    obtain ⟨k, hk⟩ := hint _ ht _ hs
    rw [Hf_nsmul] at hk
    have hk' : ((m * m' : ℕ) : ℝ) * (Hf D (tor0 D cc δ) t s).im = k := by
      rw [← hk]; simp
    have hq : ee (-(Hf D (tor0 D cc δ) t s).im / 2) ∈ Qbar := by
      refine ee_mem_Qbar _ (2 * (m * m')) (by positivity) (-k) ?_
      push_cast at hk' ⊢
      linear_combination -hk'
    have : U D (tor0 D cc δ) t (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (sgStar (tor0 D cc δ).abelian₂))) =
        (⟨_, hq⟩ : Qbar) • U D (tor0 D cc δ) (t + s) (pullB D (tor0 D cc δ) b (sgStar (tor0 D cc δ).abelian₂)) := by
      funext z
      rw [U_U]
      rfl
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨t + s, ⟨m * m', by positivity, ?_⟩, rfl⟩)
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_nsmul]; exact AddSubgroup.nsmul_mem _ ht _
    · rw [mul_nsmul']; exact AddSubgroup.nsmul_mem _ hs _
  | zero =>
    have : U D (tor0 D cc δ) t (0 : VC D N N' → ℂ) = 0 := by
      funext z; simp [U]
    rw [this]; exact zero_mem _
  | add G G' _ _ h h' =>
    have : U D (tor0 D cc δ) t (G + G') = U D (tor0 D cc δ) t G + U D (tor0 D cc δ) t G' := by
      funext z; simp [U, add_mul]
    rw [this]; exact add_mem h h'
  | smul a G _ h =>
    have : U D (tor0 D cc δ) t (a • G) = a • U D (tor0 D cc δ) t G := by
      funext z
      change U D (tor0 D cc δ) t (fun z => (a : ℂ) * G z) z = (a : ℂ) * U D (tor0 D cc δ) t G z
      simp only [U]; ring
    rw [this]; exact Submodule.smul_mem _ _ h

end GlobalTheory.TorsionTranslate
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostAdeleIso

theorem intAE_mul_mem (D : D7) {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem mem_intAE_iff_comm (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y ∈
      Formalism.L2.DIV.RInt D.host.F D.host.E := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem r hr =>
      obtain ⟨a, ha, x, rfl⟩ := hr
      have e : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
          (a ⊗ₜ[D.host.F] (x : D.host.E)) =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | neg a _ ha => rw [map_neg]; exact neg_mem ha
  · intro hw
    let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm
    have key : ∀ z ∈ Formalism.L2.DIV.RInt D.host.F D.host.E, c z ∈ intAE D := by
      intro z hz
      induction hz using Subring.closure_induction with
      | mem r hr =>
        rcases hr with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
        · exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), b, rfl⟩
        · exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | one =>
        rw [map_one]
        exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), 1, rfl⟩
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg a _ ha => rw [map_neg]; exact neg_mem ha
      | mul a b _ _ ha hb => rw [map_mul]; exact intAE_mul_mem D ha hb
    have := key _ hw
    rwa [show c (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = y from
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply _] at this

theorem exists_finiteAdele_equiv : ∀ D : D7, ∃ ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E, (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) ∧ (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) ∧ (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) := by
  intro D
  obtain ⟨ι, h1, h2, -, h4⟩ :=
    GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv D.host.F D.host.E
  refine ⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans ι,
    fun x => h1 x, fun y => (mem_intAE_iff_comm D y).trans (h2 _), fun a k P n h => h4 a k P n h⟩

end GlobalTheory.HostAdeleIso
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.galois_data_exists : ∀ D : D7, galEx D := by
  first | exact @GlobalTheory.GalExist.galEx_all | exact GlobalTheory.GalExist.galEx_all | (intros; apply GlobalTheory.GalExist.galEx_all <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.galois_conj_taylor_thetaTranslate : ∀ D : D7, gal1 D := by
  first | exact @GlobalTheory.JetConj.galois_translate_sgStar | exact GlobalTheory.JetConj.galois_translate_sgStar | (intros; apply GlobalTheory.JetConj.galois_translate_sgStar <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.theta_space_selfDual_pair_at_most_line : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → (∀ F ∈ ThSp D (tor0 D cc δ) A, ∀ G ∈ ThSp D (tor0 D cc δ) A, G ≠ 0 → ∃ c : ℂ, F = c • G) ∧ (∀ x ∈ A, ∀ F, Wd D (tor0 D cc δ) x F = fun z => al D (tor0 D cc δ) x * U D (tor0 D cc δ) x F z) ∧ (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) ∧ (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) → x ∈ A) ∧ A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ ∀ x ∈ A, ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
  first | exact @GlobalTheory.ThetaLine.theta_line | exact GlobalTheory.ThetaLine.theta_line | (intros; apply GlobalTheory.ThetaLine.theta_line <;> assumption)
end
