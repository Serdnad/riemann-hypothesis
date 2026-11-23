module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.HenselQuad

@[expose] public section

section

noncomputable section
open Classical Polynomial

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

section Abstract

variable {E : Type} [Field E] [CharZero E] [StarRing E]

theorem one_add_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) + t * s ≠ 0 := by
  intro h
  have e : star ((1:E) + t * s) = 1 - t * s := by
    rw [star_add, star_one, star_mul, hs, star_natCast]; ring
  have h2 : (1:E) - t * s = 0 := by rw [← e, h, star_zero]
  have h3 : (2:E) = 0 := by linear_combination h + h2
  exact two_ne_zero h3

theorem one_sub_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) - t * s ≠ 0 := by
  intro h
  have e : star ((1:E) - t * s) = 1 + t * s := by
    rw [star_sub, star_one, star_mul, hs, star_natCast]; ring
  have h2 : (1:E) + t * s = 0 := by rw [← e, h, star_zero]
  have h3 : (2:E) = 0 := by linear_combination h + h2
  exact two_ne_zero h3

def cay (s : E) (t : ℕ) : E := (1 + t * s) / (1 - t * s)

theorem cay_norm (s : E) (hs : star s = -s) (t : ℕ) : star (cay s t) * cay s t = 1 := by
  unfold cay
  have h1 := one_add_ne s hs t
  have h2 := one_sub_ne s hs t
  have e1 : star ((1:E) + t * s) = 1 - t * s := by
    rw [star_add, star_one, star_mul, hs, star_natCast]; ring
  have e2 : star ((1:E) - t * s) = 1 + t * s := by
    rw [star_sub, star_one, star_mul, hs, star_natCast]; ring
  rw [star_div₀, e1, e2, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero h1 h2)]
  ring

theorem cay_inj (s : E) (hs : star s = -s) (hs0 : s ≠ 0) : Function.Injective (cay s) := by
  intro a b hab
  unfold cay at hab
  have ha1 := one_sub_ne s hs a
  have hb1 := one_sub_ne s hs b
  rw [div_eq_div_iff ha1 hb1] at hab
  have h0 : ((a:E) - b) * s * 2 = 0 := by linear_combination hab
  have hab' : ((a:E) - b) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hs0
    · exact absurd h two_ne_zero
  exact_mod_cast sub_eq_zero.mp hab'

theorem exists_norm_one (s : E) (hs : star s = -s) (hs0 : s ≠ 0) (p : E[X]) (hp : p ≠ 0) :
    ∃ z : E, star z * z = 1 ∧ z ≠ 1 ∧ p.eval z ≠ 0 := by
  classical
  let S : Finset E := insert 1 p.roots.toFinset
  have hfin : (cay s ⁻¹' (S : Set E)).Finite :=
    S.finite_toSet.preimage (cay_inj s hs hs0).injOn
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff] at ht
  refine ⟨cay s t, cay_norm s hs t, ?_, ?_⟩
  · intro h
    apply ht
    simp [S, h]
  · intro h
    apply ht
    simp [S, Polynomial.mem_roots', hp, h]

theorem eval_charpolyRev' {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (z : E) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite]
  exact mul_comm _ _

theorem split_unitary (s : E) (hs : star s = -s) (hs0 : s ≠ 0) {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) E) :
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) E)).det ≠ 0 := by
  classical
  have hp : (γ : Matrix (Fin n) (Fin n) E).charpolyRev ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    rw [eval_charpolyRev', zero_smul, sub_zero, Matrix.det_one, eval_zero] at h0
    exact one_ne_zero h0
  obtain ⟨z, hz, hz1, hev⟩ := exists_norm_one s hs hs0 _ hp
  rw [eval_charpolyRev'] at hev
  have hu : (z • (1 : Matrix (Fin n) (Fin n) E)) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, one_mul,
      mul_comm z, hz, one_smul]
  have hv : (star z • (1 : Matrix (Fin n) (Fin n) E)) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, star_star, smul_mul_smul_comm, one_mul,
      hz, one_smul]
  let u : Matrix.unitaryGroup (Fin n) E := ⟨_, hu⟩
  let v : Matrix.unitaryGroup (Fin n) E := ⟨_, hv⟩
  refine ⟨v, u * γ, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (γ : Matrix (Fin n) (Fin n) E) = (star z • 1) * ((z • 1) * (γ : Matrix (Fin n) (Fin n) E))
    rw [← mul_assoc, smul_mul_smul_comm, one_mul, hz, one_smul, one_mul]
  · show (1 - star z • (1 : Matrix (Fin n) (Fin n) E)).det ≠ 0
    have e : (1 : Matrix (Fin n) (Fin n) E) - star z • 1 = (1 - star z) • 1 := by
      rw [sub_smul, one_smul]
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    apply pow_ne_zero
    intro h
    apply hz1
    have h' : star z = 1 := (sub_eq_zero.mp h).symm
    simpa using congrArg star h'
  · show (1 - (z • 1) * (γ : Matrix (Fin n) (Fin n) E)).det ≠ 0
    rwa [smul_mul_assoc, one_mul]

end Abstract

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem exists_skew (D : Car) : letI := D.host.cmStar; ∃ s : D.host.E, star s = -s ∧ s ≠ 0 := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  by_contra hno
  push Not at hno
  apply NumberField.IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => ?_
  have h := hno (x - star x) (by rw [star_sub, star_star]; ring)
  exact (sub_eq_zero.mp h).symm

theorem split_host (D : Car) {n : ℕ} :
    letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) D.host.E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  letI := D.host.cmStar
  intro γ
  obtain ⟨s, hs, hs0⟩ := exists_skew D
  exact split_unitary s hs hs0 γ

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

variable {D : Car}

theorem osmul {N : ℕ} (b : 𝓞 D.host.E) (v : Fin N → D.host.E) : b • v = (b : D.host.E) • v := rfl

theorem coe_ne {n : 𝓞 D.host.E} (hn : n ≠ 0) : (n : D.host.E) ≠ 0 := by
  intro h
  apply hn
  exact_mod_cast h

theorem mem_homL {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E} :
    A ∈ TaylorLogMetric.homL D L L' ↔ ∀ x ∈ L, A *ᵥ x ∈ L' := by
  constructor
  · intro h
    unfold TaylorLogMetric.homL at h
    induction h using Submodule.span_induction with
    | mem B hB => exact hB
    | zero => intro x _; simp
    | add B C _ _ hB hC =>
      intro x hx
      rw [Matrix.add_mulVec]
      exact L'.add_mem (hB x hx) (hC x hx)
    | smul c B _ hB =>
      intro x hx
      rw [Matrix.smul_mulVec]
      exact L'.smul_mem c (hB x hx)
  · intro h
    exact Submodule.subset_span h

theorem homL_mul_pres {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {e : Matrix (Fin N') (Fin N') D.host.E}
    (he : ∀ y ∈ L', e *ᵥ y ∈ L') {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.homL D L L') :
    e * A ∈ TaylorLogMetric.homL D L L' :=
  mem_homL.2 fun x hx => by
    rw [← Matrix.mulVec_mulVec]
    exact he _ (mem_homL.1 hA x hx)

theorem homL_mul_min {N N' : ℕ} {La Lc : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lb Ld : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {M : Matrix (Fin N') (Fin N') D.host.E}
    {n : 𝓞 D.host.E} (hn0 : n ≠ 0) (hn : ∀ u ∈ Lc, (n : D.host.E) • u ∈ La)
    (hM : ∀ y ∈ Lb, ∃ m ∈ Ld, M *ᵥ y = (n : D.host.E) • m)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.homL D La Lb) : M * A ∈ TaylorLogMetric.homL D Lc Ld :=
  mem_homL.2 fun u hu => by
    obtain ⟨m, hm, hMm⟩ := hM _ (mem_homL.1 hA _ (hn u hu))
    have h1 : (n : D.host.E) • ((M * A) *ᵥ u) = (n : D.host.E) • m := by
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hMm]
    rw [smul_right_injective _ (coe_ne hn0) h1]
    exact hm

theorem yy_mul {N N' : ℕ} {La Lc : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lb Ld : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {M : Matrix (Fin N') (Fin N') D.host.E}
    (h : ∀ A ∈ TaylorLogMetric.homL D La Lb, M * A ∈ TaylorLogMetric.homL D Lc Ld) :
    ∀ B ∈ TaylorLogMetric.YYl D La Lb, M * B ∈ TaylorLogMetric.YYl D Lc Ld := by
  intro B hB
  unfold TaylorLogMetric.YYl at hB ⊢
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    exact Submodule.subset_span ⟨a, ha, M * A, h A hA, by rw [Matrix.mul_smul]⟩
  | zero => simp
  | add B C _ _ hB hC =>
    rw [Matrix.mul_add]
    exact Submodule.add_mem _ hB hC
  | smul c B _ hB =>
    rw [Matrix.mul_smul]
    exact Submodule.smul_mem _ c hB

def phi {N N' : ℕ} (M : Matrix (Fin N') (Fin N') D.host.E) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => ∑ k, TaylorLogMetric.embT D τ (M i k) * z τ k j
  map_zero' := by funext τ i j; simp
  map_add' := by intro z w; funext τ i j; simp [mul_add, Finset.sum_add_distrib]

theorem phi_apply {N N' : ℕ} (M : Matrix (Fin N') (Fin N') D.host.E) (z : TaylorLogMetric.VC D N N') (τ i j) :
    phi M z τ i j = ∑ k, TaylorLogMetric.embT D τ (M i k) * z τ k j := rfl

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem phi_embV {N N' : ℕ} (M : Matrix (Fin N') (Fin N') D.host.E) (w : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    phi M (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) = w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (M * A) := by
  funext τ i j

  simp only [phi_apply, Pi.smul_apply, smul_eq_mul, TaylorLogMetric.embV, TaylorLogMetric.tor0, Matrix.mul_apply, map_sum, map_mul,
  Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem phi_La {N N' : ℕ} {La Lc : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lb Ld : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {M : Matrix (Fin N') (Fin N') D.host.E}
    (h : ∀ B ∈ TaylorLogMetric.YYl D La Lb, M * B ∈ TaylorLogMetric.YYl D Lc Ld) :
    ∀ z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) La Lb, phi M z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Lc Ld := by
  intro z hz
  unfold TaylorLogMetric.La at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    rw [phi_embV]
    exact AddSubgroup.subset_closure ⟨w, hw, M * A, h A hA, rfl⟩
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

theorem phi_one {N N' : ℕ} (z : TaylorLogMetric.VC D N N') : phi (1 : Matrix (Fin N') (Fin N') D.host.E) z = z := by
  funext τ i j
  simp [phi_apply, Matrix.one_apply]

theorem phi_sub {N N' : ℕ} (M M' : Matrix (Fin N') (Fin N') D.host.E) (z : TaylorLogMetric.VC D N N') :
    phi (M - M') z = phi M z - phi M' z := by
  funext τ i j
  simp [phi_apply, sub_mul, Finset.sum_sub_distrib]

theorem phi_mul {N N' : ℕ} (M M' : Matrix (Fin N') (Fin N') D.host.E) (z : TaylorLogMetric.VC D N N') :
    phi (M * M') z = phi M (phi M' z) := by
  funext τ i j

  simp only [phi_apply, Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions

variable (D : Car)

def SD {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  letI := D.host.cmStar
  IsSDLat D.host.E N L

def DetMul : Prop :=
  ∀ N (L L' L'' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → SD D L → SD D L' → SD D L'' →
    TaylorLogMetric.detId D L L'' = TaylorLogMetric.detId D L L' * TaylorLogMetric.detId D L' L''

def DetSmul : Prop :=
  letI := D.host.cmStar
  ∀ N (L₀ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    Even N → SD D L₀ → SD D L →
    TaylorLogMetric.detId D L₀ (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) =
      Submodule.span (𝓞 D.host.E) {(γ : Matrix (Fin N) (Fin N) D.host.E).det} * TaylorLogMetric.detId D L₀ L

def IopSelf : Prop :=
  ∀ (T : TaylorLogMetric.Tor D) (N N' : ℕ) (La' : AddSubgroup (TaylorLogMetric.VC D N N')), ∀ G ∈ TaylorLogMetric.ThSp D T La',
    TaylorLogMetric.Iop D T La' La' G = G

def SqP (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    Even N → Even N' → SD D L → SD D L₁ → SD D L' → SD D L'' →
    ∀ G ∈ TaylorLogMetric.Th D T L L',
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L₁ L') (TaylorLogMetric.La D T L₁ L'') (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L₁ L') G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L'') (TaylorLogMetric.La D T L₁ L'') (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L L'') G)

def Tr0L (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → Even N' → SD D L → SD D L₁ →
    ∀ G ∈ TaylorLogMetric.Th D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'),
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L₁ (StandardLatticesGL3.stdL D N'))
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L (StandardLatticesGL3.stdL D N')) G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L₁ (StandardLatticesGL3.stdL D N')) G

def Tr0R (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N → Even N' → SD D L' → SD D L'' →
    ∀ G ∈ TaylorLogMetric.Th D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'),
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L'')
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L') G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L'') G

def PullIop (T : TaylorLogMetric.Tor D) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
    Even N → Even N' → SD D L → SD D L₁ → SD D L' → SD D L₁' →
    ∀ G ∈ TaylorLogMetric.Th D T L L',
      TaylorLogMetric.pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G ∈
                      TaylorLogMetric.Th D T (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
                        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') ∧
      TaylorLogMetric.pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L₁ L₁') G) =
        TaylorLogMetric.Iop D T
          (TaylorLogMetric.La D T (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'))
          (TaylorLogMetric.La D T (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L₁)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L₁'))
          (TaylorLogMetric.pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G)

variable {D}
variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def J1 (B : Cd.Base D cc δ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (γ : Matrix.unitaryGroup (Fin N) D.host.E), Even N → Even N' →
    TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))

def J2 (B : Cd.Base D cc δ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (γ' : Matrix.unitaryGroup (Fin N') D.host.E), Even N → Even N' →
    TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
        B.thMoved N N' (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N'))

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end
