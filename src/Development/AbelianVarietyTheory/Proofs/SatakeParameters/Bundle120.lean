module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle083
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle077
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Formalism.LocalToGlobal.Columns.GSetLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle124
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem pow_wToC (σ : ℂ_[p] →+* ℂ_[p]) (hσ : ∀ w : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p (sigW p w))
    (k : ℕ) (w : FormalGroupSystem.WW p) : (σ ^ k) (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p ((sigW p)^[k] w) := by
  have h : Function.Semiconj (Formalism.L2.G.Pend.wToC p) (sigW p) σ := fun w => (hσ w).symm
  rw [RingHom.coe_pow]
  exact (h.iterate_right k w).symm

theorem comb {κ ι ρ : Type} [Fintype ρ] (S : Finset ι) (a : ι → ℂ_[p]) (b : ι → ρ → ℂ_[p])
    (L : ρ → MvPowerSeries κ ℂ_[p]) (r : ρ) (h : ∀ r', ∑ i ∈ S, a i * b i r' = if r' = r then 1 else 0) :
    ∑ i ∈ S, C (a i) * ∑ r', C (b i r') * L r' = L r := by
  simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]

  simp_rw [← Finset.sum_mul, ← map_sum, h]
  simp

theorem sum_even {M : Type} [AddCommMonoid M] {n' : ℕ} (he : Even n') (g : ℕ → M) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s), g s.val = ∑ i ∈ Finset.range (n' / 2), g (2 * i) := by
  obtain ⟨m, rfl⟩ := he
  refine Finset.sum_bij' (fun s _ => s.val / 2) (fun i hi => ⟨2 * i, by simp at hi; omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp [IsOddPos] at hs ⊢; omega
  · intro i hi; simp [IsOddPos]
  · intro s hs; simp [IsOddPos] at hs; ext; simp; omega
  · intro i hi; simp
  · intro s hs; simp [IsOddPos] at hs; congr 1; omega

theorem sum_odd {M : Type} [AddCommMonoid M] {n' : ℕ} (he : Even n') (g : ℕ → M) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s), g s.val = ∑ i ∈ Finset.range (n' / 2), g (2 * i + 1) := by
  obtain ⟨m, rfl⟩ := he
  have hm : (m + m) / 2 = m := by omega
  refine Finset.sum_bij' (fun s _ => s.val / 2) (fun i hi => ⟨2 * i + 1, by rw [Finset.mem_range, hm] at hi; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro s hs; have := s.isLt; rw [Finset.mem_range, hm]; omega
  · intro i hi; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩; show (2 * i + 1) % 2 = 1; omega
  · intro s hs; have h2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2; ext; show 2 * (s.val / 2) + 1 = s.val; omega
  · intro i hi; show (2 * i + 1) / 2 = i; omega
  · intro s hs; have h2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2; congr 1; omega

end GlobalTheory.OnePlace.Ident

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem eq_subst_subst {n' : ℕ} [NeZero n'] (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p])
    (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (ht0 : ∀ s, constantCoeff (t s) = 0)
    (hx0 : ∀ r, constantCoeff (x r) = 0) (hxt : ∀ s, subst x (t s) = X s) (f : MvPowerSeries (ZMod n') ℂ_[p]) :
    f = subst x (subst t f) := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ht0) (hasSubst_of_constantCoeff_zero hx0),
    show (fun s => subst x (t s)) = X from funext hxt, subst_self]
  rfl

theorem subst_sum_C_mul {κ τ ι : Type} (x : κ → MvPowerSeries τ ℂ_[p]) (hx : HasSubst x) (S : Finset ι)
    (c : ι → ℂ_[p]) (f : ι → MvPowerSeries κ ℂ_[p]) :
    subst x (∑ i ∈ S, C (c i) * f i) = ∑ i ∈ S, C (c i) * subst x (f i) := by
  rw [← coe_substAlgHom hx]

  simp only [map_sum, map_mul, coe_substAlgHom, subst_C]

theorem subst_lg {κ τ : Type} [Finite κ] (x : κ → MvPowerSeries τ ℂ_[p]) (hx0 : ∀ r, constantCoeff (x r) = 0) (k : κ) :
    subst x (GlobalTheory.ThBe0.lg (l := p) k) = PowerSeries.subst (x k) (Formalism.MainNotions.GL3Theta.logF p) := by
  have hx := hasSubst_of_constantCoeff_zero hx0
  rw [GlobalTheory.ThBe0.lg, GlobalTheory.BeProps.subst_psubst hx (constantCoeff_X k), subst_X hx]

theorem hasSubst_jetZ (n' r0 r1 : ℕ) [NeZero n'] : HasSubst (jetZ p n' r0 r1) :=
  hasSubst_of_constantCoeff_zero fun z => by
    rw [jetZ, ← GlobalTheory.BiextInhab.bridge]
    exact GlobalTheory.BeProps.constantCoeff_laAt _ _

theorem hasSubst_copy {n' r0 r1 : ℕ} [NeZero n'] (a : Fin r0) (b : Fin r1) :
    HasSubst (fun u : ZMod n' => (X (u, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem subst_jetZ_lin {n' r0 r1 : ℕ} [NeZero n'] (S : Finset (Fin n')) (c : Fin n' → ℂ_[p]) (a : Fin r0) (b : Fin r1) :
    subst (jetZ p n' r0 r1) (∑ s ∈ S, C (c s) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p])) =
      subst (fun u : ZMod n' => (X (u, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
        (∑ s ∈ S, C (c s) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n')) := by
  rw [subst_sum_C_mul _ (hasSubst_jetZ n' r0 r1), subst_sum_C_mul _ (hasSubst_copy a b)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [subst_X (hasSubst_jetZ n' r0 r1), jetZ, ← GlobalTheory.BiextInhab.bridge]
  rfl

end GlobalTheory.OnePlace.Ident

namespace GlobalTheory.OnePlace.Ident

open MvPowerSeries

theorem zOm_even (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[p])
    (k : ℕ) (hk : k < n') (he : Even k) :
    GlobalTheory.ThBe0.zOm σ (d := n') om om' ((k : ℕ) : ZMod n') =
      ∑ r, C ((σ ^ k) (om r)) * GlobalTheory.ThBe0.lg (l := p) (Sum.inl r : ρ ⊕ ρ) := by
  have hv : ((k : ℕ) : ZMod n').val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  rw [GlobalTheory.ThBe0.zOm, hv, if_pos he]

theorem zOm_odd (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[p])
    (k : ℕ) (hk : k < n') (he : ¬ Even k) :
    GlobalTheory.ThBe0.zOm σ (d := n') om om' ((k : ℕ) : ZMod n') =
      ∑ r, C ((σ ^ k) (om' r)) * GlobalTheory.ThBe0.lg (l := p) (Sum.inr r : ρ ⊕ ρ) := by
  have hv : ((k : ℕ) : ZMod n').val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  rw [GlobalTheory.ThBe0.zOm, hv, if_neg he]

theorem coordZ_jetZ : ∀ {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]), (∀ w : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p w) = Formalism.L2.G.Pend.wToC p (sigW p w)) → ∀ {n' : ℕ} [NeZero n'], Even n' → ∀ (B : OmBasis p n'), GlobalTheory.ThBe0.DualOm σ n' (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) → ∀ (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), (∀ s, MvPowerSeries.constantCoeff (t s) = 0) → (∀ r, MvPowerSeries.constantCoeff (x r) = 0) → (∀ s, MvPowerSeries.subst t (GlobalTheory.ThStr.laS p n' s) = GlobalTheory.ThBe0.zOm σ (fun r => Formalism.L2.G.Pend.wToC p (B.om r)) (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) s) → (∀ s, MvPowerSeries.subst x (t s) = MvPowerSeries.X s) → ∀ (r0 r1 : ℕ) (i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1), MvPowerSeries.subst (jetZ p n' r0 r1) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 i)) = PowerSeries.subst (xiE x i) (Formalism.MainNotions.GL3Theta.logF p) := by
  intro p _ σ hσ n' _ he B hD t x ht0 hx0 ht hxt r0 r1 i
  have hx : HasSubst x := hasSubst_of_constantCoeff_zero hx0
  have key : ∀ s : ZMod n', GlobalTheory.ThStr.laS p n' s = subst x (GlobalTheory.ThBe0.zOm σ (fun r => Formalism.L2.G.Pend.wToC p (B.om r))
      (fun r => Formalism.L2.G.Pend.wToC p (B.omS r)) s) := fun s => by
    rw [← ht s]; exact eq_subst_subst t x ht0 hx0 hxt _
  rcases i with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · have hm : MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 (Sum.inl (r, a, b))) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
          C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r))) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p]) := by

      simp only [coordZ, map_sum, map_mul, map_C, map_X, one_mul, Algebra.algebraMap_self, RingHom.id_apply, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap,
      pow_wToC σ hσ]
    rw [hm, subst_jetZ_lin]
    have hin : ∑ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
        C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r))) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') =
        PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p) := by
      have e1 : ∀ s ∈ Finset.univ.filter (fun s : Fin n' => ¬ IsOddPos s),
          GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') = ∑ r', C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r'))) *
            PowerSeries.subst (x (Sum.inl r')) (Formalism.MainNotions.GL3Theta.logF p) := by
        intro s hs
        have hs2 : ¬ s.val % 2 = 1 := (Finset.mem_filter.mp hs).2
        rw [key, zOm_even p σ _ _ s.val s.isLt (Nat.even_iff.mpr (by omega)), subst_sum_C_mul _ hx]
        simp only [subst_lg x hx0]
      rw [Finset.sum_congr rfl fun s hs => by rw [e1 s hs]]
      refine comb _ _ _ _ r fun r' => ?_
      rw [sum_even he (fun k => (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r')))]
      have hk : ∀ k : ℕ, (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r')) =
          (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r') * Formalism.L2.G.Pend.wToC p (B.omS r)) := fun k => by
        rw [map_mul, mul_comm]
      simp only [hk]
      rw [hD.dual r' r]
      by_cases h : r' = r <;> simp [h]
    rw [hin, GlobalTheory.BeProps.subst_psubst (hasSubst_copy a b) (hx0 _)]
    rfl
  · have hm : MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (coordZ B (FormalGroupSystem.K0 p) 1 (Sum.inr (r, a, b))) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
          C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r))) * (X (s, a, b) : MvPowerSeries (Zidx n' r0 r1) ℂ_[p]) := by

      simp only [coordZ, map_sum, map_mul, map_C, map_X, one_mul, Algebra.algebraMap_self, RingHom.id_apply, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap,
      pow_wToC σ hσ]
    rw [hm, subst_jetZ_lin]
    have hin : ∑ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
        C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.om r))) * GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') =
        PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p) := by
      have e1 : ∀ s ∈ Finset.univ.filter (fun s : Fin n' => IsOddPos s),
          GlobalTheory.ThStr.laS p n' ((s.val : ℕ) : ZMod n') = ∑ r', C ((σ ^ s.val) (Formalism.L2.G.Pend.wToC p (B.omS r'))) *
            PowerSeries.subst (x (Sum.inr r')) (Formalism.MainNotions.GL3Theta.logF p) := by
        intro s hs
        have hs2 : s.val % 2 = 1 := (Finset.mem_filter.mp hs).2
        rw [key, zOm_odd p σ _ _ s.val s.isLt (Nat.not_even_iff.mpr hs2), subst_sum_C_mul _ hx]
        simp only [subst_lg x hx0]
      rw [Finset.sum_congr rfl fun s hs => by rw [e1 s hs]]
      refine comb _ _ _ _ r fun r' => ?_
      rw [sum_odd he (fun k => (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.om r)) * (σ ^ k) (Formalism.L2.G.Pend.wToC p (B.omS r')))]
      have hk : ∀ k : ℕ, (σ ^ (2 * k + 1)) (Formalism.L2.G.Pend.wToC p (B.om r)) * (σ ^ (2 * k + 1)) (Formalism.L2.G.Pend.wToC p (B.omS r')) =
          σ ((σ ^ (2 * k)) (Formalism.L2.G.Pend.wToC p (B.om r) * Formalism.L2.G.Pend.wToC p (B.omS r'))) := fun k => by
        rw [← map_mul, pow_succ']; rfl
      simp only [hk]

      rw [← map_sum, hD.dual r r']
      by_cases h : r = r' <;> simp [h, eq_comm]
    rw [hin, GlobalTheory.BeProps.subst_psubst (hasSubst_copy a b) (hx0 _)]
    rfl

end GlobalTheory.OnePlace.Ident
end
end

section

noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open _root_.Formalism.L2.Col (ClsKer Cpl CplKer GSD fibre fibre_card_stab orbitsFib)

theorem sum_inv_eq_sum_orbits {K M H X : Type} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [Group H] [Finite H]
    [MulAction H X] [Fintype X] [Fintype (MulAction.orbitRel.Quotient H X)] (F : X → M)
    (hF : ∀ (g : H) (x : X), F (g • x) = F x) :
    ((Nat.card H : K))⁻¹ • ∑ x, F x =
      ∑ q : MulAction.orbitRel.Quotient H X, ((Nat.card (MulAction.stabilizer H q.out) : K))⁻¹ • F q.out := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient H X)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hmem : ∀ x : X, (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = q ↔ x ∈ MulAction.orbit H q.out := by
    intro x
    conv_lhs => rw [← Quotient.out_eq' q]
    rw [Quotient.eq'']
    exact MulAction.orbitRel_apply
  rw [Finset.sum_congr rfl (g := fun _ => F q.out) (by
    intro x hx
    obtain ⟨g, rfl⟩ := (hmem x).1 (Finset.mem_filter.1 hx).2
    exact hF g _), Finset.sum_const]
  have hc : (Finset.univ.filter fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = q).card
      = Nat.card (MulAction.orbit H q.out) := by
    symm
    refine Nat.subtype_card _ fun x => ?_
    rw [Finset.mem_filter, ← hmem]
    simp
  have hm : Nat.card (MulAction.orbit H q.out) * Nat.card (MulAction.stabilizer H q.out) = Nat.card H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H q.out)
  have h1 : (Nat.card (MulAction.stabilizer H q.out) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h2 : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [hc, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  congr 1
  have : (Nat.card (MulAction.orbit H q.out) : K) * Nat.card (MulAction.stabilizer H q.out) = Nat.card H := by
    exact_mod_cast congrArg (Nat.cast : ℕ → K) hm
  field_simp
  rw [← this]

theorem card_stabilizer_smul {G D : Type} [Group G] [MulAction G D] (g : G) (d : D) :
    Nat.card (MulAction.stabilizer G (g • d)) = Nat.card (MulAction.stabilizer G d) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (g := g) (a := d) (b := g • d) rfl).toEquiv).symm

theorem sum_fibre_eq_sum_orbits {K M G D D₀ : Type} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [Group G]
    [MulAction G D] [MulAction G D₀] (pr : D → D₀) (hpr : ∀ (g : G) (d : D), pr (g • d) = g • pr d)
    [Fintype (MulAction.orbitRel.Quotient G D₀)] [Fintype (MulAction.orbitRel.Quotient G D)]
    (hs : ∀ x : D₀, Finite (MulAction.stabilizer G x)) [∀ x : D₀, Fintype (fibre pr hpr x)] (F : D → M)
    (hF : ∀ (g : G) (x : D), F (g • x) = F x) :
    ∑ c : MulAction.orbitRel.Quotient G D₀, ((Nat.card (MulAction.stabilizer G c.out) : K))⁻¹ •
        ∑ y : fibre pr hpr c.out, F y =
      ∑ q : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G q.out) : K))⁻¹ • F q.out := by
  classical
  let _ : ∀ x : D₀, Fintype (MulAction.orbitRel.Quotient (MulAction.stabilizer G x) (fibre pr hpr x)) :=
    fun x => Fintype.ofFinite _
  rw [← (orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := hs c.out
  rw [sum_inv_eq_sum_orbits (H := MulAction.stabilizer G c.out) (fun y : fibre pr hpr c.out => F y)
    (fun g y => hF (g : G) (y : D))]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 : (orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)) ⟨c, q⟩
      = (Quotient.mk'' ((q.out : fibre pr hpr c.out) : D) : MulAction.orbitRel.Quotient G D) := by
    conv_lhs => rw [← Quotient.out_eq' q]
    rfl
  obtain ⟨g, hg⟩ : ∃ g : G, g • ((q.out : fibre pr hpr c.out) : D) =
      ((orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)) ⟨c, q⟩).out := by
    rw [h1]
    exact Quotient.exact' (Quotient.out_eq' (Quotient.mk'' ((q.out : fibre pr hpr c.out) : D) :
      MulAction.orbitRel.Quotient G D))
  rw [← hg, hF, card_stabilizer_smul, fibre_card_stab]

section Pairs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S₀ S S₁ : GSD K} {Y : Cpl S}

def cplFibreEquiv (Y : Cpl S) (x : S.D) :
    fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x ≃ Y.ys x where
  toFun p := ⟨p.1.1.2, by
    have h1 : p.1.1.1 = x := p.2
    exact (congrArg (fun z => p.1.1.2 ∈ Y.ys z) h1).mp p.1.2⟩
  invFun y := ⟨⟨(x, y.1), y.2⟩, rfl⟩
  left_inv p := Subtype.ext (Subtype.ext (Prod.ext (show p.1.1.1 = x from p.2).symm rfl))
  right_inv _ := rfl

theorem cplGSD_ok (Y : Cpl S) (h : S.Ok) : (cplGSD S Y).Ok := by
  refine {
    fin_orb := ?_
    fin_stab := ?_
    nab_smul := fun g d => h.nab_smul g d.1.1
    del_smul := fun g d => h.del_smul g d.1.1
    inv := h.inv }
  · have := h.fin_orb
    have : ∀ x : S.D, Finite (fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x) := fun x =>
      have := (Y.fin x).to_subtype
      Finite.of_equiv _ (cplFibreEquiv Y x).symm
    exact Finite.of_equiv _ (orbitsFib (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) Quotient.out
      (fun c => Quotient.out_eq' c))
  · intro d
    have := h.fin_stab d.1.1
    have hle : MulAction.stabilizer S.G d ≤ MulAction.stabilizer S.G d.1.1 := fun g hg =>
      congrArg (fun p : Y.Pts => p.1.1) hg
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)

def cplKer1 (A : CplKer S₀ S S₁ Y) : ClsKer S₀ (cplGSD S Y) where
  k d₀ d := A.k1 d₀ d.1.1 d.1.2
  equiv g₀ g d₀ d := A.equiv1 g₀ g d₀ d.1.1 d.1.2

def cplKer2 (A : CplKer S₀ S S₁ Y) : ClsKer (cplGSD S Y) S₁ where
  k d d₁ := A.k2 d.1.1 d.1.2 d₁
  equiv g g₁ d d₁ := A.equiv2 g g₁ d.1.1 d.1.2 d₁

theorem cpl_comp_k (A : CplKer S₀ S S₁ Y) (h : S.Ok) (d₀ : S₀.D) (d₁ : S₁.D) :
    (A.comp h S.outSec).k d₀ d₁ =
      letI := (cplGSD_ok Y h).fintypeCl
      ∑ q : (cplGSD S Y).Cl, ((((cplGSD S Y).toCSDOf (cplGSD_ok Y h) (cplGSD S Y).outSec).wt q : K))⁻¹ •
        ((cplKer2 A).k ((cplGSD S Y).outSec.rep q) d₁) ∘ₗ ((cplKer1 A).k d₀ ((cplGSD S Y).outSec.rep q)) := by
  let i1 : Fintype (MulAction.orbitRel.Quotient S.G S.D) := h.fintypeCl
  let i2 : Fintype (MulAction.orbitRel.Quotient S.G Y.Pts) := (cplGSD_ok Y h).fintypeCl
  let i3 : ∀ x : S.D, Fintype (fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x) := fun x =>
    have := (Y.fin x).to_subtype
    have := Finite.of_equiv _ (cplFibreEquiv Y x).symm
    Fintype.ofFinite _
  have key := sum_fibre_eq_sum_orbits (K := K) (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) h.fin_stab
    (fun p : Y.Pts => (A.k2 p.1.1 p.1.2 d₁) ∘ₗ (A.k1 d₀ p.1.1 p.1.2)) (by
      intro g p
      have e1 := A.equiv1 1 g d₀ p.1.1 p.1.2
      have e2 := A.equiv2 g 1 p.1.1 p.1.2 d₁
      rw [one_smul, inv_one, map_one] at e1
      rw [one_smul, map_one] at e2
      show (A.k2 (g • p.1.1) (g • p.1.2) d₁) ∘ₗ (A.k1 d₀ (g • p.1.1) (g • p.1.2)) = _
      rw [e1, e2]
      ext x
      simp only [LinearMap.comp_apply, one_apply_eq_self]
      rw [← mul_apply_eq_comp (S.ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self])
  simp only [CSD.wt, ← Nat.card_eq_fintype_card]
  refine Eq.trans ?_ key
  show ∑ c : S.Cl, _ = _
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [CSD.wt, ← Nat.card_eq_fintype_card]
  congr 1
  let _ : Fintype (Y.ys c.out) := (Y.fin c.out).fintype
  refine (Finset.sum_subtype (p := fun y => y ∈ Y.ys c.out) (F := inferInstance) _
    (fun y => (Y.fin _).mem_toFinset) _).trans ?_
  exact ((cplFibreEquiv Y c.out).symm.sum_comp
    (fun y => (A.k2 y.1.1.1 y.1.1.2 d₁) ∘ₗ (A.k1 d₀ y.1.1.1 y.1.1.2)))

end Pairs

end GlobalTheory.GO
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PointStabilizer

def stab {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : ρ a v = v := ha
    have hb' : ρ b v = v := hb
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : ρ a v = v := ha
    show ρ a⁻¹ v = v
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_of_residue {x : 𝒪[k]} (hx : IsLocalRing.residue 𝒪[k] x = 0) :
    valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one] at hx
  exact lt_of_le_of_ne x.2 hx

theorem entry_of_mem_KOne {n : ℕ} {g : GL (Fin n) k} (hg : g ∈ KOne k (Fin n)) (i j : Fin n) :
    valuation k (g.val i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 : Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]) h = 1 := hh
  have h2 : IsLocalRing.residue 𝒪[k] (h.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    have := congrArg (fun u : GL (Fin n) _ => u.val i j) h1
    simpa using this
  have h3 : IsLocalRing.residue 𝒪[k] (h.val i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) = 0 := by
    rw [map_sub, h2]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  have h4 := val_lt_one_of_residue h3
  rw [map_sub] at h4
  have h5 : algebraMap 𝒪[k] k ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) = (1 : Matrix (Fin n) (Fin n) k) i j := by
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  rw [h5] at h4
  exact h4

def pts (n : ℕ) : (Σ _ : Fin n, Fin 1) ≃ Fin n := Equiv.sigmaUnique (Fin n) fun _ => Fin 1

theorem unipRad_pts (n : ℕ) : unipRad k (pts n) = unipB k (Fin n) :=
  GlobalTheory.SmGL.EmptyBlocks.unipRad_eq k (pts n) (fun _ _ h => h)

theorem mk_ne_zero (H : GlobalTheory.Published.DepthZeroJacquetInjective) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : GlobalTheory.SplitRead.Irr k n) (v : π.V)
    (θ : Fin n → kˣ →* ℂˣ) (hv : v ≠ 0) (hI : GlobalTheory.TameIwahori.IsIwVec θ π.π v) :
    Submodule.Quotient.mk v ≠ (0 : π.V ⧸ twKer π.π (unipB k (Fin n)) 1) := by
  intro h0
  have hle : KOne k (Fin n) ⊔ (unipRad k (pts n) ⊓ KO k (Fin n)) ≤ stab π.π v := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · refine hI.1 g (iwahori_le_KO k (Fin n) (KOne_le_iwahori k (Fin n) hg)) (fun i j hij => ?_) (fun i => ?_)
      · simpa [Matrix.one_apply_ne hij.ne'] using entry_of_mem_KOne hg i j
      · simpa using entry_of_mem_KOne hg i i
    · have hu := (mem_unipB k).1 (unipRad_pts (k := k) n ▸ hg.1)
      refine hI.1 g hg.2 (fun i j hij => ?_) (fun i => ?_)
      · rw [hu.1 i j hij]; simp
      · rw [hu.2 i]; simp
  refine hv (H k n n (fun _ => 1) (pts n) π v (fun g => ?_) ?_)
  · have : π.π g v = v := hle g.2
    simpa using this
  · rw [Submodule.Quotient.mk_eq_zero] at h0 ⊢
    rw [unipRad_pts]
    exact h0

end GlobalTheory.PointStabilizer
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

theorem _root_.GlobalTheory.T.localChar_det_eq_one_of_congr_one_mod_pow : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ) (P : rowSG Pr sel mu) (n : ℕ) (k : Sp X.E n ≃ₗ[X.E] Sp X.E n),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E n) l))) →
    muAt Ch sel mu cst i P ((LinearEquiv.det k : X.Eˣ) : X.E) = 1 := by
  first | exact @GlobalTheory.AwayMat.muAt_det_congr_one | exact GlobalTheory.AwayMat.muAt_det_congr_one | (intros; apply GlobalTheory.AwayMat.muAt_det_congr_one <;> assumption)
end
