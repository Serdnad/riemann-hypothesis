module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle012
public import Mathlib.GroupTheory.Perm.Option
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgHeckeBack

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk

variable {n : ℕ}

theorem tensVd_apply (X : GMod n) (a b : Fin n) (f : Fin n → X.V) (i : Fin n) :
    tensVd X.E a b f i = X.E a b (f i) - if i = b then f a else 0 := by
  by_cases h : i = b <;> simp [tensVd, h]

theorem eeVd_apply (X : GMod n) (f : Fin n → X.V) (a : Fin n) :
    eeVd X.E f a = -∑ c, X.E a c (f c) := by
  simp [eeVd]

theorem commute_tensVd_eeVd (X : GMod n) (c d : Fin n) : Commute (tensVd X.E c d) (eeVd X.E) := by
  refine LinearMap.ext fun f => funext fun a => ?_

  simp only [Module.End.mul_apply, tensVd_apply, eeVd_apply, map_neg, map_sum, map_sub]
  simp only [comm_apply X c d a _ _, sum_sub_distrib, sum_add_distrib, apply_ite (X.E a _), map_zero]
  by_cases h : a = d
  · subst h
    simp
    abel
  · simp [h, Ne.symm h]

theorem backStable : BackStable := fun _ X z a b _ hx =>
  Module.End.mapsTo_maxGenEigenspace_of_comm (commute_tensVd_eeVd X a b).symm (-z - cn _) hx

end GlobalTheory.CompanionTheory.RgHeckeBack
end
end

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof

open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry nnPlus eeV capelliAPlus capelliExpand)

theorem eeV_eq_om {n : ℕ} (X : GMod n) : eeV X.E = om X := by
  refine LinearMap.ext fun u => funext fun b => ?_
  simp [eeV, om_apply]

theorem exists_ker {M : Type} [AddCommGroup M] [Module ℂ M] [Nontrivial M] (T : Module.End ℂ M) {k : ℕ}
    (h : T ^ k = 0) : ∃ v : M, v ≠ 0 ∧ T v = 0 := by
  obtain ⟨w, hw⟩ := exists_ne (0 : M)
  have hex : ∃ j : ℕ, (T ^ j) w = 0 := ⟨k, by simp [h]⟩
  classical
  have hj := Nat.find_spec hex
  have hmin := fun i => Nat.find_min hex (m := i)
  set j := Nat.find hex with hjdef
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0] at hj
    exact absurd (by simpa using hj) hw
  · refine ⟨(T ^ (j - 1)) w, hmin _ (by omega), ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hpos]
    exact hj

theorem eq_zero_of_nilp {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {c : ℂ} {k : ℕ}
    (hc : c ≠ 0) (h : (T - c • (1 : Module.End ℂ M)) ^ k = 0) {v : M} (hv : T v = 0) : v = 0 := by
  have key : ∀ j : ℕ, ((T - c • (1 : Module.End ℂ M)) ^ j) v = (-c) ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Module.End.mul_apply]
      have : (T - c • (1 : Module.End ℂ M)) v = (-c) • v := by simp [hv]
      rw [this, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have := key k
  rw [h] at this
  have h2 : (-c) ^ k • v = 0 := by simpa using this.symm
  exact (smul_eq_zero.mp h2).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr hc))

theorem exists_nnPlus_ne {m : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : GlRel E) (w : ℂ) {v : M} (hv0 : v ≠ 0)
    (hinj : capelliC E (w - 1) v = 0 → v = 0) :
    ∃ y : Fin (m + 1) → ℂ, nnPlus E y w v ≠ 0 := by
  by_contra hall
  push_neg at hall
  have hmin : ∀ d c : Fin (m + 1), cminor E d.succAbove c.succAbove (w - 1) v = 0 := by
    intro d c
    have h := congrFun (hall (Pi.single c 1)) d
    simp only [nnPlus, Pi.zero_apply] at h
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
      (fun hc => absurd (Finset.mem_univ c) hc)] at h
    simpa [pow_ne_zero] using h
  have hexp := (capelliExpand (𝒰 := Module.End ℂ M) m E (w - 1) hE).2 0 0
  have happ := LinearMap.congr_fun hexp v
  simp only [if_true, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, hmin, map_zero,
    smul_zero, Finset.sum_const_zero] at happ
  exact hv0 (hinj happ.symm)

theorem nonVan : NonVan := by
  intro n X χ s hX hnt hfree
  have hQ := GlobalTheory.CompanionTheory.RgExhHecke.qdetEq
  obtain ⟨k, hk⟩ := hX
  haveI := hnt
  cases n with
  | zero => exact s.elim0
  | succ m =>
    set w : ℂ := (((m + 1 : ℕ) : ℂ) - 1) / 2 - χ s with hw

    have h1 := hk (-χ s)
    have hcap0 : Formalism.QuantumDeterminants.capP χ (-χ s) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    rw [hcap0, zero_smul, sub_zero] at h1
    obtain ⟨v, hv0, hv⟩ := exists_ker _ h1
    have hCw : capelliC X.E w v = 0 := by
      rw [← hQ]
      rw [show w = -χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2 by rw [hw]; ring]
      exact hv

    have h2 := hk (-χ s - 1)
    have hc : Formalism.QuantumDeterminants.capP χ (-χ s - 1) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun t _ h => hfree t ?_
      linear_combination h
    have hinj : capelliC X.E (w - 1) v = 0 → v = 0 := by
      intro h
      rw [← hQ] at h
      rw [show w - 1 = -χ s - 1 + (((m + 1 : ℕ) : ℂ) - 1) / 2 by rw [hw]; ring] at h
      exact eq_zero_of_nilp _ hc h2 h
    obtain ⟨y, hy⟩ := exists_nnPlus_ne X.E X.gl w hv0 hinj
    have hev := capelliAPlus X.V m X.E y w v X.gl hCw
    rw [eeV_eq_om] at hev
    intro hbot
    apply hy
    have hmem : nnPlus X.E y w v ∈ stepSub X (χ s) := by
      unfold stepSub
      refine Module.End.mem_maxGenEigenspace _ _ _ |>.mpr ⟨1, ?_⟩
      rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hev]
      rw [hw, ← sub_smul]
      have : -((((m + 1 : ℕ) : ℂ) - 1) / 2 - χ s) - (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2) = 0 := by ring
      rw [this, zero_smul]
    rw [hbot] at hmem
    simpa using hmem

end GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof
end
end

section


theorem _root_.GlobalTheory.T.QuantumDeterminantEquality : CompanionTheory.RgExh.Hk.QdetEq := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.qdetEq | exact GlobalTheory.CompanionTheory.RgExhHecke.qdetEq | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.qdetEq <;> assumption)
end

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PrinSumP

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (capEntry cminor)
open Formalism.REAL (Tm qminor qdet)

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem prod_ofFn_sub : ∀ (m : ℕ) (f g : Fin (m + 1) → A) (d : Fin (m + 1)),
    (∀ j, j ≠ d → f j = g j) → f d = g d + 1 →
    (List.ofFn f).prod - (List.ofFn g).prod = (List.ofFn (f ∘ d.succAbove)).prod := by
  intro m
  induction m with
  | zero =>
    intro f g d _ hd
    have hd0 : d = 0 := Fin.fin_one_eq_zero d
    subst hd0
    simp [hd]
  | succ m ih =>
    intro f g d h hd
    rw [List.ofFn_succ (f := f), List.ofFn_succ (f := g), List.prod_cons, List.prod_cons]
    induction d using Fin.cases with
    | zero =>
      have ht : (fun i : Fin (m + 1) => f i.succ) = fun i => g i.succ :=
        funext fun i => h _ (Fin.succ_ne_zero i)
      rw [ht, hd, add_mul, one_mul, add_sub_cancel_left]
      congr 2
      funext i
      simp [ht, congrFun ht i]
    | succ e =>
      have h0 : f 0 = g 0 := h 0 (Fin.succ_ne_zero e).symm
      have key := ih (fun i => f i.succ) (fun i => g i.succ) e
        (fun j hj => h _ (fun hh => hj (Fin.succ_injective _ hh))) hd
      rw [← h0, ← mul_sub, key, List.ofFn_succ, List.prod_cons]
      congr 2
      simp [Function.comp_def, Fin.succ_succAbove_succ]

def colDet {n : ℕ} (E : Fin n → Fin n → A) (c : Fin n → ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (List.ofFn fun j : Fin n => capEntry E (c j) (σ j) j).prod

theorem Tm_eq_capEntry {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) :
    Tm E u a b = capEntry E u a b := add_comm _ _

theorem qdet_eq_colDet {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    qdet E u = colDet E (fun j => u - ((j : ℕ) : ℂ)) := by
  unfold qdet qminor colDet
  refine sum_congr rfl fun σ _ => ?_
  rw [← zsmul_eq_mul]
  congr 2
  simp only [Tm_eq_capEntry, id]

def ins {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (finSuccEquiv' d).symm.permCongr (Equiv.Perm.decomposeOption.symm (none, τ))

theorem ins_self {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : ins d τ d = d := by
  simp [ins, Equiv.permCongr_apply]

theorem ins_succAbove {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (i : Fin m) :
    ins d τ (d.succAbove i) = d.succAbove (τ i) := by
  simp [ins, Equiv.permCongr_apply]

theorem sign_ins {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (ins d τ) = Equiv.Perm.sign τ := by
  simp [ins, Equiv.Perm.decomposeOption_symm_sign]

theorem ins_injective {m : ℕ} (d : Fin (m + 1)) : Function.Injective (ins d) := by
  intro τ τ' h
  ext i
  have := congrArg (fun s : Equiv.Perm (Fin (m + 1)) => s (d.succAbove i)) h
  simp only [ins_succAbove] at this
  exact congrArg Fin.val (Fin.succAbove_right_injective this)

theorem exists_ins {m : ℕ} (d : Fin (m + 1)) (σ : Equiv.Perm (Fin (m + 1))) (h : σ d = d) :
    ∃ τ, ins d τ = σ := by
  set s : Equiv.Perm (Option (Fin m)) := (finSuccEquiv' d).permCongr σ with hs
  have hnone : s none = none := by
    simp [hs, Equiv.permCongr_apply, h]
  obtain ⟨⟨o, τ⟩, hq⟩ := Equiv.Perm.decomposeOption.symm.surjective s
  have ho : o = none := by
    rw [← hnone, ← hq]
    simp
  subst ho
  refine ⟨τ, ?_⟩
  unfold ins
  rw [hq, hs]
  ext x
  simp [Equiv.permCongr_apply]

theorem colDet_sub {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (c c' : Fin (m + 1) → ℂ)
    (d : Fin (m + 1)) (h : ∀ j, j ≠ d → c j = c' j) (hd : c d = c' d + 1) :
    colDet E c - colDet E c' = ∑ τ : Equiv.Perm (Fin m), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) •
      (List.ofFn fun i : Fin m =>
        capEntry E (c (d.succAbove i)) (d.succAbove (τ i)) (d.succAbove i)).prod := by
  have each : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (List.ofFn fun j => capEntry E (c j) (σ j) j).prod -
        ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (List.ofFn fun j => capEntry E (c' j) (σ j) j).prod =
      if σ d = d then ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        (List.ofFn ((fun j => capEntry E (c j) (σ j) j) ∘ d.succAbove)).prod else 0 := by
    intro σ
    rw [← smul_sub]
    split_ifs with hσ
    · rw [prod_ofFn_sub m _ (fun j => capEntry E (c' j) (σ j) j) d]
      · intro j hj
        simp only [h j hj]
      · simp only [capEntry, hσ, if_true, hd, map_add (f := _), map_one]
        abel
    · have : (fun j => capEntry E (c j) (σ j) j) = fun j => capEntry E (c' j) (σ j) j := by
        funext j
        by_cases hj : j = d
        · subst hj
          simp [capEntry, hσ]
        · simp only [h j hj]
      rw [this, sub_self, smul_zero]
  unfold colDet
  rw [← sum_sub_distrib, sum_congr rfl fun σ _ => each σ, ← sum_filter]
  symm
  refine sum_bij (fun τ _ => ins d τ) ?_ ?_ ?_ ?_
  · intro τ _
    simp [ins_self]
  · intro τ _ τ' _ hh
    exact ins_injective d hh
  · intro σ hσ
    obtain ⟨τ, rfl⟩ := exists_ins d σ (by simpa using hσ)
    exact ⟨τ, mem_univ _, rfl⟩
  · intro τ _
    rw [sign_ins]
    congr 2
    refine congrArg List.ofFn (funext fun i => ?_)
    simp [ins_succAbove]

def hyb {n : ℕ} (x : ℂ) (k : ℕ) (j : Fin n) : ℂ :=
  if (j : ℕ) < k then x - 1 - ((j : ℕ) : ℂ) else x - ((j : ℕ) : ℂ)

theorem hyb_step {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (x : ℂ) (d : Fin (m + 1)) :
    colDet E (hyb x (d : ℕ)) - colDet E (hyb x ((d : ℕ) + 1)) =
      cminor E d.succAbove d.succAbove (x - 1) := by
  rw [colDet_sub E _ _ d]
  · unfold cminor
    refine sum_congr rfl fun τ _ => ?_
    congr 2
    refine congrArg List.ofFn (funext fun i => ?_)
    congr 1
    unfold hyb
    rcases lt_or_ge (i : ℕ) (d : ℕ) with hi | hi
    · have e : ((d.succAbove i : Fin (m + 1)) : ℕ) = i := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hi)]
        simp
      rw [e, if_pos hi]
    · have e : ((d.succAbove i : Fin (m + 1)) : ℕ) = i + 1 := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using hi)]
        simp
      rw [e, if_neg (by omega)]
      push_cast
      ring
  · intro j hj
    have : (j : ℕ) ≠ d := fun hh => hj (Fin.ext hh)
    unfold hyb
    by_cases h1 : (j : ℕ) < d
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
  · unfold hyb
    rw [if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]
    ring

theorem sum_principal {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (x : ℂ) :
    ∑ d : Fin (m + 1), cminor E d.succAbove d.succAbove (x - 1) = qdet E x - qdet E (x - 1) := by
  have h0 : qdet E x = colDet E (hyb x 0) := by
    rw [qdet_eq_colDet]
    congr 1
  have h1 : qdet E (x - 1) = colDet E (hyb x (m + 1)) := by
    rw [qdet_eq_colDet]
    congr 1
    funext j
    simp [hyb, j.2]
  rw [h0, h1, ← sum_congr rfl fun d _ => hyb_step E x d,
    Fin.sum_univ_eq_sum_range (fun k => colDet E (hyb x k) - colDet E (hyb x (k + 1))) (m + 1),
    sum_range_sub']

theorem prinSum : CompanionTheory.RgExh.Hk.PrinSum := by
  intro m M _ _ E _ x
  exact sum_principal E x

end GlobalTheory.CompanionTheory.PrinSumP
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.CompanionTheory.PointSurjectivity

def FibAc {R : Type} [CommRing R] {X : Scheme.{0}} (a : X ⟶ Spec (CommRingCat.of R)) (N : LB X) : Prop :=
  ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
    (cechLB a N D).Acyclic

end GlobalTheory.CompanionTheory.PointSurjectivity
end

end

section

@[expose] public section


theorem _root_.GlobalTheory.T.HeckeNonVanishing : CompanionTheory.RgExh.Hk.NonVan := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | exact GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan <;> assumption)

end
end
