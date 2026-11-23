module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorBesselMoment
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle108
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.HatCommutators

section lists
variable {A : Type} [Ring A]

theorem comm_ofFn {n : ℕ} (f : Fin n → A) (a : A) (h : ∀ l, Commute a (f l)) :
    Commute a (List.ofFn f).prod := by
  apply Commute.list_prod_right
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨l, rfl⟩ := hx
  exact h l

theorem ofFn_mul_inv : ∀ {n : ℕ} (f g : Fin n → A), (∀ l, f l * g l = 1) → (∀ l m, Commute (g l) (f m)) →
    (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have ih := ofFn_mul_inv (n := n) (fun i => f i.succ) (fun i => g i.succ)
      (fun l => h l.succ) (fun l m => hc l.succ m.succ)
    have hc' := comm_ofFn (fun i : Fin n => f i.succ) (g 0) (fun l => hc 0 l.succ)
    rw [mul_assoc, ← mul_assoc _ (g 0), ← hc'.eq, mul_assoc, ih, mul_one, h]

theorem star_ofFn [StarRing A] : ∀ {n : ℕ} (f g : Fin n → A), (∀ l, star (f l) = g l) →
    (∀ l m, Commute (g l) (g m)) → star (List.ofFn f).prod = (List.ofFn g).prod
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, star_mul]
    have ih := star_ofFn (n := n) (fun i => f i.succ) (fun i => g i.succ)
      (fun l => h l.succ) (fun l m => hc l.succ m.succ)
    have hc' := comm_ofFn (fun i : Fin n => g i.succ) (g 0) (fun l => hc 0 l.succ)
    rw [ih, h, hc'.eq]

end lists

variable {A : Type} [Ring A] [Algebra ℂ A]

section level
variable {r : ℕ} (L : LevelData A r)

theorem c_mem (l : Fin r) : L.c l ∈ L.fns := by simp [LevelData.fns]
theorem ci_mem (l : Fin r) : L.ci l ∈ L.fns := by simp [LevelData.fns]
theorem cb_mem (l : Fin r) : L.cb l ∈ L.fns := by simp [LevelData.fns]
theorem cbi_mem (l : Fin r) : L.cbi l ∈ L.fns := by simp [LevelData.fns]
theorem GG_mem : L.GG ∈ L.fns := by simp [LevelData.fns]

theorem fcomm {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : Commute x y := L.fns_comm x hx y hy

theorem comm_Dr {a : A} (h : ∀ g ∈ L.fns, Commute a g) : Commute a L.Dr :=
  comm_ofFn _ _ fun l => h _ (c_mem L l)
theorem comm_Drb {a : A} (h : ∀ g ∈ L.fns, Commute a g) : Commute a L.Drb :=
  comm_ofFn _ _ fun l => h _ (cb_mem L l)

theorem Dri_Dr : L.Dri * L.Dr = 1 :=
  ofFn_mul_inv _ _ L.ci_c fun l m => fcomm L (c_mem L l) (ci_mem L m)
theorem Drbi_Drb : L.Drbi * L.Drb = 1 :=
  ofFn_mul_inv _ _ L.cbi_cb fun l m => fcomm L (cb_mem L l) (cbi_mem L m)
theorem Dr_Drb : Commute L.Dr L.Drb :=
  comm_ofFn _ _ fun l => (comm_Dr L fun _ hg => fcomm L (cb_mem L l) hg).symm

end level

variable [StarRing A] {P : M.Par} (d : Q.NFData P A)

theorem mem_span {b h : A} (hb : b ∈ bmon d) (hh : h ∈ basics d) : b * h ∈ nfSpan d (basics d) 0 0 1 :=
  Submodule.subset_span ⟨b, hb, [h], rfl, by simpa using hh, by simp⟩

theorem kap_mem (f : M.Ty P → ℂ) : d.κ f ∈ bmon d :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))

theorem ssn_mem {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) : ssn d l ∈ bmon d :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨l, by simpa using hl, rfl⟩))

theorem star_ssn_mem {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) : star (ssn d l) ∈ bmon d :=
  Submonoid.subset_closure (Or.inr ⟨l, by simpa using hl, rfl⟩)

theorem rh_eq (hR : d.Rel) (y : ℂ) :
    rh d y = d.x y * d.L.R0 y +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y) * d.L.Ahat y := by
  obtain ⟨-, hκ, hS, -⟩ := hR
  have hκ' : ∀ f, ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun f g hg => hκ f g (Or.inl hg)
  have hS' : ∀ l, ∀ g ∈ d.L.fns, Commute (d.SS l) g := fun l g hg => hS l g (Or.inl (Or.inl hg))
  have h1 : d.L.Drb * (d.L.GG * d.x y) = d.x y * (d.L.Drb * d.L.GG) := by
    have := ((comm_Drb d.L (hκ' fun ρ => M.xC P ρ y)).mul_right (hκ' _ _ (GG_mem d.L))).eq
    rw [← mul_assoc]; exact this.symm
  have h2 : ∀ l, ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y) * d.L.Ahat y =
      d.L.Drb * (d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ar y := by
    intro l
    have hc := ((comm_Dr d.L (hS' l)).mul_left (comm_Dr d.L (hκ' fun ρ => M.xEx P {l} ρ y))).eq
    calc _ = d.L.Drb * d.L.Dri * ((d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Dr) * d.L.Ar y := by
          simp only [ssn, LevelData.Ahat, mul_assoc]
      _ = d.L.Drb * (d.L.Dri * d.L.Dr) * (d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ar y := by
          rw [hc]; simp only [mul_assoc]
      _ = _ := by rw [Dri_Dr, mul_one]
  simp only [h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change d.L.Drb * ((d.L.GG * d.x y * d.L.l0 y + d.weightedSumBis y) * d.L.Ar y + d.L.GG * d.x y * d.L.Br y) =
    d.x y * (d.L.Drb * d.L.GG * (d.L.l0 y * d.L.Ar y + d.L.Br y)) + d.L.Drb * d.weightedSumBis y * d.L.Ar y
  rw [← mul_assoc (d.x y), ← h1]
  noncomm_ring

theorem rhv_eq (hR : d.Rel) (hc : ∀ l, star (d.L.c l) = d.L.cb l) (hci : ∀ l, star (d.L.ci l) = d.L.cbi l)
    (y : ℂ) :
    rhv d y = d.x y * d.L.R0v y +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l) * d.L.Ahatv y := by
  obtain ⟨-, hκ, hS, -⟩ := hR
  have hκ' : ∀ f, ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun f g hg => hκ f g (Or.inl hg)
  have hS' : ∀ l, ∀ g ∈ d.L.fns, Commute (d.SS l) g := fun l g hg => hS l g (Or.inl (Or.inl hg))
  have h1 : d.L.Dr * (d.L.GG * d.x y) = d.x y * (d.L.Dr * d.L.GG) := by
    have := ((comm_Dr d.L (hκ' fun ρ => M.xC P ρ y)).mul_right (hκ' _ _ (GG_mem d.L))).eq
    rw [← mul_assoc]; exact this.symm
  have s1 : star d.L.Drb = d.L.Dr :=
    star_ofFn _ _ (fun l => by rw [← hc, star_star]) fun l m => fcomm d.L (c_mem _ l) (c_mem _ m)
  have s2 : star d.L.Dri = d.L.Drbi :=
    star_ofFn _ _ hci fun l m => fcomm d.L (cbi_mem _ l) (cbi_mem _ m)
  have h2 : ∀ l, (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l) * d.L.Ahatv y =
      d.L.Dr * ((d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l)) * d.L.Avr y := by
    intro l
    have hs : Commute (star (d.SS l)) d.L.Dr := by
      rw [← s1]; exact (comm_Drb d.L (hS' l)).star_star
    have hc := ((comm_Dr d.L (hκ' fun ρ => M.xEx P {l} ρ y)).mul_left hs).eq
    calc _ = (d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l) * (d.L.Drbi * (d.L.Dr * d.L.Drb)) * d.L.Avr y := by
          simp only [ssn, LevelData.Ahatv, star_mul, s1, s2, mul_assoc]
      _ = (d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l) * d.L.Dr * d.L.Avr y := by
          rw [(Dr_Drb d.L).eq, ← mul_assoc d.L.Drbi, Drbi_Drb, one_mul]
      _ = _ := by rw [hc]
  simp only [h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Avr y + d.L.GG * d.x y * d.L.Bvr y) =
    d.x y * (d.L.Dr * d.L.GG * (d.L.m0 y * d.L.Avr y + d.L.Bvr y)) + d.L.Dr * d.S12 y * d.L.Avr y
  rw [← mul_assoc (d.x y), ← h1]
  noncomm_ring

theorem xinv_mul (y : ℂ) (hy : ∀ ρ : M.Ty P, M.xC P ρ y ≠ 0) :
    (d.κ fun ρ => (M.xC P ρ y)⁻¹) * d.x y = 1 := by
  rw [Q.NFData.x, ← map_mul, ← map_one d.κ]
  congr 1
  funext ρ
  exact inv_mul_cancel₀ (hy ρ)

end GlobalTheory.HatNF.HatCommutators

namespace GlobalTheory.HatNF

open HatCommutators

theorem r0_mem_nfSpan_basics : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) → d.L.R0 y ∈ nfSpan d (basics d) 0 0 1 ∧ d.L.R0v y ∈ nfSpan d (basics d) 0 0 1 := by
  intro P A _ _ _ _ d hd y hy
  obtain ⟨-, -, hR, -, hc, hci, -⟩ := hd
  have hx := xinv_mul d (y : ℂ) fun ρ => (hy ρ).1
  have hk := kap_mem d fun ρ => (M.xC P ρ (y : ℂ))⁻¹
  set k := d.κ fun ρ => (M.xC P ρ (y : ℂ))⁻¹
  constructor
  · have e : d.L.R0 y = k * rh d y - ∑ l ∈ Finset.Icc 1 (P.k - 1),
        (k * ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ahat y := by
      rw [rh_eq d hR, mul_add, ← mul_assoc, hx, one_mul, Finset.mul_sum]
      simp only [mul_assoc, add_sub_cancel_right]
    rw [e]
    refine Submodule.sub_mem _ (mem_span d hk ⟨y, hy, by simp⟩) (Submodule.sum_mem _ fun l hl => ?_)
    exact mem_span d (mul_mem (mul_mem hk (ssn_mem d hl)) (kap_mem d _)) ⟨y, hy, by simp⟩
  · have e : d.L.R0v y = k * rhv d y - ∑ l ∈ Finset.Icc 1 (P.k - 1),
        (k * (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l)) * d.L.Ahatv y := by
      rw [rhv_eq d hR hc hci, mul_add, ← mul_assoc, hx, one_mul, Finset.mul_sum]
      simp only [mul_assoc, add_sub_cancel_right]
    rw [e]
    refine Submodule.sub_mem _ (mem_span d hk ⟨y, hy, by simp⟩) (Submodule.sum_mem _ fun l hl => ?_)
    exact mem_span d (mul_mem (mul_mem hk (kap_mem d _)) (star_ssn_mem d hl)) ⟨y, hy, by simp⟩

end GlobalTheory.HatNF
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MulRelAlg

theorem exists_real_xC_ne_zero (P : M.Par) : ∃ Y : ℝ, ∀ ρ : M.Ty P, M.xC P ρ (Y : ℂ) ≠ 0 := by
  classical
  obtain ⟨Y, hY⟩ := Infinite.exists_notMem_finset
    (((Finset.univ : Finset (M.Ty P)) ×ˢ Finset.Icc 1 (P.k - 1)).image fun x => -M.rho P x.1 x.2)
  refine ⟨Y, fun ρ => ?_⟩
  unfold M.xC
  refine Finset.prod_ne_zero_iff.2 fun i hi h => hY ?_
  refine Finset.mem_image.2 ⟨(ρ, i), Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩, ?_⟩
  have h' : Y + M.rho P ρ i = 0 := by exact_mod_cast h
  show -M.rho P ρ i = Y
  linarith

theorem up_unique {P : M.Par} {l : ℕ} {σ ρ ρ' : M.Ty P} (h : M.Up P l σ ρ) (h' : M.Up P l σ ρ') : ρ = ρ' := by
  funext i
  exact Fin.ext ((h i).trans (h' i).symm)

theorem not_up_self {P : M.Par} {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) : ¬ M.Up P l ρ ρ := by
  intro h
  rw [Finset.mem_Icc] at hl
  have := h ⟨l - 1, by omega⟩
  rw [if_pos (by show l - 1 + 1 = l; omega)] at this
  omega

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem proj_raising_sum_proj_eq_zero (d : Q.NFData P A) (h : d.Rel) (Y : ℂ) (ρ : M.Ty P) :
    d.κ (Pi.single ρ 1) * d.weightedSumBis Y * d.κ (Pi.single ρ 1) = 0 := by
  classical
  unfold Q.NFData.weightedSumBis
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun l hl => ?_
  have h4 := h.2.2.2.1 l (fun σ => if M.Up P l σ ρ then 1 else 0) (Pi.single ρ 1) (by
    intro σ σ' hu
    by_cases e : σ' = ρ
    · subst e; simp [hu]
    · have : ¬ M.Up P l σ ρ := fun h2 => e (up_unique hu h2)
      simp [this, e])
  rw [← mul_assoc, h4, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
  have : ((fun σ => if M.Up P l σ ρ then (1 : ℂ) else 0) *
      ((fun σ => M.xEx P {l} σ Y) * Pi.single ρ 1) : M.Ty P → ℂ) = 0 := by
    funext σ
    by_cases e : σ = ρ
    · subst e; simp [not_up_self hl]
    · simp [e]
  rw [this, map_zero, mul_zero]

theorem eq_zero_of_blocks (d : Q.NFData P A) (X : A) (hc : ∀ f, Commute (d.κ f) X)
    (h0 : ∀ ρ, d.κ (Pi.single ρ 1) * X * d.κ (Pi.single ρ 1) = 0) : X = 0 := by
  classical
  have h1 : ∀ ρ, d.κ (Pi.single ρ 1) * X = 0 := by
    intro ρ
    have := h0 ρ
    rw [mul_assoc, ← (hc _).eq, ← mul_assoc, ← map_mul, ← Pi.single_mul, mul_one] at this
    exact this
  have h2 : ∑ ρ : M.Ty P, d.κ (Pi.single ρ 1) = 1 := by

    rw [← map_sum, ← map_one d.κ]
    congr 1
    exact Finset.univ_sum_single (1 : M.Ty P → ℂ)
  rw [← one_mul X, ← h2, Finset.sum_mul]
  exact Finset.sum_eq_zero fun ρ _ => h1 ρ

theorem star_GGi [StarModule ℂ A] {r : ℕ} (L : LevelData A r) (h : IsStarLevel L) : star L.GGi = L.GGi := by
  have hb : star L.ζb = L.ζ := by rw [← h.1, star_star]
  have hG : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, h.1, hb, ← algebraMap_star_comm, h.2.2]
  have : star L.GGi * L.GG = 1 := by rw [← hG, ← star_mul, L.GG_GGi, star_one]
  calc star L.GGi = star L.GGi * L.GG * L.GGi := by rw [mul_assoc, L.GG_GGi, mul_one]
    _ = L.GGi := by rw [this, one_mul]

theorem nab_rel (d : Q.NFData P A) (h : d.Rel) (m m' : A) (hf : ∀ f ∈ d.L.fns, Commute f m)
    (hf' : ∀ f ∈ d.L.fns, Commute f m') (hκ : ∀ f, Commute (d.κ f) m) (hκ' : ∀ f, Commute (d.κ f) m')
    (hQ : ∀ Y : ℝ, d.QQ Y 1 0 * m = m * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m' * d.QQ Y 1 1) :
    d.L.nab * m = m * d.L.nab + d.L.ζb * d.L.GGi * m' := by
  classical
  obtain ⟨Y, hY⟩ := exists_real_xC_ne_zero P
  have hQ := hQ Y
  have e10 : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  have e11 : d.QQ Y 1 1 = d.L.GG * d.x Y := rfl
  rw [e10, e11] at hQ
  have mG : d.L.GG ∈ d.L.fns := by simp [LevelData.fns]
  have mGi : d.L.GGi ∈ d.L.fns := by simp [LevelData.fns]
  have mz : d.L.ζb ∈ d.L.fns := by simp [LevelData.fns]
  have kG : ∀ f, Commute (d.κ f) d.L.GG := fun f => h.2.1 f _ (Or.inl mG)
  have kGi : ∀ f, Commute (d.κ f) d.L.GGi := fun f => h.2.1 f _ (Or.inl mGi)
  have kz : ∀ f, Commute (d.κ f) d.L.ζb := fun f => h.2.1 f _ (Or.inl mz)
  have kn : ∀ f, Commute (d.κ f) d.L.nab := fun f => h.2.1 f _ (Or.inr (by simp))
  have kk : ∀ f, Commute (d.κ f) (d.x Y) := fun f => by
    unfold Q.NFData.x; exact (Commute.all _ _).map d.κ
  set Z : A := m * d.L.nab + d.L.ζb * d.L.GGi * m' - d.L.nab * m with hZ
  set g : A := d.L.GG * d.x Y with hg
  have kZ : ∀ f, Commute (d.κ f) Z := fun f =>
    (((hκ f).mul_right (kn f)).add_right (((kz f).mul_right (kGi f)).mul_right (hκ' f))).sub_right
      ((kn f).mul_right (hκ f))
  have gm : Commute g m := (hf _ mG).mul_left (hκ _)
  have gw : Commute g (d.L.ζb * d.L.GGi * m') :=
    (Commute.mul_right (Commute.mul_right (d.L.fns_comm _ mG _ mz) (d.L.fns_comm _ mG _ mGi)) (hf' _ mG)).mul_left
      (((kz _).mul_right (kGi _)).mul_right (hκ' _))
  have um : Commute (algebraMap ℂ A ((Y : ℂ) + 1 / 2) * (d.L.ζb * d.L.GGi)) m :=
    Commute.mul_left (Algebra.commutes _ _) ((hf _ mz).mul_left (hf _ mGi))
  have hX : g * Z = m * d.weightedSumBis Y - d.weightedSumBis Y * m := by
    have e1 : m * (g * d.L.l0 Y) = g * (m * d.L.l0 Y) := by rw [← mul_assoc, ← gm.eq, mul_assoc]
    rw [add_mul, mul_add, e1, ← gw.eq] at hQ
    have e2 : Z = d.L.l0 Y * m - m * d.L.l0 Y + d.L.ζb * d.L.GGi * m' := by
      unfold LevelData.l0
      rw [sub_mul, mul_sub, um.eq, hZ]
      noncomm_ring
    rw [e2, mul_add, mul_sub, ← mul_assoc g _ m, eq_sub_of_add_eq hQ]
    abel
  have hX0 : g * Z = 0 := by
    refine eq_zero_of_blocks d _ (fun f => ((kG f).mul_right (kk f)).mul_right (kZ f)) fun ρ => ?_
    have := proj_raising_sum_proj_eq_zero d h Y ρ
    rw [hX, mul_sub, sub_mul, ← mul_assoc, (hκ _).eq, mul_assoc m, mul_assoc m, this, ← mul_assoc _ _ m,
      mul_assoc _ m, ← (hκ _).eq, ← mul_assoc, this]
    simp
  have hinv : d.κ (fun ρ => (M.xC P ρ Y)⁻¹) * d.L.GGi * g = 1 := by
    rw [hg, mul_assoc, ← mul_assoc d.L.GGi, d.L.GGi_GG, one_mul]
    unfold Q.NFData.x
    rw [← map_mul, ← map_one d.κ]
    congr 1
    funext ρ
    exact inv_mul_cancel₀ (hY ρ)
  have : Z = 0 := by rw [← one_mul Z, ← hinv, mul_assoc, hX0, mul_zero]
  exact (sub_eq_zero.1 this).symm

theorem mulRel_of_entries : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ m : ℕ → A, (∀ q, (∀ f ∈ d.L.fns, Commute f (m q)) ∧ (∀ l, d.L.p l * m q = m q * d.L.p l + m (q + 1)) ∧ (∀ l, d.L.pb l * m q = m q * d.L.pb l + m (q + 1)) ∧ (∀ f : M.Ty P → ℂ, Commute (d.κ f) (m q)) ∧ star (m q) = m q ∧ ∀ Y : ℝ, d.QQ Y 1 0 * m q = m q * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m (q + 1) * d.QQ Y 1 1) → MulRel d.L m := by
  intro P A _ _ _ _ d hd m hm q
  obtain ⟨-, hs, hr, -⟩ := hd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hm q
  obtain ⟨k1, -, -, k4, k5, -⟩ := hm (q + 1)
  have hn := nab_rel d hr (m q) (m (q + 1)) h1 k1 h4 k4 h6
  refine ⟨h1, h2, h3, hn, ?_⟩
  have hb : star d.L.ζb = d.L.ζ := by rw [← hs.1, star_star]
  have mGi : d.L.GGi ∈ d.L.fns := by simp [LevelData.fns]
  have mz : d.L.ζ ∈ d.L.fns := by simp [LevelData.fns]
  have hst := congrArg star hn
  rw [star_add, star_mul, star_mul, star_mul, star_mul, hs.2.1, h5, k5, hb, star_GGi d.L hs,
    d.L.fns_comm _ mGi _ mz, ← ((k1 _ mz).mul_left (k1 _ mGi)).eq] at hst
  rw [hst]
  abel

end GlobalTheory.HatNF.MulRelAlg
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ContDiff

namespace GlobalTheory.HatNF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mulG_normSq_contDiff : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  have h : (fun w : ℂ => Complex.normSq w) = fun w => w.re * w.re + w.im * w.im := by
    funext w; exact Complex.normSq_apply w
  rw [h]
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

theorem mulG_ld_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) :
    ContDiffOn ℝ ∞ (LE.ld q φ) (Set.Ioi 0) := by
  have h1 : ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u))) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv q hφ
  exact h1.comp_contDiffOn (Real.contDiffOn_log.mono fun x hx => by simpa using (ne_of_gt hx))

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem mulG_gR_contDiff (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    ContDiff ℝ ∞ (fun x : (Fin P.r → ℂ) × Q.Mx P.k P.r => gR P Bs x.1 x.2) := by
  unfold gR Q.GGl
  refine ContDiff.mul (mulG_normSq_contDiff.comp ?_) (ContDiff.sub (mulG_normSq_contDiff.comp ?_) contDiff_const)
  · exact contDiff_prod fun a _ => Formalism.FourierDecayAlt.P.Qx5.coord_contDiff a
  · exact (Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff _ _ _ _ _).comp contDiff_snd

theorem mulG_gR_pos (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Formalism.FourierDecayAlt.P.Qx5.OpR P.k P.r Bs.z Bs.z') : 0 < gR P Bs x.1 x.2 :=
  mul_pos (Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)) hx.2

theorem mulG_mem (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ)
    {Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (fun c g => ((LE.ld q φ (gR P Bs c g) : ℝ) : ℂ) • Φ c g) ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := by
  refine Formalism.FourierDecayAlt.P.Qx5.smul_mem (a := fun x => ((LE.ld q φ (gR P Bs x.1 x.2) : ℝ) : ℂ)) ?_ ?_ hΦ
  · refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
    exact (mulG_ld_contDiffOn hφ q).comp (mulG_gR_contDiff P Bs).contDiffOn fun x hx => mulG_gR_pos P Bs hx
  · intro x _ h hh h' hh'
    simp only [gR, Formalism.FourierDecayAlt.P.Qx5.GG_inv hh hh']

theorem exists_isMulG_of_smoothLog (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) :
    ∃ W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W := by
  refine ⟨fun q =>
    { toFun := fun Φ => ⟨_, mulG_mem P Bs hφ q Φ.2⟩
      map_add' := fun Φ Ψ => ?_
      map_smul' := fun s Φ => ?_ }, fun q Φ c g => rfl⟩
  · apply Subtype.ext
    funext c g
    simp only [Submodule.coe_add, Pi.add_apply, smul_add]
  · apply Subtype.ext
    funext c g
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

theorem mulG_exists : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ φ : ℝ → ℝ, LE.SmoothLog φ → ∃ W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W :=
  fun _ _ _ _ _ _ _ _ P Bs _ _ _ _ _ _ _ _ _ hφ => exists_isMulG_of_smoothLog P Bs hφ

end GlobalTheory.HatNF
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_orbital_integral_factors_through_right_functional : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ Bb : R.H → Wp → Wq → Wp, (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = Bb x (X (l' y)) c := by
  first | exact @GlobalTheory.besselJ_coef_through_right | exact GlobalTheory.besselJ_coef_through_right | (intros; apply GlobalTheory.besselJ_coef_through_right <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_orbital_integral_factors_through_left_functional : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ A : R.H → Wq → Wq → Wp, (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = A y (ContinuousLinearMap.adjoint X (l x)) c := by
  first | exact @GlobalTheory.BesselFirstLeft.bessel_integrate_left | exact GlobalTheory.BesselFirstLeft.bessel_integrate_left | (intros; apply GlobalTheory.BesselFirstLeft.bessel_integrate_left <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.dual_tensor_bessel_moment : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (RI : Fin (2 * r + k + 1) → Rep k r) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp), 1 ≤ k → R.IsDS ε mu → (∀ s, (RI s).IsDS ε (mu - Pi.single s 1)) → TensRaw dualM R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π l → ∀ s, ∃ c : ℂ, ‖c‖ = Formalism.QuantumDeterminants.Tz k r z * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ v ∈ R.sm, l (ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (fun c' => io s c' (∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d)))) = c • l v := by
  first | exact @GlobalTheory.bessel_ev_projector_value | exact GlobalTheory.bessel_ev_projector_value | (intros; apply GlobalTheory.bessel_ev_projector_value <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bigCellExpansion_smul : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (t : ℂ), Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁ → Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p (fun g => t • f g) b C₃ a₁ := by
  first | exact @GlobalTheory.familyDerivativeExpansion_smul | exact GlobalTheory.familyDerivativeExpansion_smul | (intros; apply GlobalTheory.familyDerivativeExpansion_smul <;> assumption)
end
