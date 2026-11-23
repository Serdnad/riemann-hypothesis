module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
namespace GlobalTheory.GLq.Model
open Polynomial Formalism.CyclotomicNorms

variable (g : ℕ) [hg : Fact g.Prime]

theorem N_pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hg.out.one_lt)


open Formalism.MainNotions.ArithmeticCylinders
variable {g}

theorem thetaOf_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Fbar g} (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  apply GlobalTheory.GLq.LabelModel.thetaOf_pow <;> assumption

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  rw [toG, dite_eq_left x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem tl_self {n : ℕ} (M : Mt g n) : tl n M = M := by
  ext i j
  simp [tl, entN]

theorem hc_full {n : ℕ} (α : Gn g n → ℂ) (hα : IsClass α) : hc n 0 α (fun _ => 1) n = α := by
  funext x

  have hpar : ∀ M : Mt g n, InPar n M := fun M i j _ hi => absurd i.isLt (not_lt.mpr hi)
  have hα' : ∀ y : Gn g n, α (y⁻¹ * x * y) = α x := fun y => by
    simpa using hα x y⁻¹
  have hcard : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [hc, hcT, hpar, if_true, mul_one, tl_self, toG_coe, hα', Finset.sum_const,
    Finset.filter_true, Finset.card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hcard _

end GlobalTheory.GLq.Model
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Model

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

variable {n : Type} [Fintype n] [DecidableEq n]

def tU : P.R.Bˣ := (isUnit_tB P).unit

theorem actQ_tU (g : GQ l) (a : ℤ) : P.actQ g ((tU P ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * tU P := by
    apply Units.ext
    simpa [tU, Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem actdR_ι (g : GQ l) (b : P.R.B) : P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := by
  have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
  exact h.symm

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  change P.actQdR g (P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)) = _ * P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)
  rw [actdR_ι, actQ_tU, map_mul, AlgHom.commutes]

end GlobalTheory.PMon.Model

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct

namespace GlobalTheory.PMon

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def FilA (a : ℤ) : AddSubgroup P.R.BdR := ((P.PD (botExt l)).Fil a).toAddSubgroup

theorem mem_Fil_iff (K : FinExt l) {a : ℤ} {x : P.R.BdR} : x ∈ Fil P a ↔ x ∈ (P.PD K).Fil a := by
  have := P.PD_Fil (botExt l) K a
  change x ∈ ((P.PD (botExt l)).Fil a : Set P.R.BdR) ↔ x ∈ ((P.PD K).Fil a : Set P.R.BdR)
  rw [this]

variable {P}

theorem Fil_zero_mem (a : ℤ) : (0 : P.R.BdR) ∈ Fil P a := (FilA P a).zero_mem
theorem Fil_add {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P a) : x + y ∈ Fil P a := (FilA P a).add_mem hx hy
theorem Fil_neg {a : ℤ} {x : P.R.BdR} (hx : x ∈ Fil P a) : -x ∈ Fil P a := (FilA P a).neg_mem hx
theorem Fil_sum {a : ℤ} {ι : Type*} {s : Finset ι} {f : ι → P.R.BdR} (h : ∀ i ∈ s, f i ∈ Fil P a) :
    ∑ i ∈ s, f i ∈ Fil P a := (FilA P a).sum_mem h
theorem Fil_mul {a b : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P b) : x * y ∈ Fil P (a + b) :=
  (P.PD (botExt l)).Fil_mul a b x y hx hy
theorem Fil_mul_left {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P 0) (hy : y ∈ Fil P a) : x * y ∈ Fil P a := by
  simpa using Fil_mul hx hy
theorem Fil_mul_right {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P 0) : x * y ∈ Fil P a := by
  simpa using Fil_mul hx hy
theorem one_mem_Fil : (1 : P.R.BdR) ∈ Fil P 0 := (P.PD (botExt l)).one_mem
theorem Fil_act (g : GQ l) {a : ℤ} {x : P.R.BdR} (hx : x ∈ Fil P a) : P.actQdR g x ∈ Fil P a := by
  have := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_botExt g⟩ a x hx
  rwa [P.PD_actdR] at this

variable (P)

def S0 : Subring P.R.BdR where
  carrier := Fil P 0
  zero_mem' := Fil_zero_mem 0
  one_mem' := one_mem_Fil
  add_mem' := Fil_add
  neg_mem' := Fil_neg
  mul_mem' := Fil_mul_left

theorem mem_S0_of_sum_eq {x : P.R.BdR} : x ∈ S0 P ↔ x ∈ Fil P 0 := Iff.rfl

theorem om_mem_Fil (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fil P 0 := by
  rw [mem_Fil_iff P (adjExt x)]
  have h := ((P.PD (adjExt x)).Fil 0).smul_mem ⟨x, mem_adjExt x⟩ (P.PD (adjExt x)).one_mem
  rw [Algebra.smul_def, mul_one] at h
  exact h

theorem kd_mem_Fil (c : ↥(MaximalUnramifiedExtension l)) : kd P c ∈ Fil P 0 := om_mem_Fil P _

theorem q_mem_Fil (q : ℚ_[l]) : algebraMap ℚ_[l] P.R.BdR q ∈ Fil P 0 := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
  exact om_mem_Fil P _

theorem iota_injective : Function.Injective P.ιB := fun a b h =>
  (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι, h])

theorem iota_act (g : GQ l) (b : P.R.B) : P.ιB (P.actQ g b) = P.actQdR g (P.ιB b) := by
  have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rwa [P.PD_actB, P.PD_ι, P.PD_ι, P.PD_actdR] at this

theorem iota_kur (c : ↥(MaximalUnramifiedExtension l)) : P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = kd P c := by
  have := (P.PD (adjExt (c : Om l))).ι.commutes ⟨c, mem_adjExt _, c.2⟩
  rw [P.PD_ι] at this
  exact this

theorem fr_zero (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := rfl
theorem fr_add (a b : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l (a + b) c = fr l a (fr l b c) := by
  simp [fr, pow_add, AlgHom.mul_apply]
theorem fr_one (c : ↥(MaximalUnramifiedExtension l)) : fr l 1 c = frobUr l c := by simp [fr]
theorem fr_q (m : ℕ) (q : ℚ_[l]) : fr l m (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q :=
  (frobUr l ^ m).commutes q
theorem fr_comm {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (m : ℕ) : fr l r (fr l m c) = fr l m c := by
  rw [← fr_add, add_comm, fr_add, h]
theorem fr_mul {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (k : ℕ) : fr l (r * k) c = c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ, fr_add, h, ih]
theorem fr_mod {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (m : ℕ) : fr l (m % r) c = fr l m c := by
  conv_rhs => rw [← Nat.mod_add_div m r, fr_add, fr_mul h]

theorem phi_iter_kur (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB^[m] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m c) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, phiB_algebraMap, add_comm, fr_add, fr_one]

def evHom (m : ℕ) : P.R.B →+* P.R.BdR :=
  (P.ιB : P.R.B →+* P.R.BdR).comp ((P.φB ^ m : P.R.B →ₐ[ℚ_[l]] P.R.B) : P.R.B →+* P.R.B)

theorem evHom_apply (m : ℕ) (b : P.R.B) : evHom P m b = ev P m b := by
  simp [evHom, ev, AlgHom.coe_pow]

theorem ev_kur (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : ev P m (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = kd P (fr l m c) := by
  rw [ev, phi_iter_kur, iota_kur]

theorem ev_act (m : ℕ) (g : GQ l) (b : P.R.B) : ev P m (P.actQ g b) = P.actQdR g (ev P m b) := by
  rw [ev, ev, ← iota_act]
  congr 1
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]

theorem act_kd {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    P.actQdR (g : GQ l) (kd P c) = kd P c := by
  change P.actQdR (g : GQ l) (algebraMap (Om l) P.R.BdR (c : Om l)) = algebraMap (Om l) P.R.BdR (c : Om l)
  rw [P.actQdR_Om, mem_GK.1 g.2 _ hc]

theorem act_kur {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c :=
  P.actQ_Kur _ c c (mem_GK.1 g.2 _ hc)

theorem act_ks {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    actSt P (g : GQ l) (ks P c) = ks P c := by
  change actSt P (g : GQ l) (Polynomial.C _) = Polynomial.C _
  rw [actSt_C, act_kur P g hc]

theorem tz_add (a b : ℤ) : tz P (a + b) = tz P a * tz P b := by simp [tz, zpow_add]
theorem tz_zero : tz P 0 = 1 := by simp [tz]
theorem tz_one : tz P 1 = P.ιB P.tB := by simp [tz]

theorem fund {b : P.R.B} (h : P.φB b = b) (h0 : P.ιB b ∈ Fil P 0) : ∃ c : ℚ_[l], algebraMap ℚ_[l] P.R.B c = b :=
  (P.PD (botExt l)).fund b (by rw [P.PD_φ, h]) (by rw [P.PD_ι]; exact h0)

end GlobalTheory.PMon

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

def MatThm : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → AdmSt P ρ

def FrameEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (AdmDR P ρ ↔ ∃ w : Fin r → n → ℤ, Framed P ρ w)

def TwistStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ), IsRat r ρ → Framed P ρ w →
    ∃ (K' : FinExt l) (r' : ℕ) (ρ' : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)) (w' : Fin r' → n → ℤ),
      IsRat r' ρ' ∧ Framed P ρ' w' ∧ ∑ m, ∑ j, w' m j = 0 ∧ (AdmSt P ρ' → AdmSt P ρ)

def SenFinite : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]),
    (∀ i j, Continuous fun g => (ρ g : Matrix n n ℚ_[l]) i j) →
    ∀ M : GL n ℂ_[l], (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) *
      (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) →
    (ρ '' (IK K : Set ↥(GK K))).Finite

def UnrStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (ρ '' (IK K : Set ↥(GK K))).Finite → AdmSt P ρ

def SenStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → Framed P ρ (0 : Fin r → n → ℤ) → AdmSt P ρ

def Hyodo : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    (∀ v : V, Continuous fun g => ρ g v) → IsSst P ρ →
    ∀ c : ↥(GK K) → V, Continuous c → (∀ g h, c (g * h) = c g + ρ g (c h)) →
    (∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) →
    ∃ b : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g b - b

def ExtStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) →
    AdmDR P ρ → AdmSt P ρ₁ → AdmSt P ρ₂ → AdmSt P ρ

def SubQuot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) →
    AdmDR P ρ → AdmDR P ρ₁ ∧ AdmDR P ρ₂

def RedStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → Splits r ρ →
    (∀ (a : Type) [Fintype a] [DecidableEq a], Fintype.card a < Fintype.card n →
      ∀ ρ' : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l), IsRat r ρ' → AdmDR P ρ' → AdmSt P ρ') → AdmSt P ρ

def ModStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (x y : Fin r × n), x ≠ y →
    IsRat r ρ → Framed P ρ w → ¬ Splits r ρ →
    ∃ ρ' : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l), IsRat r ρ' ∧ Framed P ρ' (fun m j => w m j + eps x y (m, j)) ∧
      (AdmSt P ρ' → AdmSt P ρ)

def FLAt (r : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (U : Fin r → GL n P.R.BdR) (x y : Fin r × n), x ≠ y → (∀ m, UnitM P (U m)) →
    (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) →
      ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) →
    ∃ A : GL n P.R.B, (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) ∧
      ∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) =
        (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (eps x y (m, j))) * (W : Matrix n n P.R.BdR)

def Ratio : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h s : ℕ), s < h →
    ∀ ω ω' : P.R.B, Plus T ω → Plus T ω' → P.φB^[h] ω = (l : P.R.B) ^ s * ω → P.φB^[h] ω' = (l : P.R.B) ^ s * ω' →
    ω' ≠ 0 → P.φB ω * ω' = ω * P.φB ω' → ∃ c : ℚ_[l], ω = c • ω'

def Moore : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h k : ℕ), k ≤ h →
    ∀ a : Fin k → P.R.B, (∀ j, Plus T (a j)) → (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) →
    LinearIndependent ℚ_[l] a → (Matrix.of fun i j : Fin k => P.φB^[i] (a j)).det ≠ 0

def ExI : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h →
    ∀ μ : Fin h → P.R.BdR, (∀ i, μ i ∈ Fil P 0) → (∃ i, μ i ∉ Fil P 1) →
    ∃ b : Fin h → P.R.B, (∀ j, Plus T (b j)) ∧ (∀ j, P.φB^[h] (b j) = (l : P.R.B) * b j) ∧
      LinearIndependent ℚ_[l] b ∧ ∀ j, ∑ i, μ i * ev P i (b j) ∈ Fil P 1

def ExII : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h →
    ∀ lam : Fin h → P.R.BdR, (∀ j, lam j ∈ Fil P 0) →
    (∀ c : Fin h → ℚ_[l], ∑ j, c j • lam j ∈ Fil P 1 → c = 0) →
    ∃ a : Fin h → P.R.B, a ≠ 0 ∧ (∀ j, Plus T (a j)) ∧ (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) ∧
      ∀ i : Fin h, ∑ j, lam j * ev P i (a j) ∈ Fil P 1

def WeilRes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, fr l r ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) = (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) ∧
      ∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))

end GlobalTheory.PMon

end
end

section

noncomputable section
namespace GlobalTheory.Present
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀) {k : Type} [Field k] [Algebra O k]

theorem φ_mem (T : LocLat G Qp LL O) (x : ↥(DΔ W T)) : W.φD T x ∈ DΔ W T :=
  fun δ hδ => by rw [← W.φγ_comm, x.2 δ hδ]

theorem γ_mem (T : LocLat G Qp LL O) (g : W.Gam) (x : ↥(DΔ W T)) : W.γD T g x ∈ DΔ W T :=
  fun δ hδ => by rw [← W.γD_mul, mul_comm, W.γD_mul, x.2 δ hδ]

variable {W} {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀} {γ : W.Gam}

theorem Pres.j_φ' (p : Pres W F ι τ γ) {T A q} (h : Onto T A q) (i : ZMod n) (x : ↥(DΔ W T)) :
    p.j T A q i ⟨W.φD T x, φ_mem W T x⟩ = (F.D A).φ i (p.j T A q (i - 1) x) :=
  p.j_φ T A q h i x _ rfl

end GlobalTheory.Present

namespace GlobalTheory.TopSteps.TopSit
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.PhiGam GlobalTheory.Models GlobalTheory.Present
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

end GlobalTheory.TopSteps.TopSit
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwAll

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)

def admissibleIndexBoundAllPowers (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, ABHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
      Formalism.MainNotions.BlochKatoReduction.Gen.PsiOk i A0 Q k' (ψ' ^ a) ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partAT bkP i Q k' (ψ' ^ a) eps' ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.partC N0 i Q k' (ψ' ^ a) eps' ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partD i Q k' (ψ' ^ a) eps' ∧
      partAB Y i F Q k' (ψ' ^ a) eps'

def goodTwistExistsAllCoprimePowers (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
    GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

variable {Y} (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

def TypeKept (E : ExpDat Y) : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k Q
  (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), TwOK i k Q ψ → UnrG ψ → ∀ a ∈ E.Dat0 i j b,
    Y.thPsi i j b k Q ψ a ⊆ ((((Fm0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) :
      Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b))

end GlobalTheory.TwAll
end
end
