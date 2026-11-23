module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle002
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle001
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def EntB (j : ℕ) (i0 : X.Pl → ℕ) (g : ℝ) : Prop :=
  ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      Y.geC (AddMonoidAlgebra.coeff (applyD (X.PI j I i0) (X.ThZA Y.Kc j (Y.ThA j La La' φ))) n) g

def TtL (j : ℕ) (i0 : X.Pl → ℕ) (vs : List X.Pl) (F : X.Fm j) : X.Fm j :=
  vs.foldr (fun v F' => X.Tt v (i0 v) j F') F

def FormB : Prop :=
  ∀ j < X.mm, ∀ (i0 : X.Pl → ℕ) (vs : List X.Pl) (g : ℝ), vs.Nodup → (∀ v, i0 v ≤ X.G.P.r) →
    (∀ v, v ∉ vs → i0 v = 0) → EntB X Y j i0 g →
    ∀ G ∈ X.Int j, X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (g - X.dG j)

def PlaceB (j : ℕ) (v : X.Pl) (i : ℕ) (g : ℝ) : Prop :=
  (i = 0 ∧ (Y.LowAt j v g ∨ g ≤ X.gv v (j + 1) - X.alEven v)) ∨ (1 ≤ i ∧ i ≤ X.G.P.r ∧ g ≤ X.gv v (j + 1))

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section LogInv

variable (p : ℕ) [Fact p.Prime] (K1 : Type) [Field K1] [Algebra (K0 p) K1]

def en_L : PowerSeries K1 := PowerSeries.map (algebraMap (K0 p) K1) (logF p)

theorem en_logF_zero : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, logF, PowerSeries.coeff_mk]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simp [hp.ne']

theorem en_logF_one : PowerSeries.coeff 1 (logF p) = 1 := by
  rw [logF, PowerSeries.coeff_mk]
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h1 : (1 : ℕ) ≠ p ^ (2 * 1) := by
    have : 1 < p ^ (2 * 1) := Nat.one_lt_pow (by norm_num) hp
    omega
  rw [if_neg h1]
  simp

theorem en_L_zero : PowerSeries.constantCoeff (en_L p K1) = 0 := by
  rw [en_L, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, en_logF_zero, map_zero]

theorem en_L_one : IsUnit (PowerSeries.coeff 1 (en_L p K1)) := by
  rw [en_L, PowerSeries.coeff_map, en_logF_one, map_one]
  exact isUnit_one

def en_E : PowerSeries K1 := (en_L p K1).substInvOfIsUnit (en_L_one p K1)

theorem en_E_zero : PowerSeries.constantCoeff (en_E p K1) = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _

variable {ι : Type}

def en_aL (i : ι) : MvPowerSeries ι K1 := PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1) (en_L p K1)

def en_Ec (i : ι) : MvPowerSeries ι K1 := PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1) (en_E p K1)

theorem en_inParamK_eq (f : MvPowerSeries ι K1) : inParamK p K1 f = MvPowerSeries.subst (en_aL p K1) f := rfl

theorem en_aL_zero (i : ι) : MvPowerSeries.constantCoeff (en_aL p K1 i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (en_L_zero p K1)

theorem en_Ec_zero (i : ι) : MvPowerSeries.constantCoeff (en_Ec p K1 i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (en_E_zero p K1)

variable [Finite ι]

theorem en_aL_hs : MvPowerSeries.HasSubst (en_aL p K1 : ι → MvPowerSeries ι K1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_aL_zero p K1)

theorem en_Ec_hs : MvPowerSeries.HasSubst (en_Ec p K1 : ι → MvPowerSeries ι K1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_Ec_zero p K1)

theorem en_aL_Ec (i : ι) : MvPowerSeries.subst (en_aL p K1) (en_Ec p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) := by
  have h1 : MvPowerSeries.subst (en_aL p K1) (en_Ec p K1 i) =
      PowerSeries.subst (en_aL p K1 i) (en_E p K1) := by
    unfold en_Ec PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X i).const (en_aL_hs p K1)]
    simp only [MvPowerSeries.subst_X (en_aL_hs p K1)]
  rw [h1, en_aL, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (en_L_zero p K1)) (PowerSeries.HasSubst.X i), en_E,
    PowerSeries.subst_substInvOfIsUnit_left _ (en_L_zero p K1), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

theorem en_Ec_aL (i : ι) : MvPowerSeries.subst (en_Ec p K1) (en_aL p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) := by
  have h1 : MvPowerSeries.subst (en_Ec p K1) (en_aL p K1 i) =
      PowerSeries.subst (en_Ec p K1 i) (en_L p K1) := by
    unfold en_aL PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X i).const (en_Ec_hs p K1)]
    simp only [MvPowerSeries.subst_X (en_Ec_hs p K1)]
  rw [h1, en_Ec, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (en_E_zero p K1)) (PowerSeries.HasSubst.X i), en_E,
    PowerSeries.subst_substInvOfIsUnit_right _ (en_L_zero p K1), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

theorem en_Ec_inParamK (U : MvPowerSeries ι K1) : MvPowerSeries.subst (en_Ec p K1) (inParamK p K1 U) = U := by
  rw [en_inParamK_eq, MvPowerSeries.subst_comp_subst_apply (en_aL_hs p K1) (en_Ec_hs p K1)]
  simp only [en_Ec_aL]
  rw [MvPowerSeries.subst_self]
  rfl

theorem en_inParamK_Ec (i : ι) : inParamK p K1 (en_Ec p K1 i) = (MvPowerSeries.X i : MvPowerSeries ι K1) :=
  en_aL_Ec p K1 i

theorem en_inParamK_mul (f g : MvPowerSeries ι K1) : inParamK p K1 (f * g) = inParamK p K1 f * inParamK p K1 g :=
  MvPowerSeries.subst_mul (en_aL_hs p K1) f g

theorem en_inParamK_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K1) :
    inParamK p K1 (∏ i ∈ s, f i) = ∏ i ∈ s, inParamK p K1 (f i) := by
  simp only [en_inParamK_eq, ← MvPowerSeries.coe_substAlgHom (en_aL_hs p K1), map_prod]

theorem en_inParamK_pow (f : MvPowerSeries ι K1) (n : ℕ) : inParamK p K1 (f ^ n) = inParamK p K1 f ^ n :=
  MvPowerSeries.subst_pow (en_aL_hs p K1) f n

theorem en_Ec_supp {Pl : Type} (π : ι → Pl) (i : ι) : en_Ec p K1 i ∈ Gen.SuppOn (R := K1) π (π i) := by
  unfold en_Ec PowerSeries.subst
  exact Gen.subst_mem (π := fun _ : Unit => π i) (PowerSeries.HasSubst.X i).const (fun _ _ _ _ => rfl)
    (fun _ _ => Gen.X_mem rfl)

end LogInv

theorem en_expS_supp {p : ℕ} [Fact p.Prime] {ι Pl : Type} (π : ι → Pl) (v : Pl) {f : MvPowerSeries ι (K0 p)}
    (hf : f ∈ Gen.SuppOn π v) : expS p f ∈ Gen.SuppOn π v := by
  intro n hn
  have e : MvPowerSeries.coeff n (expS p f) =
      ∑ k ∈ range (n.degree + 1), ((k.factorial : K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k) := rfl
  rw [e] at hn
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact (Subring.pow_mem _ hf k) n (right_ne_zero_of_mul hk)

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def en_pi (j : ℕ) : X.EA j ⊕ X.EA j → X.Pl := Sum.elim Sigma.fst Sigma.fst

theorem en_coordZA_zero (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

theorem en_coordZA_hs (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) : MvPowerSeries.HasSubst (X.coordZA K' j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (en_coordZA_zero X K' j)

theorem en_coordZA_supp (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    X.coordZA K' j x ∈ Gen.SuppOn (R := K') (Sigma.fst : X.ZA j → X.Pl) (en_pi X j x) := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩
  · exact Subring.sum_mem _ fun s _ => Subring.mul_mem _ (Gen.C_mem _) (Gen.X_mem rfl)
  · exact Subring.sum_mem _ fun s _ => Subring.mul_mem _ (Gen.C_mem _) (Gen.X_mem rfl)

theorem en_ThZA_supp (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (v : X.Pl)
    {f : MvPowerSeries (X.EA j ⊕ X.EA j) K'} (hf : f ∈ Gen.SuppOn (en_pi X j) v) :
    X.ThZA K' j f ∈ Gen.SuppOn (Sigma.fst : X.ZA j → X.Pl) v :=
  Gen.subst_mem (en_coordZA_hs X K' j) hf fun s hs => hs ▸ en_coordZA_supp X K' j s

theorem en_ThZA_mul (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f g : MvPowerSeries (X.EA j ⊕ X.EA j) K') :
    X.ThZA K' j (f * g) = X.ThZA K' j f * X.ThZA K' j g :=
  MvPowerSeries.subst_mul (en_coordZA_hs X K' j) f g

theorem en_ThZA_prod (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) {α : Type} (s : Finset α)
    (f : α → MvPowerSeries (X.EA j ⊕ X.EA j) K') : X.ThZA K' j (∏ i ∈ s, f i) = ∏ i ∈ s, X.ThZA K' j (f i) := by
  unfold Sys.ThZA
  simp only [← MvPowerSeries.coe_substAlgHom (en_coordZA_hs X K' j), map_prod]

theorem en_ThZA_pow (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f : MvPowerSeries (X.EA j ⊕ X.EA j) K')
    (n : ℕ) : X.ThZA K' j (f ^ n) = X.ThZA K' j f ^ n :=
  MvPowerSeries.subst_pow (en_coordZA_hs X K' j) f n

def en_F (j : ℕ) (v : X.Pl) : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc :=
  MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v))

theorem en_PhAt_supp (j : ℕ) (v : X.Pl) : Y.PhAt j v ∈ Gen.SuppOn (en_pi X j) v := by
  unfold Pend.PhAt
  refine Subring.sum_mem _ fun e _ => ?_
  unfold sub2
  refine Gen.subst_mem (π := fun _ : Fin 2 => v) MvPowerSeries.HasSubst.X_X (fun _ _ _ _ => rfl) fun s _ => ?_
  fin_cases s
  · exact Gen.X_mem rfl
  · exact Gen.X_mem rfl

theorem en_F_supp (j : ℕ) (v : X.Pl) : en_F X Y j v ∈ Gen.SuppOn (en_pi X j) v :=
  Gen.map_mem _ (en_expS_supp _ v (Subring.neg_mem _ (en_PhAt_supp X Y j v)))

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF)

section Gen

variable {K : Type} [Field K] {R : Subring K}

theorem IntR_add {ι : Type} {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) : IntR R (f + g) := by
  intro n
  rw [map_add (f := _)]
  exact R.add_mem (hf n) (hg n)

theorem IntR_zero {ι : Type} : IntR R (0 : MvPowerSeries ι K) := by
  intro n
  rw [map_zero]
  exact R.zero_mem

theorem IntR_sum {ι α : Type} (s : Finset α) (f : α → MvPowerSeries ι K) (h : ∀ a ∈ s, IntR R (f a)) :
    IntR R (∑ a ∈ s, f a) := by
  intro n

  rw [map_sum]
  exact R.sum_mem fun a ha => h a ha n

theorem IntR_X {ι : Type} (i : ι) : IntR R (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

private theorem intR_iff_mem_range_map_subtype {ι : Type} {f : MvPowerSeries ι K} :
    IntR R f ↔ f ∈ (MvPowerSeries.map R.subtype).range := by
  constructor
  · intro hf
    unfold IntR at hf
    let g : MvPowerSeries ι R := fun n => ⟨MvPowerSeries.coeff n f, hf n⟩
    refine ⟨g, ?_⟩
    ext n
    rw [MvPowerSeries.coeff_map]
    rfl
  · rintro ⟨g, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n g).2

theorem IntR_subst {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntR R (a i)) {f : MvPowerSeries σ K}
    (hf : IntR R f) : IntR R (MvPowerSeries.subst a f) := by
  classical
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hprod : ∀ d : σ →₀ ℕ, IntR R (d.prod fun s k => (a s) ^ k) := by
    intro d
    rw [intR_iff_mem_range_map_subtype, Finsupp.prod]
    exact Subring.prod_mem _ fun s _ => Subring.pow_mem _ (intR_iff_mem_range_map_subtype.1 (ha s)) _
  intro e
  rw [MvPowerSeries.coeff_subst hs]
  by_cases hfin : (Function.support fun d : σ →₀ ℕ =>
      MvPowerSeries.coeff d f • MvPowerSeries.coeff e (d.prod fun s k => (a s) ^ k)).Finite
  · rw [finsum_eq_sum _ hfin]
    exact R.sum_mem fun d _ => by
      rw [smul_eq_mul]
      exact R.mul_mem (hf d) (hprod d e)
  · rw [finsum_of_infinite_support hfin]
    exact R.zero_mem

theorem IntR_of_ps {f : PowerSeries K} (hf : ∀ n, PowerSeries.coeff n f ∈ R) :
    IntR R (f : MvPowerSeries Unit K) := by
  intro n
  have hn : n = Finsupp.single () (n ()) := Finsupp.unique_single n
  rw [hn]
  exact hf (n ())

theorem IntR_psubst {τ : Type} {L : MvPowerSeries τ K} (hL0 : MvPowerSeries.constantCoeff L = 0) (hL : IntR R L)
    {f : PowerSeries K} (hf : ∀ n, PowerSeries.coeff n f ∈ R) : IntR R (PowerSeries.subst L f) :=
  IntR_subst (fun _ : Unit => L) (fun _ => hL0) (fun _ => hL) (IntR_of_ps hf)

end Gen

section Mu

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

private theorem mul_add_one_le_succ_pow (b j : ℕ) : b * j + 1 ≤ (b + 1) ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_right (b + 1) ih, Nat.zero_le (b * b * k)]

theorem lamF_mem (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) (n : ℕ) :
    PowerSeries.coeff n (lamF p vp) ∈ Rp p K' vp := by
  have hvpR : vp ∈ Rp p K' vp := by
    unfold Rp
    exact Subring.subset_closure (Set.mem_union_right _ rfl)
  simp only [lamF, lgF, PowerSeries.coeff_mk, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  split_ifs with h
  · have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    have hle : (p ^ 2 - 1) * j + 1 ≤ (p ^ 2) ^ j := by
      have := mul_add_one_le_succ_pow (p ^ 2 - 1) j
      rwa [Nat.sub_add_cancel hp1] at this
    obtain ⟨m, hm⟩ : ∃ m, n - 1 = (p ^ 2 - 1) * j + m := by
      refine ⟨n - 1 - (p ^ 2 - 1) * j, ?_⟩
      rw [h]
      generalize (p ^ 2 - 1) * j = A at hle ⊢
      generalize (p ^ 2) ^ j = B at hle ⊢
      omega
    rw [hm, pow_add, ← hvp, ← pow_mul]
    by_cases h0 : vp ^ ((p ^ 2 - 1) * j) = 0
    · rw [h0, zero_mul, zero_mul]
      exact (Rp p K' vp).zero_mem
    · rw [mul_comm (vp ^ ((p ^ 2 - 1) * j)), mul_assoc, mul_inv_cancel₀ h0, mul_one]
      exact (Rp p K' vp).pow_mem hvpR m
  · rw [mul_zero]
    exact (Rp p K' vp).zero_mem

theorem exists_mu (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) :
    ∃ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 ∧ (∀ n, PowerSeries.coeff n μ ∈ Rp p K' vp) ∧
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X := by
  let l0 : PowerSeries (Rp p K' vp) := PowerSeries.mk fun n => ⟨_, lamF_mem p K' vp hvp n⟩
  have hmap : PowerSeries.map (Rp p K' vp).subtype l0 = lamF p vp := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  have hc : PowerSeries.constantCoeff l0 = 0 := by
    apply Subtype.ext
    have := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_lamF p vp
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at this ⊢
    rw [PowerSeries.coeff_mk]
    exact this
  have hu : IsUnit (PowerSeries.coeff 1 l0) := by
    have : PowerSeries.coeff 1 l0 = 1 := by
      apply Subtype.ext
      rw [PowerSeries.coeff_mk]
      exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.coeff_one_lamF hp.out.two_le vp
    rw [this]
    exact isUnit_one
  have h1 := PowerSeries.subst_substInvOfIsUnit_right l0 hc hu
  refine ⟨PowerSeries.map (Rp p K' vp).subtype (l0.substInvOfIsUnit hu), ?_, fun n => ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_substInvOfIsUnit, map_zero]
  · rw [PowerSeries.coeff_map]
    exact Subtype.property _
  · have h2 := congrArg (PowerSeries.map (Rp p K' vp).subtype) h1
    rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.ps_map_subst _ (PowerSeries.HasSubst.substInvOfIsUnit l0 hu), hmap, PowerSeries.map_X] at h2
    exact h2

theorem map_logF : PowerSeries.map (algebraMap (K0 p) K') (logF p) = lgF K' p := by
  ext n

  simp only [PowerSeries.coeff_map, logF, lgF, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul]
  split_ifs <;> simp

end Mu

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
