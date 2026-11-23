module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Formalism.LocalToGlobal.CharacterGerms.ExistsStrictMonoMinor
public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import ReciprocityTheory.DualLattices.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.FittingIdeal.DetMulMemFitt0
public import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Formalism.IncomingBounds.Bundle001
import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.LocalToGlobal.CharacterGerms.Bundle002
import Formalism.LocalToGlobal.CharacterGerms.Bundle012
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSg

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Flag

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {m : ZMod d → ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]

def idxS (hd : ZMod d) (g : Fin 2) (t : ZMod d) : ZMod d := if g = 0 then t else t - hd

theorem rkF_sigmaS (hd : ZMod d) (X : RowData C V d (fun _ => Σ a : ZMod d, Fin (m a)) J)
    (hty : ∀ (g : Fin 2) (x : Σ a : ZMod d, Fin (m a)), (X.G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + hd)
    (g : Fin 2) (t : ZMod d) : X.rkF g t = m (idxS hd g t) := by
  unfold RowData.rkF
  refine Finset.card_eq_of_equiv_fin
    ((Equiv.subtypeEquivRight fun c => ?_).trans (Equiv.sigmaSubtype (idxS hd g t)))
  rw [Finset.mem_filter, hty]
  simp only [Finset.mem_univ, true_and]
  unfold idxS
  by_cases hg : g = 0
  · simp only [if_pos hg]
  · simp only [if_neg hg]
    exact eq_sub_iff_add_eq.symm

def stdFlagS (hd : ZMod d) (X : RowData C V d (fun _ => Σ a : ZMod d, Fin (m a)) J)
    (hty : ∀ (g : Fin 2) (x : Σ a : ZMod d, Fin (m a)), (X.G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + hd) :
    Flag X where
  en := fun g t q => ⟨idxS hd g t, ⟨q.val, (rkF_sigmaS hd X hty g t) ▸ q.isLt⟩⟩
  en_inj := fun g t q q' h => by
    have h1 := eq_of_heq (Sigma.mk.inj h).2
    exact Fin.ext (Fin.mk.inj_iff.1 h1)
  en_ty := fun g t q => by
    rw [hty]
    unfold idxS
    by_cases hg : g = 0
    · simp [hg]
    · simp [hg]

end Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace ValuationFitting

open ReciprocityTheory.PGsh.Up CharacteristicFromRanks

variable {C : Type} [Field C]

instance factL (V : VF C) : Fact V.l.Prime := ⟨V.l_prime⟩

def ValTie (V : VF C) (vm : Valuation C NNReal) : Prop :=
  ∀ x : C, x ≠ 0 → ∃ t : ℝ, V.v x = (t : WithTop ℝ) ∧ (vm x : ℝ) = (vm (V.l : C) : ℝ) ^ t

section Val

variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

def vA (V : VF C) (R : Type) [CommRing R] [Algebra R C] : AddValuation R (WithTop ℝ) :=
  V.v.comap (algebraMap R C)

theorem vA_apply (x : R) : vA V R x = V.v (algebraMap R C x) := rfl

theorem vA_nonneg (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) : ∀ x : R, 0 ≤ vA V R x := by
  intro x
  rw [vA_apply]
  by_cases hx : algebraMap R C x = 0
  · rw [hx, V.v.map_zero]; exact le_top
  · obtain ⟨t, ht1, ht2⟩ := hT _ hx
    rw [ht1]
    have hle : (vm (algebraMap R C x) : ℝ) ≤ 1 := by exact_mod_cast hv.map_le_one x
    have : 0 ≤ t := by
      by_contra hneg
      have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (not_le.mp hneg)
      rw [← ht2] at this
      linarith
    exact_mod_cast this

theorem lenCoker_vA {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) :
    S4.lenCoker (vA V R) α = S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) := by
  unfold S4.lenCoker
  congr 1
  funext g
  rw [vA_apply, RingHom.map_det]
  rfl

end Val

theorem rpow_neg_succ {l : ℕ} (hl : 0 < l) (n : ℕ) :
    (l : ℝ) ^ (-((n : ℝ) + 1)) = ((l : ℝ) ^ (n + 1))⁻¹ := by
  have h0 : (0 : ℝ) ≤ l := by positivity
  rw [Real.rpow_neg h0, ← Nat.cast_succ, Real.rpow_natCast]

section Val2

variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem lenCoker_eq_logb (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : HasLen vm R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) (hpos : 0 < (x : ℝ)) :
    S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) =
      ((Real.logb (vm (V.l : C) : ℝ) x : ℝ) : WithTop ℝ) := by
  have hxb : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x = x :=
    Real.rpow_logb h0 (ne_of_lt h1) hpos
  rw [← lenCoker_vA]
  apply le_antisymm
  · obtain ⟨y, hy, hyV⟩ := Formalism.MainNotions.G.ValuationFitting.fitt_ge hv α hx
    have hy0 : algebraMap R C y ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hyV
      rw [← hyV] at hpos
      simp at hpos
    obtain ⟨t, ht1, ht2⟩ := hT _ hy0
    refine le_trans (S4.lenCoker_le_of_mem (vA V R) (vA_nonneg hT hv h0 h1) _ hy) ?_
    rw [vA_apply, ht1]
    have : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x ≤ (vm (V.l : C) : ℝ) ^ t := by
      rw [hxb, ← ht2, hyV]
    rw [Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at this
    exact_mod_cast this
  · unfold S4.lenCoker
    refine Finset.le_inf fun g _ => ?_
    rw [vA_apply]
    by_cases hz : algebraMap R C (α.submatrix id g).det = 0
    · rw [hz, V.v.map_zero]; exact le_top
    · obtain ⟨t, ht1, ht2⟩ := hT _ hz
      rw [ht1]
      have hle : (vm (algebraMap R C (α.submatrix id g).det) : ℝ) ≤ x := by
        exact_mod_cast Formalism.MainNotions.G.ValuationFitting.fitt_le hv α hx g
      rw [ht2, ← hxb, Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at hle
      exact_mod_cast hle

end Val2

end ValuationFitting

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

theorem tyS_add {l : ℕ} (hl : 2 ≤ l) (a b : ℕ → C) : tyS l (fun s => a s + b s) = tyS l a + tyS l b := by
  ext n
  simp only [tyS, PowerSeries.coeff_mk, map_add (f := _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

def AddCvSt (V : VF C) : Prop :=
  ∀ γ γ' : κ → PowerSeries C, IsCv V γ → IsCv V γ' →
    ∃ γ'' : κ → PowerSeries C, IsCv V γ'' ∧
      (∀ i, alongCv γ'' (X.lg i) = alongCv γ (X.lg i) + alongCv γ' (X.lg i)) ∧
      ∀ v : κ → C, (∀ i, V.Ge 0 (v i)) →
        PowerSeries.constantCoeff (alongCv γ'' (X.sg v) - alongCv γ (X.sg v) - alongCv γ' (X.sg v)) = 0 ∧
        ∀ n, V.Ge 0 (PowerSeries.coeff n (alongCv γ'' (X.sg v) - alongCv γ (X.sg v) - alongCv γ' (X.sg v)))

theorem add_mem (V : VF C) (g : Fin 2) (hA : X.AddCvSt V) (hu : ∀ g c i, V.Ge 0 (X.u g c i))
    (x y : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (hy : y ∈ X.TySet V g) : x + y ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨γ', lam', hγ', hlam', h1', h2'⟩ := hy
  obtain ⟨γ'', hγ'', hL, hS⟩ := hA γ γ' hγ hγ'
  have hty : ∀ n, tyS V.l (fun s => (x + y) s n) = tyS V.l (fun s => x s n) + tyS V.l (fun s => y s n) :=
    fun n => tyS_add hl2 _ _
  refine ⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (hu (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_add (f := _), map_add (f := _), (hlam q).1, (hlam' q).1, c0]
      simp
    · rw [map_add (f := _), map_add (f := _)]
      exact (((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)
  · intro i
    rw [hL i, h1 i, h1' i, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hty, smul_add]
  · intro q
    have hs : ∀ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => (x + y) s (Sum.inl c)) else 0) =
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) +
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => y s (Sum.inl c)) else 0) := by
      intro c
      rw [hty]
      split_ifs
      · rw [smul_add]
      · rw [add_zero]
    simp only [hs]
    rw [Finset.sum_add_distrib, hty, h2 q, h2' q]
    abel

private theorem powerSeries_rescale_smul (a c : C) (f : PowerSeries C) :
    PowerSeries.rescale a (c • f) = c • PowerSeries.rescale a f := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

private theorem alongCv_rescale_eq_rescale_alongCv {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (a : C) (f : MvPowerSeries σ C) :
    alongCv (fun i => PowerSeries.rescale a (γ i)) f = PowerSeries.rescale a (alongCv γ f) := by
  simp only [PowerSeries.rescale_eq_subst]
  exact alongCv_repar hγ (by simp) f

private theorem tyS_neg_eq_rescale_neg_one_of_odd {l : ℕ} (hl : Odd l) (a : ℕ → C) :
    tyS l (fun s => -a s) = PowerSeries.rescale (-1) (tyS l a) := by
  ext n
  simp only [tyS, PowerSeries.coeff_mk, PowerSeries.coeff_rescale, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with h
  · rw [← h, (hl.pow).neg_one_pow]
    ring
  · ring

private theorem isCv_rescale_neg_one (V : VF C) {σ : Type} {γ : σ → PowerSeries C} (h : IsCv V γ) :
    IsCv V (fun i => PowerSeries.rescale (-1 : C) (γ i)) := by
  intro i
  show PowerSeries.constantCoeff (PowerSeries.rescale (-1 : C) (γ i)) = 0 ∧
    ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.rescale (-1 : C) (γ i)))
  refine ⟨?_, fun n => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (h i).1
  · have h2 := (h i).2 n
    rw [PowerSeries.coeff_rescale]
    rcases neg_one_pow_eq_or C n with e | e
    · rw [e, one_mul]
      exact h2
    · rw [e, neg_one_mul]
      unfold VF.Ge at h2 ⊢
      rw [V.v.map_neg]
      exact h2

theorem neg_mem (V : VF C) (g : Fin 2) (hodd : V.l ≠ 2) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    -x ∈ X.TySet V g := by
  have hl : Odd V.l := V.l_prime.odd_of_ne_two hodd
  unfold RawChart.TySet at hx ⊢
  obtain ⟨γ, lam, hγ, hlam, hlg, hq⟩ := hx
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  rw [Set.mem_setOf_eq]
  refine ⟨fun i => PowerSeries.rescale (-1 : C) (γ i), fun q => PowerSeries.rescale (-1 : C) (lam q),
    isCv_rescale_neg_one V hγ, isCv_rescale_neg_one V hlam, ?_, ?_⟩
  · intro i
    simp only [Pi.neg_apply]

    rw [alongCv_rescale_eq_rescale_alongCv hγ0, hlg i, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [tyS_neg_eq_rescale_neg_one_of_odd hl, powerSeries_rescale_smul]
  · intro q
    simp only [Pi.neg_apply]
    rw [tyS_neg_eq_rescale_neg_one_of_odd hl, hq q, alongCv_rescale_eq_rescale_alongCv hγ0]

    simp only [tyS_neg_eq_rescale_neg_one_of_odd hl, map_add (f := _), map_sub, map_sum, apply_ite ⇑(PowerSeries.rescale (-1 : C)), map_zero,
    powerSeries_rescale_smul]

theorem sum_mem (V : VF C) (g : Fin 2) (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g) {ι : Type} (s : Finset ι)
    (f : ι → ℕ → I g ⊕ JJ I g → C) (hf : ∀ i ∈ s, f i ∈ X.TySet V g) : ∑ i ∈ s, f i ∈ X.TySet V g := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact h0
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OAct

open PartialDerivEval LogEx OActLog OActSg

variable {C : Type} [Field C]

theorem tyS_smul (l : ℕ) (c : C) (a : ℕ → C) : tyS l (fun s => c * a s) = c • tyS l a := by
  ext n
  rw [PowerSeries.coeff_smul]
  simp only [tyS, PowerSeries.coeff_mk, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero]

variable {dd : ℕ}

theorem uncurry_sub (f g : PS C 1 dd) : un1 (f - g) = un1 f - un1 g := by
  funext μ
  show MvPowerSeries.coeff _ (f - g) = MvPowerSeries.coeff _ f - MvPowerSeries.coeff _ g
  exact map_sub _ _ _

theorem uncurry_C_mul (c : C) (f : PS C 1 dd) : un1 (MvPowerSeries.C c * f) = MvPowerSeries.C c * un1 f := by
  funext μ
  show MvPowerSeries.coeff _ (MvPowerSeries.C c * f) = MvPowerSeries.coeff μ (MvPowerSeries.C c * un1 f)
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rfl

theorem uncurry_linear_combination (c : Fin dd → C) (f : Fin dd → PS C 1 dd) :
    un1 (∑ j, MvPowerSeries.C (c j) * f j) = ∑ j, MvPowerSeries.C (c j) * un1 (f j) := by
  funext μ
  show MvPowerSeries.coeff _ (∑ j, MvPowerSeries.C (c j) * f j) =
    MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (c j) * un1 (f j))

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rfl

theorem integralSeries_uncurry_one {V : VF C} {f : PS C 1 dd} (hf : IntS V f) : IntS V (un1 f) := fun _ => hf _

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem sgP_smul (Y : FBChart C V O dd) (c : C) (v : Fin dd → C) :
    Y.sgP (c • v) = MvPowerSeries.C c * Y.sgP v := by
  unfold FBChart.sgP
  rw [mul_neg, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

end OAct

end Formalism.L2.FormalSeriesBounds
end
end
