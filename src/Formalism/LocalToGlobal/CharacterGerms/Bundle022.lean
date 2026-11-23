module

import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupCurveLogarithmsAddSubgroupResca
public import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Formalism.LocalToGlobal.CharacterGerms.Bundle016
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigA
public import Formalism.LocalToGlobal.CharacterGerms.Bundle004
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFB

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

theorem coeff_alongCv_congr {σ : Type} [Finite σ] {a a' : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, PowerSeries.constantCoeff (a' i) = 0) {k : ℕ}
    (h : ∀ i, ∀ m < k, PowerSeries.coeff m (a i) = PowerSeries.coeff m (a' i)) (f : MvPowerSeries σ C) :
    ∀ m < k, PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv a' f) := by
  apply GlobalTheory.RowLaw.CvGroup.alongCv_congr <;> assumption

theorem coeff_tyS_congr {l : ℕ} (hl : 2 ≤ l) (a b : ℕ → C) (N : ℕ) (hab : ∀ i < N, a i = b i) (m : ℕ)
    (hm : m < l ^ N) : PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m (tyS l b) := by
  simp only [tyS, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : l ^ s = m
  · rw [if_pos hs, if_pos hs]
    apply hab
    by_contra hc
    push_neg at hc
    have h1 : l ^ N ≤ l ^ s := Nat.pow_le_pow_right (by omega) hc
    rw [hs] at h1
    exact absurd hm (not_lt.2 h1)
  · rw [if_neg hs, if_neg hs]

theorem constantCoeff_tyS {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) : PowerSeries.constantCoeff (tyS l a) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [tyS, PowerSeries.coeff_mk]
  simp

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem curve_eq_ex_lg (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (δ : κ → PowerSeries C) (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0) (i : κ) :
    δ i = alongCv (fun j => alongCv δ (X.lg j)) (X.ex i) := by
  have hA : MvPowerSeries.HasSubst X.lg := MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0
  have hB : MvPowerSeries.HasSubst δ := MvPowerSeries.hasSubst_of_constantCoeff_zero hδ
  simp only [alongCv]
  rw [← MvPowerSeries.subst_comp_subst_apply hA hB, hexlg i, MvPowerSeries.subst_X hB]

theorem Vpow_mem' (V : VF C) (g : Fin 2) (s : ℕ) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    Vpow s x ∈ X.TySet V g := by
  induction s with
  | zero => rwa [Vpow_zero]
  | succ s ih => rw [Vpow_succ]; exact X.V_mem V g _ ih

theorem sumV_mem (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g)
    (y : ℕ → ℕ → I g ⊕ JJ I g → C) (hy : ∀ s, y s ∈ X.TySet V g) : sumV y ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  have hP : ∀ N : ℕ, ∑ s ∈ Finset.range N, Vpow s (y s) ∈ X.TySet V g := fun N =>
    X.sum_mem V g h0 hadd _ _ fun s _ => X.Vpow_mem' V g s _ (hy s)
  have hPeq : ∀ N i, i < N → ∀ n, (∑ s ∈ Finset.range N, Vpow s (y s)) i n = sumV y i n := by
    intro N i hi n
    rw [Finset.sum_apply, Finset.sum_apply]
    show ∑ s ∈ Finset.range N, (if i < s then 0 else y s (i - s) n) = ∑ s ∈ Finset.range (i + 1), y s (i - s) n
    have hsub : Finset.range (i + 1) ⊆ Finset.range N := Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [if_neg]
      have := Finset.mem_range.1 hs
      omega
    · intro s _ hs
      rw [if_pos]
      have : ¬ s < i + 1 := fun h => hs (Finset.mem_range.2 h)
      omega
  choose γN lamN hγN hlamN h1N h2N using hP
  set A : κ → PowerSeries C := fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c)) with hA
  have hA0 : ∀ i, PowerSeries.constantCoeff (A i) = 0 := by
    intro i
    rw [hA]
    show PowerSeries.constantCoeff (∑ c : I g, X.u g c i • tyS V.l (fun s => sumV y s (Sum.inl c))) = 0

    rw [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_tyS hl2, smul_zero]
  set γ : κ → PowerSeries C := fun i => alongCv A (X.ex i) with hγdef
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => constantCoeff_subst_zero hA0 (hex0 i)
  have hlgγ : ∀ i, alongCv γ (X.lg i) = A i := by
    intro i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hA0
    have e1 : MvPowerSeries.subst A (MvPowerSeries.subst X.ex (X.lg i)) = A i := by
      rw [hlgex i, MvPowerSeries.subst_X hS]
    rw [← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hex0) hS]
    rfl
  have htyN : ∀ N n, ∀ m < V.l ^ N, PowerSeries.coeff m (tyS V.l fun s => sumV y s n) =
      PowerSeries.coeff m (tyS V.l fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s n) := by
    intro N n m hm
    exact coeff_tyS_congr hl2 _ _ N (fun i hi => (hPeq N i hi n).symm) m hm
  have hγN' : ∀ N i, ∀ m < V.l ^ N, PowerSeries.coeff m (γ i) = PowerSeries.coeff m (γN N i) := by
    intro N i m hm
    rw [X.curve_eq_ex_lg hlg0 hexlg (γN N) (fun i => (hγN N i).1) i]
    refine coeff_alongCv_congr hA0 (fun j => constantCoeff_subst_zero (fun i => (hγN N i).1) (hlg0 j)) ?_ _ m hm
    intro j m' hm'
    show PowerSeries.coeff m' (∑ c : I g, X.u g c j • tyS V.l (fun s => sumV y s (Sum.inl c))) =
      PowerSeries.coeff m' (alongCv (γN N) (X.lg j))
    rw [h1N N j]

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m' hm']
  have hγI : IsCv V γ := by
    intro i
    refine ⟨hγ0 i, fun n => ?_⟩
    rw [hγN' n i n (Nat.lt_pow_self (by omega))]
    exact (hγN n i).2 n
  set lam : JJ I g → PowerSeries C := fun q => tyS V.l (fun s => sumV y s (Sum.inr q)) +
      alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0) with hlamdef
  have hlamN' : ∀ N q, ∀ m < V.l ^ N, PowerSeries.coeff m (lam q) = PowerSeries.coeff m (lamN N q) := by
    intro N q m hm
    have e : lamN N q = tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inr q)) +
        alongCv (γN N) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) •
          tyS V.l (fun s => (∑ s ∈ Finset.range N, Vpow s (y s)) s (Sum.inl c)) else 0) := by
      rw [h2N N q]
      abel
    rw [e, hlamdef]
    show PowerSeries.coeff m (tyS V.l (fun s => sumV y s (Sum.inr q)) +
      alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => sumV y s (Sum.inl c)) else 0)) = _

    rw [map_sub, map_sub, map_add (f := _), map_add (f := _), map_sum, map_sum, htyN N _ m hm,
    coeff_alongCv_congr hγ0 (fun i => (hγN N i).1) (fun i => hγN' N i) _ m hm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, htyN N _ m hm]
    · rfl
  have hlamI : IsCv V lam := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hlamN' 0 q 0 (by simp),
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hlamN 0 q).1
    · rw [hlamN' n q n (Nat.lt_pow_self (by omega))]
      exact (hlamN n q).2 n
  refine ⟨γ, lam, hγI, hlamI, hlgγ, ?_⟩
  intro q
  have hab : ∀ a b c : PowerSeries C, a = (a + b - c) - b + c := by
    intro a b c
    abel
  exact hab _ _ _

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

structure LetSys (C : Type) [Field C] (dd : ℕ) where
  ι : ℕ → Type
  fin : ∀ N, Fintype (ι N)
  cp : ∀ N, ι N → Fin N
  uv : ∀ N, ι N → Fin dd → C
  FF : ∀ N, Set (MvPolynomial (ι N) C)

attribute [instance] LetSys.fin

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.nab (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) (f : PS C n dd) (P : MvPolynomial (Ls.ι n) C) : C :=
  nabValN Y.B C Y.h Y.w0 Y.k f (Ls.cp n) (Ls.uv n) P

def FBChart.valSet (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) : Set (WithTop ℝ) :=
  {x | ∃ P ∈ Ls.FF n, ∃ f : PS C n dd, IntS V f ∧ x = V.v (Y.nab Ls n f P)}

def FBChart.nuPlE (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) : EReal :=
  ⨅ x ∈ Y.valSet Ls n, (WithBot.some x : WithBot (WithTop ℝ))

theorem map_prod_add (V : VF C) {α : Type} (s : Finset α) (x : α → C) : V.v (∏ o ∈ s, x o) = ∑ o ∈ s, V.v (x o) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

variable {d : ℕ} [NeZero d]

section One

variable {I : Fin 2 → Type} [∀ g, Fintype (I g)]

variable (Y : FBChart C V O dd) (p : PairData Y d I) (H : (Y.raw p).Hyps V) (Ls : LetSys C dd) (n : ℕ)

end One

section Orb

variable {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

abbrev WVO (I : Orb → Fin 2 → Type) := Σ o : Orb, WV (I o)

def IsImgO (X : ∀ o, RawChart C d (I o) (Fin dd)) {N : ℕ} {ι : Type} (cp : ι → Fin N) (uv : ι → Fin dd → C)
    (P : MvPolynomial ι C) (Q : MvPolynomial (Fin N × WVO I) C) : Prop :=
  ∃ co : ι → WVO I → C, (∀ ℓ ∈ P.vars, uv ℓ = ∑ w : WVO I, co ℓ w • (X w.1).u w.2.1 w.2.2) ∧
    Q = MvPolynomial.aeval
      (fun ℓ => ∑ w : WVO I, MvPolynomial.C (co ℓ w) * MvPolynomial.X (cp ℓ, w)) P

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)

def PairsSep : Prop :=
  ∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' →
    ∃ a : O, V.v ((p x.1).em x.2.1 x.2.2 a - (p x'.1).em x'.2.1 x'.2.2 a) = 0

def toAll {N : ℕ} (o : Orb) (Q : MvPolynomial (Fin N × WV (I o)) C) : MvPolynomial (Fin N × WVO I) C :=
  MvPolynomial.rename (fun x : Fin N × WV (I o) => (x.1, (⟨o, x.2⟩ : WVO I))) Q

def ValEqPSt : Prop :=
  PairsSep Y p → ∀ P ∈ Ls.FF n, ∀ Po : ∀ o, MvPolynomial (Fin n × WV (I o)) C,
    IsImgO (fun o => Y.raw (p o)) (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o)) →
    ∀ kind : Orb → Fin n → Option (Fin 2 × ZMod d × ZMod d),
    (∀ o, RowsOK ((Y.raw (p o)).rowData (H o)).G ((Y.raw (p o)).rowData (H o)).Alt (Po o) (kind o)) →
    ∀ (S : ∀ o g, Sys (((Y.raw (p o)).rowData (H o)).G g)) (t : ∀ o g, I o g → MvPowerSeries (I o g) C),
    (∀ o g, (S o g).IsT (t o g)) →
    ∀ gr : ∀ o, Fin n → MvPowerSeries (WV (I o)) C, (∀ o ρ, gr o ρ ∈ IntGerm V (t o)) →
      ∃ f : PS C n dd, IntS V f ∧
        Y.nab Ls n f P = ∏ o, ValOf ((Y.raw (p o)).rowData (H o)).hL (Po o) (kind o) (gr o)

end Orb

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey RowTiePProj GmExArith

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {n d : ℕ} (K : KeyData C V O n d)

theorem em_iter (x : O) (a : ZMod d) (k : ℕ) : V.MM (K.em (a + k) x - K.em a x ^ V.l ^ k) := by
  induction k with
  | zero => simp [mm_zero]
  | succ k ih =>
    have h1 := K.em_frob (a + k) x
    have h2 := mm_pow_sub (K.em_int _ x) ((K.em_int a x).pow _) ih V.l
    have e : K.em (a + ((k + 1 : ℕ) : ZMod d)) x - K.em a x ^ V.l ^ (k + 1) =
        (K.em (a + k + 1) x - K.em (a + k) x ^ V.l) + (K.em (a + k) x ^ V.l - (K.em a x ^ V.l ^ k) ^ V.l) := by
      rw [← pow_mul, ← pow_succ, Nat.cast_succ, ← add_assoc]; ring
    rw [e]
    exact mm_add h1 h2

theorem em_cong (x : O) (a : ZMod d) : V.MM (K.em a (x ^ V.l ^ d - x)) := by
  have h := em_iter K x a d
  rw [ZMod.natCast_self, add_zero] at h
  rw [map_sub, map_pow]
  have := mm_neg h
  rwa [neg_sub] at this

theorem star_S (x : O) : (V.l : C)⁻¹ • ((K.P * K.ρ x) ^ V.l ^ d - K.P * K.ρ x) ∈ Acl K := by
  obtain ⟨y, hy⟩ := K.ε_ann (x ^ V.l ^ d - x) fun a => em_cong K x a
  have hl0 : (V.l : C) ≠ 0 := V.l_ne_zero
  have hq : V.l ^ d = (V.l ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero _ V.l_prime.ne_zero))).symm
  have eM : (K.P * K.ρ x) ^ V.l ^ d - K.P * K.ρ x = K.P * (K.P * K.ρ (x ^ V.l ^ d - x)) := by
    rw [← Matrix.mul_assoc, P_idem, map_sub, Matrix.mul_sub, hq, S_pow, ← hq]
  rw [eM]
  refine ⟨fun k => K.ε ^ (V.l ^ k - 1) * y, ?_⟩
  have key : ∀ k : ℕ, K.P * K.ρ (K.ε ^ (V.l ^ k - 1) * y) =
      (V.l : C)⁻¹ • (K.ρ (K.ε ^ V.l ^ k) * (K.P * K.ρ (x ^ V.l ^ d - x))) := by
    intro k
    have hk : V.l ^ k ≠ 0 := pow_ne_zero _ V.l_prime.ne_zero
    have e1 : K.ε ^ V.l ^ k * (x ^ V.l ^ d - x) = (V.l : O) * (K.ε ^ (V.l ^ k - 1) * y) := by
      rw [← pow_sub_one_mul hk, mul_assoc, hy]; ring
    rw [← Matrix.mul_assoc, ← P_comm, Matrix.mul_assoc, ← map_mul, e1, ρ_natmul, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ hl0, one_smul]
  have hseq : (fun k => K.P * K.ρ (K.ε ^ (V.l ^ k - 1) * y)) =
      fun k => (V.l : C)⁻¹ • (K.ρ (K.ε ^ V.l ^ k) * (K.P * K.ρ (x ^ V.l ^ d - x))) := funext key
  rw [hseq]
  exact MT.smul _ ((hPT K).mul (MT.const _))

theorem star_mem {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) : (V.l : C)⁻¹ • (B ^ V.l ^ d - B) ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  exact closed_mem K (fun k => star_S K (s k)) (MT.smul _ ((hs.pow _).sub hs))

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
end
end
