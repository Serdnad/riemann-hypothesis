module

public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34

section Ser

variable {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V]

theorem finsum_mem_sub {ι : Type} (S : Submodule LL V) (t : ι → V) (ht : ∀ j, t j ∈ S) :
    ∑ᶠ j, t j ∈ S := by
  classical
  by_cases h : (Function.support t).Finite
  · rw [finsum_eq_sum _ h]
    exact Submodule.sum_mem _ fun j _ => ht j
  · rw [finsum_of_infinite_support h]
    exact Submodule.zero_mem _

theorem serMul_eq_sum (g : PowerSeries LL) (f : ℤ → V) (m : ℤ) (hf : ∀ k < m, f k = 0)
    (i : ℤ) (N : ℕ) (hN : i - m < N) :
    serMul g f i = ∑ j ∈ Finset.range N, PowerSeries.coeff j g • f (i - j) := by
  unfold serMul
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hj ⊢
  by_contra hjN
  push_neg at hjN
  apply hj
  rw [hf (i - j) (by omega), smul_zero]

theorem serMul_one (f : ℤ → V) (i : ℤ) : serMul (1 : PowerSeries LL) f i = f i := by
  unfold serMul
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem serMul_mem (S : ℤ → Submodule LL V) (hS : Monotone S) (g : PowerSeries LL) (m : ℕ)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) (f : ℤ → V) (hf : ∀ i, f i ∈ S i) (i : ℤ) :
    serMul g f i ∈ S (i - m) := by
  unfold serMul
  apply finsum_mem_sub
  intro j
  by_cases hj : j < m
  · rw [hg j hj, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (hS (by omega) (hf (i - j)))

theorem serMul_inv (S : ℤ → Submodule LL V) (hS : Monotone S) (g : PowerSeries LL) (m : ℕ)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) (hgm : PowerSeries.coeff m g ≠ 0) (f : ℤ → V)
    (m₀ : ℤ) (hf0 : ∀ k < m₀, f k = 0) (hF : ∀ i, serMul g f (i + m) ∈ S i) (i : ℤ) :
    f i ∈ S i := by
  have key : ∀ i, (∀ i' < i, f i' ∈ S i') → f i ∈ S i := by
    intro i ih
    by_cases hi : i < m₀
    · rw [hf0 i hi]; exact Submodule.zero_mem _
    push_neg at hi
    have hN : i + m - m₀ < (((i + m - m₀).toNat + m + 1 : ℕ) : ℤ) := by omega
    have hsum := serMul_eq_sum g f m₀ hf0 (i + m) ((i + m - m₀).toNat + m + 1) hN
    have hmN : m ∈ Finset.range ((i + m - m₀).toNat + m + 1) := Finset.mem_range.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ hmN] at hsum
    have hrest : ∑ j ∈ (Finset.range ((i + m - m₀).toNat + m + 1)).erase m,
        PowerSeries.coeff j g • f (i + m - j) ∈ S i := by
      refine Submodule.sum_mem _ fun j hj => ?_
      have hjm : j ≠ m := Finset.ne_of_mem_erase hj
      rcases Nat.lt_or_gt_of_ne hjm with hlt | hgt
      · rw [hg j hlt, zero_smul]; exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (hS (by omega) (ih _ (by omega)))
    have hmain : PowerSeries.coeff m g • f i ∈ S i := by
      have h1 := hF i
      rw [hsum] at h1
      have h2 := Submodule.sub_mem _ h1 hrest
      simp only [add_sub_cancel_right] at h2
      simpa using h2
    exact (Submodule.smul_mem_iff _ hgm).mp hmain
  have hall : ∀ n : ℕ, ∀ i, i < m₀ + n → f i ∈ S i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [hf0 i (by simpa using hi)]
      exact Submodule.zero_mem _
    | succ n ihn =>
      intro i hi
      apply key
      intro i' hi'
      exact ihn i' (by push_cast at hi; omega)
  exact hall ((i - m₀).toNat + 1) i (by omega)

end Ser

section Lev

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem lev_letE (c : ZMod n) (ζ : LL) : W.lev c ζ (letE c : LetA O n) = 1 := by
  have h1 : W.lev c ζ (1 - letE c : LetA O n) = 0 :=
    W.lev_letter c ζ _ (by simp [letE])
  rw [map_sub, map_one, sub_eq_zero] at h1
  exact h1.symm

theorem levN_eq_serMul (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T))
    (k : ℤ) : W.levN T c ζ (a • x) k = serMul (W.lev c ζ a) (W.levN T c ζ x) k :=
  W.levN_smul T c ζ a x k

theorem levN_letE (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ) :
    W.levN T c ζ ((letE c : LetA O n) • x) k = W.levN T c ζ x k := by
  rw [levN_eq_serMul, lev_letE, serMul_one]

theorem Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  show (W.φA ^ (W.s - 1)) W.q = W.q
  rw [hs, Nat.sub_self, pow_zero]
  rfl

theorem levQ_pt (hs : W.s = 1) (i : ZMod n) (ζ : LL) (hζ : ζ ^ PD.p = 1) (hζ1 : ζ ≠ 1) :
    PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev i ζ W.Q) ≠ 0 := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hprim : IsPrimitiveRoot ζ (PD.p ^ 1) := by
    have h := IsPrimitiveRoot.orderOf ζ
    rw [orderOf_eq_prime hζ hζ1] at h
    rwa [pow_one]
  obtain ⟨E, hE0, hED, hE⟩ := W.lev_π i ζ ⟨1, hprim⟩
  have hprod : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext j
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ,
      LocWach.q]
    exact W.q₀_def
  have hl := congrArg (W.lev i ζ) hprod
  rw [map_mul, map_sub, map_pow, map_add (f := _), map_one, hE] at hl
  rw [Q_eq_q W hs]
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have := W.v_l
    rw [h, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  have ha0 : PowerSeries.constantCoeff (W.lev i ζ letπ) = ζ - 1 := by
    have h := congrArg PowerSeries.constantCoeff hE
    rw [map_add (f := _), map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at h
    linear_combination h
  have hz : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hc0 : PowerSeries.constantCoeff (W.lev i ζ W.q) = 0 := by
    have h := congrArg PowerSeries.constantCoeff hl
    rw [map_mul, map_sub, map_one, map_pow, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one,
      hζ, sub_self, ha0] at h
    exact (mul_eq_zero.1 h).resolve_left hz
  refine ⟨hc0, ?_⟩
  obtain ⟨b', hb'⟩ := PowerSeries.X_dvd_iff.2 hc0
  have hEp : PowerSeries.coeff 1 (E ^ PD.p) = (PD.p : LL) := by
    have hd : PowerSeries.derivative (R := LL) (E ^ PD.p) = (PD.p : LL) • E ^ PD.p := by
      rw [Derivation.leibniz_pow, hED, smul_eq_mul, ← pow_succ, Nat.sub_add_cancel PD.hp.one_lt.le,
        Nat.cast_smul_eq_nsmul]
    have h := congrArg (PowerSeries.coeff 0) hd
    have hc : PowerSeries.coeff 0 (E ^ PD.p) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hE0, one_pow]
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_smul, hc] at h
    simpa using h
  have h1 := congrArg (PowerSeries.coeff 1) hl
  rw [hb', mul_left_comm, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, ha0, mul_pow, ← map_pow, hζ, map_one, one_mul, map_sub, hEp, PowerSeries.coeff_one,
    if_neg one_ne_zero, sub_zero] at h1
  rw [hb', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  intro h0
  rw [h0, mul_zero] at h1
  exact hp0 h1.symm

end Lev

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLE

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

theorem exists_fin_sum {O M N' : Type*} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N']
    [Module O N'] (t : M ⊗[O] N') : ∃ (m : ℕ) (a : Fin m → M) (s : Fin m → N'), t = ∑ j, a j ⊗ₜ s j := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a s => exact ⟨1, fun _ => a, fun _ => s, by simp⟩
  | add t t' ht ht' =>
    obtain ⟨m, a, s, rfl⟩ := ht
    obtain ⟨m', a', s', rfl⟩ := ht'
    refine ⟨m + m', Fin.append a a', Fin.append s s', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem toLA_tmul (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ) (s : ↥S) :
    toLA W T π' c S (a ⊗ₜ s) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) :=
  rfl

theorem smulLA_tmul (a : LetA O n) (e : W.EE) (s : LcQ W T π' c) :
    smulLA W T π' c a (e ⊗ₜ s) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ s := rfl

theorem smulLA_smulLA (a b : LetA O n) (x : LA W T π' c) :
    smulLA W T π' c a (smulLA W T π' c b x) = smulLA W T π' c (a * b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e s => simp only [smulLA_tmul, map_mul, mul_assoc]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem smul_eq_smulLA (o : O) (x : LA W T π' c) :
    o • x = smulLA W T π' c (algebraMap O (LetA O n) o) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e s =>
    rw [smulLA_tmul, TensorProduct.smul_tmul', Algebra.smul_def,
      IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy]

theorem rep_exists {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨m, a, s, rfl⟩ := exists_fin_sum t
  have hs : ∀ j, ∃ yy : ↥(NcS W T (c - 1)), Submodule.Quotient.mk yy = ((s j : ↥(⊤ : Submodule O _)) :
      LcQ W T π' c) := fun j => Submodule.Quotient.mk_surjective _ _
  choose yy hyy using hs
  refine ⟨m, a, fun j => (yy j : W.DD T), ⟨fun j => (yy j).2, ?_⟩⟩

  rw [← ht, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [toLA_tmul, ← hyy j]
  rfl

theorem rep_append {x x' : LA W T π' c} {m m' : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    {a' : Fin m' → ↥W.AΔ} {y' : Fin m' → W.DD T} (h : IsRepL W T π' Eπ h' c x a y)
    (h₂ : IsRepL W T π' Eπ h' c x' a' y') :
    IsRepL W T π' Eπ h' c (x + x') (Fin.append a a') (Fin.append y y') := by
  obtain ⟨hy, hx⟩ := h
  obtain ⟨hy', hx'⟩ := h₂
  refine ⟨fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact hy j
    · rw [Fin.append_right]; exact hy' j
  · rw [map_add (f := _), hx, hx', Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.append_left]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.append_right]

theorem expS_append (ζ : LL) {m m' : ℕ} (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T)
    (a' : Fin m' → ↥W.AΔ) (y' : Fin m' → W.DD T) :
    expS W T c ζ (fun j => ((Fin.append a a' j : ↥W.AΔ) : LetA O n)) (Fin.append y y') =
      expS W T c ζ (fun j => (a j : LetA O n)) y + expS W T c ζ (fun j => (a' j : LetA O n)) y' := by
  funext i
  simp only [expS, Pi.add_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem rep_smul {x : LA W T π' c} {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    (h : IsRepL W T π' Eπ h' c x a y) {b : LetA O n} (hb : b ∈ W.AΔ) :
    IsRepL W T π' Eπ h' c (smulLA W T π' c b x) (fun j => ⟨b * a j, W.AΔ.mul_mem hb (a j).2⟩) y := by
  obtain ⟨hy, hx⟩ := h
  refine ⟨hy, ?_⟩

  rw [smulLA_smulLA, mul_comm, ← smulLA_smulLA, hx, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smulLA_tmul, ← map_mul]
  congr 2
  ring

end Generic

end Formalism.MainNotions.N.Ln34.MLE

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Coeff

variable {R : Type} [CommRing R]

theorem framepf_coeff_pow_lt (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) (m j : ℕ)
    (hj : j < m) : PowerSeries.coeff j (f ^ m) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem framepf_coeff_pow_self (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) (m : ℕ) :
    PowerSeries.coeff m (f ^ m) = PowerSeries.coeff 1 f ^ m := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

end Coeff

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

theorem framepf_ιV_inj : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem framepf_levB_gam (hc : IsCrys PD T.ρ) (g : W.Gam)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - 1)) (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ) :
    Ct.levB T i 1 ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Ct.levB T i 1 x k :=
  Ct.levB_Γ T hc g i 1 1 0 1 (by simpa using IsPrimitiveRoot.one) (by simpa using hv) (by simp) x hx k

theorem framepf_levB_zero (hc : IsCrys PD T.ρ) (i : ZMod n)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1))
    (hχ : ∀ r : ℤ, 1 ≤ r → (algebraMap O LL (W.χΓ W.gam : O)) ^ r ≠ 1)
    (a : LetA O n) (R : ℕ) (ha : ∀ j < R, PowerSeries.coeff j (W.lev i 1 a) = 0)
    (x w : ↥(W.N T)) (hxw : W.γD T W.gam (x : W.DD T) - x = a • (w : W.DD T))
    (hw : ∀ r : ℤ, r < 0 → W.levN T i 1 w r = 0) (r : ℤ) (h1 : 1 ≤ r) (hR : r < R) :
    Ct.levB T i 1 x r = 0 := by
  have hx : W.γD T W.gam (x : W.DD T) ∈ W.N T := W.N_Γ T W.gam x x.2
  have haw : a • (w : W.DD T) ∈ W.N T := (W.N T).smul_mem a w.2
  have hsub : (⟨_, hx⟩ : ↥(W.N T)) - x = ⟨_, haw⟩ := Subtype.ext (by simp [hxw])
  have hlev := congrArg (fun y => Ct.levB T i 1 y r) hsub
  simp only [map_sub, Pi.sub_apply] at hlev
  rw [framepf_levB_gam Ct T hc W.gam hv i x hx r] at hlev
  have hzero : Ct.levB T i 1 ⟨_, haw⟩ r = 0 := by
    refine framepf_ιV_inj (PD := PD) T ?_
    rw [map_zero, ← Ct.levN_eq]
    have : (⟨_, haw⟩ : ↥(W.N T)) = a • w := rfl
    rw [this, W.levN_smul]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    by_cases hj : j < R
    · rw [ha j hj, zero_smul]
    · simp only [hw (r - (j : ℤ)) (by omega), smul_zero]
  rw [hzero] at hlev
  have h2 : ((algebraMap O LL (W.χΓ W.gam : O)) ^ r - 1) • Ct.levB T i 1 x r = 0 := by
    rw [sub_smul, one_smul]; exact hlev
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hχ r h1))

theorem framepf_levB_phi (hc : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (x : ↥(W.N T)) (m R : ℕ) (hm : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T)
    (hQ : ∀ j < m, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) = 0)
    (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (i - 1) 1 x r = 0)
    (hmid : ∀ r : ℤ, 1 ≤ r → r < R → Ct.levB T (i - 1) 1 x r = 0) (k : ℤ) (hk : k < m + R) :
    Ct.levB T i ζ ⟨_, hm⟩ k =
      serC (W.lev i ζ (W.Q ^ m)) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (i - 1) 1 x 0)) k := by
  rw [Ct.levB_φ T hc i ζ hζ x m hm k, hζ1]
  unfold serC
  split_ifs with hk0
  · rw [finsum_eq_single _ k.toNat]
    · have : k - (k.toNat : ℤ) = 0 := by omega
      rw [this, zpow_zero, one_smul]
    · intro j hj
      by_cases hjm : j < m
      · rw [hQ j hjm, zero_smul]
      · by_cases hjk : (j : ℤ) < k
        · rw [hmid (k - (j : ℤ)) (by omega) (by omega), map_zero, smul_zero, smul_zero]
        · have : (j : ℤ) ≠ k := fun h => hj (by omega)
          rw [hneg (k - (j : ℤ)) (by omega), map_zero, smul_zero, smul_zero]
  · apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [hneg (k - (j : ℤ)) (by omega), map_zero, smul_zero, smul_zero]

theorem framepf_valAt (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : ↥(W.N T)) (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (c - 1) 1 x r = 0)
    (hex : ∃ k : ℕ, W.Q ^ k • W.φD T (x : W.DD T) ∈ W.N T) :
    valAt W T c ζ (x : W.DD T) = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (c - 1) 1 x 0)) := by
  classical
  unfold valAt
  rw [dite_eq_left hex]
  have hm := Nat.find_spec hex
  have hC := framepf_levB_phi Ct T hc c ζ hζ hζ1 x (Nat.find hex) 1 hm
    (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) hneg
    (fun r h1 h2 => by omega) (Nat.find hex : ℤ) (by omega)
  rw [Ct.levN_eq, hC]
  unfold serC
  rw [if_pos (by omega), map_smul, map_pow, Int.toNat_natCast, framepf_coeff_pow_self _ hQ0, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hQ1), one_smul]

theorem framepf_levN_phi (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : ↥(W.N T)) (m R : ℕ) (hm : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T)
    (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (c - 1) 1 x r = 0)
    (hmid : ∀ r : ℤ, 1 ≤ r → r < R → Ct.levB T (c - 1) 1 x r = 0) (k : ℤ) (hk : k < m + R) :
    W.levN T c ζ ⟨_, hm⟩ k = serC (W.lev c ζ (W.Q ^ m)) (valAt W T c ζ (x : W.DD T)) k := by
  rw [framepf_valAt Ct T hc c ζ hζ hζ1 hQ0 hQ1 x hneg ⟨m, hm⟩, Ct.levN_eq,
    framepf_levB_phi Ct T hc c ζ hζ hζ1 x m R hm
      (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) hneg hmid k hk]
  unfold serC
  split_ifs
  · rw [map_smul]
  · rw [map_zero]

end Local

end Formalism.MainNotions.N.Ln34

end
end
