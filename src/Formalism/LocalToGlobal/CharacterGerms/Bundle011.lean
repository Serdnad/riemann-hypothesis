module

import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLimitsIntegralEndomorphisms
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
public import Formalism.FrobeniusBaseCase.Statement
public import Formalism.IncomingBounds.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Formalism.LocalToGlobal.CharacterGerms.Bundle010
import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
public import Formalism.LocalToGlobal.CharacterGerms.Bundle009
public import Mathlib.Data.Matrix.Mul
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePE0

open PartialDerivEval

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem actK_self (B : FB C dd O) (a : O) : B.actK C a = B.A.act a := by
  funext i; unfold FB.actK; rw [show algebraMap C C = RingHom.id C from rfl, map_id]; rfl

theorem TendsS.ev {m n : ℕ} {a : ℕ → Fin m → Pt C n dd} {A : Fin m → Pt C n dd} {f : ℕ → PS C m dd}
    {F : PS C m dd} (ha0 : ∀ k, Z0 (a k)) (hA0 : Z0 A) (ha : ∀ j i, TendsS V (fun k => a k j i) (A j i))
    (hf : TendsS V f F) : TendsS V (fun k => ev (a k) (f k)) (ev A F) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  exact TendsS.subst (fun k p => ha0 k p.1 p.2) (fun p => hA0 p.1 p.2) (fun p => ha p.1 p.2) hf

theorem constant_zero_two_points {n : ℕ} (P Q : Pt C n dd) (hP : ∀ i, constantCoeff (P i) = 0) (hQ : ∀ i, constantCoeff (Q i) = 0) :
    Z0 (![P, Q] : Fin 2 → Pt C n dd) := by
  intro j i; fin_cases j
  · exact hP i
  · exact hQ i

theorem tends_two {n : ℕ} {P Q : ℕ → Pt C n dd} {P' Q' : Pt C n dd} (hP : ∀ i, TendsS V (fun k => P k i) (P' i))
    (hQ : ∀ i, TendsS V (fun k => Q k i) (Q' i)) :
    ∀ j i, TendsS V (fun k => (![P k, Q k] : Fin 2 → Pt C n dd) j i) ((![P', Q'] : Fin 2 → Pt C n dd) j i) := by
  intro j i; fin_cases j
  · exact hP i
  · exact hQ i

theorem const_comp1 {n : ℕ} {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) {b : Pt C n dd}
    (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin dd) : constantCoeff (comp1 φ b i) = 0 :=
  const_ev (z0_1 b hb) (hφ i)

theorem TendsS.comp1 {n : ℕ} {φ : ℕ → Pt C 1 dd} {Φ : Pt C 1 dd} {b : ℕ → Pt C n dd} {B : Pt C n dd}
    (hb0 : ∀ k i, constantCoeff (b k i) = 0) (hB0 : ∀ i, constantCoeff (B i) = 0)
    (hφ : ∀ i, TendsS V (fun k => φ k i) (Φ i)) (hb : ∀ i, TendsS V (fun k => b k i) (B i)) (i : Fin dd) :
    TendsS V (fun k => comp1 (φ k) (b k) i) (comp1 Φ B i) :=
  TendsS.ev (fun k => z0_1 _ (hb0 k)) (z0_1 _ hB0)
    (fun j i' => by rw [Fin.fin_one_eq_zero j]; exact hb i') (hφ i)

theorem TendsS.expS {n : ℕ} {g : ℕ → PS C n dd} {G : PS C n dd} (hg0 : ∀ k, constantCoeff (g k) = 0)
    (hG0 : constantCoeff G = 0) (hg : TendsS V g G) : TendsS V (fun k => FB.expS C (g k)) (FB.expS C G) := by
  unfold FB.expS PowerSeries.subst
  exact TendsS.subst (fun k _ => hg0 k) (fun _ => hG0) (fun _ => hg) (TendsS.const _)

theorem exists_lim (Y : FBChart C V O dd) {φ : ℕ → Pt C 1 dd}
    (hφ : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (coeff μ (φ (n + 1) i) - coeff μ (φ n i))) :
    ∃ e : Pt C 1 dd, ∀ i, TendsS V (fun n => φ n i) (e i) := by
  have h : ∀ i μ, ∃ x, Tends V (fun n => coeff μ (φ n i)) x := fun i μ => exists_tends Y.cpl fun N => hφ N i μ
  choose L hL using h
  exact ⟨fun i => (fun μ => L i μ : MvPowerSeries (Fin 1 × Fin dd) C), fun i μ => hL i μ⟩

theorem const_of_lim (Y : FBChart C V O dd) {a : ℕ → O} {e : Pt C 1 dd}
    (he : ∀ i, TendsS V (fun n => Y.B.A.act (a n) i) (e i)) (i : Fin dd) : constantCoeff (e i) = 0 := by
  have h := he i 0
  simp only [coeff_zero_eq_constantCoeff_apply, Y.B.A.const] at h
  exact h.unique (tends_const 0)

theorem endomorphism_limit_integral (Y : FBChart C V O dd) : EndomorphismLimitIntegral Y := by
  apply GlobalTheory.ActLimit.limit_endomorphisms <;> assumption

end RowTiePE0

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace VP

section Gen

variable {C : Type} [Field C] {σ τ ρ : Type}

theorem hs [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.HasSubst a := hasSubst_of_ordGE (fun s => by
    unfold Formalism.BaseCaseIdentities.OrdGE
    intro A hA
    have h0 : A = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]
      omega
    subst h0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ha s)

theorem og {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (s : σ) :
    Formalism.BaseCaseIdentities.OrdGE 1 (a s) := by
  unfold Formalism.BaseCaseIdentities.OrdGE
  intro A hA
  have h0 : A = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact ha s

theorem cc_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  have h : Formalism.BaseCaseIdentities.OrdGE 1 (MvPowerSeries.subst a f) :=
    ordGE_subst (og ha) (og (a := fun _ : Unit => f) (fun _ => hf) ())
  have h0 := h 0 (by simp)
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0

theorem subst_mul [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f * g) = MvPowerSeries.subst a f * MvPowerSeries.subst a g := MvPowerSeries.subst_mul (hs ha) f g

theorem subst_one [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (1 : MvPowerSeries σ C) = 1 := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_one _

theorem subst_prod [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∏ i ∈ s, F i) = ∏ i ∈ s, MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_prod _ _ _

theorem subst_sum [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∑ i ∈ s, F i) = ∑ i ∈ s, MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_sum _ _ _

theorem subst_smul [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (c : C) (f : MvPowerSeries σ C) :
    MvPowerSeries.subst a (c • f) = c • MvPowerSeries.subst a f := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_smul _ c f

theorem subst_exp [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := subst_mvExp (og ha) (og (a := fun _ : Unit => f) (fun _ => hf) ())

theorem subst_subst [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C} {b : τ → MvPowerSeries ρ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    MvPowerSeries.subst b (MvPowerSeries.subst a f) =
      MvPowerSeries.subst (fun s => MvPowerSeries.subst b (a s)) f := MvPowerSeries.subst_comp_subst_apply (hs ha) (hs hb) f

theorem subst_X [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (s : σ) :
    MvPowerSeries.subst a (MvPowerSeries.X s : MvPowerSeries σ C) = a s := MvPowerSeries.subst_X (hs ha) s

end Gen

section Exp

variable {C : Type} [Field C] [CharZero C] {n dd : ℕ}

theorem expS_eq (f : PS C n dd) (hf : MvPowerSeries.constantCoeff f = 0) : FB.expS C f = mvExp f := by
  have hpow : ∀ (k : ℕ) (m : Fin n × Fin dd →₀ ℕ), m.degree < k → MvPowerSeries.coeff m (f ^ k) = 0 := by
    intro k m hm
    have h1 := ordGE_finsupp_prod (fun _ : Unit => f) (fun _ => og (a := fun _ : Unit => f) (fun _ => hf) ())
      (Finsupp.single () k)
    simp only [Finsupp.prod_single_index, pow_zero, Finsupp.degree_single] at h1
    exact h1 m hm
  ext m
  rw [FB.expS, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf)]
  change _ = ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (m.degree + 1)) ?_]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [PowerSeries.coeff_exp]
    simp only [smul_eq_mul, map_div₀, map_one, map_natCast]
    ring
  · intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hk (by rw [hpow k m (by omega), smul_zero])

end Exp

end VP

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds.AltInv

variable {C : Type*} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem intS_invG {σ : Type*} [Fintype σ] (Φ t G : σ → MvPowerSeries σ C) (hΦ0 : ∀ x, constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (hG : ∀ x, IntS v (G x)) (heq : ∀ x, subst t (Φ x) = G x) :
    ∀ y, IntS v (t y) := by
  set L : Matrix σ σ C := Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x) with hLdef
  have hdet0 : L.det ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hL; exact WithTop.top_ne_coe hL
  have hord : ∀ s, OrdV 1 (t s) := fun s μ hμ => by
    have : μ = 0 := (Finsupp.degree_eq_zero_iff μ).1 (by omega)
    subst this; simpa using ht0 s
  have hs : HasSubst t := hasSubst_of_constantCoeff_zero ht0
  suffices key : ∀ E : ℕ, ∀ y, LowLt (v := v) E (t y) by
    intro y μ; exact key (μ.degree + 1) y μ (Nat.lt_succ_self _)
  intro E
  induction E with
  | zero => intro y μ h; exact absurd h (Nat.not_lt_zero _)
  | succ E ih =>
    intro y μ hμ
    rcases Nat.lt_succ_iff_lt_or_eq.mp hμ with hlt | heqd
    · exact ih y μ hlt

    cases E with
    | zero =>
      have : μ = 0 := (Finsupp.degree_eq_zero_iff μ).1 heqd
      subst this; simp [ht0 y, intC_zero]
    | succ E' =>

      have hlow : ∀ s, LowLt (v := v) (E' + 1) (t s) := ih
      have hbig : ∀ d : σ →₀ ℕ, 2 ≤ d.degree → IntC v (coeff μ (d.prod fun s n => t s ^ n)) := by
        intro d hd
        have hp := low_prod (v := v) hord hlow d.support d
        have : (d.prod fun s n => t s ^ n) = ∏ s ∈ d.support, t s ^ d s := rfl
        rw [this]
        have hdeg : d.degree = ∑ s ∈ d.support, d s := rfl
        exact hp.2 μ (by omega)

      have heqx : ∀ x, ∑ y', L x y' * coeff μ (t y') = coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n)) := by
        intro x
        have h1 := congrArg (coeff μ) (heq x)
        rw [coeff_subst hs] at h1
        have hfin := coeff_subst_finite hs (Φ x) μ
        set T : (σ →₀ ℕ) → C := fun d => coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n) with hT
        have hsplit : ∀ d, T d = (if d.degree = 1 then T d else 0) + (if d.degree = 1 then 0 else T d) := by
          intro d; split_ifs <;> simp
        have hfg : (Function.support fun d => if d.degree = 1 then T d else 0).Finite :=
          hfin.subset (fun d hd => by
            simp only [Function.mem_support] at hd ⊢; split_ifs at hd; exact hd; exact absurd rfl hd)
        have hfh : (Function.support fun d => if d.degree = 1 then 0 else T d).Finite :=
          hfin.subset (fun d hd => by
            simp only [Function.mem_support] at hd ⊢; split_ifs at hd; exact absurd rfl hd; exact hd)
        have h2 : ∑ᶠ d, T d = (∑ᶠ d, if d.degree = 1 then T d else 0) +
            ∑ᶠ d, (if d.degree = 1 then 0 else T d) := by
          rw [← finsum_add_distrib hfg hfh]; exact finsum_congr hsplit
        have h3 : (∑ᶠ d, if d.degree = 1 then T d else 0) = ∑ y', L x y' * coeff μ (t y') := by
          rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun y' => Finsupp.single y' 1)
            (fun d hd => by
              simp only [Function.mem_support] at hd
              split_ifs at hd with hd1
              · obtain ⟨y', rfl⟩ := deg_one_single d hd1
                simp
              · exact absurd rfl hd)]
          rw [Finset.sum_image (fun a _ b _ hab => (Finsupp.single_left_inj one_ne_zero).mp hab)]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [if_pos (by simp), hT]
          simp only [smul_eq_mul]
          rw [Finsupp.prod_single_index (by simp), pow_one]
          rfl
        rw [h2, h3] at h1
        exact eq_sub_of_add_eq h1

      have hc : ∀ x, IntC v (coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n))) := by
        intro x
        refine intC_sub ?_ (intC_finsum fun d => ?_)
        · exact hG x μ
        · split_ifs with hd1
          · exact intC_zero
          · by_cases hd0 : d = 0
            · subst hd0; rw [coeff_zero_eq_constantCoeff_apply, hΦ0, zero_smul]; exact intC_zero
            · have : 2 ≤ d.degree := by
                have : d.degree ≠ 0 := fun h0 => hd0 ((Finsupp.degree_eq_zero_iff d).1 h0)
                omega
              rw [smul_eq_mul]; exact intC_mul (hΦ x d) (hbig d this)

      set w : σ → C := fun y' => coeff μ (t y') with hw
      set c : σ → C := fun x => coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n)) with hcdef
      have hLw : L.mulVec w = c := by
        funext x; simp only [Matrix.mulVec, dotProduct]; exact heqx x
      have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet0
      have hwsol : w = L⁻¹.mulVec c := by
        rw [← hLw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hunit, Matrix.one_mulVec]
      have hinv : ∀ i j, IntC v (L⁻¹ i j) := by
        intro i j
        rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
        refine intC_mul ?_ ?_
        · unfold IntC; rw [AddValuation.map_inv, hL]; simp
        · rw [Matrix.adjugate_apply]
          refine intC_det _ fun a b => ?_
          rw [Matrix.updateRow_apply]
          split_ifs
          · rw [Pi.single_apply]; split_ifs; exact intC_one; exact intC_zero
          · exact hΦ a _
      have : w y = (L⁻¹.mulVec c) y := by rw [← hwsol]
      show IntC v (w y)
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      exact intC_sum _ fun x _ => intC_mul (hinv y x) (hc x)

end Formalism.L2.FormalSeriesBounds.AltInv
end
end

section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

def TeichSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C),
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) →
    ∀ (n d : ℕ), d ≠ 0 → ∀ (A : Set (Matrix (Fin n) (Fin n) C)),
      (∀ a ∈ A, ∀ b ∈ A, a + b ∈ A) → (∀ a ∈ A, -a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, ∀ i j, V.Ge 0 (a i j)) →
      (∀ (s : ℕ → Matrix (Fin n) (Fin n) C) (b : Matrix (Fin n) (Fin n) C), (∀ k, s k ∈ A) →
        (∀ i j, RowTiePE0.Tends V (fun k => s k i j) (b i j)) → b ∈ A) →
      (∀ a ∈ A, ((V.l : C)⁻¹) • (a ^ V.l ^ d - a) ∈ A) →
      ∀ b ∈ A, ∃ τ ∈ A, τ ^ V.l ^ d = τ ∧ ((V.l : C)⁻¹) • (b - τ) ∈ A

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
