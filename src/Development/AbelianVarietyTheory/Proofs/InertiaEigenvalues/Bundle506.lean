module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle496
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle471
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle498
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PSer

theorem iterate_phiB_eB_symm (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (j : ℕ) (a : Formalism.Per.Acris l) :
    P.φB^[j] (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)) =
      T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)
        ((GlobalTheory.MemLoc.phiA l)^[j] a)) := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have h1 : P.φB (T.eB.symm (algebraMap _ (Formalism.Per.Bcris l) a)) =
        T.eB.symm (algebraMap _ (Formalism.Per.Bcris l) (GlobalTheory.MemLoc.phiA l a)) := by
      apply T.eB.injective
      rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact GlobalTheory.CrisMaps.φB_phiA l a
    rw [h1, ih]

theorem iterate_phiB_algebraMap_mul (l : ℕ) [Fact l.Prime] (P : LocPrime l) (c : ℚ_[l]) (j : ℕ)
    (x : P.R.B) : P.φB^[j] (algebraMap ℚ_[l] P.R.B c * x) = algebraMap ℚ_[l] P.R.B c * P.φB^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, AlgHom.commutes]

theorem series_residues : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧
      (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧
      (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧
      ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) →
        ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧
          ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y := by
  intro l _ P AI T
  obtain ⟨S, θ, Θ, hS, hθ1, hθc, hΘn, hΘt, hΘ⟩ := GlobalTheory.T.exists_theta_deRhamFiltration_acris l P AI T
  refine ⟨S, θ, hS, hθ1, hθc, ?_⟩
  intro h r y hh hr hy
  have hp : l.Prime := Fact.out
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hy 0)
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hlpos hr
  have hNle : N ≤ l ^ (h * N) :=
    (Nat.lt_pow_self hp.one_lt).le.trans (Nat.pow_le_pow_right hp.pos (Nat.le_mul_of_pos_left N (by omega)))
  have key : ∀ k, ‖sh (y k ^ l ^ (h * N))‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro k
    rw [(GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l).2.2.2.1, norm_pow]
    calc ‖sh (y k)‖ ^ (l ^ (h * N)) ≤ r ^ (l ^ (h * N)) := pow_le_pow_left₀ (norm_nonneg _) (hy k) _
      _ ≤ r ^ N := pow_le_pow_of_le_one hr0 hr.le hNle
      _ ≤ ‖(l : ℂ_[l])‖ := hN.le
  obtain ⟨w, hwφ, hwΘ⟩ := GlobalTheory.T.exists_acris_phi_pow_eigenvector_double_series l h (fun k => y k ^ l ^ (h * N)) hh key
  set c : ℚ_[l] := ((l : ℚ_[l]) ^ N)⁻¹ with hcdef
  set b' : P.R.B := T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) w) with hb'
  refine ⟨algebraMap ℚ_[l] P.R.B c * b', ?_, ?_, ?_⟩
  · refine ⟨N, w, ?_⟩
    have hc : (l : P.R.B) ^ N * algebraMap ℚ_[l] P.R.B c = 1 := by
      rw [← map_natCast (algebraMap ℚ_[l] P.R.B), ← map_pow, ← map_mul, hcdef,
        mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one]
    rw [← mul_assoc, hc, one_mul, hb', RingEquiv.apply_symm_apply]
  · rw [iterate_phiB_algebraMap_mul, hb', iterate_phiB_eB_symm, hwφ, map_mul, map_natCast, map_mul,
      map_natCast]
    ring
  · intro j
    obtain ⟨hm1, e1⟩ := hθc c
    obtain ⟨hm2, e2⟩ := hΘ ((GlobalTheory.MemLoc.phiA l)^[j] w)
    have heq : ev P j (algebraMap ℚ_[l] P.R.B c * b') = algebraMap ℚ_[l] P.R.BdR c *
        P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)
          ((GlobalTheory.MemLoc.phiA l)^[j] w))) := by
      rw [ev, iterate_phiB_algebraMap_mul, hb', iterate_phiB_eB_symm, map_mul, AlgHom.commutes]
    refine ⟨heq ▸ S.mul_mem hm1 hm2, ?_⟩
    have hsub : (⟨ev P j (algebraMap ℚ_[l] P.R.B c * b'), heq ▸ S.mul_mem hm1 hm2⟩ : ↥S) =
        ⟨algebraMap ℚ_[l] P.R.BdR c, hm1⟩ * ⟨_, hm2⟩ := Subtype.ext heq
    rw [hsub, map_mul, e1, e2, hwΘ Θ hΘn hΘt j,
      (GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h j r y (by omega) hr hy).2.2.2 N, hcdef, map_inv₀, map_pow, map_natCast,
      inv_mul_cancel_left₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero))]

end GlobalTheory.PSer

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem fil_add_nat_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (a : ℤ) (k : ℕ) {x : P.R.BdR}
    (hx : x ∈ (P.PD (botExt l)).Fil (a + k)) : x ∈ (P.PD (botExt l)).Fil a := by
  induction k generalizing a with
  | zero => simpa using hx
  | succ k ih =>
    apply ih
    have h := (P.PD (botExt l)).Fil_anti (a + k)
    apply h
    have : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rwa [← this]

theorem no_fil_zero_neg_slope : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (h d : ℕ), 0 < h → 0 < d → ∀ c : P.R.B, (l : P.R.B) ^ d * P.φB^[h] c = c →
    (∀ j < h, ev P j c ∈ Fil P 0) → c = 0 := by
  intro l _ P AI T h d hh hd c hc hfil
  have hF : IsField P.R.BdR := GlobalTheory.RegularRing.isField_of_tied T
  have hι : Function.Injective P.ιB := fun a b hab => (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι, hab])
  set PD := P.PD (botExt l) with hPD
  have hdom : ∀ a b : P.R.B, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    have h0 : P.ιB a * P.ιB b = 0 := by rw [← map_mul, hab, map_zero]
    by_cases ha : P.ιB a = 0
    · exact Or.inl (hι (by rw [ha, map_zero]))
    · right
      obtain ⟨y, hy⟩ := hF.mul_inv_cancel ha
      apply hι
      rw [map_zero]
      calc P.ιB b = (y * P.ιB a) * P.ιB b := by rw [mul_comm y, hy, one_mul]
        _ = 0 := by rw [mul_assoc, h0, mul_zero]
  haveI : NoZeroDivisors P.R.B := ⟨fun {a b} hab => hdom a b hab⟩
  haveI : Nontrivial P.R.B := nontrivial_B P
  by_contra hc0
  set N : P.R.B := ∏ j ∈ Finset.range h, P.φB^[j] c with hN
  have hφN : c * P.φB N = N * P.φB^[h] c := by
    have e1 : P.φB N = ∏ j ∈ Finset.range h, P.φB^[j + 1] c := by
      rw [hN, map_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Function.iterate_succ_apply']
    rw [e1, hN]
    have e2 := Finset.prod_range_succ' (fun j => P.φB^[j] c) h
    have e3 := Finset.prod_range_succ (fun j => P.φB^[j] c) h
    simp only [Function.iterate_zero, id] at e2
    rw [mul_comm c, ← e2, e3]
  have hlN : (l : P.R.B) ^ d * P.φB N = N := by
    have : c * ((l : P.R.B) ^ d * P.φB N - N) = 0 := by
      calc c * ((l : P.R.B) ^ d * P.φB N - N) = (l : P.R.B) ^ d * (c * P.φB N) - N * c := by ring
        _ = N * ((l : P.R.B) ^ d * P.φB^[h] c) - N * c := by rw [hφN]; ring
        _ = 0 := by rw [hc, sub_self]
    rcases hdom _ _ this with h1 | h1
    · exact absurd h1 hc0
    · exact sub_eq_zero.mp h1
  set x : P.R.B := N * P.tB ^ d with hx
  have hφx : PD.φ x = x := by
    rw [P.PD_φ, hx, map_mul, map_pow, localPrime_frobenius_periodT, Algebra.smul_def, map_natCast, mul_pow]
    linear_combination (P.tB ^ d) * hlN
  have hmul : ∀ (a b : ℤ) (u v : P.R.BdR), u ∈ PD.Fil a → v ∈ PD.Fil b → u * v ∈ PD.Fil (a + b) :=
    fun a b u v hu hv => PD.Fil_mul a b u v hu hv
  have hιN : P.ιB N ∈ PD.Fil 0 := by
    rw [hN, map_prod]
    refine Finset.prod_induction _ (fun u => u ∈ PD.Fil 0) (fun u v hu hv => by simpa using hmul 0 0 u v hu hv)
      (by simpa using PD.one_mem) fun j hj => ?_
    exact hfil j (Finset.mem_range.mp hj)
  have hιt : P.ιB P.tB ∈ PD.Fil 1 := by
    have := PD.mem_filtration_one
    rwa [P.PD_ι, P.period_datum_t_eq] at this
  have hιtd : ∀ k : ℕ, P.ιB (P.tB ^ k) ∈ PD.Fil k := by
    intro k
    induction k with
    | zero => simpa using PD.one_mem
    | succ k ih =>
      rw [pow_succ, map_mul]
      have := hmul k 1 _ _ ih hιt
      simpa using this
  have hιx1 : P.ιB x ∈ PD.Fil 1 := by
    have h1 : P.ιB x ∈ PD.Fil (0 + d) := by rw [hx, map_mul]; exact hmul 0 d _ _ hιN (hιtd d)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d = k + 1 := ⟨d - 1, by omega⟩
    apply fil_add_nat_le P 1 k
    have : (1 : ℤ) + (k : ℤ) = 0 + (d : ℤ) := by rw [hk]; push_cast; ring
    rwa [this]
  have hιx0 : P.ιB x ∈ PD.Fil 0 := fil_add_nat_le P 0 1 (by simpa using hιx1)
  obtain ⟨q, hq⟩ := PD.fund x hφx (by rw [P.PD_ι]; exact hιx0)
  by_cases hq0 : q = 0
  · have hx0 : x = 0 := by rw [← hq, hq0, map_zero]
    have hN0 : N = 0 := by
      rcases hdom _ _ hx0 with h1 | h1
      · exact h1
      · exact absurd (pow_eq_zero_iff (by omega) |>.mp h1) (isUnit_tB P).ne_zero
    rw [hN, Finset.prod_eq_zero_iff] at hN0
    obtain ⟨j, -, hj⟩ := hN0
    apply hc0
    apply (phiB_injective P).iterate j
    rw [hj, iterate_map_zero]
  · have hqx : P.ιB x = algebraMap ℚ_[l] P.R.BdR q := by rw [← hq, AlgHom.commutes]
    have hinv : algebraMap ℚ_[l] P.R.BdR q⁻¹ ∈ PD.Fil 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_of_tower_mem _ _ PD.one_mem
    have hone : algebraMap ℚ_[l] P.R.BdR q⁻¹ * P.ιB x = 1 := by
      rw [hqx, ← map_mul, inv_mul_cancel₀ hq0, map_one]
    have h2 : P.ιB P.tB ∈ PD.Fil 2 := by
      have := hmul 1 (0 + 1) _ _ hιt (hmul 0 1 _ _ hinv hιx1)
      rw [hone, mul_one] at this
      simpa using this
    have := PD.not_mem_filtration_two
    rw [P.PD_ι, P.period_datum_t_eq] at this
    exact this h2

end GlobalTheory.PMon

end
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.rationalFormLength_eq_definiteFamily : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → ZRat D (tup t) ((i : ℕ) + 1) ∧ ∀ w, etaRat D (tup t) ((i : ℕ) + 1) w = A.fam.etaJ P ψ Zs i t (D.plEq w) := by
  first | exact @GlobalTheory.EtaJoin.Side.zRat_and_etaRat_eq | exact GlobalTheory.EtaJoin.Side.zRat_and_etaRat_eq | (intros; apply GlobalTheory.EtaJoin.Side.zRat_and_etaRat_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowNT

theorem logb_le_of_le_four_exp {l x large₂ : ℝ} (hl : 11 ≤ l) (hLg : 0 ≤ large₂) (hx0 : 0 ≤ x)
    (hx : x ≤ 4 * Real.exp large₂) : Real.logb l x ≤ 3 + large₂ := by
  rcases hx0.eq_or_lt with h | hpos
  · subst h; simp; linarith
  have hlogl : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h4 : Real.log x ≤ Real.log 4 + large₂ := by
    have := Real.log_le_log hpos hx
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  have h43 : Real.log 4 ≤ 3 := by have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  unfold Real.logb
  rcases le_or_gt (Real.log x) 0 with hn | hp
  · have : Real.log x / Real.log l ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn (by linarith)
    linarith
  · have : Real.log x / Real.log l ≤ Real.log x := div_le_self hp.le hlogl
    linarith

theorem lift_shape_le {l H hB e : ℝ} (hl : 11 ≤ l) (hB1 : 1 ≤ hB) (hH0 : 0 ≤ H) (hH : H ≤ 2 * hB)
    (he : e ≤ 23 * (1 + H / l + (1 + Real.logb l (H + 1)))) :
    e ≤ 69 * (1 + hB / l + Real.logb l hB) := by
  have hl1 : 1 < l := by linarith
  have hl0 : 0 < l := by linarith
  have h1 : H / l ≤ 2 * hB / l := div_le_div_of_nonneg_right hH hl0.le
  have h2 : Real.logb l (H + 1) ≤ Real.logb l (3 * hB) :=
    Real.logb_le_logb_of_le hl1 (by linarith) (by linarith)
  have h3 : Real.logb l (3 * hB) = Real.logb l 3 + Real.logb l hB :=
    Real.logb_mul (by norm_num) (by linarith)
  have h4 : Real.logb l 3 ≤ 1 := by
    have := Real.logb_le_logb_of_le hl1 (show (0:ℝ) < 3 by norm_num) (show (3:ℝ) ≤ l by linarith)
    rwa [Real.logb_self_eq_one hl1] at this
  have h5 : 0 ≤ Real.logb l hB := Real.logb_nonneg hl1 hB1
  have h6 : 0 ≤ hB / l := div_nonneg (by linarith) hl0.le
  have h7 : 2 * hB / l = 2 * (hB / l) := by ring
  linarith

theorem bound_real {l n r m h w η S lg band e' hB wP eta₃ Sc large₂ ind cE : ℝ}
    (hl : 11 ≤ l) (hn : 0 ≤ n) (hr : 0 ≤ r) (hm : 0 ≤ m)
    (hh : h ≤ hB) (hw : w ≤ wP) (hη : η ≤ eta₃) (hS : S ≤ Sc) (h0w : 0 ≤ w) (h0η : 0 ≤ η)
    (h0S : 0 ≤ S) (h0h : 0 ≤ h) (hlg : lg ≤ 3 + large₂) (hLg : 1 ≤ large₂) (hband : band ≤ ind)
    (hind0 : 0 ≤ ind) (he : e' ≤ 69 * cE) (hcE : 0 ≤ cE) :
    320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) + 320 * n * m * e' ≤
      368 * ((n + 1) * r * (hB / l ^ 2)) +
        2082 * ((n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)) + 22365 * (n * m * cE) := by
  have hl0 : 0 < l := by linarith
  have hA : 0 ≤ (n + 1) * r := mul_nonneg (by linarith) hr
  have e1 : h / l ^ 2 ≤ hB / l ^ 2 := div_le_div_of_nonneg_right hh (by positivity)
  have e2 : (w + η) / l ≤ (wP + eta₃) / l := div_le_div_of_nonneg_right (by linarith) hl0.le
  have e3 : η * band ≤ eta₃ * ind := by
    have hb0 : 0 ≤ band ∨ band < 0 := le_or_gt 0 band
    rcases hb0 with hb0 | hb0
    · exact mul_le_mul hη hband hb0 (by linarith)
    · have : η * band ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0η hb0.le
      have : 0 ≤ eta₃ * ind := mul_nonneg (by linarith) hind0
      linarith
  have e4 : 0 ≤ (wP + eta₃) / l := div_nonneg (by linarith) hl0.le
  have e5 : 0 ≤ eta₃ * ind := mul_nonneg (by linarith) hind0
  have e6 : 0 ≤ hB / l ^ 2 := div_nonneg (by linarith) (by positivity)
  have hbr : h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band ≤
      hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind) := by
    nlinarith
  have k1 : 320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) ≤
      320 * ((n + 1) * r) * (hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)) := by
    rw [mul_assoc 320 (n + 1) r]
    exact mul_le_mul_of_nonneg_left hbr (by positivity)
  have k2 : 320 * n * m * e' ≤ 320 * n * m * (69 * cE) :=
    mul_le_mul_of_nonneg_left he (by positivity)
  have hf : 0 ≤ (n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind) :=
    mul_nonneg hA (by linarith)
  have hH : 0 ≤ (n + 1) * r * (hB / l ^ 2) := mul_nonneg hA e6
  have hM : 0 ≤ n * m * cE := by positivity
  nlinarith

end GlobalTheory.NLink.RowNT

namespace GlobalTheory.NLink.RowNT

attribute [local instance] Formalism.MainNotions.N.nLet_neZero

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)), ArcLiftingSetup.aux₃ D HW F 320 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordsNT Wd → RowL i r ρ π w hw Cx (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  intro D L P HW F C₂ i r ρ π w hw Cx hG Wd h17 h54 hpar h11 hπ hb hbox hN
  intro T₁ T₂ Fm h2 h1 hF
  classical
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  have hcA := caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hG hb.unram (by omega)
  have hT := h17 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG hb.unram
  have hS := GlobalTheory.Survey.InertPlacesGoodSet.setting_of_wordsNT (by omega) hb hN inferInstance T₁ T₂ Fm h2 h1 hF
  have hX := (hT (by rw [hp]; exact h11) T₁ T₂ Fm Wd.b Wd.w Wd.S Wd.η Wd.m Wd.up Wd.sz Wd.Mi Wd.hi hS
    hN.w20 hN.η20 hN.twenty_words_le_b hN.some_nt).1 hN.alt
  rw [hp] at hX
  have hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
    obtain ⟨e, -⟩ := h2
    rw [e.finrank_eq]; simp
  have hnl : Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) = TwistedPlaces.nLam D w := by
    have e : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.2 hb.unram
    rw [e]
    exact hb.deg
  have hO := h54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁ Wd.Mi Wd.hi
    (hb.t1 T₁ h1).1 (hb.t1 T₁ h1).2.2
  have hl : (11 : ℝ) ≤ (D.nd.l i : ℝ) := by exact_mod_cast h11
  have hb1 : (1 : ℝ) ≤ L.sc.b := TwistedPlaces.one_le_b L
  have hSc := L.Sc_pos
  have hEt := L.etaSz_pos
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hB1 : (1 : ℝ) ≤ TwistedPlaces.hB L := by unfold TwistedPlaces.hB; linarith
  have hB2 : TwistedPlaces.hB L ≤ 2 * L.sc.b := by unfold TwistedPlaces.hB; unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hpar; linarith
  have hHm : (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ 2 * TwistedPlaces.hB L := by
    have hfl : LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi ≤ ⌊2 * TwistedPlaces.hB L⌋₊ := by
      unfold LiftingTheory.Hmax
      apply Finset.sup_le
      intro k _
      apply Nat.le_floor
      exact hbox.box_le _
    calc (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ (⌊2 * TwistedPlaces.hB L⌋₊ : ℝ) := by exact_mod_cast hfl
      _ ≤ 2 * TwistedPlaces.hB L := Nat.floor_le (by linarith)
  have he : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤
      69 * coreE L (D.nd.l i) := by
    have hO' : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤
        23 * (1 + (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) / ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p +
          (1 + Real.logb ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p
            ((LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) + 1))) := hO.1 hcA
    rw [hp] at hO'
    unfold coreE
    exact GlobalTheory.NLink.RowNT.lift_shape_le hl hB1 (Nat.cast_nonneg _) hHm hO'
  have hh : (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) ≤ TwistedPlaces.hB L := by
    have hwb : (Wd.w : ℝ) ≤ Wd.b := by have := hN.w20; exact_mod_cast (by omega : Wd.w ≤ Wd.b)
    have hle := hb.h_le
    unfold TruncatedSeriesCountingBounds.hB
    split_ifs
    · push_cast; linarith
    · push_cast; have : (0:ℝ) ≤ Wd.η := Nat.cast_nonneg _; linarith
  have hlg : Real.logb (D.nd.l i : ℝ) (2 * (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤ 3 + TwistedPlaces.large₂ L := by
    apply GlobalTheory.NLink.RowNT.logb_le_of_le_four_exp hl (by linarith [TwistedPlaces.L_ge_one L]) (by positivity)
    rw [← TwistedPlaces.b_eq]; linarith
  have hband : ((if TruncatedSeriesCountingBounds.Band (D.nd.l i) Wd.b Wd.S Wd.η Wd.sz
        (Real.logb (↑(D.nd.l i)) (2 * ↑(TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz))) 320 then 1 else 0) : ℝ) ≤
      (if bandOf L HW 320 i r ρ w then 1 else 0) := by
    split_ifs with hx hy
    · exact le_rfl
    · exact absurd ⟨h11, π, hπ, hw, Cx, hG, Wd, hb, hbox, hN, hx⟩ hy
    · norm_num
    · exact le_rfl
  have key := GlobalTheory.NLink.RowNT.bound_real (l := (D.nd.l i : ℝ)) (n := (TwistedPlaces.nLam D w : ℝ))
    (r := (D.R.r : ℝ)) (m := (D.R.m : ℝ)) hl (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hh hb.w_le hb.η_le hb.S_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hlg (TwistedPlaces.L_ge_one L) hband (by split_ifs <;> norm_num) he
    (by unfold coreE; have := Real.logb_nonneg (by linarith : (1:ℝ) < D.nd.l i) hB1
        have : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) := div_nonneg (by linarith) (by linarith)
        linarith)
  obtain ⟨mm, k, e1, e2, e3⟩ := hX
  refine ⟨mm, k, e1, e2, e3.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))⟩
  have hnlR : ((Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ) := by
    exact_mod_cast hnl
  have hrkR : ((Module.finrank ↥Cx.LL.1 T₂.V : ℕ) : ℝ) = (D.R.r : ℝ) := by exact_mod_cast hrk
  have hmR : ((Wd.m : ℕ) : ℝ) = (D.R.m : ℝ) := by exact_mod_cast hb.m_eq
  rw [hnlR, hrkR, hmR]
  simp only [bdCD, coreH, coreF, coreM, flat, rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃]
  refine le_trans key (le_of_eq ?_)
  norm_num

end GlobalTheory.NLink.RowNT
end
end

section

namespace GlobalTheory.WeightSumSplit

theorem sum_above {N : ℕ} (i : Fin N) (c : ℤ) :
    (∑ j : Fin N, if i < j then c else 0) = ((N : ℤ) - 1 - (i : ℕ)) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi,
    Fin.card_Ioi, nsmul_eq_mul]
  have hi := i.isLt
  congr 1
  omega

theorem sum_below {N : ℕ} (j : Fin N) (c : ℤ) :
    (∑ i : Fin N, if i < j then c else 0) = ((j : ℕ) : ℤ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
    Fin.card_Iio, nsmul_eq_mul]

theorem sum_pairs_eq (N : ℕ) (a : Fin N → ℤ) :
    (∑ i : Fin N, ∑ j : Fin N, if i < j then a i - a j else 0)
      = ∑ i : Fin N, ((N : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * a i := by
  have h1 : ∀ i j : Fin N, (if i < j then a i - a j else 0) =
      (if i < j then a i else 0) - (if i < j then a j else 0) := by
    intro i j
    split_ifs <;> simp
  simp_rw [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin N => if i < j then a j else 0)]
  simp_rw [sum_above, sum_below, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem wtS_eq : ∀ (N : ℕ) (a : Fin N → ℤ),
    GlobalTheory.CellDec.wtS N a = ∑ i : Fin N, ((↑N : ℤ) - (1 : ℤ) - (2 : ℤ) * (↑(↑i : ℕ) : ℤ)) * a i := by
  intro N a
  unfold GlobalTheory.CellDec.wtS
  exact sum_pairs_eq N a

end GlobalTheory.WeightSumSplit
end
