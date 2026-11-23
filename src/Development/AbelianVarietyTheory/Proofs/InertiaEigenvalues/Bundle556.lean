module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle497
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle479
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle341
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusFrameOfPeriodMatrix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallinePeriodUnramifiedRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle544
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle533
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section
namespace GlobalTheory.GLq.UpperWeight

def cnt {g : ℕ} (L : List (Pc g)) (i : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i)).card

theorem sum_get_fst {g : ℕ} (L : List (Pc g)) : ∑ j : Fin L.length, (L.get j).1 = degL L := by
  induction L with
  | nil => simp [degL]
  | cons a L ih =>
    show ∑ j : Fin (L.length + 1), ((a :: L).get j).1 = _
    rw [Fin.sum_univ_succ]
    simp only [List.length_cons, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ] at ih ⊢
    rw [ih]; simp [degL]

theorem comb_bound {g : ℕ} (L : List (Pc g)) (hg : 1 ≤ g) (hpos : ∀ p ∈ L, 0 < p.1) (k : ℕ) :
    (∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + cnt L k
      ≤ (1 + 1 / (g : ℝ)) ^ (degL L) * (g : ℝ) ^ k := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  set w : Finset (Fin L.length) → ℕ := fun I => ∑ j ∈ I, (L.get j).1 with hw
  set x : ℝ := 1 / (g : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity

  have h1 : (∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + cnt L k
      ≤ ∑ i ∈ Finset.range (k + 1), (cnt L i : ℝ) * (g : ℝ) ^ (k - i) := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hs : ∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))
        ≤ ∑ i ∈ Finset.range k, (cnt L i : ℝ) * (g : ℝ) ^ (k - i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have : (0 : ℝ) ≤ (g : ℝ) ^ (k - i - 1) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg (cnt L i))
    linarith

  have h2 : ∑ i ∈ Finset.range (k + 1), (cnt L i : ℝ) * (g : ℝ) ^ (k - i)
      = ∑ I : Finset (Fin L.length), if w I ≤ k then (g : ℝ) ^ (k - w I) else 0 := by
    have : ∀ i, (cnt L i : ℝ) = ∑ I : Finset (Fin L.length), if w I = i then (1 : ℝ) else 0 := by
      intro i
      simp only [cnt, Finset.sum_boole, hw]
    simp_rw [this, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, Nat.lt_succ_iff]

  have h3 : ∀ I : Finset (Fin L.length), (if w I ≤ k then (g : ℝ) ^ (k - w I) else 0) ≤ (g : ℝ) ^ k * x ^ w I := by
    intro I
    split_ifs with h
    · rw [pow_sub₀ _ hg0.ne' h, hx, one_div_pow, one_div]
    · positivity

  have h4 : ∑ I : Finset (Fin L.length), x ^ w I = ∏ j : Fin L.length, (1 + x ^ (L.get j).1) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hw, Finset.prod_pow_eq_pow_sum]
  have h5 : ∏ j : Fin L.length, (1 + x ^ (L.get j).1) ≤ (1 + x) ^ degL L := by
    rw [← sum_get_fst, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
    have hj : 0 < (L.get j).1 := hpos _ (List.get_mem L j)
    have := pow_add_pow_le (zero_le_one' ℝ) hx0 hj.ne'
    simpa using this
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ ∑ I : Finset (Fin L.length), (g : ℝ) ^ k * x ^ w I := Finset.sum_le_sum fun I _ => h3 I
    _ = (g : ℝ) ^ k * ∏ j : Fin L.length, (1 + x ^ (L.get j).1) := by rw [← Finset.mul_sum, h4]
    _ ≤ (g : ℝ) ^ k * (1 + x) ^ degL L := by gcongr
    _ = _ := by rw [mul_comm]

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem wtC_eJ_le : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ f : (ZMod g)[X], f.Monic → f.natDegree = N → f.coeff 0 ≠ 0 →
    Squarefree f → wtC L (eJ g N k s ψ) f ≤ (1 + 1 / (g : ℝ)) ^ N * wtC L (eU g N ψ) f := by
  intro g _ L hg hG ψ hψ N k s hN hk f hm hd hc hsq
  obtain ⟨Q, hQ, -, hdeg, hset⟩ := (GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG N).2.2 f hm hd hc hsq
  set τ := hcL (Q.map Prod.snd) N with hτ
  have hser : eSerC L N f = zOf τ := by
    unfold eSerC; rw [hset, finsum_mem_singleton]
  have hirr : IsIrr τ := by
    have : τ ∈ {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f} := by rw [hset]; rfl
    exact this.1
  have hcl := isClass_of_isIrr hirr
  obtain ⟨d, hdpos, hd1⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g N) (eU g N ψ) τ).2.1 hirr
  have hL : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 ∧ wh ψ p.2 = 1 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact ⟨(hQ q hq).1.2.1, GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one g ψ hψ _ _ (hQ q hq).1.2.1 (hQ q hq).2⟩
  have hlb := fun i (hi : i ≤ N) => GlobalTheory.T.bernsteinZelevinskyDerivative_harishChandraProduct g ψ hψ (Q.map Prod.snd) N i hdeg hi hL
  have hwhU : tr (eU g N ψ) τ = 1 := (hlb 0 (Nat.zero_le _)).2
  have hkN : k < N := by omega
  set TR : ℝ := (∑ i ∈ Finset.range k, (cnt (Q.map Prod.snd) i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1)))
    + cnt (Q.map Prod.snd) k with hTR
  have hJ : tr (eJ g N k s ψ) τ = (TR : ℂ) := by
    rw [GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN τ hcl, GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives g ψ hψ N k hk hkN τ hcl, (hlb k hkN.le).1, hTR]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(hlb i (by simp at hi; omega)).1]
    rfl
  obtain ⟨-, hU1, hJ', -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g N k s ψ
  obtain ⟨-, hJ1⟩ := hJ' hN
  have hb := comb_bound (Q.map Prod.snd) (by omega) (fun p hp => (hL p hp).1.1) k
  rw [hdeg] at hb
  unfold wtC
  rw [hser, (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ (eJ g N k s ψ) τ).2.2, (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ (eU g N ψ) τ).2.2, hwhU, hJ, hJ1, hU1, hd1]
  set M := N * (N - 1) / 2
  set a : ℝ := (d : ℝ) / (Fintype.card (Gn g N) : ℝ) with ha
  set m : ℝ := ((g : ℝ) ^ M)⁻¹ with hm'
  have e1 : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) * (TR : ℂ) = ((a * TR : ℝ) : ℂ) := by rw [ha]; push_cast; ring
  have e2 : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) * 1 = ((a : ℝ) : ℂ) := by rw [ha]; push_cast; ring
  have e3 : (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = (((g : ℝ) ^ k * m : ℝ) : ℂ) := by rw [hm']; push_cast; ring
  have e4 : ((g : ℂ) ^ M)⁻¹ = ((m : ℝ) : ℂ) := by rw [hm']; push_cast; ring
  rw [e1, e2, e3, e4, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  have hm0 : 0 < m := by rw [hm']; positivity
  have ha0 : 0 < a := by
    rw [ha]; apply div_pos (by exact_mod_cast hdpos); exact_mod_cast Fintype.card_pos
  have hT : TR / (g : ℝ) ^ k ≤ (1 + 1 / (g : ℝ)) ^ N := by rw [div_le_iff₀ hgk]; exact hb
  calc a * TR / ((g : ℝ) ^ k * m) = (a / m) * (TR / (g : ℝ) ^ k) := by rw [div_mul_div_comm, mul_comm ((g : ℝ) ^ k) m]
    _ ≤ (a / m) * (1 + 1 / (g : ℝ)) ^ N := mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (1 + 1 / (g : ℝ)) ^ N * (a / m) := by ring

end GlobalTheory.GLq.UpperWeight
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_bdRPlus_frame_of_period_matrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n P.R.BdR) (Q : GL n P.R.BdR), (∀ g i j, A g i j ∈ Fil P 0) → (∀ g : ↥(GK K), A g * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K), A g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := by
  first | exact @GlobalTheory.PMon.FrameOne.frame_of_period_matrix | exact GlobalTheory.PMon.FrameOne.frame_of_period_matrix | (intros; apply GlobalTheory.PMon.FrameOne.frame_of_period_matrix <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_crystalline_period_unramified_rep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g ∈ IK K, ρ g = 1) → (∀ g i j, ‖(((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) - (1 : Matrix n n (Om l)) i j‖ < 1) → ∃ Q : GL n P.R.B, ∀ g : ↥(GK K), (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) * (Q : Matrix n n P.R.B).map (P.actQ (g : GQ l)) = Q := by
  first | exact @GlobalTheory.UnrPer.exists_period_unramified | exact GlobalTheory.UnrPer.exists_period_unramified | (intros; apply GlobalTheory.UnrPer.exists_period_unramified <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.RatioTransport

open GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem lift_phi {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) :
    T.eB (P.φB b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l y) := by
  rw [T.frob, h, (GlobalTheory.PMon.Trans.acris_bcris l).2.1]

theorem lift_iter {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) (j : ℕ) :
    T.eB (P.φB^[j] b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((φc l)^[j] y) := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact lift_phi T ih

theorem iter_lpow (m j : ℕ) (x : P.R.B) :
    P.φB^[m] ((l : P.R.B) ^ j * x) = (l : P.R.B) ^ j * P.φB^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem isUnit_lpow (m : ℕ) : IsUnit ((l : P.R.B) ^ m) := by
  have h : IsUnit (l : ℚ_[l]) := (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0).isUnit
  have h2 := h.map (algebraMap ℚ_[l] P.R.B)
  rw [map_natCast] at h2
  exact h2.pow m

theorem ratio_integral {h s : ℕ} (hs : s < h) {b b' : P.R.B} {y y' : Formalism.Per.Acris l}
    (hb : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y)
    (hb' : T.eB b' = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y')
    (he : P.φB^[h] b = (l : P.R.B) ^ s * b) (he' : P.φB^[h] b' = (l : P.R.B) ^ s * b')
    (h0 : b' ≠ 0) (hr : P.φB b * b' = b * P.φB b') : ∃ c : ℚ_[l], b = c • b' := by
  obtain ⟨hinj, -, hz⟩ := GlobalTheory.PMon.Trans.acris_bcris l
  have e1 : (φc l)^[h] y = (l : Formalism.Per.Acris l) ^ s * y := by
    apply hinj
    rw [← lift_iter T hb, he, map_mul, map_pow, map_natCast, hb, map_mul, map_pow, map_natCast]
  have e2 : (φc l)^[h] y' = (l : Formalism.Per.Acris l) ^ s * y' := by
    apply hinj
    rw [← lift_iter T hb', he', map_mul, map_pow, map_natCast, hb', map_mul, map_pow, map_natCast]
  have e3 : y' ≠ 0 := by
    rintro rfl
    apply h0
    apply T.eB.injective
    rw [hb', map_zero, map_zero]
  have e4 : φc l y * y' = y * φc l y' := by
    apply hinj
    rw [map_mul, map_mul, ← lift_phi T hb, ← lift_phi T hb', ← hb, ← hb', ← map_mul, ← map_mul, hr]
  obtain ⟨c, d, hc, hcd⟩ := ratio_proportional_target l h s hs y y' e1 e2 e3 e4
  have e5 : algebraMap ℚ_[l] P.R.B (c : ℚ_[l]) * b = algebraMap ℚ_[l] P.R.B (d : ℚ_[l]) * b' := by
    apply T.eB.injective
    rw [map_mul, map_mul, T.zB, T.zB, hb, hb', ← hz, ← hz, ← map_mul, ← map_mul, hcd]
  have hc' : (c : ℚ_[l]) ≠ 0 := fun e => hc (Subtype.ext e)
  refine ⟨(c : ℚ_[l])⁻¹ * d, ?_⟩
  rw [Algebra.smul_def, map_mul, mul_assoc, ← e5, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc', map_one, one_mul]

theorem ratio_of_acris : Ratio := by
  intro l _ P AI T h s hs ω ω' hω hω' he he' h0 hr
  obtain ⟨N, x, hx⟩ := hω
  obtain ⟨M, x', hx'⟩ := hω'
  have hb : T.eB ((l : P.R.B) ^ (N + M) * ω) =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ M * x) := by
    have e : (l : P.R.B) ^ (N + M) * ω = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * ω) := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ M), hx]
    simp only [map_mul, map_pow, map_natCast]
  have hb' : T.eB ((l : P.R.B) ^ (N + M) * ω') =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ N * x') := by
    have e : (l : P.R.B) ^ (N + M) * ω' = (l : P.R.B) ^ N * ((l : P.R.B) ^ M * ω') := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ N), hx']
    simp only [map_mul, map_pow, map_natCast]
  have hu := isUnit_lpow (P := P) (N + M)
  obtain ⟨c, hc⟩ := ratio_integral T hs hb hb'
    (by rw [iter_lpow, he]; ring) (by rw [iter_lpow, he']; ring)
    (fun e => h0 ((hu.mul_right_eq_zero).1 e))
    (by
      simp only [map_mul, map_pow, map_natCast]
      linear_combination ((l : P.R.B) ^ (N + M)) ^ 2 * hr)
  refine ⟨c, hu.mul_left_cancel ?_⟩
  rw [hc, Algebra.smul_def, Algebra.smul_def]
  ring

end GlobalTheory.PMon.RatioTransport
end

section

noncomputable section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst

namespace GlobalTheory.TwistAbove

def twGL {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K) :
    Γ →* GL (Fin a) K where
  toFun g := ⟨((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    (((χ g)⁻¹ : Kˣ) : K) • (((r g)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    by rw [smul_mul_smul_comm, Units.mul_inv, Units.mul_inv, one_smul],
    by rw [smul_mul_smul_comm, Units.inv_mul, Units.inv_mul, one_smul]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by
    change ((χ (g * h) : Kˣ) : K) • ((r (g * h) : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) *
      (((χ h : Kˣ) : K) • ((r h : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))
    rw [smul_mul_smul_comm, map_mul, map_mul, Units.val_mul, Units.val_mul])

@[simp] theorem twGL_val {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (g : Γ) : ((twGL χ r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      ((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := rfl

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a : ℕ}

abbrev chr {L : FinExt l} (m : ↥Gw →* GL (Fin 1) ↥L.1) : ↥Gw →* (↥L.1)ˣ :=
  Matrix.GeneralLinearGroup.det.comp m

theorem isModel_twGL {L : FinExt l} {r r' : ↥Gw →* GL (Fin a) (Om l)} {μ : ↥Gw →* (Om l)ˣ}
    (hr' : ∀ g, ((r' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
      ((μ g : (Om l)ˣ) : Om l) • ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))
    {r₁ : ↥Gw →* GL (Fin a) ↥L.1} {m : ↥Gw →* GL (Fin 1) ↥L.1}
    (h₁ : IsModel Bw r L r₁) (h₂ : IsModel Bw (rk1 μ) L m) :
    IsModel Bw r' L (twGL (chr m) r₁) := by
  refine ⟨h₁.1, ?_⟩
  ext g i j
  have e1 := congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) =>
    ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) h₁.2
  have e2 := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) =>
    ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) h₂.2
  simp only [mapRep, rk1] at e1 e2 ⊢
  simp at e1 e2 ⊢
  rw [hr']
  simp [← e1, ← e2]

section Common

variable {L : FinExt l} (r₁ : ↥Gw →* GL (Fin a) ↥L.1) (m : ↥Gw →* GL (Fin 1) ↥L.1)

theorem repE_twGL (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L (twGL (chr m) r₁) g x = ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • Bw.repE L r₁ g x := by
  change Matrix.toLin' ((twGL (chr m) r₁ (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x =
    ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) •
      Matrix.toLin' ((r₁ (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x
  rw [twGL_val, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Matrix.smul_mulVec _ _ _

theorem repE_rank_one (g : ↥(GK Bw.Kw)) (x : Fin 1 → ↥L.1) :
    Bw.repE L m g x = ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • x := by
  funext i
  fin_cases i
  simp [LocBridge.repE, Matrix.mulVec, dotProduct, Matrix.det_unique]

theorem isDR_iff (P : LocPrime l) {n : ℕ} (s : ↥Gw →* GL (Fin n) ↥L.1) :
    IsDR (P.PD Bw.Kw) (Bw.repE L s) ↔ Bw.IsdRE P L s := by
  rw [IsDR, LocBridge.IsdRE, Module.finrank_fin_fun]

theorem twist_common {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    (Bw.IsdRE P L r₁ → Bw.IsdRE P L m → Bw.IsdRE P L (twGL (chr m) r₁)) ∧
    (Bw.IsCrysE P L r₁ → Bw.IsCrysE P L m → Bw.IsCrysE P L (twGL (chr m) r₁)) ∧
    (Bw.IsPotCrysE P L r₁ → Bw.IsPotCrysE P L m → Bw.IsPotCrysE P L (twGL (chr m) r₁)) ∧
    ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (b : ℤ), Bw.IsdRE P L m →
      (∀ n, Bw.multE P L m τ' n = if n = b then 1 else 0) →
      ∀ n, Bw.multE P L (twGL (chr m) r₁) τ' (n + b) = Bw.multE P L r₁ τ' n := by
  have hν := repE_rank_one Bw m
  have hρ := repE_twGL Bw r₁ m
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, ?_, ?_⟩
  · rw [← isDR_iff] at h1 h2 ⊢
    exact (GlobalTheory.TwistDR.isDR_twist_iff l P AI T Bw.Kw L (Fin a → ↥L.1) _ _ _ _ hν hρ h2).1 h1
  · exact (GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T Bw.Kw L (Fin a → ↥L.1)
      _ _ _ _ hν hρ h2).1 h1
  · rintro ⟨K₁, k₁, c₁⟩ ⟨K₂, k₂, c₂⟩
    have l₁ : K₁.1 ≤ (supExt K₁ K₂).1 := le_sup_left
    have l₂ : K₂.1 ≤ (supExt K₁ K₂).1 := le_sup_right
    have k₃ : Bw.Kw.1 ≤ (supExt K₁ K₂).1 := k₁.trans l₁
    have d₁ := GlobalTheory.Per.TiedRestrict.isCrys_restrict l₁ _ T c₁
    have d₂ := GlobalTheory.Per.TiedRestrict.isCrys_restrict l₂ _ T c₂
    have e₁ : ((Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₁))).comp (Subgroup.inclusion (GK_le l₁)) =
        (Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₃)) := MonoidHom.ext fun _ => rfl
    have e₂ : ((Bw.repE L m).comp (Subgroup.inclusion (GK_le k₂))).comp (Subgroup.inclusion (GK_le l₂)) =
        (Bw.repE L m).comp (Subgroup.inclusion (GK_le k₃)) := MonoidHom.ext fun _ => rfl
    rw [e₁] at d₁
    rw [e₂] at d₂
    exact ⟨supExt K₁ K₂, k₃, (GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T
      (supExt K₁ K₂) L (Fin a → ↥L.1) ((Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₃))) _
      ((Bw.repE L m).comp (Subgroup.inclusion (GK_le k₃))) _ (fun g x => hν _ x) (fun g x => hρ _ x) d₂).1 d₁⟩
  · intro τ' b hm hmult n
    exact GlobalTheory.TwistJump.multV_twist_char l P AI T Bw.Kw L (Fin a → ↥L.1) _ _ _ _ hν hρ
      ((isDR_iff Bw P m).2 hm) τ' b hmult n

end Common

theorem twist_above : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ), ∀ (r r' : ↥Gw →* GL (Fin a) (Loc.Om l)) (μ : ↥Gw →* (Loc.Om l)ˣ), (∀ g, ((r' g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l)) = ((μ g : (Loc.Om l)ˣ) : Loc.Om l) • ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → (IsdRAt P Bw r → IsdRAt P Bw (rk1 μ) → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw (rk1 μ) → IsCrysAt P Bw r') ∧ (IsPotCrysAt P Bw r → IsPotCrysAt P Bw (rk1 μ) → IsPotCrysAt P Bw r') ∧ ∀ (τ : E →+* Loc.Om l) (J : Multiset ℤ) (c : ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw (rk1 μ) τ {c} → IsJumpsAt P Bw r' τ (J.map (· + c)) := by
  intro l _ P AI hT E Ω _ _ _ _ Gw O _ _ _ Bw a r r' μ hr'
  obtain ⟨T⟩ := hT
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun τ J c h1 h2 => ?_⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).1 ((local_ext P Bw l₁ r₁).2.1.2 d₁) ((local_ext P Bw l₂ r₂).2.1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).2.1 ((local_ext P Bw l₁ r₁).1.2 d₁) ((local_ext P Bw l₂ r₂).1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).2.2.1 ((local_ext P Bw l₁ r₁).2.2.1.2 d₁) ((local_ext P Bw l₂ r₂).2.2.1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁, τ₁, i₁, c₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂, τ₂, i₂, c₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have j₁ : IsInduced Bw τ ((IntermediateField.inclusion l₁).comp τ₁) := fun x => i₁ x
    have j₂ : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ₂) := fun x => i₂ x
    have eτ := IsInduced.unique j₁ j₂
    have hd₂ := (local_ext P Bw l₂ r₂).2.1.2 d₂
    have hc := twist_common Bw (mapRep (IntermediateField.inclusion l₁).toRingHom r₁)
      (mapRep (IntermediateField.inclusion l₂).toRingHom r₂) T
    have hm : ∀ n, Bw.multE P (supExt L₁ L₂) (mapRep (IntermediateField.inclusion l₂).toRingHom r₂)
        ((IntermediateField.inclusion l₁).comp τ₁) n = if n = c then 1 else 0 := by
      intro n
      rw [eτ, (local_ext P Bw l₂ r₂).2.2.2 τ₂ n, ← c₂ n, Multiset.count_singleton]
      split_ifs <;> simp
    refine ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      hc.1 ((local_ext P Bw l₁ r₁).2.1.2 d₁) hd₂, _, j₁, fun n => ?_⟩
    have e1 := Multiset.count_map_eq_count' (fun x : ℤ => x + c) J (add_left_injective c) (n - c)
    simp only [sub_add_cancel] at e1
    have e2 := hc.2.2.2 _ c hd₂ hm (n - c)
    rw [sub_add_cancel] at e2
    rw [e1, e2, (local_ext P Bw l₁ r₁).2.2.2 τ₁ (n - c), c₁]

end GlobalTheory.TwistAbove
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isSemilinearBaseChange_of_basis_maps_to_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (ι : Type) (e : Module.Basis ι A M) (b : Module.Basis ι B N), (∀ i, b i = u (e i)) → SemiBC u := by
  first | exact @GlobalTheory.BSP.semiBC_of_basis | exact GlobalTheory.BSP.semiBC_of_basis | (intros; apply GlobalTheory.BSP.semiBC_of_basis <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isLocalizedFraction_semilinear_transition : ∀ (A A' : Type) [CommRing A] [CommRing A'] (k : A →+* A') (N : Type) [AddCommGroup N] [Module A N] (N' : Type) [AddCommGroup N'] [Module A' N'] (τ : N →ₛₗ[k] N') (t : A) (t' : A') (a : ℕ) (y : LocalizedModule (Submonoid.powers t) N) (y' : LocalizedModule (Submonoid.powers t') N') (z m : N) (z' n : N') (i j : ℕ), IsFrac t y z a → IsFrac t y m i → IsFrac t' y' z' a → IsFrac t' y' n j → t' ^ a • τ z = k t ^ a • z' → ∃ r : ℕ, (k t * t') ^ r • (t' ^ j • τ m - k t ^ i • n) = 0 := by
  first | exact @GlobalTheory.BSP.isFrac_transition | exact GlobalTheory.BSP.isFrac_transition | (intros; apply GlobalTheory.BSP.isFrac_transition <;> assumption)
end
