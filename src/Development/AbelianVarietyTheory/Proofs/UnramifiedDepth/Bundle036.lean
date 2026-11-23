module

public import ReciprocityTheory.DualLattices.Bundle012
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvRegaugedSecondLawFamily
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteTorsOfFiniteTorsion
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChF

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.Regauge

variable {R : Type} [CommRing R] {d : ℕ}

private theorem gp_mulF (F : FGLaw R d) (N : ℕ) : GP (mulF F.F N) :=
  FormalMul.constantCoeff_mulF F.F F.const N

private theorem nsum_add (F : FGLaw R d) (a b : ℕ) :
    mulF F.F (a + b) = addOf F.F (mulF F.F a) (mulF F.F b) := by
  induction b with
  | zero => exact (addOf_zero F (gp_mulF F a)).symm
  | succ b ih =>
    change addOf F.F (mulF F.F (a + b)) (pt R d 0) = addOf F.F _ (addOf F.F (mulF F.F b) (pt R d 0))
    rw [ih, addOf_assoc F (gp_mulF F a) (gp_mulF F b) (gp_pt 0)]

private theorem nsum_mul (F : FGLaw R d) (N M : ℕ) :
    mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M) := by
  have hV := single_point_zero_constant (gp_mulF F M)
  induction N with
  | zero =>
    rw [Nat.zero_mul]
    exact (evP_zero _ hV).symm
  | succ N ih =>
    rw [Nat.succ_mul, nsum_add, ih]
    change _ = evP ![mulF F.F M] (addOf F.F (mulF F.F N) (pt R d 0))
    rw [evP_addOf _ hV _ _ _ (gp_mulF F N) (gp_pt 0), evP_pt _ hV]
    rfl

private theorem ev_mem_pow {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, GP (a j))
    {K : Ideal (PS R n d)} (hK : ∀ j i, a j i ∈ K) {N : ℕ} {f : PS R m d}
    (hf : f ∈ germIdeal (Fin m × Fin d) R ^ N) : ev a f ∈ K ^ N := by
  have h : (germIdeal (Fin m × Fin d) R ^ N).map (substAlgHom (R := R) (gt_hasSubst a ha)) ≤ K ^ N := by
    rw [Ideal.map_pow, germIdeal_eq_span]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    rw [substAlgHom_X]
    exact hK _ _
  have := h (Ideal.mem_map_of_mem _ hf)
  rwa [substAlgHom_apply] at this

private theorem mem_sq_iff {σ : Type} [Finite σ] {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ 2 ↔ constantCoeff g = 0 ∧ ∀ s, coeff (Finsupp.single s 1) g = 0 := by
  rw [mem_germIdeal_pow_iff]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by simp), fun s => h _ (by simp)⟩
  · rintro ⟨h0, h1⟩ e he
    rcases (by omega : e.degree = 0 ∨ e.degree = 1) with h | h
    · obtain rfl := (Finsupp.degree_eq_zero_iff e).1 h
      simpa using h0
    · obtain ⟨s, rfl⟩ : e ∈ Set.range (fun s : σ => Finsupp.single s 1) := by
        rw [Finsupp.range_single_one]; exact h
      exact h1 s

private theorem coeff_single_X' {σ : Type} [DecidableEq σ] (s t : σ) :
    coeff (Finsupp.single s 1) (X t : MvPowerSeries σ R) = if s = t then 1 else 0 := by
  rw [coeff_X]
  simp [Finsupp.single_left_inj]

private theorem sub_lin_mem {σ : Type} [Fintype σ] {g : MvPowerSeries σ R} (hg : constantCoeff g = 0) :
    g - ∑ s, coeff (Finsupp.single s 1) g • X s ∈ germIdeal σ R ^ 2 := by
  classical
  refine mem_sq_iff.2 ⟨by simp [hg], fun s => ?_⟩
  simp [coeff_single_X']

private theorem ev_sub_lin_mem {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, GP (a j))
    {f : PS R m d} (hf : constantCoeff f = 0) :
    ev a f - ∑ s : Fin m × Fin d, coeff (Finsupp.single s 1) f • a s.1 s.2 ∈
      germIdeal (Fin n × Fin d) R ^ 2 := by
  have h := ev_mem_pow ha (K := germIdeal (Fin n × Fin d) R) (fun j i => ha j i) (sub_lin_mem hf)
  unfold ev at h ⊢
  rw [← substAlgHom_apply (gt_hasSubst a ha)] at h ⊢

  simpa only [map_sub, map_sum, map_smul, substAlgHom_X] using h

private theorem coeff_law (F : FGLaw R d) (i : Fin d) (l : Fin 2) (j : Fin d) :
    coeff (Finsupp.single (l, j) 1) (F.F i) = if j = i then 1 else 0 := by
  have hp : GP (pt R (n := 1) d 0) := gp_pt 0
  fin_cases l
  · have h := (mem_sq_iff.1 (ev_sub_lin_mem (pair_points_zero_constant hp gp_zero₂) (F.const i))).2 (0, j)
    have e : ev ![pt R (n := 1) d 0, 0] (F.F i) = X (0, i) := congrFun (addOf_zero F hp) i
    rw [e] at h
    simp [Fintype.sum_prod_type, pt, coeff_single_X', sub_eq_zero] at h
    simpa using h.symm
  · have h := (mem_sq_iff.1 (ev_sub_lin_mem (pair_points_zero_constant gp_zero₂ hp) (F.const i))).2 (0, j)
    rw [F.unit i] at h
    simp [Fintype.sum_prod_type, pt, coeff_single_X', sub_eq_zero] at h
    simpa using h.symm

private theorem nsum_sub_mem (F : FGLaw R d) (N : ℕ) (i : Fin d) :
    mulF F.F N i - (N : R) • X (0, i) ∈ germIdeal (Fin 1 × Fin d) R ^ 2 := by
  induction N with
  | zero => simp [mulF]
  | succ N ih =>
    have h := ev_sub_lin_mem (pair_points_zero_constant (gp_mulF F N) (gp_pt 0)) (F.const i)
    simp only [Fintype.sum_prod_type, coeff_law, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    convert add_mem h ih using 1
    change ev ![mulF F.F N, pt R d 0] (F.F i) - _ = _
    simp only [pt, Nat.cast_succ, add_smul, one_smul]
    abel

private theorem lin_nsum (F : FGLaw R d) (N : ℕ) :
    lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  ext i j
  have h := (mem_sq_iff.1 (nsum_sub_mem F N i)).2 (0, j)
  rw [map_sub, sub_eq_zero, map_smul, coeff_single_X'] at h
  simp [lin, h, Matrix.one_apply, eq_comm]

private theorem span_nsum_le (F : FGLaw R d) (N M : ℕ) :
    Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M)) := by
  rw [Ideal.span_le, nsum_mul]
  rintro _ ⟨j, rfl⟩
  have := ev_mem_pow (single_point_zero_constant (gp_mulF F M)) (K := Ideal.span (Set.range (mulF F.F M))) (N := 1)
    (f := mulF F.F N j) (fun l i => by fin_cases l; exact Ideal.subset_span ⟨i, rfl⟩)
    (by rw [pow_one]; exact gp_mulF F N j)
  rwa [pow_one] at this

private theorem nsum_pow_mem (F : FGLaw R d) (p k : ℕ) (j : Fin d) :
    mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (C : R →+* PS R 1 d) ⊔
      Ideal.span (Set.range (X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) := by
  set J := (Ideal.span {(p : R)}).map (C : R →+* PS R 1 d) ⊔
      Ideal.span (Set.range (X : Fin 1 × Fin d → PS R 1 d)) with hJ
  induction k generalizing j with
  | zero =>
    rw [zero_add, pow_one, hJ, ← germIdeal_eq_span]
    exact Ideal.mem_sup_right (gp_mulF F _ j)
  | succ k ih =>
    have hV := single_point_zero_constant (gp_mulF F (p ^ k))
    have h := ev_mem_pow hV (K := J ^ (k + 1)) (fun l i => by fin_cases l; exact ih i)
      (nsum_sub_mem F p j)
    rw [← pow_mul, gt_ev_sub _ hV, smul_eq_C_mul, gt_ev_mul _ hV, gt_ev_X _ hV] at h
    have h1 := Ideal.pow_le_pow_right (show k + 1 + 1 ≤ (k + 1) * 2 by omega) h
    have hC : ev ![mulF F.F (p ^ k)] (C (p : R) : PS R 1 d) = C (p : R) := subst_C _
    have h2 : C (p : R) * mulF F.F (p ^ k) j ∈ J ^ (k + 1 + 1) := by
      rw [pow_succ' J (k + 1)]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_map_of_mem _
        (Ideal.subset_span rfl))) (ih j)
    rw [hC] at h1
    have h3 := add_mem h1 h2
    rw [pow_succ' p k, nsum_mul]
    simpa [comp1] using h3

end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF

theorem lin_mulF_and_comp_and_span_le_and_mem_pow : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d), (∀ N : ℕ, lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R)) ∧ (∀ N M : ℕ, mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M)) ∧ (∀ N M : ℕ, Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M))) ∧ ∀ (p k : ℕ) (j : Fin d), mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (MvPowerSeries.C : R →+* PS R 1 d) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) :=
  fun _ _ _ F => ⟨lin_nsum F, nsum_mul F, span_nsum_le F, nsum_pow_mem F⟩

end GlobalTheory.ChF
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem isAdicComplete_germIdeal (R κ : Type) [CommRing R] [Finite κ] :
    IsAdicComplete (germIdeal κ R) (MvPowerSeries κ R) := by
  have h := (mem_sup_span_X_pow_iff_and_isAdicComplete R ⊥ κ).2 inferInstance
  rwa [Ideal.map_bot, bot_sup_eq, ← germIdeal_eq_span] at h

private theorem eq_zero_or_single {κ : Type} {e : κ →₀ ℕ} (he : e.degree < 2) :
    e = 0 ∨ ∃ k, e = Finsupp.single k 1 := by
  classical
  by_cases h0 : e = 0
  · exact Or.inl h0
  · right
    obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h0
    have hle : Finsupp.single k 1 ≤ e := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 hk
    obtain ⟨c, hc⟩ := exists_add_of_le hle
    have hd : e.degree = 1 + c.degree := by rw [hc, map_add (f := _), Finsupp.degree_single]
    have : c = 0 := (Finsupp.degree_eq_zero_iff c).1 (by omega)
    exact ⟨k, by rw [hc, this, add_zero]⟩

theorem sub_surjective_of_lin_leftInverse : ∀ (R : Type) [CommRing R] (d r : ℕ) (φ : Fin d → PS R 1 r) (A' : Matrix (Fin r) (Fin d) R), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → A' * lin φ = 1 → Function.Surjective (fun f : PS R 1 d => sub ![φ] f) := by
  intro R _ d r φ A' h0 hA
  classical
  set a : Fin 1 × Fin d → PS R 1 r := fun q => (![φ] : Fin 1 → Fin d → PS R 1 r) q.1 q.2 with ha
  have ha' : ∀ q : Fin 1 × Fin d, a q = φ q.2 := by
    rintro ⟨i, j⟩
    fin_cases i
    rfl
  have hs : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by rw [ha', h0]
  let f : PS R 1 d →+* PS R 1 r := (MvPowerSeries.substAlgHom (R := R) hs).toRingHom
  have hf : ∀ u, f u = sub ![φ] u := fun u => by
    change MvPowerSeries.substAlgHom hs u = MvPowerSeries.subst a u
    rw [MvPowerSeries.coe_substAlgHom]
  have hfX : ∀ q, f (MvPowerSeries.X q) = φ q.2 := fun q => by
    change MvPowerSeries.substAlgHom hs _ = _
    rw [MvPowerSeries.substAlgHom_X, ha']
  have hC1 := isAdicComplete_germIdeal R (Fin 1 × Fin d)
  have hC2 := isAdicComplete_germIdeal R (Fin 1 × Fin r)
  have hmap : (germIdeal (Fin 1 × Fin d) R).map f = germIdeal (Fin 1 × Fin r) R := by
    apply le_antisymm
    · rw [germIdeal_eq_span, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      rw [hfX]
      exact RingHom.mem_ker.2 (h0 _)
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := germIdeal (Fin 1 × Fin r) R) ?_
        (IsAdicComplete.le_jacobson_bot _) ?_
      · rw [germIdeal_eq_span]
        exact Submodule.fg_span (Set.finite_range _)
      · rw [smul_eq_mul, ← pow_two]
        conv_lhs => rw [germIdeal_eq_span]
        rw [Ideal.span_le]
        rintro _ ⟨⟨i0, i⟩, rfl⟩
        obtain rfl : i0 = 0 := Subsingleton.elim _ _
        have h1 : ∑ j, A' i j • φ j ∈ (germIdeal (Fin 1 × Fin d) R).map f := by
          refine Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ ?_
          rw [← hfX (0, j)]
          exact Ideal.mem_map_of_mem _ (X_mem_germIdeal _)
        have h2 : (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 r) - ∑ j, A' i j • φ j ∈
            germIdeal (Fin 1 × Fin r) R ^ 2 := by
          refine mem_germIdeal_pow_iff.2 fun e he => ?_
          rcases eq_zero_or_single he with rfl | ⟨⟨k0, k⟩, rfl⟩
          · simp [h0]
          · obtain rfl : k0 = 0 := Subsingleton.elim _ _
            have h3 := congrFun (congrFun hA i) k
            rw [Matrix.mul_apply, Matrix.one_apply] at h3
            simp only [lin, Matrix.of_apply] at h3

            rw [map_sub, map_sum]
            simp only [map_smul, smul_eq_mul]
            rw [h3, MvPowerSeries.coeff_X]
            simp [Finsupp.single_left_inj, eq_comm]
        have h4 := Submodule.add_mem_sup h1 h2
        rwa [add_sub_cancel] at h4
  have hsurj : Function.Surjective f := by
    have : IsHausdorff ((germIdeal (Fin 1 × Fin d) R).map f) (PS R 1 r) := by
      rw [hmap]
      exact hC2.toIsHausdorff
    refine surjective_of_mk_map_comp_surjective (I := germIdeal (Fin 1 × Fin d) R) f fun y => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPowerSeries.C (MvPowerSeries.constantCoeff y), ?_⟩
    have h5 : f (MvPowerSeries.C (MvPowerSeries.constantCoeff y)) =
        MvPowerSeries.C (MvPowerSeries.constantCoeff y) :=
      (MvPowerSeries.substAlgHom (R := R) hs).commutes _
    rw [RingHom.comp_apply, h5, Ideal.Quotient.eq, hmap]
    exact RingHom.mem_ker.2 (by simp)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, (hf x).symm.trans hx⟩

end GlobalTheory.ChF
end

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem nv_eq_sum {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ} (f : PS R n d)
    (a : Fin n → Fin d → S) (N : ℕ) (hN : ∀ q : Fin n × Fin d, a q.1 q.2 ^ N = 0) :
    nv s f a = ∑ e : Fin n × Fin d → Fin N, s (MvPowerSeries.coeff
      (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) f) * ∏ i, a i.1 i.2 ^ (e i : ℕ) := by
  letI := s.toAlgebra
  exact evBasic_nEval_eq_tEval f (fun q : Fin n × Fin d => a q.1 q.2) N hN

private theorem nEval_sqZero {R S κ : Type} [CommRing R] [CommRing S] [Algebra R S] [Fintype κ] [DecidableEq κ]
    (f : MvPowerSeries κ R) (a : κ → S) (ha : ∀ i, IsNilpotent (a i)) (h : ∀ i j, a i * a j = 0) :
    nEval f a = algebraMap R S (MvPowerSeries.constantCoeff f) +
      ∑ q, algebraMap R S (MvPowerSeries.coeff (Finsupp.single q 1) f) * a q := by
  have h0 : ∀ i : κ, IsNilpotent ((0 : κ → S) i) := fun _ => IsNilpotent.zero
  have hm : ∀ i, a i ∈ Ideal.span (Set.range a) := fun i => Ideal.subset_span ⟨i, rfl⟩
  have h1 := ChartCompare.nEval_sub_mem f a 0 ha h0 _ _ hm (fun _ => Ideal.zero_mem _)
    (fun i => by simpa using hm i)
  have h2 : Ideal.span (Set.range a) * Ideal.span (Set.range a) ≤ ⊥ := by
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact h i j
  have h3 := (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; simp) : Ideal.span _ ≤ (⊥ : Ideal S))
    (evBasic_nEval_sub_coeff_mem f (0 : κ → S) h0)
  have h4 := h2 h1
  rw [Ideal.mem_bot, sub_eq_zero] at h3 h4
  rw [h3, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, sub_eq_iff_eq_add'] at h4
  simpa [Algebra.smul_def] using h4

theorem nv_calculus : ∀ (R S : Type) [CommRing R] [CommRing S] (s : R →+* S) (n d : ℕ) (a : Fin n → Fin d → S), (∀ i j, IsNilpotent (a i j)) → (∃ ψ : PS R n d →+* S, (∀ f, ψ f = nv s f a) ∧ (∀ c, ψ (MvPowerSeries.C c) = s c) ∧ ∀ q : Fin n × Fin d, ψ (MvPowerSeries.X q) = a q.1 q.2) ∧ (∀ f : PS R n d, MvPowerSeries.constantCoeff f = 0 → IsNilpotent (nv s f a) ∧ nv s f a ∈ Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2)) ∧ (∀ (m e : ℕ) (b : Fin m → Fin e → PS R n d) (f : PS R m e), (∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) → nv s (sub b f) a = nv s f (fun i j => nv s (b i j) a)) ∧ (∀ (R' : Type) [CommRing R'] (β : R' →+* R) (f : PS R' n d), nv (s.comp β) f a = nv s (MvPowerSeries.map β f) a) ∧ (∀ (S' : Type) [CommRing S'] (t : S →+* S') (f : PS R n d), t (nv s f a) = nv (t.comp s) f (fun i j => t (a i j))) ∧ ((∀ i j i' j', a i j * a i' j' = 0) → ∀ f : PS R n d, nv s f a = s (MvPowerSeries.constantCoeff f) + ∑ q : Fin n × Fin d, s (MvPowerSeries.coeff (Finsupp.single q 1) f) * a q.1 q.2) := by
  intro R S _ _ s n d a ha
  have ha' : ∀ q : Fin n × Fin d, IsNilpotent (a q.1 q.2) := fun q => ha _ _
  obtain ⟨N, -, hN⟩ := evBasic_exists_pow (fun q : Fin n × Fin d => a q.1 q.2) ha'
  letI := s.toAlgebra
  refine ⟨?_, fun f hf => ⟨ChartCompare.isNilpotent_nEval f hf _ ha', ?_⟩, fun m e b f hb => ?_,
    fun R' _ β f => ?_, fun S' _ t f => ?_,
    fun h f => nEval_sqZero f (fun q : Fin n × Fin d => a q.1 q.2) ha' fun _ _ => h _ _ _ _⟩
  · let ψ : PS R n d →+* S := (MvPowerSeries.constantCoeff : MvPowerSeries Empty S →+* S).comp
      (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C _ ha')).toRingHom
    have hψ : ∀ f, ψ f = nv s f a := fun f => by
      simp [ψ, nv, MvPowerSeries.coe_substAlgHom, ChartCompare.subst_C_eq f _ ha']
    refine ⟨ψ, hψ, fun c => ?_, fun q => (hψ _).trans (ChartCompare.nEval_X _ ha' q)⟩
    have := (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C _ ha')).commutes c
    exact (congrArg MvPowerSeries.constantCoeff this).trans (by
      rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C]; rfl)
  · have := evBasic_nEval_sub_coeff_mem f _ ha'
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_zero, sub_zero] at this
    exact this
  · exact ChartCompare.nEval_subst (fun q : Fin m × Fin e => b q.1 q.2) (fun q => hb _ _) f _ ha'
  · rw [nv_eq_sum _ _ a N hN, nv_eq_sum _ _ a N hN]
    simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]
  · rw [nv_eq_sum _ _ a N hN, nv_eq_sum _ _ _ N (fun q => by rw [← map_pow, hN q, map_zero])]

    simp only [map_sum, map_mul, map_prod, map_pow, RingHom.comp_apply]

end GlobalTheory.ChF
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G' G f φ) {Z : Scheme.{0}}
    (t' : Z ⟶ S') (t : Z ⟶ S) (ht : t' ≫ f = t) :
    ∃ P : (Over.mk t' ⟶ G') →* (Over.mk t ⟶ G), (∀ x, (P x).left = x.left ≫ φ) ∧ Function.Bijective P := by
  subst ht
  let p : (Over.mk t' ⟶ G') → (Over.mk (t' ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      have := Over.w x
      simp only [Over.mk_hom] at this ⊢
      rw [Category.assoc, h.1.w, ← Category.assoc, this])
  refine ⟨MonoidHom.mk' p fun x y => Over.OverMorphism.ext (h.2 (Over.mk t') x y (p x) (p y) rfl rfl).symm,
    fun _ => rfl, fun x y hxy => ?_, fun z => ?_⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) hxy
    · exact (Over.w x).trans (Over.w y).symm
  · refine ⟨Over.homMk (h.1.lift z.left t' (Over.w z)) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _

private theorem spec_comp {R₀ : Type} [CommRing R₀] {O R : LAlg R₀} (s : LHom O R) :
    Spec.map (CommRingCat.ofHom s.1.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type))) =
      Spec.map (CommRingCat.ofHom (algebraMap R₀ (R : Type))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact s.1.comp_algebraMap

theorem bxChart_of_nilChart : ∀ (R₀ : Type) [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ → ∀ (g : ℕ) (F : Fin g → PS (O : Type) 2 g) (X : Fam G' g), NilChart G' F X → ∃ Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R, BXChart B O F Y ∧ ∀ (f : G' ⟶ G') (α : Fin g → PS (O : Type) 1 g) (A : OEnd B O), Reads X X f α → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.f s x)).left) → ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a]) := by
  intro R₀ _ G _ _ B e hb hm hn O G' _ _ φ hφ g F X hX
  have h0 : ∀ R, e R 0 = 1 := fun R => by
    have := hm R 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  choose P hP hPb using fun (R : LAlg R₀) (s : LHom O R) => exists_push hφ _ _ (spec_comp s)
  let X' : ∀ R : LAlg R₀, ∀ s : LHom O R, (Fin g → (R : Type)) →
      (Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G') := fun R s a =>
    @X R _ s.1.toRingHom.toAlgebra a
  choose Y hY using fun (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)) => (hb R).2 (P R s (X' R s a))
  have hYl : ∀ R s a, (e R (Y R s a)).left = (X' R s a).left ≫ φ := fun R s a => by rw [hY, hP]
  refine ⟨Y, ⟨fun R s => ?_, fun R R' s f a ha => ?_, fun R s a b ha hb' hab => ?_,
    fun R S s π σ hπσ hσ hπ x hx => ?_, fun R s a b ha hb' => ?_⟩, fun f α A hr hA R s a ha => ?_⟩
  · apply (hb R).1
    rw [hY, h0]
    letI := s.1.toRingHom.toAlgebra
    have : X' R s 0 = 1 := hX.zero R
    rw [this, map_one]
  · apply (hb R').1
    apply Over.OverMorphism.ext
    rw [hn, Over.comp_left, hYl, hYl]
    letI := s.1.toRingHom.toAlgebra
    letI := (f.comp s).1.toRingHom.toAlgebra
    let f' : (R : Type) →ₐ[(O : Type)] (R' : Type) := ⟨f.1.toRingHom, fun _ => rfl⟩
    have := congrArg (fun z => z.left ≫ φ) (hX.nat R R' f' a ha)
    exact (Category.assoc _ _ _).symm.trans this
  · letI := s.1.toRingHom.toAlgebra
    refine hX.inj R a b ha hb' ((hPb R s).1 ?_)
    exact (hY R s a).symm.trans ((congrArg (e R) hab).trans (hY R s b))
  · obtain ⟨z, hz⟩ := (hPb R s).2 (e R x)
    letI := s.1.toRingHom.toAlgebra
    letI := (π.comp s).1.toRingHom.toAlgebra
    let ρ : (R : Type) →ₐ[(O : Type)] (S : Type) := ⟨π.1.toRingHom, fun _ => rfl⟩
    let σ' : (S : Type) →ₐ[(O : Type)] (R : Type) :=
      ⟨σ.1.toRingHom, fun r => congrArg (fun u : LHom O R => u.1 r) hσ⟩
    have h1 : ρ.comp σ' = AlgHom.id _ _ := AlgHom.ext fun r => congrArg (fun u : LHom S S => u.1 r) hπσ
    have h2 : IsNilpotent (RingHom.ker ρ) := ⟨2, hπ.2⟩
    have h3 : spMap ρ ≫ z = 1 := by
      apply (hPb S (π.comp s)).1
      refine Eq.trans ?_ (map_one (P S (π.comp s))).symm
      rw [← h0, ← hx, hn, ← hz]
      apply Over.OverMorphism.ext
      rw [hP, Over.comp_left, Over.comp_left, hP]
      exact Category.assoc _ _ _
    obtain ⟨a, ha, hza⟩ := hX.surj R S ρ σ' h1 h2 z h3
    refine ⟨a, ha, (hb R).1 ?_⟩
    rw [hY, ← hz, hza]
  · apply (hb R).1
    letI := s.1.toRingHom.toAlgebra
    rw [hm, hY, hY, hY, ← map_mul]
    exact congrArg (P R s) (hX.law R a b ha hb')
  · apply (hb R).1
    apply Over.OverMorphism.ext
    letI := s.1.toRingHom.toAlgebra
    rw [← hA s (Y R s a) (X' R s a) (hYl R s a).symm, hYl]
    exact congrArg (fun z => z.left ≫ φ) (hr.2 R a ha)

end GlobalTheory.ChF
end
end
