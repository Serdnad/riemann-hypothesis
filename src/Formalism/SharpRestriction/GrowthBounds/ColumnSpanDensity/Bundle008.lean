module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundLargeConductor
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.PolynomialDimension.Bundle001

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem letterWt_anti (m d : ℕ) (b : Bool) : Antitone (letterWt m d b) := by
  intro i j hij
  cases b
  · simp only [letterWt, Bool.false_eq_true, if_false]
    by_cases hi : i = Fin.last m
    · have hj : j = Fin.last m := le_antisymm (Fin.le_last j) (hi ▸ hij)
      simp [hi, hj]
    · simp only [hi, if_false]
      split_ifs <;> omega
  · simp only [letterWt, if_true]
    by_cases hj : j = 0
    · have hi : i = 0 := le_antisymm (hj ▸ hij) (Fin.zero_le i)
      simp [hj, hi]
    · simp only [hj, if_false]
      split_ifs <;> omega

theorem twoLat_le_twoSp {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m P Q : ℕ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) (hΛ : IsLattice O Λ) :
    ∀ x ∈ twoLat O m P Q Λ, x ∈ twoSp Kf m P Q := by
  obtain ⟨g, hg, hΛg⟩ := hΛ
  have hsub : ∀ b : Bool, ∀ F ∈ H0 O m (letterWt m (if b then P else Q) b) Λ,
      F ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m (if b then P else Q) b)) := by
    intro b F hF
    have hle := H0_le_twisted_nabla (O := O) m _ (letterWt_anti m (if b then P else Q) b) g hg
    rw [← hΛg] at hle
    exact la_nablaLTw_le m _ g hg F (hle hF)
  intro x hx
  unfold twoLat tensorLat at hx
  unfold twoSp tensorLat
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    exact Submodule.subset_span ⟨F, fun b => hsub b (F b) (hF b), rfl⟩
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul c y _ hy => exact Submodule.smul_of_tower_mem _ c hy

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility MvPolynomial

theorem P_rev (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hF : F ∈ nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w))) :
    (algebraMap O Kf w ^ (-(((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) *
      lam (Fin.last m)))) • F ∈ nablaLTw O Kf m lam g := by
  classical
  set c : Kf := algebraMap O Kf w with hc
  set ν : Fin (m + 1) → ℕ := fun t => (lam t - lam (Fin.last m)).toNat with hν
  set e : ℤ := lam (Fin.last m) with he
  obtain ⟨b, hb, -⟩ := lb_basis O (m + 1) (m + 1) ν
  set t : Fin (m + 1) → Kf := fun a => if a.val < r then c⁻¹ else 1 with ht
  have ht0 : ∀ a, t a ≠ 0 := by
    intro a
    simp only [ht]
    split_ifs
    · exact inv_ne_zero hw
    · exact one_ne_zero
  have hB := (nablaLBasis O Kf hinj (m + 1) (m + 1) ν b _ hb g hg).2
  have hD := (nablaLDiag O Kf hinj (m + 1) (m + 1) ν b _ hb g t hg ht0).2
  have hle : nablaL O Kf (m + 1) (m + 1) ν (g * Matrix.diagonal t) ≤ nablaL O Kf (m + 1) (m + 1) ν g := by
    rw [← hD, ← hB, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    set Fi := rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)) with hFi
    set π' : ℕ := ∑ a : Fin (m + 1) with a.val < r, rowWt i.1 a with hπ
    have h2 : ∏ a, t a ^ rowWt i.1 a = (c⁻¹) ^ π' := by
      rw [hπ, ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro a _
      simp only [ht]
      split_ifs <;> simp
    have h6 : ((c⁻¹) ^ π')⁻¹ = c ^ π' := by rw [inv_pow, inv_inv]
    show (∏ a, t a ^ rowWt i.1 a)⁻¹ • Fi ∈ _
    rw [h2, h6, hc, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨F0, hF0, rfl⟩ := hF
  refine ⟨F0, hle hF0, ?_⟩
  set ρ : ℕ := (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card with hρ
  show g.det ^ (-e) • F0 = c ^ (-((ρ : ℤ) * e)) • ((g * lb_D (m + 1) r c).det ^ (-e) • F0)
  have h1 : (g * lb_D (m + 1) r c).det = g.det * (c⁻¹) ^ ρ := by
    rw [Matrix.det_mul, lb_D, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one]
  have h5 : ((c⁻¹) ^ ρ) ^ (-e) = c ^ ((ρ : ℤ) * e) := by
    rw [inv_pow, inv_zpow, zpow_neg, inv_inv, ← zpow_natCast c ρ, ← zpow_mul]
  rw [smul_smul, h1, mul_zpow, h5, mul_comm (g.det ^ (-e)), ← mul_assoc, ← zpow_add₀ hw, neg_add_cancel, zpow_zero,
    one_mul]

theorem zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hF : F ∈ H0 O m lam (colSpan O (g * lb_D (m + 1) r (algebraMap O Kf w)))) :
    (algebraMap O Kf w ^ (-(((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) *
      lam (Fin.last m)))) • F ∈ H0 O m lam (colSpan O g) := by
  have hgD : IsUnit (g * lb_D (m + 1) r (algebraMap O Kf w)).det := by
    rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ _ hw)
  unfold H0 at hF ⊢
  rw [if_pos hlam] at hF ⊢
  have h1 : F ∈ nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) :=
    (iInf₂_le _ ⟨hgD, rfl⟩ : _ ≤ nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w))) hF
  have h2 := P_rev O Kf hinj m r lam w hw g hg F h1
  exact (le_iInf₂ fun h hh => lb_indep O Kf hinj m lam _ h hg hh.1 hh.2 : nablaLTw O Kf m lam g ≤ _) h2

section RSLat

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

theorem extO_RS (s : ℕ) {k : ℕ} (g : Matrix (Fin k) (Fin k) R.Qq) :
    extO R.O R.ι R.σ s (colSpan R.W g) = colSpan R.O (la_tw R.ι R.σ s g) :=
  la_extO R.ι R.σ R.jO (fun x => by obtain ⟨y, hy⟩ := R.std.1.frob x; exact ⟨_, hy⟩) R.std.1.ι_comp s g

theorem tw_p (s : ℕ) {k : ℕ} (x : Fin k → R.Qq) (i : Fin k) :
    twistVec R.ι R.σ s ((p : R.W) • x) i = (p : R.Kf) * R.ι ((R.σ ^ s) (x i)) := by
  show R.ι ((R.σ ^ s) ((p : R.W) • x i)) = _
  rw [Algebra.smul_def, map_natCast, map_mul, map_mul, map_natCast, map_natCast]

theorem edgeLat_RS (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) :
    ∃ gs : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf, (∀ s, IsUnit (gs s).det) ∧
      (∀ s, extO R.O R.ι R.σ s e.src = colSpan R.O (gs s)) ∧
      (∀ s, LeAt p R.ι R.σ R.w s e = colSpan R.O (gs s * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w))) ∧
      (∀ s, extO R.O R.ι R.σ s e.tgt =
        colSpan R.O (gs s * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w) * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w))) := by
  have hfrW : IsFractionRing R.W R.Qq := R.std.1.frac_alt
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e he
  unfold lb_D
  set c : R.Kf := algebraMap R.O R.Kf R.w with hc
  have hw : c ≠ 0 := R.w_ne
  have hpK : (p : R.Kf) = c ^ 2 := R.p_eq
  have hpK0 : (p : R.Kf) ≠ 0 := by rw [hpK]; exact pow_ne_zero _ hw
  have hpQ0 : (p : R.Qq) ≠ 0 := by
    intro h0
    apply hpK0
    have := congrArg R.ι h0
    simpa using this
  set dK : Fin (m + 1) → R.Kf := fun a => if a.val < 1 then c⁻¹ else 1 with hdK
  set dQ : Fin (m + 1) → R.Qq := fun a => if a.val < 1 then ((p : R.Qq))⁻¹ else 1 with hdQ
  have hDD : ∀ s, la_tw R.ι R.σ s (g * Matrix.diagonal dQ) =
      la_tw R.ι R.σ s g * Matrix.diagonal dK * Matrix.diagonal dK := by
    intro s
    ext i j
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal, lb_tw_apply, lb_tw_apply,
      Matrix.mul_diagonal, map_mul, map_mul]
    congr 1
    simp only [hdQ, hdK]
    split_ifs
    · rw [map_inv₀, map_inv₀, map_natCast, map_natCast, hpK, pow_two, mul_inv]
    · simp
  have e1 : ∀ s, extO R.O R.ι R.σ s e.src = colSpan R.O (la_tw R.ι R.σ s g) :=
    fun s => by rw [hsrc]; exact extO_RS R s g
  have e3 : ∀ s, extO R.O R.ι R.σ s e.tgt =
      colSpan R.O (la_tw R.ι R.σ s g * Matrix.diagonal dK * Matrix.diagonal dK) :=
    fun s => by rw [htgt, extO_RS R, hDD]
  refine ⟨fun s => la_tw R.ι R.σ s g, fun s => la_tw_det _ _ s g hg, e1, ?_, e3⟩
  intro s
  set gK := la_tw R.ι R.σ s g with hgK
  apply le_antisymm
  · unfold LeAt
    refine sup_le ?_ ?_
    · rw [e1]
      intro x hx
      have h1 : gK = gK * Matrix.diagonal dK *
          Matrix.diagonal (fun a : Fin (m + 1) => if a.val < 1 then c else 1) := by
        rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
        have h2 : (fun a : Fin (m + 1) => dK a * (if a.val < 1 then c else 1)) = fun _ => 1 := by
          funext a
          simp only [hdK]
          split_ifs
          · exact inv_mul_cancel₀ hw
          · simp
        rw [h2, Matrix.diagonal_one, Matrix.mul_one]
      have hx' : x ∈ colSpan R.O gK := hx
      rw [h1] at hx'
      have h3 := lb_col (gK * Matrix.diagonal dK) _
        (fun a : Fin (m + 1) => if a.val < 1 then R.w else 1) 1
        (by intro j; split_ifs <;> simp [hc]) x hx'
      rw [one_smul] at h3
      exact h3
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : c⁻¹ • twistVec R.ι R.σ s ((p : R.W) • x) =
          R.w • twistVec R.ι R.σ s x := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply, tw_p R, smul_eq_mul, Algebra.smul_def, ← hc, hpK]
        show c⁻¹ * (c ^ 2 * _) = c * R.ι ((R.σ ^ s) (x i))
        field_simp
      have h2 : twistVec R.ι R.σ s x ∈
          colSpan R.O (gK * Matrix.diagonal dK * Matrix.diagonal dK) := by
        rw [← e3]; exact Submodule.subset_span ⟨x, hx, rfl⟩
      show c⁻¹ • twistVec R.ι R.σ s ((p : R.W) • x) ∈ _
      rw [h1]
      exact lb_col (gK * Matrix.diagonal dK) dK
        (fun a : Fin (m + 1) => if a.val < 1 then 1 else R.w) R.w
        (by
          intro j
          simp only [hdK]
          split_ifs
          · rw [← hc, mul_inv_cancel₀ hw, map_one]
          · rw [mul_one]) _ h2
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    unfold LeAt
    by_cases hj : j.val < 1
    · apply Submodule.mem_sup_right
      apply Submodule.subset_span
      refine ⟨fun i => (g * Matrix.diagonal dQ) i j, ?_, ?_⟩
      · rw [htgt]; exact Submodule.subset_span ⟨j, rfl⟩
      · funext i
        show c⁻¹ • twistVec R.ι R.σ s
          ((p : R.W) • fun i => (g * Matrix.diagonal dQ) i j) i = (gK * Matrix.diagonal dK) i j
        rw [tw_p R, Matrix.mul_diagonal, Matrix.mul_diagonal, smul_eq_mul, hgK, lb_tw_apply]
        simp only [hdQ, hdK, hj, if_true, map_mul, map_inv₀, map_natCast]
        field_simp
    · apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine ⟨fun i => g i j, ?_, ?_⟩
      · rw [hsrc]; exact Submodule.subset_span ⟨j, rfl⟩
      · funext i
        simp only [twistVec, Matrix.mul_diagonal, hdK, hj, if_false, mul_one, lb_tw_apply]

end RSLat

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

section Gen

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}

def emb (w : Fin k → W) : Fin k → Qq := fun i => algebraMap W Qq (w i)

abbrev mapM (N : Matrix (Fin k) (Fin k) W) : Matrix (Fin k) (Fin k) Qq := (algebraMap W Qq).mapMatrix N

theorem mem_colSpan_iff (h : Matrix (Fin k) (Fin k) Qq) (x : Fin k → Qq) :
    x ∈ colSpan W h ↔ ∃ y : Fin k → W, x = fun i => ∑ c, h i c * algebraMap W Qq (y c) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [Finset.sum_apply, Algebra.smul_def, mul_comm]

theorem colSpan_mul_le (h : Matrix (Fin k) (Fin k) Qq) (N : Matrix (Fin k) (Fin k) W) :
    colSpan W (h * mapM N) ≤ colSpan W h := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, rfl⟩
  refine (mem_colSpan_iff h _).2 ⟨fun j => N j c, funext fun i => ?_⟩
  simp [Matrix.mul_apply, mapM, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem colSpan_unimod (h : Matrix (Fin k) (Fin k) Qq) (N : Matrix (Fin k) (Fin k) W) (hN : IsUnit N.det) :
    colSpan W (h * mapM N) = colSpan W h := by
  refine le_antisymm (colSpan_mul_le h N) ?_
  have h1 : h * mapM N * mapM N⁻¹ = h := by
    rw [Matrix.mul_assoc, ← map_mul, Matrix.mul_nonsing_inv N hN, map_one, Matrix.mul_one]
  calc colSpan W h = colSpan W (h * mapM N * mapM N⁻¹) := by rw [h1]
    _ ≤ colSpan W (h * mapM N) := colSpan_mul_le _ _

theorem map_colSpan (g : GL (Fin k) Qq) (h : Matrix (Fin k) (Fin k) Qq) :
    (colSpan W h).map (nt_phi W g) = colSpan W ((g : Matrix (Fin k) (Fin k) Qq) * h) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

def dj (j : Fin k) (c : Qq) : Matrix (Fin k) (Fin k) Qq := Matrix.diagonal fun i => if i = j then c else 1

theorem dj_det (j : Fin k) (c : Qq) : (dj j c).det = c := by
  simp [dj, Matrix.det_diagonal]

theorem dj_mul (j : Fin k) (c d : Qq) : dj j c * dj j d = dj j (c * d) := by
  simp only [dj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem dj_one (j : Fin k) : dj j (1 : Qq) = 1 := by
  simp [dj]

end Gen

section Base

variable {p n' : ℕ} (R : RS p n') {k : ℕ}

theorem RS.injW : Function.Injective (algebraMap R.W R.Qq) := by
  haveI := R.std.1.frac_alt
  exact IsFractionRing.injective R.W R.Qq

theorem RS.pQ_ne : (p : R.Qq) ≠ 0 := by
  have h1 : (p : R.W) ≠ 0 := R.std.1.p_unif.ne_zero
  rw [← map_natCast (algebraMap R.W R.Qq)]
  exact fun h => h1 ((map_eq_zero_iff _ (RS.injW R)).1 h)

def embLin (R : RS p n') (k : ℕ) : (Fin k → R.W) →ₗ[R.W] (Fin k → R.Qq) where
  toFun := emb
  map_add' := by intro x y; funext i; simp [emb]
  map_smul' := by intro c x; funext i; simp [emb, Algebra.smul_def]

theorem embLin_inj : Function.Injective (embLin R k) := by
  intro x y hxy
  funext i
  exact RS.injW R (congrFun hxy i)

theorem colSpan_one_eq : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) = LinearMap.range (embLin R k) := by
  ext x
  rw [mem_colSpan_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [embLin, emb, Matrix.one_apply]
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [embLin, emb, Matrix.one_apply]

theorem mem_dj_iff (j : Fin k) (x : Fin k → R.Qq) :
    x ∈ colSpan R.W (dj j (p : R.Qq)) ↔ ∃ y : Fin k → R.W, x = emb (fun i => (if i = j then (p : R.W) else 1) * y i) := by
  rw [mem_colSpan_iff]
  constructor <;> rintro ⟨y, rfl⟩ <;> refine ⟨y, funext fun i => ?_⟩ <;>
    by_cases hij : i = j <;> simp [dj, emb, Matrix.diagonal_apply, hij]

theorem baseEdge (j : Fin k) :
    IsEdge p n' 1 (⟨colSpan R.W (dj j (p : R.Qq)), colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)⟩ :
      Edge R.W R.Qq k) := by
  classical
  have hstd := R.std.1
  have htgt : ∀ x, x ∈ colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ↔ ∃ y, embLin R k y = x := by
    intro x
    rw [colSpan_one_eq R]
    exact LinearMap.mem_range
  have hsrc : ∀ x, x ∈ colSpan R.W (dj j (p : R.Qq)) ↔
      ∃ y : Fin k → R.W, x = emb y ∧ y j ∈ Ideal.span {(p : R.W)} := by
    intro x
    rw [mem_dj_iff R]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨_, rfl, ?_⟩
      simp only [if_pos rfl]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rintro ⟨y, rfl, hy⟩
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hy
      refine ⟨fun i => if i = j then z else y i, ?_⟩
      congr 1
      funext i
      by_cases hij : i = j
      · subst hij
        simp [← hz, mul_comm]
      · simp [hij]
  let e := LinearEquiv.ofInjective (embLin R k) (embLin_inj R)
  let E : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ≃ₗ[R.W] (Fin k → R.W) :=
    (LinearEquiv.ofEq _ _ (colSpan_one_eq R)).trans e.symm
  have hE : ∀ x, emb (E x) = (x : Fin k → R.Qq) := by
    intro x
    have h2 := congrArg Subtype.val (e.apply_symm_apply (LinearEquiv.ofEq _ _ (colSpan_one_eq R) x))
    rw [LinearEquiv.ofInjective_apply] at h2
    exact h2
  let ψ : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) →ₗ[R.W] R.W ⧸ Ideal.span {(p : R.W)} :=
    (Ideal.span {(p : R.W)}).mkQ ∘ₗ LinearMap.proj j ∘ₗ E.toLinearMap
  have hψ : ∀ x, ψ x = (Submodule.Quotient.mk (E x j) : R.W ⧸ Ideal.span {(p : R.W)}) := fun x => rfl
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨E.symm (Pi.single j a), ?_⟩
    rw [hψ, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
  have hker : Submodule.comap (colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)).subtype
      (colSpan R.W (dj j (p : R.Qq))) = LinearMap.ker ψ := by
    ext x
    rw [Submodule.mem_comap, LinearMap.mem_ker, hψ, Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, hsrc]
    constructor
    · rintro ⟨y, hy, hyj⟩
      have hxy : E x = y := embLin_inj R ((hE x).trans hy)
      rw [hxy]
      exact hyj
    · intro h
      exact ⟨E x, (hE x).symm, h⟩
  refine ⟨⟨dj j (p : R.Qq), ?_, rfl⟩, ⟨1, by simp, rfl⟩, ?_, ?_, ?_⟩
  · rw [dj_det]
    exact isUnit_iff_ne_zero.2 (RS.pQ_ne R)
  · intro x hx
    obtain ⟨y, rfl, -⟩ := (hsrc x).1 hx
    exact (htgt _).2 ⟨y, rfl⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := (htgt x).1 hx
    refine (hsrc _).2 ⟨(p : R.W) • y, ?_, ?_⟩
    · funext i
      simp [embLin, emb, Algebra.smul_def]
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · show Nat.card (↥(colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)) ⧸
      Submodule.comap (colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)).subtype
        (colSpan R.W (dj j (p : R.Qq)))) = p ^ (n' * 1)
    rw [hker, Nat.card_congr (ψ.quotKerEquivOfSurjective hsurj).toEquiv, hstd.res_card, mul_one]

end Base

end Formalism.MainNotions.flipOneThree.Pf

end
end
