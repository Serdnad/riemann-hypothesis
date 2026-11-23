module

public import Development.EtaleCohomology.TateTwists.Bundle014
public import Development.EtaleCohomology.TateTwists.Bundle015
public import Development.EtaleCohomology.TateTwists.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AwPf

abbrev sb {n : ℕ} (j l : ℕ) (h : j + l ≤ n) : SimplexCategory.mk l ⟶ SimplexCategory.mk n :=
  SimplexCategory.subinterval j l h

@[simp] lemma sb_apply {n : ℕ} (j l : ℕ) (h : j + l ≤ n) (i : Fin (l + 1)) :
    (((sb j l h).toOrderHom i : Fin (n + 1)) : ℕ) = i + j := rfl

lemma m_last (p r : ℕ) (h1 : 0 + (p + 1) ≤ p + r + 1) (h2 : 0 + p ≤ p + r + 1) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ sb 0 (p + 1) h1 = sb 0 p h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_zero (p r : ℕ) (h1 : p + (r + 1) ≤ p + r + 1) (h2 : (p + 1) + r ≤ p + r + 1) :
    SimplexCategory.δ 0 ≫ sb p (r + 1) h1 = sb (p + 1) r h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_lo (p r : ℕ) (k : Fin (p + r + 2)) (hk : (k : ℕ) ≤ p) (h1 : 0 + p ≤ p + r)
    (h2 : 0 + (p + 1) ≤ p + r + 1) :
    sb 0 p h1 ≫ SimplexCategory.δ k = SimplexCategory.δ (⟨k, by omega⟩ : Fin (p + 2)) ≫ sb 0 (p + 1) h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma simplex_subinterval_back_comp_face_within_front (p r : ℕ) (k : Fin (p + r + 2)) (hk : (k : ℕ) ≤ p) (h1 : p + r ≤ p + r)
    (h2 : (p + 1) + r ≤ p + r + 1) :
    sb p r h1 ≫ SimplexCategory.δ k = sb (p + 1) r h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_hi (p r : ℕ) (k : Fin (p + r + 2)) (hk : p < (k : ℕ)) (h1 : 0 + p ≤ p + r)
    (h2 : 0 + p ≤ p + r + 1) :
    sb 0 p h1 ≫ SimplexCategory.δ k = sb 0 p h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma simplex_subinterval_back_comp_face_above_front (p r : ℕ) (k : Fin (p + r + 2)) (hk : p < (k : ℕ)) (h1 : p + r ≤ p + r)
    (h2 : p + (r + 1) ≤ p + r + 1) :
    sb p r h1 ≫ SimplexCategory.δ k = SimplexCategory.δ (⟨k - p, by omega⟩ : Fin (r + 2)) ≫ sb p (r + 1) h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

def T (n p r : ℕ) (h : p + r ≤ n) : Pr n := ⟨p, r, sb 0 p (by omega), sb p r h⟩

noncomputable def S (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then Finsupp.single (T n x.1 x.2 h) 1 else 0

noncomputable def g1 (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then Pr.d₁ (T n x.1 x.2 h) else 0

noncomputable def g2 (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then (-1 : ℤ) ^ x.1 • Pr.d₂ (T n x.1 x.2 h) else 0

lemma aw_eq (n : ℕ) : Pr.aw n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, S n x := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range (fun k => S n (k, n - k))]
  unfold Pr.aw
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.isLt
  simp only [S]
  rw [dite_eq_left (by omega)]
  rfl

lemma bd_sum {N : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Pr N →₀ ℤ) :
    Pr.bd (∑ x ∈ s, g x) = ∑ x ∈ s, Pr.bd (g x) := by
  unfold Pr.bd

  simp only [map_sum, Finset.smul_sum]
  exact Finset.sum_comm

lemma d_S (n : ℕ) (x : ℕ × ℕ) : Pr.d n (S n x) = g1 n x + g2 n x := by
  unfold S g1 g2
  split_ifs with h
  · simp only [Pr.d, Finsupp.linearCombination_single, one_smul]
    rfl
  · simp

lemma split_sum {M : Type*} [AddCommMonoid M] (p r : ℕ) (f : Fin (p + r + 2) → M) :
    ∑ k, f k = ∑ i : Fin (p + 1), f ⟨i, by omega⟩ + ∑ j : Fin (r + 1), f ⟨p + 1 + j, by omega⟩ := by
  rw [← (finCongr (by omega : (p + 1) + (r + 1) = p + r + 2)).sum_comp, Fin.sum_univ_add]
  rfl

lemma bd_single (n : ℕ) (z : Pr n) : Pr.bd (Finsupp.single z 1) =
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • Finsupp.single
      (⟨z.1, z.2.1, z.2.2.1 ≫ SimplexCategory.δ k, z.2.2.2 ≫ SimplexCategory.δ k⟩ : Pr (n + 1)) 1 := by
  unfold Pr.bd
  simp [Pr.push]

lemma key (p r : ℕ) :
    Pr.d₁ (T (p + r + 1) (p + 1) r (by omega)) + (-1 : ℤ) ^ p • Pr.d₂ (T (p + r + 1) p (r + 1) (by omega)) =
      Pr.bd (Finsupp.single (T (p + r) p r le_rfl) 1) := by
  have e1 : Pr.d₁ (T (p + r + 1) (p + 1) r (by omega)) = ∑ i : Fin (p + 2),
      Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ sb 0 (p + 1) (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ (i : ℕ)) := rfl
  have e2 : Pr.d₂ (T (p + r + 1) p (r + 1) (by omega)) = ∑ j : Fin (r + 2),
      Finsupp.single (⟨p, r, sb 0 p (by omega), SimplexCategory.δ j ≫ sb p (r + 1) (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ (j : ℕ)) := rfl
  rw [e1, e2, bd_single, split_sum, Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := r + 1)]
  have hlo : ∀ i : Fin (p + 1),
      (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (⟨(T (p + r) p r le_rfl).1, (T (p + r) p r le_rfl).2.1,
        (T (p + r) p r le_rfl).2.2.1 ≫ SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + r + 2)),
        (T (p + r) p r le_rfl).2.2.2 ≫ SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + r + 2))⟩ : Pr (p + r + 1)) 1 =
      Finsupp.single (⟨p, r, SimplexCategory.δ i.castSucc ≫ sb 0 (p + 1) (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.castSucc i : Fin (p + 2)) : ℕ)) := by
    intro i
    have hi := i.isLt
    simp only [T]
    rw [m_lo p r _ (by show (i : ℕ) ≤ p; omega) _ (by omega), simplex_subinterval_back_comp_face_within_front p r _ (by show (i : ℕ) ≤ p; omega) _ (by omega),
      Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  have hhi : ∀ j : Fin (r + 1),
      (-1 : ℤ) ^ (p + 1 + (j : ℕ)) • Finsupp.single (⟨(T (p + r) p r le_rfl).1, (T (p + r) p r le_rfl).2.1,
        (T (p + r) p r le_rfl).2.2.1 ≫ SimplexCategory.δ (⟨p + 1 + j, by omega⟩ : Fin (p + r + 2)),
        (T (p + r) p r le_rfl).2.2.2 ≫ SimplexCategory.δ (⟨p + 1 + j, by omega⟩ : Fin (p + r + 2))⟩ : Pr (p + r + 1)) 1 =
      (-1 : ℤ) ^ p • Finsupp.single (⟨p, r, sb 0 p (by omega), SimplexCategory.δ j.succ ≫ sb p (r + 1) (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.succ j : Fin (r + 2)) : ℕ)) := by
    intro j
    have hj := j.isLt
    simp only [T]
    rw [m_hi p r _ (by show p < p + 1 + (j : ℕ); omega) _ (by omega), simplex_subinterval_back_comp_face_above_front p r _ (by show p < p + 1 + (j : ℕ); omega) _ (by omega),
      Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]
    have hf : (⟨p + 1 + (j : ℕ) - p, by omega⟩ : Fin (r + 2)) = j.succ := by
      ext; simp; omega
    rw [hf, Fin.val_succ]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun i _ => hlo i), Finset.sum_congr rfl (fun j _ => hhi j), ← Finset.smul_sum,
    m_last p r (by omega) (by omega), m_zero p r (by omega) (by omega), smul_add]
  have hc : Finsupp.single (⟨p, r, sb 0 p (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ)) +
      (-1 : ℤ) ^ p • Finsupp.single (⟨p, r, sb 0 p (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((0 : Fin (r + 2)) : ℕ)) = 0 := by
    rw [Finsupp.smul_single, ← Finsupp.single_add]
    simp [pow_succ]
  apply eq_of_sub_eq_zero
  rw [← hc]
  abel

theorem leaf_aw_of : LateralTheory.EtaleFoundations.SteenPf.leaf_aw := by
  intro N

  rw [aw_eq, aw_eq, map_sum, bd_sum]
  simp only [d_S]
  rw [Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  have z1 : g1 (N + 1) (0, N + 1) = 0 := by
    unfold g1; rw [dite_eq_left (by simp)]; rfl
  have z2 : g2 (N + 1) (N + 1, 0) = 0 := by
    unfold g2; rw [dite_eq_left (by simp)]
    show (-1 : ℤ) ^ (N + 1) • (0 : Pr (N + 1) →₀ ℤ) = 0
    exact smul_zero _
  rw [z1, z2, zero_add, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨p, r⟩ := x
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  simp only at hx
  subst hx
  unfold g1 g2 S
  rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega), dite_eq_left (by simp)]
  exact key p r

end LateralTheory.EtaleFoundations.AwPf
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem stair_loc_bind (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hSP⟩ := hP
  refine ⟨Sieve.bind S.arrows (fun V g hg => Classical.choose (h V g (hSP V g hg))), ?_, ?_⟩
  · exact (Scheme.etaleTopology).bind_covering hS (fun V g hg => (Classical.choose_spec (h V g (hSP V g hg))).1)
  · rintro W f ⟨V, k, g, hg, hk, rfl⟩
    exact (Classical.choose_spec (h V g (hSP V g hg))).2 W k hk

theorem stair_loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

theorem stair_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.map φ (Sec.res g y) = Sec.res g (Sec.map φ y) := by
  have := congrArg (fun m => (ModuleCat.Hom.hom m) y) (φ.hom.naturality g.op)
  simpa using this.symm

theorem stair_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y := by
  simp [Sec.res]

def EtaleTensorCyclesLocallyLiftOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    ∀ (w : ℤ) (U : Scheme.{0}) (x : Tens C J U w), Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ z : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z = Sec.res g (τ.lift U w x)

theorem etale_tensor_complex_locally_exact_of_lifted_sections (hL : EtaleTensorCyclesLocallyLiftOfFlatBounded) : EtaleTensorComplexLocallyExactOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC w U y hy
  refine stair_loc_bind U _ _ (hτ.1 U w y) ?_
  rintro V g ⟨x, hx⟩
  have hcyc : Sec.map (T.sc w).g (τ.lift V w x) = 0 := by
    have h1 := stair_map_res (T.sc w).g g y
    have h2 : Sec.map (T.sc w).g (τ.lift V w x) = Sec.map (T.sc w).g (Sec.res g y) := congrArg _ hx
    refine h2.trans (h1.trans ?_)
    rw [hy]
    simp
  refine stair_loc_mono V _ _ (hL R a b τ hτ hJ hC w V x hcyc) ?_
  rintro W k ⟨z, hz⟩
  refine ⟨z, ?_⟩
  exact hz.trans ((congrArg (Sec.res k) hx).trans (stair_res_res k g y))

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated

def SecSep : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U),
    (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b

lemma res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  exact congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op).symm

lemma res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ x y

lemma res_usmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (x : Sec F U) :
    Sec.res g (u • x) = u • Sec.res g x := by
  simp only [Units.smul_def]; exact map_zsmul _ _ x

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hP V g hg)⟩

lemma leib_lift {R : Type} [CommRing R] {I J K T M L : Cx R} (τ : Pair I J T) (μ' : Pair J K M) (ν' : Pair I M L)
    (m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U)
    (heq : ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c))
    (V : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (x : Tens I J V s) (b : Sec (K.X t) V) :
    Sec.map (L.d w (w + 1)) (m V s t w h (τ.lift V s x) b) = m V (s + 1) t (w + 1) (by omega) (Sec.map (T.d s (s + 1)) (τ.lift V s x)) b +
          s.negOnePow • m V s (t + 1) (w + 1) (by omega) (τ.lift V s x) (Sec.map (K.d t (t + 1)) b) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add (f := _), LinearMap.add_apply, smul_add, Sec.map] at hx hy ⊢
    rw [hx, hy]; abel
  | of p z =>
    obtain ⟨⟨s1, t1⟩, hp⟩ := p
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add (f := _), LinearMap.add_apply, smul_add, Sec.map] at hx hy ⊢
      rw [hx, hy]; abel
    | tmul a1 b1 =>
      have hl : τ.lift V s (DirectSum.of _ ⟨(s1, t1), hp⟩ (a1 ⊗ₜ b1)) = τ.mul V s1 t1 s hp a1 b1 := by
        unfold Pair.lift
        rw [← DirectSum.lof_eq_of (ULift.{1} R), DirectSum.toModule_lof, TensorProduct.lift.tmul]
      simp only at hp
      rw [hl, τ.leibniz V s1 t1 s hp a1 b1]
      rw [heq V s1 t1 t s (t1 + t) w hp h (by omega) (by omega)]
      rw [ν'.leibniz V s1 (t1 + t) w (by omega), μ'.leibniz V t1 t (t1 + t) rfl]
      simp only [map_add (f := _), LinearMap.add_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply]
      rw [heq V (s1 + 1) t1 t (s + 1) (t1 + t) (w + 1) (by omega) (by omega) (by omega) (by omega),
        heq V s1 (t1 + 1) t (s + 1) (t1 + t + 1) (w + 1) (by omega) (by omega) (by omega) (by omega),
        heq V s1 t1 (t + 1) s (t1 + t + 1) (w + 1) hp (by omega) (by omega) (by omega)]
      have hs : ((s.negOnePow : ℤˣ) : ℤ) = (s1.negOnePow : ℤ) * (t1.negOnePow : ℤ) := by
        rw [← Units.val_mul, ← Int.negOnePow_add, hp]
      rw [hs, mul_smul, smul_add]
      abel

end LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated

open LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated in
theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_leibniz_of_separated (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) :
    LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz := by
  intro R _ I J K T τ hτ M L μ' ν' m hnat heq U s t w h a b
  apply hsep R (L.X (w + 1)) U
  refine loc_mono (hτ.1 U s a) ?_
  rintro V g ⟨x, hx⟩
  rw [res_map, hnat, res_add, res_usmul, hnat, hnat, res_map, res_map, ← hx, leib_lift τ μ' ν' m heq]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.acyc

def LocAcyc {R : Type} [CommRing R] (C : Cx R) : Prop :=
  ∀ (U : Scheme.{0}) (n : ℤ) (z : Sec (C.X n) U), Sec.map (C.d n (n + 1)) z = 0 →
    Loc U fun V g => ∃ y : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) y = Sec.res g z

def ColExact {R : Type} [CommRing R] (C J : Cx R) : Prop :=
  ∀ (U : Scheme.{0}) (s t : ℤ) (x : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U),
    TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id x = 0 →
    Loc U fun V g => ∃ y : Sec (C.X (s - 1)) V ⊗[ULift.{1} R] Sec (J.X t) V,
      TensorProduct.map ((C.d (s - 1) s).hom.app (op V)).hom LinearMap.id y =
        TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom x

def acycIff : Prop := ∀ (R : Type) [CommRing R] (C : Cx R), C.Acyclic ↔ LocAcyc C

def column : Prop := ∀ (R : Type) [CommRing R] (C J : Cx R), (∀ t, FlatS (J.X t)) → LocAcyc C → ColExact C J

def stair : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → ColExact C J → LocAcyc T

end LateralTheory.EtaleFoundations.acyc

open LateralTheory.EtaleFoundations.acyc in
theorem LateralTheory.EtaleFoundations.tqis.acyc_of (hI : acycIff) (hC : column) (hS : stair) : LateralTheory.EtaleFoundations.tqis.acyc := by
  intro R _ C J T a b _ _ τ hτ hJ hCa
  exact (hI R T).2 (hS R a b τ hτ (hC R C J hJ ((hI R C).1 hCa)))
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

theorem kt_mono_sh (q : ℕ) (T G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G)
    (hι : ∀ A, Function.Injective (ι.app A).hom) :
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι)) := by
  have : ∀ U, Mono ((Functor.whiskerLeft Scheme.Γ ι).app U) := fun U =>
    (ModuleCat.mono_iff_injective _).2 (hι _)
  have : Mono (Functor.whiskerLeft Scheme.Γ ι) := NatTrans.mono_of_mono_app _
  infer_instance

theorem kt_res_sec (q : ℕ) (G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (V U : Scheme.{0}) (g : V ⟶ U)
    (x : G.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec (R := ZMod q) G U x) = ofRings.sec (R := ZMod q) G V ((G.map g.appTop).hom x) := by
  unfold Sec.res ofRings.sec ofRings
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x)
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ G)).naturality g.op)
  exact this.symm

theorem kt_map_sec (q : ℕ) (T G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G) (U : Scheme.{0})
    (x : T.obj Γ(U, ⊤)) :
    Sec.map ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι))
      (ofRings.sec (R := ZMod q) T U x) = ofRings.sec (R := ZMod q) G U ((ι.app _).hom x) := by
  unfold Sec.map ofRings.sec
  have := congrArg (fun f => (ModuleCat.Hom.hom (NatTrans.app f (op U))) x)
    (toSheafify_naturality Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ ι))
  exact this.symm

def MuTwistQuotientEmbedsInUnitTorsorPresheaf : Prop :=
  ∀ (q : ℕ) [NeZero q] (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    (∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) →
    ∃ (G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G),
      (∀ A, Function.Injective (ι.app A).hom) ∧
      ∃ s : ∀ A : CommRingCat.{0}, Aˣ → G.obj A,
        (∀ (A B : CommRingCat.{0}) (f : A ⟶ B) (v : Aˣ), (G.map f).hom (s A v) = s B (Units.map f.hom.toMonoidHom v)) ∧
        ∀ (A : CommRingCat.{0}) (ζ : Prim q A) (v w : Aˣ), (w : A) = ζ.1 * v →
          s A w = s A v + (ι.app A).hom ((τ.app A).hom (twGenR A ζ))

theorem etale_mu_twist_mono_extends_of_presheaf_torsor_embedding (hpre : MuTwistQuotientEmbedsInUnitTorsorPresheaf) : EtaleMuTwistMonoExtendsToTorsorSheaf := by
  intro q _ T τ hm hl
  obtain ⟨G, ι, hι, s, hs, hr⟩ := hpre q T τ hl
  have hmι := kt_mono_sh q T G ι hι
  refine ⟨ofRings (ZMod q) G, (presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ) ≫
    (presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι), @mono_comp _ _ _ _ _ _ hm _ hmι,
    fun U v => ofRings.sec (R := ZMod q) G U (s _ v), ?_, ?_⟩
  · intro V U g v _
    rw [kt_res_sec]
    exact congrArg _ (hs _ _ g.appTop v)
  · intro U ζ v w h
    beta_reduce
    rw [hr _ ζ v w h]
    rw [show ofRings.sec (R := ZMod q) G U (s _ v + (ι.app _).hom ((τ.app _).hom (twGenR _ ζ))) =
      ofRings.sec (R := ZMod q) G U (s _ v) + ofRings.sec (R := ZMod q) G U ((ι.app _).hom ((τ.app _).hom (twGenR _ ζ))) by
        unfold ofRings.sec
        exact map_add _ _ _]
    congr 1
    exact ((kt_map_sec q T G ι U _).symm.trans (congrArg _ (kt_map_sec q (twF q 1) T τ U (twGenR _ ζ)).symm))

theorem exists_etale_mono_mu_twist_into_torsor_sheaf_of_presheaf (h1 : ExistsEtaleMonoMuTwistKillingRootRelations) (h2 : MuTwistQuotientEmbedsInUnitTorsorPresheaf) :
    EtaleKummerSectionsIntoTwistEmbeddingExist :=
  exists_etale_mono_muTwist_into_torsorSheaf h1 (etale_mu_twist_mono_extends_of_presheaf_torsor_embedding h2)
end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_kInjective_hom_lift_along_quasiIso_holds : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy := by
  intro R _ K L I _ f _
  have hI := CochainComplex.IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hI
  have hf : (HomotopyCategory.subcategoryAcyclic (Shv R)).trW
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance
  have hb := hI _ hf
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨m', hm'⟩ := hb.2 ((HomotopyCategory.quotient _ _).map a)
    obtain ⟨m, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective m'
    refine ⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
    rw [Functor.map_comp]; exact hm'
  · obtain ⟨h⟩ := h
    have e := HomotopyCategory.eq_of_homotopy _ _ h
    rw [Functor.map_comp, Functor.map_comp] at e
    exact ⟨HomotopyCategory.homotopyOfEq _ _ (hb.1 e)⟩
end
