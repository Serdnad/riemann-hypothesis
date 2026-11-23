module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SecondProjectionOrthogonalComplement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle002

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

lemma act_omega_expand {dim : (E →+* ℂ) → ℕ} (ω : Fin (Module.finrank ℚ E) → 𝓞 E)
    (hω : LinearIndependent ℚ (fun j => (ω j : E))) (α : 𝓞 E) (y : Vsp dim) :
    act α y ∈ Submodule.span ℝ (Set.range fun j => act (ω j) y) := by
  classical
  have hsp : Submodule.span ℚ (Set.range fun j => (ω j : E)) = ⊤ :=
    by
      first
      | exact hω.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)
      | (haveI : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
         exact hω.span_eq_top_of_card_eq_finrank (Fintype.card_fin _))
  have hα : (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)) := by
    rw [hsp]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℚ E) → ℚ, ∑ j, c j • (ω j : E) = α := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 hα
    | exact Submodule.mem_span_range_iff_exists_fun.1 hα
  have key : act α y = ∑ j, ((c j : ℝ)) • act (ω j) y := by
    ext i
    simp only [act, ← hc]

    simp [map_sum, Rat.smul_def, map_mul, map_ratCast, Finset.sum_mul, Complex.real_smul, mul_assoc]
  rw [key]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma rank_bound {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim))
    (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (hact : ∀ (α : 𝓞 E) u, u ∈ Xg L I → act α u ∈ Xg L I)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (σ : E →+* ℂ) (b : Set (Vsp dim)) [Fintype b] (hb : b ⊆ prj σ '' (Xg L I))
    (hli : LinearIndependent ℂ (fun s : b => (s : Vsp dim))) :
    Module.finrank ℚ E * Fintype.card b ≤ Module.finrank ℝ (IR I) := by
  classical
  have hpre : ∀ s : b, ∃ u, u ∈ Xg L I ∧ prj σ u = (s : Vsp dim) := by
    intro s
    obtain ⟨u, hu, h⟩ := hb s.2
    exact ⟨u, hu, h⟩
  choose u hu hus using hpre
  let v : Fin (Module.finrank ℚ E) × b → Vsp dim := fun p => act (ω p.1) (u p.2)
  have hvX : ∀ p, v p ∈ Xg L I := fun p => hact _ _ (hu p.2)
  have hvIR : ∀ p, v p ∈ IR I := by
    intro p
    have h : ∃ x ∈ L, IsU I x (v p) := hvX p
    obtain ⟨x, _, hx⟩ := h
    exact hx.1
  have hprj : ∀ (α : 𝓞 E) (w : Vsp dim), prj σ (act α w) = σ (α : E) • prj σ w := by
    intro α w
    ext i
    by_cases h : i.1 = σ
    · simp [prj, act_apply, h]
    · simp [prj, h]

  have hZ : ∀ m : Fin (Module.finrank ℚ E) × b → ℤ, ∑ p, m p • v p = 0 → ∀ p, m p = 0 := by
    intro m hm
    have h1 : ∑ s : b, (∑ j, ((m (j, s) : ℂ) * σ (ω j : E))) • (s : Vsp dim) = 0 := by
      have := congrArg (prj σ) hm

      rw [map_sum, map_zero] at this
      rw [← this, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      show _ = prj σ (m (j, s) • act (ω j) (u s))
      rw [map_zsmul, hprj, hus, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    rintro ⟨j, s⟩
    have h2 := Fintype.linearIndependent_iff.mp hli
      (fun s => ∑ j, ((m (j, s) : ℂ) * σ (ω j : E))) h1 s
    have h3 : σ (∑ j, ((m (j, s) : E)) * (ω j : E)) = 0 := by

      rw [map_sum]; simpa [map_mul, map_intCast] using h2
    have h4 : ∑ j, ((m (j, s) : ℚ)) • (ω j : E) = 0 := by
      have h5 := (map_eq_zero_iff σ σ.injective).mp h3
      simpa [Rat.smul_def] using h5
    have h6 := Fintype.linearIndependent_iff.mp hω (fun j => (m (j, s) : ℚ)) h4 j
    exact_mod_cast h6

  have hR : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc p
    by_contra hcp
    let y : ℕ → Vsp dim := fun k => -(∑ q, ⌊(k : ℝ) * c q⌋ • v q)
    have hyX : ∀ k, y k ∈ Xg L I := fun k =>
      neg_mem (sum_mem fun q _ => zsmul_mem (hvX q) _)
    have hyeq : ∀ k : ℕ, y k = ∑ q, Int.fract ((k : ℝ) * c q) • v q := by
      intro k
      have h0 : ∑ q, ((k : ℝ) * c q) • v q = 0 := by
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, hc, smul_zero]
      simp only [y, Int.fract, sub_smul, Finset.sum_sub_distrib, h0, zero_sub]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
    have hyn : ∀ k, ‖y k‖ ≤ ∑ q, ‖v q‖ := by
      intro k
      rw [hyeq]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    have hfin : {x | x ∈ (Xg L I : Set (Vsp dim)) ∧ ‖x‖ ≤ ∑ q, ‖v q‖}.Finite :=
      finite_sep _ (sep_of_group (Xg L I) hsep _ subset_rfl) _
    let g : ℕ → (Fin (Module.finrank ℚ E) × b → ℤ) := fun k q => ⌊(k : ℝ) * c q⌋
    let Φ : (Fin (Module.finrank ℚ E) × b → ℤ) → Vsp dim := fun m => -(∑ q, m q • v q)
    have hΦ : Function.Injective Φ := by
      intro m m' h
      have h' : ∑ q, m q • v q = ∑ q, m' q • v q := neg_inj.mp h
      have h'' : ∑ q, (m q - m' q) • v q = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, h', sub_self]
      funext q
      exact sub_eq_zero.mp (hZ _ h'' q)
    have hrg : (Set.range g).Finite := by
      refine Set.Finite.of_finite_image ?_ hΦ.injOn
      refine hfin.subset ?_
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨hyX k, hyn k⟩
    have hrp : (Set.range fun k : ℕ => ⌊(k : ℝ) * c p⌋).Finite :=
      (hrg.image (fun m => m p)).subset (by rintro _ ⟨k, rfl⟩; exact ⟨g k, ⟨k, rfl⟩, rfl⟩)
    obtain ⟨B, hB⟩ := hrp.bddAbove
    obtain ⟨B', hB'⟩ := hrp.bddBelow
    have hcpos : 0 < |c p| := abs_pos.mpr hcp
    obtain ⟨k, hk⟩ := exists_nat_gt ((|(B : ℝ)| + |(B' : ℝ)| + 2) / |c p|)
    have hkc : |(B : ℝ)| + |(B' : ℝ)| + 2 < (k : ℝ) * |c p| := by
      rwa [div_lt_iff₀ hcpos] at hk
    have hup : ⌊(k : ℝ) * c p⌋ ≤ B := hB ⟨k, rfl⟩
    have hlo : B' ≤ ⌊(k : ℝ) * c p⌋ := hB' ⟨k, rfl⟩
    have h1 : (k : ℝ) * c p - 1 < (⌊(k : ℝ) * c p⌋ : ℝ) := Int.sub_one_lt_floor _
    have h2 : (⌊(k : ℝ) * c p⌋ : ℝ) ≤ (k : ℝ) * c p := Int.floor_le _
    have hup' : (⌊(k : ℝ) * c p⌋ : ℝ) ≤ B := by exact_mod_cast hup
    have hlo' : (B' : ℝ) ≤ ⌊(k : ℝ) * c p⌋ := by exact_mod_cast hlo
    have hB0 := abs_nonneg (B : ℝ)
    have hB'0 := abs_nonneg (B' : ℝ)
    rcases lt_or_gt_of_ne hcp with hneg | hpos
    · rw [abs_of_neg hneg, mul_neg] at hkc
      have := neg_abs_le (B' : ℝ)
      linarith
    · rw [abs_of_pos hpos] at hkc
      have := le_abs_self (B : ℝ)
      linarith
  have hw : LinearIndependent ℝ (fun p => (⟨v p, hvIR p⟩ : IR I)) :=
    LinearIndependent.of_comp (IR I).subtype hR
  have := hw.fintype_card_le_finrank
  simpa [Fintype.card_prod, Fintype.card_fin] using this

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def Zs {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (μ : ℝ) : Submodule ℝ (Vsp dim) :=
  Submodule.span ℝ {x | ∃ α : 𝓞 E, ∃ y ∈ Xg L I, ‖y‖ ≤ μ ∧ x = act α y}

lemma Zs_mono {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) {μ μ' : ℝ} (h : μ ≤ μ') :
    Zs L I μ ≤ Zs L I μ' := Submodule.span_mono fun _ ⟨α, y, hy, hyμ, hx⟩ => ⟨α, y, hy, hyμ.trans h, hx⟩

lemma Zs_self {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) {μ : ℝ} {y : Vsp dim}
    (hy : y ∈ Xg L I) (hμ : ‖y‖ ≤ μ) : y ∈ Zs L I μ := by
  refine Submodule.subset_span ⟨1, y, hy, hμ, ?_⟩
  ext i
  simp [act]

private lemma act_add_lemma {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (x y : Vsp dim) :
    act β (x + y) = act β x + act β y := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_smul_lemma_2 {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (r : ℝ) (x : Vsp dim) :
    act β (r • x) = r • act β x := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_zero_lemma_4 {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) : act β (0 : Vsp dim) = 0 := by
  ext i
  simp [act]

private lemma act_mul_lemma_5 {dim : (E →+* ℂ) → ℕ} (β α : 𝓞 E) (y : Vsp dim) :
    act β (act α y) = act (β * α) y := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_span_lemma_3 {dim : (E →+* ℂ) → ℕ} (S : Set (Vsp dim)) (β : 𝓞 E)
    (hS : ∀ y ∈ S, act β y ∈ Submodule.span ℝ S) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : act β a ∈ Submodule.span ℝ S := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [act_zero_lemma_4]; exact zero_mem _
  | add x y _ _ hx hy => rw [act_add_lemma]; exact add_mem hx hy
  | smul r x _ hx => rw [act_smul_lemma_2]; exact Submodule.smul_mem _ r hx

lemma Zs_act {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (μ : ℝ) (β : 𝓞 E)
    {x : Vsp dim} (hx : x ∈ Zs L I μ) : act β x ∈ Zs L I μ := by
  refine act_span_lemma_3 _ β ?_ hx
  rintro _ ⟨α, y, hy, hyμ, rfl⟩
  exact Submodule.subset_span ⟨β * α, y, hy, hyμ, act_mul_lemma_5 β α y⟩

lemma Zs_IR {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (μ : ℝ) : Zs L I μ ≤ IR I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨α, y, hy, -, rfl⟩
  obtain ⟨x, -, hu⟩ : ∃ x ∈ L, IsU I x y := hy
  exact act_span_lemma_3 _ α (fun z hz => Submodule.subset_span (hIs α z hz)) hu.1

lemma prj_rsmul {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (r : ℝ) (x : Vsp dim) :
    prj σ (r • x) = r • prj σ x := by
  simp only [prj]
  exact LinearMap.map_smul_of_tower _ r x

private lemma prj_add_lemma_6 {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (x y : Vsp dim) :
    prj σ (x + y) = prj σ x + prj σ y := by
  simp only [prj]
  exact map_add _ x y

private lemma prj_zero_lemma_7 {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : prj σ (0 : Vsp dim) = 0 := by
  simp only [prj]
  exact map_zero _

lemma prj_mem_of_span {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim))
    (S : Set (Vsp dim)) (hS : ∀ y ∈ S, prj σ y ∈ W) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : prj σ a ∈ W := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [prj_zero_lemma_7]; exact zero_mem _
  | add x y _ _ hx hy => rw [prj_add_lemma_6]; exact add_mem hx hy
  | smul r x _ hx => rw [prj_rsmul]; exact W.smul_of_tower_mem r hx

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MvPolynomial

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ} {dim : (E →+* ℂ) → ℕ}

section Expand
variable (bs : Fin nb → Block E n dim)

abbrev Choice := ∀ j : Fin nb, Fin (bs j).c → Equiv.Perm (Fin (bs j).i)

abbrev Slot := Σ j : Fin nb, Fin (bs j).c × Fin (bs j).i

def sgnT (T : Choice bs) : ℂ := ∏ j, ∏ r, ((Equiv.Perm.sign (T j r) : ℤ) : ℂ)

def letter (T : Choice bs) (t : Slot bs) : Letter n dim :=
  ((bs t.1).col t.2.2, ⟨(bs t.1).τ, Fin.castLE (bs t.1).hi (T t.1 t.2.1 t.2.2)⟩)

theorem block_poly_expand (B : Block E n dim) :
    B.poly = ∑ p : Fin B.c → Equiv.Perm (Fin B.i),
      (∏ r, ((Equiv.Perm.sign (p r) : ℤ) : MvPolynomial (Letter n dim) ℂ)) *
        ∏ r, ∏ b, X (B.col b, ⟨B.τ, Fin.castLE B.hi (p r b)⟩) := by
  rw [Block.poly, Matrix.det_apply', ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem determinantPoly_expand :
    P1 bs = ∑ T : Choice bs, sgnT bs T • ∏ t : Slot bs, X (letter bs T t) := by
  rw [P1]
  simp only [block_poly_expand]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, MvPolynomial.smul_eq_C_mul]
  congr 1
  · simp only [sgnT, map_prod, map_intCast]
  · rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.prod_prod_type]
    rfl

end Expand

section PD
variable (X : PT E) (bs : Fin nb → Block E n X.dim)


open Classical in
def lst (T : Choice bs) : List (Fin n × Vsp X.dim) :=
  by
    classical
    exact (Multiset.map (letter bs T) Finset.univ.val).toList.map
      (fun l => (l.1, EuclideanSpace.single l.2 (1 : ℂ)))

theorem prod_X_letter (T : Choice bs) :
    (∏ t : Slot bs, MvPolynomial.X (letter bs T t) : MvPolynomial (Letter n X.dim) ℂ) =
      monomial (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) 1 := by
  rw [MvPolynomial.monomial_sum_one]
  rfl

theorem toMultiset_letters (T : Choice bs) :
    Finsupp.toMultiset (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) =
      Multiset.map (letter bs T) Finset.univ.val := by

  rw [map_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  rw [Finset.sum_eq_multiset_sum]
  have h : ∀ (s : Multiset (Slot bs)),
      (s.map fun t => ({letter bs T t} : Multiset (Letter n X.dim))).sum = s.map (letter bs T) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih]
  exact h _

theorem polyDeriv_determinantPoly_tensor (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ)
    (hs : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (s k)) :
    polyDeriv (P1 bs) dir (tens X s) 0 =
      ∑ T : Choice bs, sgnT bs T * ∏ k, d1 (s k) (colL (lst X bs T) k).length
        (fun j => (colL (lst X bs T) k).get j) := by
  rw [determinantPoly_expand, jof_polyDeriv_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [polyDeriv_smul, prod_X_letter, polyDeriv_monomial_one, pdTerm_eq_itD, toMultiset_letters]
  congr 1
  have hl : (Multiset.map (letter bs T) Finset.univ.val).toList.map dir =
      (lst X bs T).map (fun p => Pi.single p.1 p.2) := by
    rw [lst, List.map_map]
    rfl
  rw [hl]
  have hg : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (fun z : Vsp X.dim => s k (fun _ => z)) := fun k =>
    (hs k).comp (contDiff_pi.2 fun _ => contDiff_id)
  have h1 := itD_prod hg (lst X bs T) 0
  rw [show tens X s = fun v : Fin n → Vsp X.dim => ∏ k, s k (fun _ => v k) from rfl, h1]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.zero_apply, itD_col (hs k)]
  rfl


end PD

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

def IK {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Submodule ℤ (IR I) :=
  I.comap ((IR I).subtype.toAddMonoidHom.toIntLinearMap)

theorem mem_IK {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x : IR I} :
    x ∈ IK I ↔ (x : Vsp dim) ∈ I := Iff.rfl

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem IK_discrete (hI : IsSplit P I) : DiscreteTopology (IK I) := by
  let f : IK I → X.L := fun x => ⟨((x : IR I) : Vsp X.dim), hI.le (mem_IK.1 x.2)⟩
  have hc : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  exact DiscreteTopology.of_continuous_injective hc hinj

theorem IK_span : Submodule.span ℝ (IK I : Set (IR I)) = ⊤ := by
  apply Submodule.map_injective_of_injective (IR I).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  show _ = Submodule.span ℝ (I : Set (Vsp X.dim))
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_IK.1 hz
  · intro hy
    exact ⟨⟨y, Submodule.subset_span hy⟩, mem_IK.2 hy, rfl⟩

def Ib (hI : IsSplit P I) : Module.Basis (Fin (Module.finrank ℝ (IR I))) ℝ (IR I) :=
  haveI := IK_discrete hI
  haveI : IsZLattice ℝ (IK I) := ⟨IK_span⟩
  haveI := ZLattice.module_free ℝ (IK I)
  (Module.Basis.ofZLatticeBasis ℝ (IK I) (Module.Free.chooseBasis ℤ (IK I))).reindex
    (Fintype.equivFinOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]))

theorem Ib_span (hI : IsSplit P I) : Submodule.span ℤ (Set.range (Ib hI)) = IK I := by
  unfold Ib
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

theorem Ib_mem (hI : IsSplit P I) (i : Fin (Module.finrank ℝ (IR I))) :
    ((Ib hI i : IR I) : Vsp X.dim) ∈ I := by
  have h : Ib hI i ∈ IK I := by
    rw [← Ib_span hI]
    exact Submodule.subset_span (Set.mem_range_self i)
  exact mem_IK.1 h

theorem Ib_det_ne (hI : IsSplit P I) : (Col.ob (IR I)).toBasis.det (Ib hI) ≠ 0 := ((Module.Basis.is_basis_iff_det _).1 ⟨(Ib hI).linearIndependent, (Ib hI).span_eq⟩).ne_zero

def zmG (I : Submodule ℤ (Vsp X.dim)) (s : (Fin 1 → Vsp X.dim) → ℂ) (v : Vsp X.dim) : ℂ :=
  s (fun _ => v) * Complex.exp (-(Real.pi / 2) * Col.S (IR I) v)

def zmBox (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}

def zmC (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) (n : Fin (Module.finrank ℝ (IR I)) → ℤ)
    (v : Vsp X.dim) : ℂ :=
  ∫ t in zmBox (Module.finrank ℝ (IR I)),
    Complex.exp (-(2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * (t i : ℂ))) *
      zmG I s (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim))

def zmB (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ :=
  fun t => zmC hI s 0 (Col.jj (IR I) t)

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end
