module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.PrAcyc

def cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨(Fin.cons (0 : Fin (N + 1)) fun k : Fin (p + 1) => a.toOrderHom k : Fin (p + 2) → Fin (N + 1)),
    by
      intro x y hxy
      induction x using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ x =>
        induction y using Fin.cases with
        | zero => exact absurd hxy (by simp [Fin.le_def])
        | succ y =>
          simp only [Fin.cons_succ]
          exact a.toOrderHom.monotone (Fin.succ_le_succ_iff.1 hxy)⟩

theorem cone_succ {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (k : Fin (p + 1)) :
    (cone a).toOrderHom k.succ = a.toOrderHom k := rfl

theorem δ_zero_cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 0 ≫ cone a = a := by
  ext k
  simp [SimplexCategory.δ, cone_succ]

theorem δ_succ_cone {p N : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (i : Fin (p + 2)) :
    SimplexCategory.δ i.succ ≫ cone a = cone (SimplexCategory.δ i ≫ a) := by
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun k => ?_))
  induction k using Fin.cases with
  | zero => rfl
  | succ k =>
    show (cone a).toOrderHom (i.succ.succAbove k.succ) = (cone (SimplexCategory.δ i ≫ a)).toOrderHom k.succ
    rw [Fin.succ_succAbove_succ, cone_succ, cone_succ]
    rfl

abbrev v0 (N : ℕ) : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N := SimplexCategory.const _ _ 0

theorem δ_one_cone {N : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 1 ≫ cone a = v0 N := by
  ext k
  fin_cases k
  rfl

theorem d₁_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

theorem d₂_zero {N p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

theorem d₁_succ {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) 1 := by
  show ∑ i : Fin (p + 2), Finsupp.single _ _ = _
  simp only [Finsupp.smul_single_one]

theorem d₂_succ {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) =
      ∑ j : Fin (r + 2), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) 1 := by
  show ∑ j : Fin (r + 2), Finsupp.single _ _ = _
  simp only [Finsupp.smul_single_one]

end GlobalTheory.PrAcyc

namespace GlobalTheory.PrAcyc

theorem d₁_cone_succ {N q r : ℕ} (a : SimplexCategory.mk (q + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨q + 1 + 1, r, cone a, b⟩ : Pr N) = Finsupp.single (⟨q + 1, r, a, b⟩ : Pr N) 1 -
      ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (⟨q + 1, r, cone (SimplexCategory.δ i ≫ a), b⟩ : Pr N) 1 := by
  rw [d₁_succ, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [δ_zero_cone, Fin.val_zero, pow_zero, one_smul]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, δ_succ_cone]

theorem d₁_cone_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0 + 1, r, cone a, b⟩ : Pr N) = Finsupp.single (⟨0, r, a, b⟩ : Pr N) 1 - Finsupp.single (⟨0, r, v0 N, b⟩ : Pr N) 1 := by
  rw [d₁_succ, Fin.sum_univ_two, δ_zero_cone, δ_one_cone]
  simp [sub_eq_add_neg]

theorem d₂_cone_succ {N p s : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (s + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, s + 1 + 1, a, cone b⟩ : Pr N) = Finsupp.single (⟨p, s + 1, a, b⟩ : Pr N) 1 -
      ∑ j : Fin (s + 2), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (⟨p, s + 1, a, cone (SimplexCategory.δ j ≫ b)⟩ : Pr N) 1 := by
  rw [d₂_succ, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [δ_zero_cone, Fin.val_zero, pow_zero, one_smul]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, δ_succ_cone]

def hz {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  Finsupp.single (⟨z.1 + 1, z.2.1, cone z.2.2.1, z.2.2.2⟩ : Pr N) 1 +
    if z.1 = 0 then Finsupp.single (⟨0, z.2.1 + 1, v0 N, cone z.2.2.2⟩ : Pr N) 1 else 0

def H (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := Finsupp.linearCombination ℤ hz

theorem H_single {N : ℕ} (z : Pr N) : H N (Finsupp.single z 1) = hz z := by
  simp [H, Finsupp.linearCombination_single]

theorem d_single {N : ℕ} (z : Pr N) : Pr.d N (Finsupp.single z 1) = z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂ := by
  simp [Pr.d, Finsupp.linearCombination_single]

theorem H_sum {N n : ℕ} (f : Fin n → Pr N) :
    H N (∑ i : Fin n, ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (f i) 1) = ∑ i : Fin n, ((-1 : ℤ) ^ (i : ℕ)) • hz (f i) := by

  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, H_single]

theorem key {N : ℕ} (z : Pr N) (hpos : 0 < z.1 + z.2.1) :
    Pr.d N (H N (Finsupp.single z 1)) + H N (Pr.d N (Finsupp.single z 1)) = Finsupp.single z 1 := by
  rcases z with ⟨p, r, a, b⟩
  rw [H_single, d_single]
  cases p with
  | zero =>
    cases r with
    | zero => simp at hpos
    | succ s =>
      simp only [hz, if_pos rfl, if_true, map_add (f := _), d_single]
      rw [d₁_cone_zero, d₂_succ, d₁_zero, d₂_cone_succ, d₁_zero, d₂_succ, map_zero, map_smul, H_sum]
      simp only [hz, if_true, ↓reduceIte, Finset.sum_add_distrib, smul_add]
      module
  | succ q =>
    simp only [hz, Nat.succ_ne_zero, if_false, ↓reduceIte, add_zero, map_add (f := _), d_single, map_smul]
    rw [d₁_cone_succ, d₁_succ, H_sum]
    have hX : ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • hz (⟨q, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) =
        ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (⟨q + 1, r, cone (SimplexCategory.δ i ≫ a), b⟩ : Pr N) 1 := by
      simp only [hz, smul_add, Finset.sum_add_distrib]
      rcases q with _ | t
      · simp [Fin.sum_univ_two]
      · simp
    rw [hX]
    cases r with
    | zero => rw [d₂_zero, d₂_zero, map_zero]; module
    | succ s =>
      rw [d₂_succ, d₂_succ, H_sum]
      simp only [hz, Nat.succ_ne_zero, if_false, ↓reduceIte, add_zero]
      rw [pow_succ]
      module

end GlobalTheory.PrAcyc

namespace GlobalTheory.PrAcyc

theorem hz_deg {N : ℕ} (w z : Pr N) (h : z ∈ (hz w).support) : z.1 + z.2.1 = w.1 + w.2.1 + 1 := by
  rcases w with ⟨p, r, a, b⟩
  have h' := Finsupp.support_add h
  rcases Finset.mem_union.1 h' with h1 | h1
  · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h1
    split_ifs at h1 with he
    · subst he; simp; omega
    · simp at h1
  · split_ifs at h1 with hp
    · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h1
      split_ifs at h1 with he
      · subst he; simp at hp ⊢; omega
      · simp at h1
    · simp at h1

theorem deg_H {N k : ℕ} (c : Pr N →₀ ℤ) (hc : Pr.Deg (k + 1) c) : Pr.Deg (k + 2) (H N c) := by
  intro z hz'
  rw [H, Finsupp.linearCombination_apply] at hz'
  obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hz')
  have := hz_deg w z (Finsupp.support_smul hzw)
  rw [this, hc w hw]

theorem homotopy {N k : ℕ} (c : Pr N →₀ ℤ) (hc : Pr.Deg (k + 1) c) :
    Pr.d N (H N c) + H N (Pr.d N c) = c := by
  have step : ∀ z ∈ c.support, Pr.d N (H N (Finsupp.single z (c z))) + H N (Pr.d N (Finsupp.single z (c z))) =
      Finsupp.single z (c z) := by
    intro z hz'
    have := key z (by rw [hc z hz']; omega)
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul, ← smul_add, this]
  calc Pr.d N (H N c) + H N (Pr.d N c)
      = Pr.d N (H N (c.sum Finsupp.single)) + H N (Pr.d N (c.sum Finsupp.single)) := by rw [Finsupp.sum_single]
    _ = ∑ z ∈ c.support, Finsupp.single z (c z) := by

        simp only [Finsupp.sum, map_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl step
    _ = c := Finsupp.sum_single c

theorem pr_acyclic : ∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 → ∃ e, Pr.Deg (k + 2) e ∧ Pr.d N e = c := by
  intro N k c hc hd
  refine ⟨H N c, deg_H c hc, ?_⟩
  have := homotopy c hc
  rwa [hd, map_zero, add_zero] at this

end GlobalTheory.PrAcyc
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ConeSec

variable {R : Type} [CommRing R]

lemma smap_comp {F G K : Shv R} (a : F ⟶ G) (b : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

lemma smap_add {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a + b) x = Sec.map a x + Sec.map b x := rfl

lemma smap_neg {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (-a) x = -Sec.map a x := rfl

lemma smap_sub {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a - b) x = Sec.map a x - Sec.map b x := rfl

lemma smap_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

lemma smap_add' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map a (x + y) = Sec.map a x + Sec.map a y := (a.hom.app (op U)).hom.map_add x y

lemma smap_neg' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a (-x) = -Sec.map a x := (a.hom.app (op U)).hom.map_neg x

lemma sres_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := a.hom.naturality g.op
  exact congrArg (fun t => t.hom x) this.symm

lemma smap_zero {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} :
    Sec.map a (0 : Sec F U) = 0 := (a.hom.app (op U)).hom.map_zero

lemma sres_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := (F.obj.map g.op).hom.map_add x y

end GlobalTheory.EtC.ConeSec


open GlobalTheory.EtC.ConeSec in
theorem GlobalTheory.EtC.cone_sec_exact : ∀ (R : Type) [CommRing R] {I J : Cx R} (f : I ⟶ J) (U : Scheme.{0}) (n : ℤ), (∀ (b₁ : Sec (I.X (n + 1)) U) (b₂ : Sec (J.X n) U), Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 → Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec (I.X n) V) (a₂ : Sec (J.X (n - 1)) V), Sec.map (I.d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map (f.f n) a₁ + Sec.map (J.d (n - 1) n) a₂ = Sec.res g b₂) → ∀ b : Sec ((mappingCone f).X n) U, Sec.map ((mappingCone f).d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec ((mappingCone f).X (n - 1)) V, Sec.map ((mappingCone f).d (n - 1) n) a = Sec.res g b := by
  intro R _ I J f U n hyp b hb
  obtain ⟨b₁, hb₁⟩ : ∃ x, Sec.map ((mappingCone.fst f).1.v n (n + 1) rfl) b = x := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ x, Sec.map ((mappingCone.snd f).v n n (add_zero n)) b = x := ⟨_, rfl⟩
  have h1 : Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 := by
    have e := congrArg (fun φ => Sec.map φ b) (mappingCone.d_fst_v f n (n + 1) (n + 2) rfl (by ring))
    simp only [smap_comp, smap_neg, hb, smap_zero, hb₁] at e
    exact neg_eq_zero.mp e.symm
  have h2 : Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 := by
    have e := congrArg (fun φ => Sec.map φ b) (mappingCone.d_snd_v f n (n + 1) rfl)
    simp only [smap_comp, smap_add, hb, smap_zero, hb₁, hb₂] at e
    exact e.symm
  have hid := congrArg (fun φ => Sec.map φ b) (mappingCone.id_X f n (n + 1) rfl)
  simp only [smap_comp, smap_add, smap_id, hb₁, hb₂] at hid
  obtain ⟨S, hS, h⟩ := hyp b₁ b₂ h1 h2
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨a₁, a₂, e1, e2⟩ := h V g hg
  refine ⟨Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁ + Sec.map ((mappingCone.inr f).f (n - 1)) a₂, ?_⟩
  have k1 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁) =
      Sec.map ((mappingCone.inr f).f n) (Sec.map (f.f n) a₁) -
        Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.map (I.d n (n + 1)) a₁) := by
    rw [← smap_comp, mappingCone.inl_v_d f n (n - 1) (n + 1) (by ring) (by ring), smap_sub, smap_comp, smap_comp]
  have k2 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inr f).f (n - 1)) a₂) =
      Sec.map ((mappingCone.inr f).f n) (Sec.map (J.d (n - 1) n) a₂) := by
    rw [← smap_comp, mappingCone.inr_f_d, smap_comp]
  have k3 : Sec.res g b = Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.res g b₁) +
      Sec.map ((mappingCone.inr f).f n) (Sec.res g b₂) := by
    rw [← hid, sres_add, sres_map, sres_map]
  rw [smap_add', k1, k2, e1, k3, ← e2, smap_add', smap_neg']
  abel
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.loc_iff_etale_affine_points : ∀ (U : Scheme.{0})
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop),
    (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) →
    (_root_.GlobalTheory.EtC.Loc U P ↔ ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U),
      IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g) := by
  intro U P hP
  unfold _root_.GlobalTheory.EtC.Loc
  constructor
  · rintro ⟨S, hS, hSP⟩ x
    obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
    haveI : Scheme.JointlySurjective (Scheme.precoverage (@Etale : MorphismProperty Scheme.{0})) :=
      Scheme.instJointlySurjectivePrecoverage
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    let A := (𝒰.X i).affineCover
    obtain ⟨z, hz⟩ := A.covers y
    have hE : Etale (𝒰.f i) := 𝒰.map_prop i
    refine ⟨A.X (A.idx y), A.f (A.idx y) ≫ 𝒰.f i, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩
    · rw [Scheme.Hom.comp_apply, hz]
    · exact hSP _ _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk i)) _)
  · intro h
    choose V g hV hE hx hPg using h
    let S : Sieve U :=
      { arrows := fun W f => P W f, downward_closed := fun hf k => hP _ _ _ k hf }
    refine ⟨S, ?_, fun W f hf => hf⟩
    refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).2
      ⟨Scheme.Cover.mkOfCovers U V g (fun x => ?_) (fun x => hE x), ?_⟩
    · obtain ⟨y, hy⟩ := hx x
      exact ⟨x, y, hy⟩
    · rintro _ _ ⟨x⟩
      exact hPg x

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.SecGlueLoc

theorem isSheaf_forget {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)

theorem res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem ext_of_sieve {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (S : Sieve U)
    (hS : S ∈ Scheme.etaleTopology U) (s t : Sec F U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g s = Sec.res g t) : s = t :=
  ((isSheaf_forget F) S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem exists_loc {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0})
    (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), A U x s → A V (g ≫ x) (Sec.res g s))
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t)
    (U : Scheme.{0}) (x : U ⟶ X) (h3 : Loc U fun V g => ∃ s, A V (g ≫ x) s) :
    ∃ s : Sec F U, Loc U fun V g => A V (g ≫ x) (Sec.res g s) := by
  obtain ⟨S, hS, hP⟩ := h3
  let t : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) S.arrows :=
    fun V g hg => (hP V g hg).choose
  have ht : ∀ (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g), A V (g ≫ x) (t g hg) :=
    fun V g hg => (hP V g hg).choose_spec
  have hc : t.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ w
    change Sec.res g₁ (t f₁ hf₁) = Sec.res g₂ (t f₂ hf₂)
    have a1 := h1 _ _ g₁ _ _ (ht _ f₁ hf₁)
    have a2 := h1 _ _ g₂ _ _ (ht _ f₂ hf₂)
    rw [← Category.assoc, w] at a1
    rw [← Category.assoc] at a2
    exact h2 _ _ _ _ a1 a2
  obtain ⟨s, hs, -⟩ := (isSheaf_forget F) S hS t hc
  refine ⟨s, S, hS, fun V g hg => ?_⟩
  have e : Sec.res g s = t g hg := hs g hg
  show A V (g ≫ x) (Sec.res g s)
  rw [e]
  exact ht V g hg

theorem loc_unique {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0})
    (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop)
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t)
    (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U)
    (hs : Loc U fun V g => A V (g ≫ x) (Sec.res g s)) (ht : Loc U fun V g => A V (g ≫ x) (Sec.res g t)) :
    s = t := by
  obtain ⟨S, hS, hPs⟩ := hs
  obtain ⟨T, hT, hPt⟩ := ht
  refine ext_of_sieve F (S ⊓ T) (Scheme.etaleTopology.intersection_covering hS hT) s t (fun V g hg => ?_)
  exact h2 V (g ≫ x) _ _ (hPs V g hg.1) (hPt V g hg.2)

end GlobalTheory.EtC.SecGlueLoc


open GlobalTheory.EtC.SecGlueLoc in
theorem GlobalTheory.EtC.secGlue_of_loc : ∀ {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop),
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), A U x s → A V (g ≫ x) (Sec.res g s)) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => ∃ s, A V (g ≫ x) s) →
    ∃ e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (e U x) = e V (g ≫ x)) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (s : Sec F U), A U x s → e U x = s := by
  intro R _ F X A h1 h2 h3
  let e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U := fun U x => (exists_loc F X A h1 h2 U x (h3 U x)).choose
  have he : ∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => A V (g ≫ x) (Sec.res g (e U x)) :=
    fun U x => (exists_loc F X A h1 h2 U x (h3 U x)).choose_spec
  refine ⟨e, fun V U g x => ?_, fun U x s hs => ?_⟩
  · refine loc_unique F X A h2 V (g ≫ x) _ _ ?_ (he V (g ≫ x))
    obtain ⟨S, hS, hP⟩ := he U x
    refine ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W h hh => ?_⟩
    show A W (h ≫ g ≫ x) (Sec.res h (Sec.res g (e U x)))
    rw [res_comp, ← Category.assoc]
    exact hP W (h ≫ g) hh
  · refine loc_unique F X A h2 U x _ _ (he U x) ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h1 V U g x s hs⟩

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP0⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hP0 V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : Loc U P') :
    Loc U fun V g => P V g ∧ P' V g := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hP'⟩ := h'
  exact ⟨S ⊓ S', Scheme.etaleTopology.intersection_covering hS hS', fun V g hg => ⟨hP V g hg.1, hP' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  classical
  obtain ⟨S, hS, hP0⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => hP V g (hP0 V g hg)
  refine ⟨Sieve.bind S.arrows fun V g hg => T V g hg, Scheme.etaleTopology.bind_covering hS fun V g hg => hT V g hg, ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hT' V g hg W k hk

end GlobalTheory.EtC.RedChern
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sec_ext_glue : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg := by
  intro R _ F U
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).2
  refine ⟨fun a b ⟨S, hS, h⟩ => ?_, fun S hS s hs => ?_⟩
  · exact (hF S hS).isSeparatedFor.ext fun V g hg => h V g hg
  · let x : Presieve.FamilyOfElements (F.obj ⋙ forget _) S.arrows := fun V g hg => s V g hg
    have hx : x.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro V W g k hg
      exact (hs V W g k hg).symm
    obtain ⟨a, ha, -⟩ := hF S hS x hx
    exact ⟨a, fun V g hg => ha g hg⟩

end GlobalTheory.EtC
end
