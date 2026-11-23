module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.PairVal

theorem cubN_succ {A U : Type} [CommGroup A] [CommGroup U] (θ : A → A → A → U) (k : ℕ) (m x : A) :
    cubN θ (k + 1) 1 m x = cubN θ k 1 m x * θ (m ^ k) m x := by
  simp [cubN, Finset.prod_range_succ]

theorem comp_one {B C : Type} [CommGroup B] [CommGroup C] {r : ℕ} {φ : B → Fin r → C}
    (h : ∀ x y j, φ (x * y) j = φ x j * φ y j) (j : Fin r) : φ 1 j = 1 := by
  have := h 1 1 j
  rw [_root_.one_mul] at this
  exact mul_eq_left.1 this.symm

theorem comp_pow {B C : Type} [CommGroup B] [CommGroup C] {r : ℕ} {φ : B → Fin r → C}
    (h : ∀ x y j, φ (x * y) j = φ x j * φ y j) (x : B) (m : ℕ) (j : Fin r) : φ (x ^ m) j = φ x j ^ m := by
  induction m with
  | zero => simp [comp_one h]
  | succ m ih => rw [pow_succ, h, ih, pow_succ]

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

theorem cube_prod (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (U : N'.A → Fˣ)
    (hφ : ∀ x y j, φ (x * y) j = φ x j * φ y j)
    (hc : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u =
      (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) *
      U (x * y) * U (x * u) * U (y * u) * U 1) (k : ℕ) (b a : N'.A) :
    cubN N'.θ k 1 b a * U (b ^ k * a) * U 1 * (U b * U a) ^ k =
      (∏ i, ∏ j, (cubN N.θ k 1 (φ b i * φ b j) (φ a i * φ a j) /
        (cubN N.θ k 1 (φ b i) (φ a i) * cubN N.θ k 1 (φ b j) (φ a j))) ^ W i j) *
      U (b ^ k) * U a * (U (b * a) * U 1) ^ k := by
  induction k with
  | zero => simp [cubN, mul_comm]
  | succ k ih =>
    have h := hc (b ^ k) b a
    simp only [comp_pow hφ, ← mul_pow] at h
    have split : ∀ P p Q q R s : Fˣ, P * p / (Q * q * (R * s)) = P / (Q * R) * (p / (q * s)) := by
      intro P p Q q R s
      rw [_root_.mul_mul_mul_comm, div_mul_div_comm]
    simp only [cubN_succ, split, mul_zpow, Finset.prod_mul_distrib, pow_succ]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_mul, ofMul_pow] at ih' h' ⊢
    linear_combination (norm := abel) ih' + h'

theorem torusExtensionPair_correction_eq_value_quotient (N : NumD F) (g g' : N.Gt) (z z' : N.X) (C C₁ C₂ : Fˣ) :
    g'.s z * g.s z' / (N.θ (N.c z') g'.b (N.c z) * N.θ (N.c z') g'.b g.b * N.θ (N.c z) g.b (N.c z' * g'.b)) *
      (C / (C₁ * C₂)) = (g * g').s (z + z') * C / (g.s z * C₁ * (g'.s z' * C₂)) := by
  rw [NumD.Gt.mul_s, N.c_add]
  have m1 := g.mult z z'
  have m2 := g'.mult z z'
  have co := N.cub.coc (N.c z) (N.c z') g'.b g.b
  rw [N.cub.s12 (N.c z * N.c z') g'.b g.b] at co
  rw [N.cub.s12 (N.c z') g'.b (N.c z), N.cub.s01 (N.c z') (N.c z), N.cub.s12 (N.c z) g.b]
  apply Additive.ofMul.injective
  replace m1 := congrArg Additive.ofMul m1
  replace m2 := congrArg Additive.ofMul m2
  replace co := congrArg Additive.ofMul co
  simp only [ofMul_mul, ofMul_div] at m1 m2 co ⊢
  linear_combination (norm := abel) -m1 - m2 + co

end GlobalTheory.Mum.TensTor.PairVal

namespace GlobalTheory.Mum.TensTor.PairVal

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

theorem tk_tens (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (hT : TensFacts W φ e wv) (U : N'.A → Fˣ) (hU : ∀ x, wv x = (U x : F)) {k : ℕ} (q' p' : N'.QT k)
    (qs ps : Fin r → N.QT k) (hq : QRelV W φ e wv q' qs) (hp : QRelV W φ e wv p' ps) :
    N'.tk q' p' * (U p'.1.2.b * U q'.1.2.b) ^ k =
      (∏ i, ∏ j, (N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j))) ^ W i j) *
      (U (p'.1.2.b * q'.1.2.b) * U 1) ^ k := by
  obtain ⟨hφ, -, -, -, -, -, hcube, -⟩ := hT
  have hcU : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u =
      (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) *
      U (x * y) * U (x * u) * U (y * u) * U 1 := by
    intro x y u
    apply Units.ext
    simp only [Units.val_mul, ← hU]
    exact hcube x y u
  have hA := cube_prod W φ U hφ hcU k p'.1.2.b q'.1.2.b
  simp only [hp.2.1, hq.2.1] at hA
  have hG := hq.2.2 p'.1.1.toAdd
  simp only [hU, ← Units.val_mul] at hG
  replace hG := Units.ext hG
  simp only [hp.1, hq.2.1, ← N'.QT_pow_b p'] at hG
  have hX : ∀ i j, N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) =
      (qs j).1.2.s (ps i).1.1.toAdd * (qs i).1.2.s (ps j).1.1.toAdd /
        (N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (N.c (ps i).1.1.toAdd) *
          N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (qs i).1.2.b *
          N.θ (N.c (ps i).1.1.toAdd) (qs i).1.2.b (N.c (ps j).1.1.toAdd * (qs j).1.2.b)) *
      (cubN N.θ k 1 ((ps i).1.2.b * (ps j).1.2.b) ((qs i).1.2.b * (qs j).1.2.b) /
        (cubN N.θ k 1 (ps i).1.2.b (qs i).1.2.b * cubN N.θ k 1 (ps j).1.2.b (qs j).1.2.b)) :=
    fun i j => (torusExtensionPair_correction_eq_value_quotient N (qs i).1.2 (qs j).1.2 (ps i).1.1.toAdd (ps j).1.1.toAdd _ _ _).symm
  simp only [hX, mul_zpow, Finset.prod_mul_distrib]
  rw [NumD.tk]
  apply Additive.ofMul.injective
  have hA' := congrArg Additive.ofMul hA
  have hG' := congrArg Additive.ofMul hG
  simp only [ofMul_mul, ofMul_pow] at hA' hG' ⊢
  linear_combination (norm := abel) hA' + hG'

theorem wp_eq_prod : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (k : ℕ), 1 ≤ k → ∀ (q' p' : N'.QT k) (qs ps : Fin r → N.QT k), QRelV W φ e wv q' qs → QRelV W φ e wv p' ps → N'.wp q' p' = ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j := by
  intro F _ N N' r W φ e wv hT k _ q' p' qs ps hq hp
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hT.2.2.2.2.2.1 x)
  have hU : ∀ x, wv x = (U x : F) := fun x => rfl
  have h1 := tk_tens W φ e wv hT U hU q' p' qs ps hq hp
  have h2 := tk_tens W φ e wv hT U hU p' q' ps qs hp hq
  rw [mul_comm q'.1.2.b p'.1.2.b] at h2
  have hper : ∀ i j, N.wp (qs i) (ps j) * N.wp (qs j) (ps i) =
      N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) /
        (N.tk (ps i * ps j) (qs i * qs j) / (N.tk (ps i) (qs i) * N.tk (ps j) (qs j))) := by
    intro i j
    have e1 := WpPairing.wp_mul_left N (qs i) (qs j) (ps i * ps j)
    have e2 := WpPairing.wp_mul_right N (qs i) (ps i) (ps j)
    have e3 := WpPairing.wp_mul_right N (qs j) (ps i) (ps j)
    simp only [NumD.wp] at e1 e2 e3 ⊢
    apply Additive.ofMul.injective
    replace e1 := congrArg Additive.ofMul e1
    replace e2 := congrArg Additive.ofMul e2
    replace e3 := congrArg Additive.ofMul e3
    simp only [ofMul_mul, ofMul_div] at e1 e2 e3 ⊢
    linear_combination (norm := abel) -e1 - e2 - e3
  have hR : ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j =
      ∏ i, ∏ j, (N.wp (qs i) (ps j) * N.wp (qs j) (ps i)) ^ W i j := by
    simp only [Matrix.add_apply, Matrix.transpose_apply, zpow_add, Finset.prod_mul_distrib, mul_zpow]
    congr 1
    rw [Finset.prod_comm]
  have hD : ∀ f g : Fin r → Fin r → Fˣ, ∏ i, ∏ j, (f i j / g i j) ^ W i j =
      (∏ i, ∏ j, f i j ^ W i j) / ∏ i, ∏ j, g i j ^ W i j := by
    intro f g
    simp only [div_zpow, Finset.prod_div_distrib]
  rw [hR]
  simp only [hper]
  rw [hD]
  rw [NumD.wp]
  apply Additive.ofMul.injective
  have h1' := congrArg Additive.ofMul h1
  have h2' := congrArg Additive.ofMul h2
  simp only [ofMul_mul, ofMul_pow, ofMul_div] at h1' h2' ⊢
  linear_combination (norm := abel) h1' - h2'

end GlobalTheory.Mum.TensTor.PairVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem eq_zero_of_sum_smul_matrix {G : Type} [AddCommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : IsUnit M.det) (f : Fin r → G) (h : ∀ i, ∑ j, M i j • f j = 0) (k : Fin r) : f k = 0 := by
  have e1 : f k = ∑ j, (1 : Matrix (Fin r) (Fin r) ℤ) k j • f j := by
    simp [Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_mul M hM]
  simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, h, smul_zero, Finset.sum_const_zero]

theorem eq_one_of_prod_zpow_matrix {G : Type} [CommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : IsUnit M.det) (f : Fin r → G) (h : ∀ i, ∏ j, f j ^ M i j = 1) (k : Fin r) : f k = 1 := by
  have := eq_zero_of_sum_smul_matrix M hM (fun j => Additive.ofMul (f j)) (fun i => by
    simpa [← ofMul_zpow, ← ofMul_prod] using congrArg Additive.ofMul (h i)) k
  simpa using this

theorem gtRelV_prod_tor_mul {F : Type} [Field F] {N : NumD F} {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (x : Fin r → N.X)
    (vs : Fin r → N.Gt) (T : Fin r → (Multiplicative N.X →* Fˣ)) :
    (∏ i, ∏ j, ((N.tor (T j) * vs j).s (x i) * (N.tor (T i) * vs i).s (x j) /
        (N.θ (N.c (x j)) (N.tor (T j) * vs j).b (N.c (x i)) * N.θ (N.c (x j)) (N.tor (T j) * vs j).b
            (N.tor (T i) * vs i).b *
          N.θ (N.c (x i)) (N.tor (T i) * vs i).b (N.c (x j) * (N.tor (T j) * vs j).b))) ^ W i j : Fˣ) =
      (∏ i, ∏ j, ((vs j).s (x i) * (vs i).s (x j) /
        (N.θ (N.c (x j)) (vs j).b (N.c (x i)) * N.θ (N.c (x j)) (vs j).b (vs i).b *
          N.θ (N.c (x i)) (vs i).b (N.c (x j) * (vs j).b))) ^ W i j) *
      ∏ i, ∏ j, (T j (Multiplicative.ofAdd (x i)) * T i (Multiplicative.ofAdd (x j))) ^ W i j := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← mul_zpow]
  congr 1
  simp only [NumD.tor_mul_s_apply, NumD.Gt.mul_b, NumD.tor_b, one_mul, div_eq_mul_inv]
  ac_rfl

theorem gtRelV_prod_single {G : Type} [CommGroup G] {A : Type} [AddCommGroup A] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Fin r → (Multiplicative A →* G)) (i : Fin r) (χ : A) :
    (∏ a, ∏ b, (T b (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) a)) *
        T a (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) b))) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ (W + W.transpose) i j := by
  simp only [mul_zpow, Finset.prod_mul_distrib]
  have h1 : (∏ a, ∏ b, T b (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) a)) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ W i j := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro a _ ha
      simp [Pi.single_apply, ha]
    · simp
  have h2 : (∏ a, ∏ b, T a (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) b)) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ W j i := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.add_apply, Matrix.transpose_apply, zpow_add]

theorem gtRelV_components_unique : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F),
    TensFacts W φ e wv → IsUnit (W + W.transpose).det →
      ∀ (v' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv v' us → vs = us := by
  intro F _ N N' r W φ e wv hT hdet v' vs us hv hu
  have hb : ∀ j, (us j).b = (vs j).b := fun j => (hu.1 j).symm.trans (hv.1 j)
  have ht : ∀ j, ∃ t, N.tor t = us j / vs j := fun j =>
    (N.exists_tor_iff _).2 (by rw [div_eq_mul_inv, NumD.Gt.mul_b, NumD.Gt.inv_b, hb, mul_inv_cancel])
  choose T hT' using ht
  have hus : us = fun j => N.tor (T j) * vs j := funext fun j => by rw [hT', div_mul_cancel]
  subst hus
  have hwv : ∀ x, wv x ≠ 0 := hT.2.2.2.2.2.1
  have key : ∀ χ', (∏ i, ∏ j, (T j (Multiplicative.ofAdd (e χ' i)) * T i (Multiplicative.ofAdd (e χ' j))) ^ W i j) = 1 := by
    intro χ'
    have a := hv.2 χ'
    have b := hu.2 χ'
    rw [a, gtRelV_prod_tor_mul W (e χ') vs T] at b
    have c := mul_right_cancel₀ (hwv _) (mul_right_cancel₀ (hwv 1) b)
    have d := Units.ext c
    exact (mul_eq_left.1 d.symm)
  have hall : ∀ χ j, T j (Multiplicative.ofAdd χ) = 1 := by
    intro χ
    refine eq_one_of_prod_zpow_matrix (W + W.transpose) hdet (fun j => T j (Multiplicative.ofAdd χ)) fun i => ?_
    obtain ⟨χ', hχ'⟩ := hT.2.2.2.1.2 (Pi.single i χ)
    have := key χ'
    rw [hχ', gtRelV_prod_single W T i χ] at this
    exact this
  funext j
  have : T j = 1 := MonoidHom.ext fun m => by simpa using hall m.toAdd j
  rw [this, NumD.tor_one, _root_.one_mul]

end GlobalTheory.Mum.TensTor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section
namespace GlobalTheory.Mum.TensTor.PsiVal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem stalk_gm {Z Y : Scheme.{0}} (f : Z ⟶ Y) {X : Scheme.{0}} (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (f z) ∈ U)
    (a : Γ(X, U)ˣ) : (f.stalkMap z).hom (gm r (f z) U a).val = (gm (f ≫ r) z U a).val := by
  rw [gm_val r (f z) U h, gm_val (f ≫ r) z U h]
  have := Scheme.Hom.germ_stalkMap_apply f (r ⁻¹ᵁ U) z h ((r.app U).hom a.val)
  rw [this]
  rfl

theorem stalk_val {Z Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι)
    (h : f z ∈ LB.wchart L φ (fun k => J (f ≫ φ k))) :
    (f.stalkMap z).hom (val t (𝟙 Y) (f z) (fun ψ => J (f ≫ ψ))).val = (val t f z J).val := by
  rw [val_of t (𝟙 Y) (f z) _ (fun k => J (f ≫ φ k)) (fun k => by simp only [Category.id_comp])]
  refine (stalk_gm f (𝟙 Y) z _ h _).trans ?_
  rw [Category.comp_id]
  rfl

theorem toStk_vF {F : Type} [Field F] {Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (z : Sp F) (J : (Sp F ⟶ X) → L.ι) (hJ : Good L z J) :
    toStk z (vF t r J) = (val t r z J).val :=
  toStk_valF r _ z (hJ.mem φ r) _

theorem toUnit_left {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem stalkU {Z Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    Units.map (f.stalkMap z).hom.toMonoidHom (val t (𝟙 Y) (f z) (fun ψ => J (f ≫ ψ))) = val t f z J :=
  Units.ext (stalk_val t f z J (hJ.mem φ f))

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

theorem good_of (ν : NumOf D F N) (z : Sp F) : Good D.P.L z ν.J := fun ψ => (top_le_iff_mem ψ _ z).1 (ν.good ψ)

theorem goodK_of (ν : NumOf D F N) (z : Sp F) : Good D.P.L (jFK (R := R) F z) (fun ψ => ν.J (jFK (R := R) F ≫ ψ)) :=
  fun ψ => (top_le_iff_mem (jFK (R := R) F ≫ ψ) _ z).1 (ν.good _)

theorem wv_toStk (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) (z : Sp F)
    (p : Sp F ⟶ D'.P.A.left) (hp : (ν'.eA x).left = p) :
    toStk z (wv T ν ν' x) = (gm p z _ (T.w.s (fun k => ν.J (p ≫ tensφ T.pr k), ν'.J p))).val := by
  subst hp
  exact toStk_valF _ _ z (show (ν'.eA x).left z ∈ LB.wchart D.P.L (tensφ T.pr) (fun k => ν.J ((ν'.eA x).left ≫ tensφ T.pr k)) ⊓
    D'.P.L.U (ν'.J (ν'.eA x).left) from ⟨(good_of ν z).mem _ _, good_of ν' z _⟩) _

theorem rig_val (ν : NumOf D F N) (z : Sp F) :
    val (LB.pullGen D.P.L _ _ D.rig (toUnit (TK R)).left) (jFK (R := R) F) z ν.J = val D.rig (jFK (R := R) F ≫ jK R) z ν.J := by
  rw [val_pull (good_of ν z), toUnit_left]
  rfl

theorem psi_m (ν : NumOf D F N) (z : Sp F) (χ : N.X) :
    Units.map (toStk z).toMonoidHom (N.ψ χ) = val (D.psi (ν.eX χ)) (jFK (R := R) F) z ν.J * val D.rig (jFK (R := R) F ≫ jK R) z ν.J := by
  apply Units.ext
  change toStk z (N.ψ χ : F) = _
  rw [ν.ψ_eq χ, map_mul, toStk_vF _ _ z _ (good_of ν z), toStk_vF _ _ z _ (good_of ν z)]
  rfl

theorem tau_m (ν : NumOf D F N) (z : Sp F) (a b : N.X) :
    val (D.tau (ν.eX a) (ν.eX b)) (jFK (R := R) F) z ν.J = Units.map (toStk z).toMonoidHom (N.τ a b) := by
  have hG := good_of ν z
  unfold DegPre.tau DegPre.rigK
  rw [val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv, rig_val ν z]
  rw [NumD.τ, map_div, map_div, psi_m ν z, psi_m ν z, psi_m ν z, map_add (f := _)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

theorem pt_eq (ν' : NumOf D' F N') (χ : N'.X) : (ν'.eA (N'.c χ)).left = jFK (R := R) F ≫ D'.xK (ν'.eX χ) := by
  rw [ν'.c_eq]
  simp only [DegPre.cF, DegPre.xK, ptK, Over.comp_left, toUnit_left]
  rfl

theorem w_stalk (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (z : Sp F) (y : D'.X) :
    Units.map (Scheme.Hom.stalkMap (jFK (R := R) F) z).hom.toMonoidHom
      (gm (D'.xK y) (jFK (R := R) F z) _ (T.w.s (fun k => ν.J (jFK (R := R) F ≫ D'.xK y ≫ tensφ T.pr k),
        ν'.J (jFK (R := R) F ≫ D'.xK y)))) =
    gm (jFK (R := R) F ≫ D'.xK y) z _ (T.w.s (fun k => ν.J ((jFK (R := R) F ≫ D'.xK y) ≫ tensφ T.pr k),
        ν'.J (jFK (R := R) F ≫ D'.xK y))) := by
  have e : (fun k => ν.J ((jFK (R := R) F ≫ D'.xK y) ≫ tensφ T.pr k)) =
      (fun k => ν.J (jFK (R := R) F ≫ D'.xK y ≫ tensφ T.pr k)) := funext fun k => by rw [Category.assoc]
  rw [e]
  apply Units.ext
  refine stalk_gm (jFK (R := R) F) (D'.xK y) z _ ?_ _
  exact (show (jFK (R := R) F ≫ D'.xK y) z ∈ LB.wchart D.P.L (tensφ T.pr) (fun k => ν.J (jFK (R := R) F ≫ D'.xK y ≫ tensφ T.pr k)) ⊓
    D'.P.L.U (ν'.J (jFK (R := R) F ≫ D'.xK y)) from ⟨Set.mem_iInter.2 fun k => by
      have := good_of ν z ((jFK (R := R) F ≫ D'.xK y) ≫ tensφ T.pr k)
      rwa [Category.assoc] at this, good_of ν' z _⟩)

theorem psi_stk (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (z : Sp F) (χ' : N'.X) :
    toStk z (N'.ψ χ' : F) = toStk z (wv T ν ν' (N'.c χ')) *
      toStk z ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) *
      (val D'.rig (jFK (R := R) F ≫ jK R) z ν'.J).val := by
  have key := T.psi (ν'.eX χ') (jFK (R := R) F z) (fun ψ => ν.J (jFK (R := R) F ≫ ψ)) (fun ψ => ν'.J (jFK (R := R) F ≫ ψ))
    (goodK_of ν z) (goodK_of ν' z)
  have key2 := congrArg (Units.map (Scheme.Hom.stalkMap (jFK (R := R) F) z).hom.toMonoidHom) key
  rw [map_mul, stalkU _ _ z _ (good_of ν' z), w_stalk] at key2
  simp only [map_prod, map_zpow, stalkU _ _ z ν.J (good_of ν z)] at key2
  have hL : toStk z (N'.ψ χ' : F) = (Units.map (toStk z).toMonoidHom (N'.ψ χ')).val := rfl
  have hP : toStk z ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) =
      (∏ i, ∏ j, val (D.tau (T.xe (ν'.eX χ') i) (T.xe (ν'.eX χ') j)) (jFK (R := R) F) z ν.J ^ W i j).val := by
    change (Units.map (toStk z).toMonoidHom _).val = _
    congr 1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, ← tau_m ν z, show ν.eX (chi T ν ν' χ' i) = T.xe (ν'.eX χ') i from ν.eX.apply_symm_apply _,
      show ν.eX (chi T ν ν' χ' j) = T.xe (ν'.eX χ') j from ν.eX.apply_symm_apply _]
  rw [hL, psi_m ν' z χ', hP, wv_toStk T ν ν' _ z _ (pt_eq ν' χ'), key2]
  simp only [Units.val_mul]
  try ring

theorem psi_main (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ' : N'.X) :
    (N'.ψ χ' : F) * wv T ν ν' 1 = wv T ν ν' (N'.c χ') * ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) := by
  obtain ⟨z⟩ : Nonempty (Sp F) := ⟨(default : PrimeSpectrum F)⟩
  have h0 := psi_stk T ν ν' z 0
  have hc : chi T ν ν' 0 = 0 := funext fun i => by
    show ν.eX.symm (T.xe (ν'.eX 0) i) = 0
    rw [map_zero, map_zero, Pi.zero_apply, map_zero]
  have hp : (∏ i, ∏ j, N.τ (chi T ν ν' 0 i) (chi T ν ν' 0 j) ^ W i j : Fˣ) = 1 := by
    rw [hc]
    exact Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
      rw [Pi.zero_apply, NumD.τ_zero_left, one_zpow]
  rw [NumD.ψ_zero, NumD.c_zero, hp, Units.val_one, map_one, _root_.mul_one] at h0
  apply (toStk z).injective
  rw [map_mul, map_mul, psi_stk T ν ν' z χ']
  linear_combination (-(toStk z (wv T ν ν' (N'.c χ')) *
      toStk z ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F))) * h0

end GlobalTheory.Mum.TensTor.PsiVal


open GlobalTheory.Mum.TensTor.PsiVal in
theorem GlobalTheory.Mum.TensTor.tensFacts_psi : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), ∀ χ', (N'.ψ χ' : F) * wv T ν ν' 1 = wv T ν ν' (N'.c χ') * ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' χ'
  exact psi_main T ν ν' χ'
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam


open GlobalTheory.HalfBC in
theorem refAt_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (I : Ideal R) (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg ρ D.toPre D'), RefAt (pol D) ρ D' hD.xe (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf ρ)) := by
  intro R R' _ _ _ _ ρ hρ I D D' hD
  letI := D'.P.isAb.comm
  have gp := pull_grp hD
  refine ⟨sqOf gp, lamIso gp hD.w, gp, isSquare_sqOf gp, isGen_lamIso gp hD.w hD.w_gen, fun a => hD.c_pr a,
    fun κ hκ a b z J J' hJ hJ' => ?_⟩
  obtain rfl : κ = GlobalTheory.ArcPull.genMap hρ := by
    have : Mono (jK R) := Wit.mono_jK
    refine (cancel_mono (jK R)).1 (hκ.trans ?_)
    rw [← GlobalTheory.ArcPull.fracMap_sq hρ, Category.id_comp]
  rw [← GlobalTheory.FactorPull.tau_lam hD hρ a b hJ hJ']
  refine congrArg₂ (· * ·) ?_ ((Wit.exists_tau D.toPre (hD.xe a) (hD.xe b)).choose_spec.2 _ _ z J hJ).symm
  symm
  show gw (lamIso gp hD.w) _ z (fun I => J (_ ≫ sqOf gp ≫ GlobalTheory.PrimCocycle.lamφ D.toPre.P.A I))
    (fun I => J' (_ ≫ GlobalTheory.PrimCocycle.lamφ D'.P.A I)) = _
  refine (gw_lamIso gp hD.w _ z _ _ (fun I => by
      have := hJ ((lift (toUnit (TK R') ≫ D'.c a) (toUnit (TK R') ≫ D'.c b)).left ≫ sqOf gp ≫ GlobalTheory.PrimCocycle.lamφ D.toPre.P.A I)
      erw [← pt_sqOf gp I]
      exact this) (fun I => hJ' _)).trans ?_
  refine Finset.prod_congr rfl fun I _ => ?_
  show _ = gw hD.w _ z _ _ ^ _
  erw [Category.assoc, ← sqOf_lamφ gp I]
  rfl

end GlobalTheory.MumFam
end
end
