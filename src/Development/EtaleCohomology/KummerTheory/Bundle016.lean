module

public import Development.EtaleCohomology.KummerTheory.Bundle006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle036
public import Development.EtaleCohomology.KummerTheory.InjSlice
public import Development.EtaleCohomology.KummerTheory.CupAWCutEv
public import Development.EtaleCohomology.TateTwists.Bundle011
public import Development.EtaleCohomology.TateTwists.Bundle010
public import Development.EtaleCohomology.TateTwists.Bundle020
public import Development.EtaleCohomology.TateTwists.Bundle013
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.LocalStructure
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
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open Polynomial IsLocalRing CategoryTheory AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ShSectPf

theorem isUnit_of_map {A K : Type} [CommRing A] [IsLocalRing A] [Field K] (φ : A →+* K)
    (hφ : ∀ a ∈ maximalIdeal A, φ a = 0) {a : A} (h : IsUnit (φ a)) : IsUnit a := by
  by_contra ha
  have := hφ a ((mem_maximalIdeal a).2 ha)
  rw [this] at h; exact not_isUnit_zero h

theorem alg_sect (A B : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A B) = maximalIdeal A) : Nonempty (B →ₐ[A] A) := by
  obtain ⟨s, hsQ, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let S := Localization.Away s
  let P : StandardEtalePresentation A S := hst.nonempty_standardEtalePresentation.some
  let K := Q.ResidueField
  have hsu : IsUnit ((IsScalarTower.toAlgHom A B K) s) := by
    rw [isUnit_iff_ne_zero]
    show algebraMap B Q.ResidueField s ≠ 0
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact hsQ
  let ψ : S →ₐ[A] K := IsLocalization.Away.liftAlgHom s hsu
  let xb : K := ψ P.x
  have hmap := P.hasMap.map ψ
  have hder := hmap.isUnit_derivative_f

  have hkill : ∀ a ∈ maximalIdeal A, algebraMap A K a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply A B K, Ideal.algebraMap_residueField_eq_zero]
    rw [← hQ] at ha; exact ha
  have hloc : IsLocalHom (algebraMap A K) := ⟨fun a h => isUnit_of_map _ hkill h⟩
  let i : ResidueField A →+* K := ResidueField.lift (algebraMap A K)
  have hi : ∀ a, i (residue A a) = algebraMap A K a := fun a => ResidueField.lift_residue_apply _ a
  let _ : Algebra (ResidueField A) K := i.toAlgebra
  have hev : ∀ q : A[X], aeval xb (q.map (residue A)) = aeval xb q := by
    intro q
    rw [aeval_def, aeval_def, eval₂_map]
    congr 1
  let fb := P.f.map (residue A)
  have hint : IsIntegral (ResidueField A) xb :=
    ⟨fb, P.monic_f.map _, by rw [← aeval_def, hev]; exact hmap.1⟩
  have hirr := minpoly.irreducible hint
  have hsep : (minpoly (ResidueField A) xb).Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hirr]
    intro h0
    obtain ⟨h, hh⟩ := minpoly.dvd (ResidueField A) xb (p := fb) (by rw [hev]; exact hmap.1)
    have : aeval xb (derivative fb) = 0 := by
      rw [hh, derivative_mul, h0]; simp
    rw [show derivative fb = (derivative P.f).map (residue A) from derivative_map _ _,
      hev] at this
    rw [this] at hder; exact not_isUnit_zero hder
  obtain ⟨a0, ha0⟩ := IsSepClosed.exists_root _ (minpoly.degree_pos hint).ne' hsep
  have hd0 : X - C a0 ∣ minpoly (ResidueField A) xb := dvd_iff_isRoot.2 ha0
  have hdvd : minpoly (ResidueField A) xb ∣ X - C a0 :=
    Irreducible.dvd_symm (irreducible_X_sub_C a0) hirr hd0
  obtain ⟨a00, ha00⟩ := residue_surjective a0
  have hxb : xb = algebraMap A K a00 := by
    have h1 : aeval xb (X - C a0) = 0 := by
      obtain ⟨c, hc⟩ := hdvd; rw [hc, map_mul, minpoly.aeval, zero_mul]
    rw [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
    rw [h1, ← ha00]; exact hi a00
  have hzero : ∀ a : A, algebraMap A K a = 0 → a ∈ maximalIdeal A := by
    intro a ha; by_contra hn
    have := ((mem_maximalIdeal a).not.1 hn |> not_not.1).map (algebraMap A K)
    rw [ha] at this; exact not_isUnit_zero this
  have hev' : ∀ q : A[X], algebraMap A K (q.eval a00) = aeval xb q := by
    intro q; rw [hxb, aeval_algebraMap_apply, coe_aeval_eq_eval]
  obtain ⟨r, hr, hra⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a00
    (hzero _ (by rw [hev']; exact hmap.1)) (isUnit_of_map _ hkill (by rw [hev']; exact hder))
  have hrK : algebraMap A K r = xb := by
    rw [hxb, ← sub_eq_zero, ← map_sub]; exact hkill _ hra
  have hr' : P.HasMap r := by
    refine ⟨by rw [coe_aeval_eq_eval]; exact hr, isUnit_of_map _ hkill ?_⟩
    rw [← aeval_algebraMap_apply, hrK]; exact hmap.2
  exact ⟨((P.lift r hr').comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom A B S)⟩

theorem ShSect_of : LateralTheory.KummerTheory.SecSHPf.ShSect := by
  intro A _ hA Y f hf hsurj
  obtain ⟨hH, hsc⟩ := hA
  obtain ⟨y, hy⟩ := hsurj.surj (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))
  let 𝒰 := Y.affineOpenCover
  let j := 𝒰.idx y
  obtain ⟨y', hy'⟩ := 𝒰.covers y
  let g := 𝒰.f j
  let φ : CommRingCat.of A ⟶ 𝒰.X j := Spec.preimage (g ≫ f)
  have hφ : Spec.map φ = g ≫ f := Spec.map_preimage _
  have het : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  algebraize [φ.hom]
  have hpt : (Spec.map φ) y' = IsLocalRing.closedPoint A := by
    rw [hφ, Scheme.Hom.comp_apply]
    simp only [g, j] at hy' ⊢
    rw [hy', hy]
  have hQ : y'.asIdeal.comap (algebraMap A (𝒰.X j)) = IsLocalRing.maximalIdeal A := by
    have := congrArg PrimeSpectrum.asIdeal hpt
    exact this
  have : y'.asIdeal.IsPrime := PrimeSpectrum.isPrime y'
  obtain ⟨ψ⟩ := alg_sect A (𝒰.X j) y'.asIdeal hQ
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ g, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of A)
  ext a
  exact ψ.commutes a

end LateralTheory.KummerTheory.ShSectPf
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

universe u

namespace LateralTheory.KummerTheory.KerPf

theorem seqSec (S : ℕ → Type u) [∀ a, Finite (S a)] [∀ a, Nonempty (S a)] (t : ∀ a, S (a + 1) → S a) :
    ∃ s : ∀ a, S a, ∀ a, t a (s (a + 1)) = s a :=
  _root_.UpperTheory.Reformulated.B.DYra4.main S t

variable (l : ℕ) [Fact l.Prime]

theorem redk (hA : A11) (E : Spc) (n i : ℤ) (x : Hl l E n i) (m : ℕ) :
    ∀ a : ℕ, red (l ^ (m + a)) (l ^ m) E n i (x.1 (m + a)) = x.1 m := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  intro a
  induction a with
  | zero => exact (@hA (l ^ m) (l ^ m) _ dvd_rfl E).2.2.1 n i _
  | succ a ih =>
    have h := (@hA (l ^ (m + (a + 1))) (l ^ (m + a)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m)
      (pow_dvd_pow l (by omega)) n i (x.1 (m + (a + 1)))
    rw [← h, ← ih]
    exact congrArg _ (x.2 (m + a))

omit [Fact l.Prime] in
theorem smul_zero_of (E : Spc) (n i : ℤ) (k b : ℕ) (hkb : k ≤ b) (z : Ht (l ^ k) E n i) : (l ^ b) • z = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ k)), (CharP.cast_eq_zero_iff (ZMod (l ^ k)) (l ^ k) _).2 (pow_dvd_pow l hkb), zero_smul]

theorem ker (hA : A11) (E : Spc) (i : ℤ) (hB : ∀ b, BockData l b E i)
    (hFin : ∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) (n : ℤ) (b : ℕ) (x : Hl l E n i) (hx : lev l x b = 0) :
    ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ b) • y := by
  obtain ⟨u, d, h⟩ := hB b
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ a) E n i // u a n w = x.1 (b + a)}
  have hS : ∀ a, Finite (S a) := fun a => by have := hFin a n; exact Subtype.finite
  have hN : ∀ a, Nonempty (S a) := fun a => by
    obtain ⟨w, hw⟩ := ((h a n).1 (x.1 (b + a))).1 (by rw [redk l hA E n i x b a]; exact hx)
    exact ⟨⟨w, hw⟩⟩
  let t : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (a + 1)) (l ^ a) E n i w.1, by
    rw [← (h a n).2.2.2.2.2 w.1, w.2]; exact x.2 (b + a)⟩
  obtain ⟨s, hs⟩ := seqSec S t
  let y : Hl l E n i := ⟨fun a => (s a).1, fun a => congrArg Subtype.val (hs a)⟩
  refine ⟨y, ?_⟩
  have e : ((l : ℤ_[l]) ^ b) • y = (l ^ b : ℕ) • y := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]; push_cast; rfl
  rw [e]
  apply Subtype.ext
  funext k
  change x.1 k = (l ^ b) • (s k).1
  rcases le_or_gt b k with hk | hk
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hr := redk l hA E n i y a b
    rw [Nat.add_comm a b] at hr
    rw [← (h a n).2.2.2.1 ((s (b + a)).1)]
    change x.1 (b + a) = u a n (red _ _ E n i (y.1 (b + a)))
    rw [hr]
    exact (s a).2.symm
  · rw [smul_zero_of l E n i k b hk.le]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hk.le
    rw [← redk l hA E n i x k c]
    change red _ _ E n i (lev l x (k + c)) = 0
    rw [hx, map_zero]

end LateralTheory.KummerTheory.KerPf

namespace LateralTheory.KummerTheory

theorem AdicKer_holds : AdicKer := fun hA l _ E i hB hFin n k x hx => KerPf.ker l hA E i hB hFin n k x hx

end LateralTheory.KummerTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AW
variable {R : Type} [CommRing R] {E : Spc} {I J K : Cx R} {n m k : ℤ} {U : Scheme.{0}}

def ev0 (α : Cochain ((chains R).obj E) I n) (s : ℤ) (U : Scheme.{0}) (p : ℕ) (x : Sx E p U) : Sec (I.X s) U :=
  if h : -(p : ℤ) + n = s then ev α p s h U x else 0

theorem ev_delta {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + m = t) (x : Sx E p U) :
    ev (δ n m α) p t ht U x = Sec.map (I.d s t) (ev α p s hs U x) + m.negOnePow • bd (ev0 α t U) p x := by
  cases p with
  | zero => rw [ev_delta_zero hm α s t hs]; simp [bd]
  | succ p =>
    rw [ev_delta_succ hm α p s t hs]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dite_eq_left]

def pr (μ : Pair I J K) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (w : ℤ) (U : Scheme.{0})
    (p q : ℕ) (y : Sx E p U) (z : Sx E q U) : Sec (K.X w) U :=
  if h : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w then μ.mul U _ _ w h (ev α p _ rfl U y) (ev β q _ rfl U z) else 0

variable (μ : Pair I J K) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)

theorem mul_ev {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (ev α p s hs U y) (ev β q t ht U z) = pr μ α β w U p q y z := by
  subst hs ht
  rw [pr, dite_eq_left h]

theorem mul_bd_left {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + (n + 1) = s) (ht : -(q : ℤ) + m = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (bd (ev0 α s U) p y) (ev β q t ht U z) = bd (fun a y => pr μ α β w U a q y z) p y := by
  cases p with
  | zero => simp [bd]
  | succ p =>

    simp only [bd, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dite_eq_left (by omega), mul_ev]

theorem mul_bd_right {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + (m + 1) = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (ev α p s hs U y) (bd (ev0 β t U) q z) = bd (fun b z => pr μ α β w U p b y z) q z := by
  cases q with
  | zero => simp [bd]
  | succ q =>

    simp only [bd, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dite_eq_left (by omega), mul_ev]

theorem d_pr {w : ℤ} {p q : ℕ} (h : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w) (y : Sx E p U) (z : Sx E q U) :
    Sec.map (K.d w (w + 1)) (pr μ α β w U p q y z) =
      (pr μ (δ n (n + 1) α) β (w + 1) U p q y z -
        (((n + 1).negOnePow : ℤˣ) : ℤ) • bd (fun a y => pr μ α β (w + 1) U a q y z) p y) +
      (((-(p : ℤ) + n).negOnePow : ℤˣ) : ℤ) • (pr μ α (δ m (m + 1) β) (w + 1) U p q y z -
        (((m + 1).negOnePow : ℤˣ) : ℤ) • bd (fun b z => pr μ α β (w + 1) U p b y z) q z) := by
  rw [pr, dite_eq_left h, μ.leibniz, Units.smul_def]
  congr 1
  · rw [← mul_ev μ (δ n (n + 1) α) β (s := -(p : ℤ) + n + 1) (t := -(q : ℤ) + m) (by omega) (by omega) rfl,
      ev_delta rfl α p _ _ rfl, ← mul_bd_left μ α β (s := -(p : ℤ) + n + 1) (t := -(q : ℤ) + m) (by omega) (by omega) rfl,
      map_add, Units.smul_def, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, add_sub_cancel_right]
  · rw [← mul_ev μ α (δ m (m + 1) β) (s := -(p : ℤ) + n) (t := -(q : ℤ) + m + 1) (by omega) rfl (by omega),
      ev_delta rfl β q _ _ rfl, ← mul_bd_right μ α β (s := -(p : ℤ) + n) (t := -(q : ℤ) + m + 1) (by omega) rfl (by omega),
      map_add, Units.smul_def, map_zsmul, add_sub_cancel_right]

variable {μ α β} in
theorem aw_eq {hk : n + m = k} {γ : Cochain ((chains R).obj E) K k} (hγ : μ.IsAW hk α β γ) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + k = w) (x : Sx E N U) : ev γ N w h U x = ∑ p : Fin (N + 1), (((m * (p : ℕ)).negOnePow : ℤˣ) : ℤ) •
      pr μ α β w U p (N - p) (x.sub 0 p (by omega)) (x.sub p (N - p) (by omega)) := by
  rw [hγ N w h U x]
  exact Finset.sum_congr rfl fun p _ => by rw [mul_ev, Units.smul_def]

theorem leibniz : LateralTheory.EtaleFoundations.cupflip_aw_leibniz := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ h h1 h2
  refine ev_ext _ _ fun M w' hw' U x => ?_
  obtain ⟨w, rfl⟩ : ∃ w, w' = w + 1 := ⟨w' - 1, by omega⟩
  have hw : -(M : ℤ) + k = w := by omega
  have hb : bd (ev0 γ (w + 1) U) M x = _ :=
    (bd_congr (fun N y e => by rw [ev0, dite_eq_left (by omega), aw_eq h]) x).trans
      (bd_aw (pr μ α β (w + 1) U) (fun p => (((m * p).negOnePow : ℤˣ) : ℤ))
        (fun p => ((m.negOnePow * (m * p).negOnePow : ℤˣ) : ℤ)) (fun p => by
          push_cast
          rw [mul_add, mul_one, Int.negOnePow_add]
          rcases Int.units_eq_one_or m.negOnePow with e | e <;> simp [e]) M x)

  rw [ev_delta rfl γ M w _ hw, ev_add, ev_units_smul, aw_eq h, aw_eq h1, aw_eq h2, hb, Sec.map, map_sum,
  Units.smul_def, Units.smul_def, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.2
  have hd := d_pr μ α β (w := w) (p := p) (q := M - p) (by omega) (x.sub 0 p (by omega)) (x.sub p (M - p) (by omega))
  rw [Sec.map] at hd
  rw [map_zsmul, hd]
  have e : (-1 : ℤ) ^ (p : ℕ) = ((((p : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) := by simp [Int.coe_negOnePow_natCast]
  rw [e, ← hk, add_mul, one_mul]
  simp only [Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_one]
  generalize (m * (p : ℕ)).negOnePow = c
  generalize ((p : ℕ) : ℤ).negOnePow = d
  generalize n.negOnePow = a
  rcases Int.units_eq_one_or m.negOnePow with e | e <;> rw [e] <;> push_cast <;> module

theorem aw_cochain : LateralTheory.EtaleFoundations.cupflip_aw_cochain :=
  LateralTheory.EtaleFoundations.cupflip_aw_cochain_of LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data
    (fun _ _ _ _ _ α p s h _ _ g x => ev_res α p s h g x) LateralTheory.EtaleFoundations.cupflip_sub_res_holds

theorem aw_exists : LateralTheory.EtaleFoundations.cupflip_aw_exists := LateralTheory.EtaleFoundations.cupflip_aw_exists_of aw_cochain leibniz

variable {μ α β} in
theorem aw_unique {hk : n + m = k} {γ γ' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk α β γ) (h' : μ.IsAW hk α β γ') :
    γ = γ' := ev_ext _ _ fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm

theorem wd_aw : LateralTheory.EtaleFoundations.cupflip_wd_aw := by
  intro R _ I J K μ E n m k hk
  refine ⟨aw_exists R μ E hk, fun _ _ _ _ => aw_unique, fun α α' β γ γ' h h' N w hw U x => ?_,
    fun α β β' γ γ' h h' N w hw U x => ?_⟩ <;>
  · rw [ev_add, h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [ev_add, map_add (f := _), LinearMap.add_apply, smul_add]

theorem wd_cobdry : LateralTheory.EtaleFoundations.cupflip_wd_cobdry := by
  rintro R _ I J K μ E n m k hk α β γ h (⟨n', hn, η, hη⟩ | ⟨m', hm, η, hη⟩)
  · subst hn
    obtain rfl : k = n' + m + 1 := by omega
    obtain ⟨θ, hθ⟩ := aw_cochain R μ E rfl η β.1
    refine ⟨n' + m, rfl, θ, ?_⟩
    rw [leibniz R μ rfl η β.1 θ γ.1 0 hθ (by rw [hη]; exact h)
      (by rw [Cocycle.δ_eq_zero]; exact LateralTheory.EtaleFoundations.isAW_zero_right μ _ _), smul_zero, add_zero]
  · subst hm
    obtain rfl : k = n + m' + 1 := by omega
    obtain ⟨θ, hθ⟩ := aw_cochain R μ E rfl α.1 η
    refine ⟨n + m', rfl, n.negOnePow • θ, ?_⟩
    rw [δ_units_smul, leibniz R μ rfl α.1 η θ 0 γ.1 hθ
      (by rw [Cocycle.δ_eq_zero]; exact LateralTheory.EtaleFoundations.isAW_zero_left μ _ _) (by rw [hη]; exact h), zero_add, smul_smul,
      Int.units_mul_self, one_smul]

theorem wd : LateralTheory.EtaleFoundations.cupflip_wd := LateralTheory.EtaleFoundations.cupflip_wd_of wd_aw wd_cobdry

theorem cup_mk {hk : n + m = k} (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) :
    μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
  pick_spec (wd R μ E hk) α β γ h

end LateralTheory.KummerTheory.AW

theorem LateralTheory.KummerTheory.CupAW_of : LateralTheory.KummerTheory.CupAW := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := AW.aw_exists R μ E hk α β
  exact ⟨γ, hγ, AW.cup_mk μ α β γ hγ⟩

end
end
