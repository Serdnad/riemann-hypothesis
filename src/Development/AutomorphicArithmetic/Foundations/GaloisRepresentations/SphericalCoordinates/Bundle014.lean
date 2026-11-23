module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.SameEigenvalues

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} {β : G.Cˣ}

private theorem toV_mul (y y' : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    ((GlobalTheory.LKCx.toV G v β (y * y') : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z =
      (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
        ((GlobalTheory.LKCx.toV G v β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]

private theorem toV_inv_cancel (y : GlobalTheory.LKCx.grp G β) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    Matrix.one_mulVec]

private theorem same_symm {x : (AfP p ⊗[ℚ] G.C)ˣ} {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t}
    {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)} {a b : GlobalTheory.LKCx.Dat G v β}
    (h : GlobalTheory.LKCx.Same G v β x t hx Kf K' a b) : GlobalTheory.LKCx.Same G v β x t hx Kf K' b a := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  refine ⟨y⁻¹, k⁻¹, c⁻¹, inv_mem hk1, inv_mem hk2, inv_ne_zero hc, ?_, ?_⟩
  · rw [h1, map_inv, map_inv, ← Prod.inv_mk]
    group
  · rw [h2, Matrix.mulVec_smul, toV_inv_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem same_trans {x : (AfP p ⊗[ℚ] G.C)ˣ} {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t}
    {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)} {a b d : GlobalTheory.LKCx.Dat G v β}
    (h : GlobalTheory.LKCx.Same G v β x t hx Kf K' a b) (h' : GlobalTheory.LKCx.Same G v β x t hx Kf K' b d) :
    GlobalTheory.LKCx.Same G v β x t hx Kf K' a d := by
  obtain ⟨y, k, c, hk1, hk2, hc, h1, h2⟩ := h
  obtain ⟨y', k', c', hk1', hk2', hc', h1', h2'⟩ := h'
  refine ⟨y' * y, k * k', c' * c, mul_mem hk1 hk1', mul_mem hk2 hk2', mul_ne_zero hc' hc, ?_, ?_⟩
  · rw [h1', h1, map_mul, map_mul]
    simp only [← Prod.mk_mul_mk, _root_.mul_assoc]
  · rw [h2', h2, Matrix.mulVec_smul, toV_mul, smul_smul]

private theorem minpoly_conj {F C : Type} [Field F] [Ring C] [Algebra F C] (u : Cˣ) (x : C) :
    minpoly F ((u : C) * x * ((u⁻¹ : Cˣ) : C)) = minpoly F x := by
  let e : C ≃ₐ[F] C :=
    { toFun := fun w => (u : C) * w * ((u⁻¹ : Cˣ) : C)
      invFun := fun w => ((u⁻¹ : Cˣ) : C) * w * (u : C)
      left_inv := fun w => by simp [_root_.mul_assoc]
      right_inv := fun w => by simp [_root_.mul_assoc]
      map_mul' := fun w w' => by simp [_root_.mul_assoc]
      map_add' := fun w w' => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show (u : C) * algebraMap F C r * ((u⁻¹ : Cˣ) : C) = algebraMap F C r
        rw [← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one] }
  exact minpoly.algEquiv_eq e x

private theorem posV_ne (z : GlobalTheory.LKCx.PosV G v β) : z.1 ≠ 0 := by
  intro h
  have := z.2
  rw [h] at this
  simp at this

private theorem eigL_eq {y : GlobalTheory.LKCx.grp G β} {z : Fin G.n → ℂ} {e : ℂ} (hz : z ≠ 0)
    (h : (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = e • z) :
    GlobalTheory.RootSumWeights.eigL G v β y z = e := by
  have hf : GlobalTheory.LKCx.FixL G v β y z := ⟨e, h⟩
  unfold GlobalTheory.RootSumWeights.eigL
  rw [dite_eq_left hf]
  have hs := hf.choose_spec
  exact smul_left_injective ℂ hz (hs.symm.trans h)

private theorem conj_eig (y₀ y : GlobalTheory.LKCx.grp G β) (c e : ℂ) (hc : c ≠ 0) (z : Fin G.n → ℂ) :
    (GlobalTheory.LKCx.toV G v β (y₀ * y * y₀⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
                 (c • ((GlobalTheory.LKCx.toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) =
      e • (c • ((GlobalTheory.LKCx.toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) ↔
    (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = e • z := by
  rw [Matrix.mulVec_smul, toV_mul, toV_mul, toV_inv_cancel, smul_comm e c,
    ← Matrix.mulVec_smul _ e z]
  constructor
  · intro h
    have h' := smul_right_injective (Fin G.n → ℂ) hc h
    have h'' := congrArg (fun w => (GlobalTheory.LKCx.toV G v β y₀⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h'
    simpa only [toV_inv_cancel] using h''
  · intro h
    rw [h]

end UpperTheory.Gal.W2.SameEigenvalues

open UpperTheory.Gal.W2.SameEigenvalues in
theorem UpperTheory.Gal.W2.eigSame_of :
    UpperTheory.Gal.W2.EigSame := by
  intro p _ G v c B K S hS a a' hq
  have hE := Quot.eqvGen_exact hq
  have hsame := (Equivalence.eqvGen_iff ⟨fun _ => GlobalTheory.LKCx.same_refl _ _ _ _ _ _ _ _ _,
    fun h => same_symm h, fun h h' => same_trans h h'⟩).mp hE
  obtain ⟨y₀, k, d, hk1, hk2, hd, h1, h2⟩ := hsame
  refine ⟨(MulAut.conj y₀).toEquiv, by simp, fun y => ?_⟩
  have hA : a'.1.1 = B.toAf y₀ * a.1.1 * k.1 := congrArg Prod.fst h1
  have hP : a'.1.2 = GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2 := congrArg Prod.snd h1
  have hV : a'.2.1 =
      d • ((GlobalTheory.LKCx.toV G v B.β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1) := h2
  have hFix : GlobalTheory.LKCx.FixL G v B.β (y₀ * y * y₀⁻¹) a'.2.1 ↔ GlobalTheory.LKCx.FixL G v B.β y a.2.1 := by
    unfold GlobalTheory.LKCx.FixL
    rw [hV]
    exact exists_congr fun e => conj_eig y₀ y d e hd a.2.1
  have hAf : a'.1.1⁻¹ * B.toAf (y₀ * y * y₀⁻¹) * a'.1.1 ∈ S ↔ a.1.1⁻¹ * B.toAf y * a.1.1 ∈ S := by
    rw [hA, map_mul, map_mul, map_inv]
    have : (B.toAf y₀ * a.1.1 * k.1)⁻¹ * (B.toAf y₀ * B.toAf y * (B.toAf y₀)⁻¹) *
        (B.toAf y₀ * a.1.1 * k.1) = k.1⁻¹ * (a.1.1⁻¹ * B.toAf y * a.1.1) * k.1 := by group
    rw [this]
    exact hS k.1 hk1 _
  have hP1 : a'.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β (y₀ * y * y₀⁻¹) * a'.1.2 ∈ KHT p G.m G.n 1 G.Fw ↔
      a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 ∈ KHT p G.m G.n 1 G.Fw := by
    rw [hP, map_mul, map_mul, map_inv]
    have : (GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2)⁻¹ *
        (GlobalTheory.LKCx.toP1 G B.β y₀ * GlobalTheory.LKCx.toP1 G B.β y * (GlobalTheory.LKCx.toP1 G B.β y₀)⁻¹) *
        (GlobalTheory.LKCx.toP1 G B.β y₀ * a.1.2 * k.2) =
        k.2⁻¹ * (a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2) * k.2 := by group
    rw [this]
    constructor
    · intro hm
      have h3 := mul_mem (mul_mem hk2 hm) (inv_mem hk2)
      simpa [_root_.mul_assoc] using h3
    · intro hm
      exact mul_mem (mul_mem (inv_mem hk2) hm) hk2
  have hSees : Sees B S a' (y₀ * y * y₀⁻¹) ↔ Sees B S a y := and_congr hFix (and_congr hAf hP1)
  refine ⟨hSees.symm, fun hs => ⟨?_, ?_⟩⟩
  · show minpoly G.F (((y₀ * y * y₀⁻¹ : GlobalTheory.LKCx.grp G B.β) : G.Cˣ × ℚˣ).1 : G.C) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, Units.val_mul]
    exact minpoly_conj _ _
  · obtain ⟨e, he⟩ := hs.1
    rw [eigL_eq (posV_ne a.2) he]
    apply eigL_eq (posV_ne a'.2)
    rw [hV]
    exact (conj_eig y₀ y d e hd a.2.1).mpr he
end

section

noncomputable section

open GlobalTheory.PELU GlobalTheory.UPel.HT

namespace UpperTheory.Gal.W2

private lemma power_free {T : Type} (X Y : T → ℤ) (a b : ℕ) (hab : a.Coprime b)
    (h : ∀ t, (b : ℤ) * X t = a * Y t)
    (hP : ∀ q k : ℕ, q.Prime → ((∀ t, ((q ^ k : ℕ) : ℤ) ∣ X t) ↔ ∀ t, ((q ^ k : ℕ) : ℤ) ∣ Y t))
    (t₀ : T) (h0 : Y t₀ ≠ 0) : a = 1 := by
  classical
  by_contra ha
  obtain ⟨q, hq, hqa⟩ := Nat.exists_prime_and_dvd ha
  have hqb : ¬ q ∣ b := fun hqb => hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hab hqa hqb)
  have hex : ∃ k, ¬ ∀ t, ((q ^ k : ℕ) : ℤ) ∣ Y t := by
    refine ⟨(Y t₀).natAbs, fun hall => h0 ?_⟩
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hall t₀) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self hq.one_lt
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact this (fun t => by simp)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmY : ∀ t, ((q ^ m : ℕ) : ℤ) ∣ Y t := by
    by_contra hc
    exact Nat.find_min hex (by omega) hc
  have hcop : IsCoprime ((q ^ (m + 1) : ℕ) : ℤ) (b : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqb))
  have hX : ∀ t, ((q ^ (m + 1) : ℕ) : ℤ) ∣ X t := by
    intro t
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [h t, pow_succ, Nat.cast_mul, mul_comm (a : ℤ)]
    exact mul_dvd_mul (hmY t) (Int.natCast_dvd_natCast.mpr hqa)
  have := Nat.find_spec hex
  rw [hm] at this
  exact this ((hP q (m + 1) hq).mp hX)

private lemma genus_dvd {O : Type} [Ring O] {bar : O → O} {p N : ℕ} {D₀ D' : PLat O bar}
    {t : D₀.La → D'.La} (h : Genus p N D₀ D' t) (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) :
    (∀ x y, (n : ℤ) ∣ D'.EF x y) ↔ ∀ a a', (n : ℤ) ∣ D₀.EF a a' := by
  obtain ⟨f, ν, -, -, H⟩ := h
  obtain ⟨hν, -, -, honto, hsim⟩ := H n hn hc
  constructor
  · intro hd a a'
    have h1 : (n : ℤ) ∣ ν n * D₀.EF a a' := (dvd_sub_right (hd _ _)).1 (hsim a a')
    exact hν.symm.dvd_of_dvd_mul_left h1
  · intro hd x y
    obtain ⟨a, e, rfl⟩ := honto x
    obtain ⟨a', e', rfl⟩ := honto y
    have h1 : (n : ℤ) ∣ D'.EF (f n a) (f n a') := by
      have h2 := hsim a a'
      have h3 : (n : ℤ) ∣ ν n * D₀.EF a a' := Dvd.dvd.mul_left (hd a a') _
      exact (dvd_sub_left h3).1 h2
    simp only [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_add (dvd_add h1 (Dvd.intro _ rfl)) (Dvd.intro _ rfl)

private lemma half_value {O : Type} [Ring O] {bar : O → O} {p : ℕ} {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] :
    ∃ (E₁ : LinearMap.BilinForm ℤ D'.La) (e : ℕ) (x y : D'.La), D'.EF = (2 : ℤ) • E₁ ∧ e.Coprime p ∧ E₁ x y = e := by
  obtain ⟨E₁, hE, e, he, hx⟩ := h
  let b := Module.Free.chooseBasis ℤ D'.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨x, hx⟩ := hx (b.coord i)
  refine ⟨E₁, e, x, b i, hE, he, ?_⟩
  rw [hx]
  simp

private lemma half_dvd {O : Type} [Ring O] {bar : O → O} {p : ℕ} {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] (k : ℕ) :
    (∀ x y, ((p ^ k : ℕ) : ℤ) ∣ D'.EF x y) ↔ ((p ^ k : ℕ) : ℤ) ∣ 2 := by
  obtain ⟨E₁, e, x, y, hE, he, hxy⟩ := half_value h
  constructor
  · intro hall
    have h1 := hall x y
    rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, hxy, smul_eq_mul] at h1
    have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (e : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ he.symm)
    exact hcop.dvd_of_dvd_mul_right h1
  · intro h2 x' y'
    rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_left h2 _

private lemma half_ne {O : Type} [Ring O] {bar : O → O} {p : ℕ} (hp : p.Prime) {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] : ∃ x y, D'.EF x y ≠ 0 := by
  obtain ⟨E₁, e, x, y, hE, he, hxy⟩ := half_value h
  refine ⟨x, y, ?_⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp he)
  rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, hxy, smul_eq_mul]
  exact mul_ne_zero two_ne_zero (by exact_mod_cast he0)

private lemma genus_nontrivial {O : Type} [Ring O] {bar : O → O} {p N : ℕ} {D₀ D' : PLat O bar}
    {t : D₀.La → D'.La} (hp : p.Prime) (h : Genus p N D₀ D' t) [Nontrivial D₀.La] : Nontrivial D'.La := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  obtain ⟨f, ν, -, -, hf⟩ := h
  have hn : 0 < 1 + p := by omega
  have hc : (1 + p).Coprime p := Nat.coprime_add_self_left.mpr (Nat.coprime_one_left p)
  obtain ⟨-, -, hdiv, -, -⟩ := hf (1 + p) hn hc
  let b := Module.Free.chooseBasis ℤ D₀.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨e, he⟩ := (hdiv (b i)).mp ⟨0, Subsingleton.elim _ _⟩
  have h1 := congrArg (b.coord i) he
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul,
    Finsupp.smul_apply, nsmul_eq_mul] at h1
  have h2 := Int.eq_one_of_mul_eq_one_right (by positivity) h1.symm
  have := hp.two_le
  omega

theorem clsScalar_of : ClsScalar := by
  intro p _ D N N' D' t D'' t'' hD' hD'' w r hr hEF
  have hp : p.Prime := Fact.out
  haveI : Nontrivial D.plat.La := by
    show Nontrivial D.La
    refine Module.nontrivial_of_finrank_pos (R := ℤ) ?_
    rw [D.rankLa]
    have h1 := D.m_pos
    have h2 := D.n_pos
    have h3 : 0 < Module.finrank ℚ D.F := Module.finrank_pos
    positivity
  haveI : Nontrivial D'.La := genus_nontrivial hp hD'.1
  haveI : Nontrivial D''.La := genus_nontrivial hp hD''.1
  let X : D''.La × D''.La → ℤ := fun u => D'.EF (w u.1) (w u.2)
  let Y : D''.La × D''.La → ℤ := fun u => D''.EF u.1 u.2
  have hXall : ∀ m : ℤ, (∀ u, m ∣ X u) ↔ ∀ x y, m ∣ D'.EF x y := fun m =>
    ⟨fun h x y => by simpa [X] using h (w.symm x, w.symm y), fun h u => h _ _⟩
  have hYall : ∀ m : ℤ, (∀ u, m ∣ Y u) ↔ ∀ x y, m ∣ D''.EF x y := fun m =>
    ⟨fun h x y => h (x, y), fun h u => h _ _⟩
  have hP : ∀ q k : ℕ, q.Prime → ((∀ u, ((q ^ k : ℕ) : ℤ) ∣ X u) ↔ ∀ u, ((q ^ k : ℕ) : ℤ) ∣ Y u) := by
    intro q k hq
    rw [hXall, hYall]
    by_cases hqp : q = p
    · subst hqp
      rw [half_dvd hD'.2, half_dvd hD''.2]
    · have hpos : 0 < q ^ k := pow_pos hq.pos k
      have hcop : (q ^ k).Coprime p := Nat.Coprime.pow_left k ((Nat.coprime_primes hq hp).mpr hqp)
      rw [genus_dvd hD'.1 _ hpos hcop, genus_dvd hD''.1 _ hpos hcop]
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hkey : ∀ u, (r.den : ℤ) * X u = (r.num.natAbs : ℤ) * Y u := by
    intro u
    rw [Int.natAbs_of_nonneg hnum.le]
    have h1 := hEF u.1 u.2
    have h2 : ((r.den : ℤ) * X u : ℚ) = (r.num * Y u : ℚ) := by
      push_cast
      rw [show (X u : ℚ) = ((D'.EF (w u.1) (w u.2) : ℤ) : ℚ) from rfl, h1, ← Rat.mul_den_eq_num]
      ring
    exact_mod_cast h2
  obtain ⟨x₀, y₀, h0⟩ := half_ne hp hD''.2
  obtain ⟨x₁, y₁, h1⟩ := half_ne hp hD'.2
  have ha : r.num.natAbs = 1 :=
    power_free X Y r.num.natAbs r.den r.reduced hkey hP (x₀, y₀) h0
  have hb : r.den = 1 :=
    power_free Y X r.den r.num.natAbs r.reduced.symm (fun u => (hkey u).symm)
      (fun q k hq => (hP q k hq).symm) (w.symm x₁, w.symm y₁) (by simpa [X] using h1)
  have hn1 : r.num = 1 := by omega
  rw [← Rat.num_div_den r, hn1, hb]
  norm_num

end UpperTheory.Gal.W2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem finsum_sigma {I : Type} {κ : I → Type} (f : (Σ i, κ i) → ℂ)
    (hf : (Function.support f).Finite) : ∑ᶠ s, f s = ∑ᶠ i, ∑ᶠ k, f ⟨i, k⟩ := by
  classical
  have hfi : ∀ i, (Function.support (fun k : κ i => f ⟨i, k⟩)).Finite := fun i =>
    hf.preimage (fun a _ b _ h => sigma_mk_injective h)
  rw [finsum_eq_sum_of_support_subset f (s := hf.toFinset) (by simp)]
  have hg : Function.support (fun i => ∑ᶠ k, f ⟨i, k⟩) ⊆ ↑(hf.toFinset.image Sigma.fst) := by
    intro i hi
    obtain ⟨k, hk⟩ : ∃ k, f ⟨i, k⟩ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hi (finsum_eq_zero_of_forall_eq_zero h)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨⟨i, k⟩, by simpa using hk, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hg]
  have hk : ∀ i, ∑ᶠ k, f ⟨i, k⟩ = ∑ k ∈ (hfi i).toFinset, f ⟨i, k⟩ := fun i =>
    finsum_eq_sum_of_support_subset _ (by simp)
  simp_rw [hk]
  rw [← Finset.sum_sigma]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ⟨i, k⟩
  simp only [Set.Finite.mem_toFinset, Function.mem_support, Finset.mem_sigma, Finset.mem_image]
  constructor
  · intro h
    exact ⟨⟨⟨i, k⟩, h, rfl⟩, h⟩
  · rintro ⟨-, h⟩
    exact h

private noncomputable def tm {p : ℕ} [Fact p.Prime] {G : HTGroup p} (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ)
    (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G) (b : GlobalTheory.LKCx.Dat G v B.β) : ℂ :=
  ((Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if GlobalTheory.LKCx.FixL G v B.β y b.2.1 then
      (S.indicator (1 : G.GAf → ℂ)) (b.1.1⁻¹ * B.toAf y * b.1.1) *
        (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator (1 : Gr G 1 → ℂ))
          (b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2) *
        c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0

private theorem tm_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ)
    (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G) (b : GlobalTheory.LKCx.Dat G v B.β)
    (hK : ∀ y, Sees B (K : Set G.GAf) b y → y = 1) :
    tm v c K S B b = ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if Sees B S b y then
      c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0 := by
  have hcard : Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun s t => ?_⟩, ⟨LKCx.Stab.one G v B.β _ _ _ K _ b⟩⟩
    obtain ⟨y, hy1, hy2, hy3⟩ := s
    obtain ⟨y', hy1', hy2', hy3'⟩ := t
    have e1 : y = 1 := hK y ⟨hy3, hy1, hy2⟩
    have e2 : y' = 1 := hK y' ⟨hy3', hy1', hy2'⟩
    subst e1
    subst e2
    rfl
  unfold tm
  rw [hcard, Nat.cast_one, inv_one, _root_.one_mul]
  apply finsum_congr
  intro y
  unfold Sees
  by_cases hF : GlobalTheory.LKCx.FixL G v B.β y b.2.1
  · by_cases h1 : b.1.1⁻¹ * B.toAf y * b.1.1 ∈ S
    · by_cases h2 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2 ∈ KHT p G.m G.n 1 G.Fw
      · simp [hF, h1, h2]
      · simp [hF, h1, h2]
    · simp [hF, h1]
  · simp [hF]

theorem UpperTheory.Gal.W2.sumPts_of :
    UpperTheory.Gal.W2.EigSame → UpperTheory.Gal.W2.SumPts := by
  intro hE p _ G v c K S hconj hK hS T Φ Fb w hx
  classical
  let g : LKCx.AllPts G v K (KHT p G.m G.n 1 G.Fw) → ℂ := fun s => tm v c K S (Quot.out s.1) (Quot.out s.2)
  have key : ∀ x : T, g (Φ x) = if x ∈ Fb then w x else 0 := by
    intro x
    obtain ⟨q, a, hΦ, hFb, hw⟩ := hx x
    obtain ⟨pt, hpt⟩ : ∃ pt : LKCx.Form.Pts v (Quot.out q) K (KHT p G.m G.n 1 G.Fw), Quot.mk _ a = pt := ⟨_, rfl⟩
    rw [hpt] at hΦ
    have hmk : Quot.mk _ a = Quot.mk _ (Quot.out pt) := hpt.trans (Quot.out_eq pt).symm
    obtain ⟨E, -, hE1⟩ := hE p G v c (Quot.out q) K S hconj a (Quot.out pt) hmk
    obtain ⟨E', -, hE2⟩ := hE p G v c (Quot.out q) K S hconj (Quot.out pt) a hmk.symm
    have hg : g (Φ x) = g ⟨q, pt⟩ := by rw [hΦ]
    rw [hg]
    show tm v c K S (Quot.out q) (Quot.out pt) = _
    rw [tm_eq v c K S _ _ (hK _ _)]
    by_cases hxF : x ∈ Fb
    · rw [if_pos hxF]
      obtain ⟨y, hy⟩ := hFb.1 hxF
      have hy' := ((hE1 y).1).1 hy
      rw [finsum_eq_single _ (E y)]
      · rw [if_pos hy', ((hE1 y).2 hy).1, ((hE1 y).2 hy).2, hw y hy]
      · intro y' hne
        rw [if_neg]
        intro hs
        exact hne (hS _ _ _ _ hs hy')
    · rw [if_neg hxF]
      apply finsum_eq_zero_of_forall_eq_zero
      intro y'
      rw [if_neg]
      intro hs
      exact hxF (hFb.2 ⟨E' y', ((hE2 y').1).1 hs⟩)
  have hsupp : Function.support (fun x => g (Φ x)) ⊆ ↑Fb := by
    intro x hx0
    by_contra hn
    exact hx0 (by show g (Φ x) = 0; rw [key x, if_neg (show x ∉ Fb from hn)])
  have hfin : (Function.support g).Finite := by
    apply ((Fb.finite_toSet).image Φ).subset
    intro s hs
    refine ⟨Φ.symm s, hsupp ?_, Φ.apply_symm_apply s⟩
    show g (Φ (Φ.symm s)) ≠ 0
    rw [Φ.apply_symm_apply]
    exact hs
  have h1 : RootSumWeights.cxTotalM G v c K (S.indicator 1) (KHT p G.m G.n 1 G.Fw)
      ((↑(KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1) = ∑ᶠ s, g s := by
    rw [finsum_sigma g hfin]
    rfl
  rw [h1, ← finsum_comp_equiv Φ, finsum_eq_sum_of_support_subset (fun x => g (Φ x)) hsupp]
  exact Finset.sum_congr rfl (fun x hx => by rw [key, if_pos hx])
end
