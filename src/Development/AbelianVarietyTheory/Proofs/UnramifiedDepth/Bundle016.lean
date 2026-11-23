module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle002
public import ReciprocityTheory.DualLattices.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.GoingUp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import ReciprocityTheory.DualLattices.IsPairingValueAddRight
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.DualLattices.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private theorem tenLocal_sub_mem {O A : Type} [CommRing O] [CommRing A] [IsLocalRing O]
    [IsLocalRing A] [Algebra O A] (φ : A →ₐ[O] O) (a : A) :
    a - algebraMap O A (φ a) ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have h2 := h.map φ
  simp at h2

theorem isLocalRing_tensorProduct_of_finite_of_points :
  (∀ (O A A' : Type) [CommRing O] [CommRing A] [CommRing A'] [IsLocalRing O] [IsLocalRing A] [IsLocalRing A'] [Algebra O A] [Algebra O A']
    [Module.Finite O A] [Module.Finite O A'], (A →ₐ[O] O) → (A' →ₐ[O] O) → IsLocalRing (A ⊗[O] A')) := by
  intro O A A' _ _ _ _ _ _ _ _ _ _ φ φ'
  let Φ : A ⊗[O] A' →ₐ[O] O := Algebra.TensorProduct.productMap φ φ'
  have hsurj : Function.Surjective Φ := fun o => ⟨algebraMap _ _ o, Φ.commutes o⟩
  have hM0 : ((maximalIdeal O).comap Φ).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective Φ hsurj
  refine IsLocalRing.of_unique_max_ideal ⟨(maximalIdeal O).comap Φ, hM0, ?_⟩
  intro M hM
  have hint : Algebra.IsIntegral O (A ⊗[O] A') := Algebra.IsIntegral.of_finite _ _
  have key : ∀ {B : Type} [CommRing B] [IsLocalRing B] [Algebra O B] (f : B →ₐ[O] A ⊗[O] A'),
      M.comap f = maximalIdeal B := by
    intro B _ _ _ f
    have hf : (f : B →+* A ⊗[O] A').IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap O B) _ ?_
      rw [f.comp_algebraMap]
      exact fun x => hint.isIntegral x
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (f : B →+* A ⊗[O] A') hf M
    exact IsLocalRing.eq_maximalIdeal this
  have hA := key (Algebra.TensorProduct.includeLeft : A →ₐ[O] A ⊗[O] A')
  have hA' := key (Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A')
  have hO := key (Algebra.ofId O (A ⊗[O] A'))
  have hx : ∀ x : A ⊗[O] A', x - algebraMap O _ (Φ x) ∈ M := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      have := M.add_mem hx hy
      rw [map_add (f := _), map_add (f := _)]
      convert this using 1
      ring
    | tmul a a' =>
      have h1 := tenLocal_sub_mem φ a
      have h2 := tenLocal_sub_mem φ' a'
      rw [← hA, Ideal.mem_comap, map_sub, AlgHom.commutes] at h1
      rw [← hA', Ideal.mem_comap, map_sub, AlgHom.commutes] at h2
      have h3 := M.add_mem
        (M.mul_mem_right ((Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A') a') h1)
        (M.mul_mem_left (algebraMap O (A ⊗[O] A') (φ a)) h2)
      have e1 : a ⊗ₜ[O] a' = (Algebra.TensorProduct.includeLeft : A →ₐ[O] A ⊗[O] A') a *
          (Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A') a' := by simp
      have e2 : Φ (a ⊗ₜ[O] a') = φ a * φ' a' := by simp [Φ]
      rw [e2, map_mul, e1]
      convert h3 using 1
      ring
  refine hM.eq_of_le hM0.ne_top ?_
  intro x hxM
  rw [Ideal.mem_comap, ← hO, Ideal.mem_comap]
  have := M.sub_mem hxM (hx x)
  simpa using this

end GlobalTheory
end

section

namespace GlobalTheory.TypicalCurve

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem pow_pow_mod {p h : ℕ} (hp : 0 < p) {ζ : C} (hζ : ζ ^ (p ^ h - 1) = 1) (e : ℕ) :
    ζ ^ (p ^ e) = ζ ^ (p ^ (e % h)) := by
  have h1 : ∀ y : C, y ^ (p ^ h - 1) = 1 → y ^ (p ^ h) = y := by
    intro y hy
    have : p ^ h = (p ^ h - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)).symm
    rw [this, pow_succ, hy, one_mul]
  have h2 : ∀ k : ℕ, ζ ^ ((p ^ h) ^ k) = ζ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, h1 ζ hζ]
  conv_lhs => rw [← Nat.div_add_mod e h, pow_add, pow_mul, pow_mul, h2]

theorem pow_pow_eq_iff {p h : ℕ} (hp : 1 < p) (hh : 0 < h) {ζ : C}
    (hζ : IsPrimitiveRoot ζ (p ^ h - 1)) (e e' : ℕ) :
    ζ ^ (p ^ e) = ζ ^ (p ^ e') ↔ (e : ZMod h) = (e' : ZMod h) := by
  have hp0 : 0 < p := by omega
  have hN : p ^ h - 1 ≠ 0 := by
    have := Nat.one_lt_pow hh.ne' hp
    omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  rw [ZMod.natCast_eq_natCast_iff', pow_pow_mod hp0 hζ.pow_eq_one e,
    pow_pow_mod hp0 hζ.pow_eq_one e']
  refine ⟨fun H => ?_, fun H => by rw [H]⟩
  have key : ∀ a, a < h → p ^ a - 1 < p ^ h - 1 := fun a ha => by
    have h1 := Nat.pow_lt_pow_right hp ha
    have h2 := Nat.one_le_pow a p hp0
    omega
  have s : ∀ a, ζ ^ (p ^ a) = ζ ^ (p ^ a - 1) * ζ := fun a => by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp0)]
  rw [s, s] at H
  have H2 := hζ.pow_inj (key _ (Nat.mod_lt _ hh)) (key _ (Nat.mod_lt _ hh))
    (mul_right_cancel₀ hζ0 H)
  have h1 := Nat.one_le_pow (e % h) p hp0
  have h2 := Nat.one_le_pow (e' % h) p hp0
  exact Nat.pow_right_injective hp (show p ^ (e % h) = p ^ (e' % h) by omega)

theorem isCurve_nsmulF (G : LogFGL v d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    ∀ n, IsCurve v (G.nsmulF n ga)
  | 0 => isCurve_zero
  | n + 1 => isCurve_add G h (isCurve_nsmulF G h n)

theorem lgCurve_nsmulF (G : LogFGL v d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    ∀ n a, G.lgCurve (G.nsmulF n ga) a = (n : C) • G.lgCurve ga a
  | 0, a => by
    rw [Nat.cast_zero, zero_smul]; exact lgCurve_zero G a
  | n + 1, a => by
    rw [LogFGL.nsmulF, lgCurve_add G (fun b => (h b).1) (fun b => (isCurve_nsmulF G h n b).1),
      lgCurve_nsmulF G h n a, Nat.cast_succ, add_smul, one_smul, add_comm]

def muCurve {G : LogFGL v d} {p h : ℕ} {ty : Fin d → ZMod h} (μ : MuAction G p h ty) (z : C)
    (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst ga (μ.mul z a)

theorem isCurve_muCurve {G : LogFGL v d} {p h : ℕ} {ty : Fin d → ZMod h} (μ : MuAction G p h ty)
    {z : C} (hz : z ^ (p ^ h - 1) = 1) {ga : Fin d → PowerSeries C} (hga : IsCurve v ga) :
    IsCurve v (muCurve μ z ga) := fun a =>
  ⟨constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun b => (hga b).1)
      (fun b => (hga b).1) (μ.mul_const z a),
    psIsInt_iff.2 (mvIsInt_subst v (μ.mul_int z hz a) (fun b => psIsInt_iff.1 (hga b).2)
      (fun b => (hga b).1))⟩

theorem lgCurve_muCurve {G : LogFGL v d} {p h : ℕ} {ty : Fin d → ZMod h} (μ : MuAction G p h ty)
    {z : C} (hz : z ^ (p ^ h - 1) = 1) {ga : Fin d → PowerSeries C} (hga : IsCurve v ga)
    (a : Fin d) :
    G.lgCurve (muCurve μ z ga) a = (z ^ (p ^ (ty a).val)) • G.lgCurve ga a := by
  have hs : HasSubst ga := hasSubst_of_constantCoeff_zero fun b => (hga b).1
  have hm : HasSubst (μ.mul z) := hasSubst_of_constantCoeff_zero (μ.mul_const z)
  have e := subst_comp_subst_apply hm hs (G.lg a)
  rw [μ.lg_mul z hz a, subst_smul hs] at e
  exact e.symm

theorem typicalCurves_of_type_of_typical_tangents :
  (∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d : ℕ) (G : LogFGL v d) (u : Fin d → C), (∀ a, IsIntV v (u a)) → ∃ γ : Fin d → PowerSeries C, IsCurve v γ ∧ G.IsPTypical p γ ∧ tangent γ = u) →
  TypicalCurveEigenspace := by
  intro H C _ _ _ v p hp hv d h hh ty G μ i u hu hui
  obtain ⟨γ, hγ, hγt, hγu⟩ := H C v p hp hv d G u hu
  have : NeZero h := ⟨hh.ne'⟩
  have hN : p ^ h - 1 ≠ 0 := by
    have := Nat.one_lt_pow hh.ne' hp.one_lt
    omega
  have hpN : ¬ p ∣ p ^ h - 1 := by
    intro hd
    have h1 : p ∣ p ^ h := dvd_pow_self p hh.ne'
    have h2 := Nat.dvd_sub h1 hd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hN0 : ((p ^ h - 1 : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 hN
  have : NeZero ((p ^ h - 1 : ℕ) : C) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C (p ^ h - 1)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  have hpow : ∀ y : C, y ^ (p ^ h - 1) = 1 → ∀ j : ℕ, (y ^ j) ^ (p ^ h - 1) = 1 := fun y hy j => by
    rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have hζi : ζ⁻¹ ^ (p ^ h - 1) = 1 := by rw [inv_pow, hζ.pow_eq_one, inv_one]
  let x : ℕ → C := fun j => (ζ⁻¹ ^ (p ^ i.val)) ^ j
  have hx : ∀ j, IsIntV v (x j) := fun j => by
    unfold IsIntV
    rw [v_eq_zero_of_pow_eq_one hN (hpow _ (hpow _ hζi _) j)]
  let g : Fin (p ^ h - 1) → Fin d → PowerSeries C := fun j =>
    muCurve μ (ζ ^ (j : ℕ)) (rescaleCurve (x j) γ)
  have hg : ∀ j, IsCurve v (g j) := fun j =>
    isCurve_muCurve μ (hpow _ hζ.pow_eq_one _) (isCurve_rescale (hx j) hγ)
  obtain ⟨ε, ⟨hε, hεe⟩, -⟩ := pt1 C v p hp hv d G (p ^ h - 1) hpN (G.sumF g) (isCurve_sumF G g hg)
  have hlg : ∀ a m, ((p ^ h - 1 : ℕ) : C) * PowerSeries.coeff m (G.lgCurve ε a) =
      (∑ j ∈ Finset.range (p ^ h - 1), (ζ ^ (p ^ (ty a).val) * ζ⁻¹ ^ (p ^ i.val * m)) ^ j) *
        PowerSeries.coeff m (G.lgCurve γ a) := by
    intro a m
    have e := congrArg (PowerSeries.coeff m) (lgCurve_nsmulF G hε (p ^ h - 1) a)

    rw [hεe, lgCurve_sumF G g hg, map_sum, PowerSeries.coeff_smul, smul_eq_mul] at e
    rw [← e, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g]
    rw [lgCurve_muCurve μ (hpow _ hζ.pow_eq_one _) (isCurve_rescale (hx j) hγ),
      lgCurve_rescale G _ (fun b => (hγ b).1), PowerSeries.coeff_smul, smul_eq_mul,
      PowerSeries.coeff_rescale]
    simp only [x]
    ring
  have hlc : ∀ a n, G.lc p ε n a = if ty a = i + (n : ZMod h) then G.lc p γ n a else 0 := by
    intro a n
    have e := hlg a (p ^ n)
    rw [← pow_add] at e
    have hiff := pow_pow_eq_iff hp.one_lt hh hζ (ty a).val (i.val + n)
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hiff
    have hne : ζ ^ (p ^ (i.val + n)) ≠ 0 := pow_ne_zero _ hζ0
    split_ifs with hc
    · rw [hiff.2 hc, inv_pow, mul_inv_cancel₀ hne] at e
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at e
      exact mul_left_cancel₀ hN0 e
    · have h1 : ζ ^ (p ^ (ty a).val) * ζ⁻¹ ^ (p ^ (i.val + n)) ≠ 1 := by
        intro h1
        rw [inv_pow, mul_inv_eq_one₀ hne] at h1
        exact hc (hiff.1 h1)
      rw [geom_sum_eq h1, mul_pow, hpow _ hζ.pow_eq_one, hpow _ hζi, mul_one, sub_self, zero_div,
        zero_mul] at e
      exact (mul_eq_zero.1 e).resolve_left hN0
  refine ⟨ε, hε, ⟨fun a m hm => ?_, fun n a ha => ?_⟩, ?_⟩
  · have e := hlg a m
    rw [hγt a m hm, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_left hN0
  · rw [hlc, if_neg ha]
  · rw [tangent_eq_lc_zero G p (fun b => (hε b).1)]
    funext a
    rw [hlc, ← tangent_eq_lc_zero G p (fun b => (hγ b).1), hγu, Nat.cast_zero, add_zero]
    split_ifs with hc
    · rfl
    · exact (hui a hc).symm

end

end GlobalTheory.TypicalCurve
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section
variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}

private lemma smul_inj {x y : B.G R} (w : B.P R x y) {l l' : (R : Type)ˣ}
    (h : B.smul l w = B.smul l' w) : l = l' :=
  (B.trans w (B.smul l' w)).unique h rfl

private lemma transport_left_smul_frame (b : ∀ x y, B.P R x y) {x x' y : B.G R} (h : x = x') (l : (R : Type)ˣ) :
    B.tr1 h (B.smul l (b x y)) = B.smul l (b x' y) := by
  subst h; rfl

private lemma transport_right_smul_frame (b : ∀ x y, B.P R x y) {x y y' : B.G R} (h : y = y') (l : (R : Type)ˣ) :
    B.tr2 h (B.smul l (b x y)) = B.smul l (b x y') := by
  subst h; rfl

private lemma transport_left_of_heq {x x' y : B.G R} (h : x = x') {u : B.P R x y} {w : B.P R x' y}
    (e : HEq u w) : B.tr1 h u = w := by
  subst h; exact eq_of_heq e

private lemma transport_right_of_heq {x y y' : B.G R} (h : y = y') {u : B.P R x y} {w : B.P R x y'}
    (e : HEq u w) : B.tr2 h u = w := by
  subst h; exact eq_of_heq e

private lemma heq_transport_left {x x' y : B.G R} (h : x = x') (u : B.P R x y) : HEq (B.tr1 h u) u := by
  subst h; rfl

private lemma heq_transport_right {x y y' : B.G R} (h : y = y') (u : B.P R x y) : HEq (B.tr2 h u) u := by
  subst h; rfl

private lemma add_left_transport_heq {x x' x'' y : B.G R} (h : x = x') (u : B.P R x y) (w : B.P R x'' y) :
    HEq (B.add1 (B.tr1 h u) w) (B.add1 u w) := by
  subst h; rfl

private lemma add_right_transport_heq {x y y' y'' : B.G R} (h : y = y') (u : B.P R x y) (w : B.P R x y'') :
    HEq (B.add2 (B.tr2 h u) w) (B.add2 u w) := by
  subst h; rfl

private lemma frame_zero1 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x x' y, B.add1 (b x y) (b x' y) = B.smul (t x x' y) (b (x + x') y)) (y : B.G R) :
    b 0 y = B.smul (t 0 0 y) (B.zero1 y) := by
  obtain ⟨l, hl, -⟩ := B.trans (b 0 y) (B.zero1 y)
  have h1 := transport_left_of_heq B (zero_add (0 : B.G R)) (B.zeroFst_add (B.zero1 y))
  rw [← hl, B.addFst_smul, h, ← B.mul_smul, transport_left_smul_frame] at h1
  have h2 := smul_inj B _ h1
  have h3 : t 0 0 y * l = 1 := by
    rw [_root_.mul_assoc, mul_eq_left] at h2
    rw [mul_comm, h2]
  rw [← hl, ← B.mul_smul, h3, B.one_smul]

private lemma frame_zero2 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x y y', B.add2 (b x y) (b x y') = B.smul (t x y y') (b x (y + y'))) (x : B.G R) :
    b x 0 = B.smul (t x 0 0) (B.zero2 x) := by
  obtain ⟨l, hl, -⟩ := B.trans (b x 0) (B.zero2 x)
  have h1 := transport_right_of_heq B (zero_add (0 : B.G R)) (B.zeroSnd_add (B.zero2 x))
  rw [← hl, B.addSnd_smul, h, ← B.mul_smul, transport_right_smul_frame] at h1
  have h2 := smul_inj B _ h1
  have h3 : t x 0 0 * l = 1 := by
    rw [_root_.mul_assoc, mul_eq_left] at h2
    rw [mul_comm, h2]
  rw [← hl, ← B.mul_smul, h3, B.one_smul]

private lemma frame_nsmul1 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x x' y, B.add1 (b x y) (b x' y) = B.smul (t x x' y) (b (x + x') y)) (x y : B.G R)
    (N : ℕ) : B.nsmul1 (b x y) (N + 1) =
      B.smul (∏ k ∈ Finset.range N, t ((k + 1) • x) x y) (b ((N + 1) • x) y) := by
  induction N with
  | zero =>
    rw [Finset.prod_range_zero, ← transport_left_smul_frame B b (show x = (0 + 1) • x by simp), B.one_smul]
    apply eq_of_heq
    unfold BX.nsmul1 BX.nsmul1
    exact (heq_transport_left B _ _).trans ((add_left_transport_heq B _ _ _).trans
      ((B.zeroFst_add _).trans (heq_transport_left B _ _).symm))
  | succ N ih =>
    rw [BX.nsmul1, ih, Finset.prod_range_succ]
    conv_lhs => rw [← B.one_smul (b x y), B.addFst_smul, h, ← B.mul_smul, transport_left_smul_frame, _root_.mul_one]

private lemma frame_nsmul2 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x y y', B.add2 (b x y) (b x y') = B.smul (t x y y') (b x (y + y'))) (x y : B.G R)
    (N : ℕ) : B.nsmul2 (b x y) (N + 1) =
      B.smul (∏ k ∈ Finset.range N, t x ((k + 1) • y) y) (b x ((N + 1) • y)) := by
  induction N with
  | zero =>
    rw [Finset.prod_range_zero, ← transport_right_smul_frame B b (show y = (0 + 1) • y by simp), B.one_smul]
    apply eq_of_heq
    unfold BX.nsmul2 BX.nsmul2
    exact (heq_transport_right B _ _).trans ((add_right_transport_heq B _ _ _).trans
      ((B.zeroSnd_add _).trans (heq_transport_right B _ _).symm))
  | succ N ih =>
    rw [BX.nsmul2, ih, Finset.prod_range_succ]
    conv_lhs => rw [← B.one_smul (b x y), B.addSnd_smul, h, ← B.mul_smul, transport_right_smul_frame, _root_.mul_one]

private lemma coboundary_rearrange {G : Type*} [CommGroup G] (m m' p q r s t : G) (h : r * s = t * (p * q)) :
    m * m' * t * r⁻¹ = m * m' * (p⁻¹ * q⁻¹) * s := by
  rw [← eq_inv_mul_iff_mul_eq] at h
  rw [h, ← mul_inv, ← _root_.mul_assoc r⁻¹, _root_.mul_assoc (m * m') (p * q)⁻¹,
    mul_comm (p * q)⁻¹, mul_inv_cancel_right, _root_.mul_assoc (m * m'), mul_comm t]

private noncomputable def frameEquiv {x y : B.G R} (w : B.P R x y) : (R : Type)ˣ ≃ B.P R x y :=
  Equiv.ofBijective (fun l => B.smul l w)
    ⟨fun _ _ h => smul_inj B w h, fun v => (B.trans w v).exists⟩

private lemma frameEquiv_trans {x y x' y' : B.G R} (w : B.P R x y) (w' : B.P R x' y')
    (l : (R : Type)ˣ) :
    ((frameEquiv B w).symm.trans (frameEquiv B w')) (B.smul l w) = B.smul l w' := by
  have : B.smul l w = frameEquiv B w l := rfl
  rw [this, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

end

theorem bx_frame_pairing_adj :
  (∀ {R₀ : Type} [CommRing R₀] (B : BX R₀) (b : ∀ R x y, B.P R x y) (t₁ t₂ : ∀ R : LAlg R₀, B.G R → B.G R → B.G R → (R : Type)ˣ),
    (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R x x' y) (b R (x + x') y)) →
    (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R x y y') (b R x (y + y'))) →
    (∀ R (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ), B.IsPairing (N + 1) x y z ↔ (N + 1) • x = 0 ∧ (N + 1) • y = 0 ∧
      z = (t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) / (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) ∧
    ∀ (O : LAlg R₀) (a a' : OEnd B O) (u : ∀ {R : LAlg R₀}, LHom O R → B.G R → B.G R → (R : Type)ˣ),
      (∀ {R : LAlg R₀} (s : LHom O R) x x' y, u s (x + x') y * t₁ R x x' (a'.f s y) = t₁ R (a.f s x) (a.f s x') y * (u s x y * u s x' y)) →
      (∀ {R : LAlg R₀} (s : LHom O R) x y y', u s x (y + y') * t₂ R x (a'.f s y) (a'.f s y') = t₂ R (a.f s x) y y' * (u s x y * u s x y')) →
      ∃ A : OAdj B O, A.a = a ∧ A.ab = a') := by
  intro R₀ _ B b t₁ t₂ h₁ h₂
  refine ⟨fun R N x y z => ?_, fun O a a' u hu₁ hu₂ => ?_⟩
  · have key : ∀ (hx : (N + 1) • x = 0) (hy : (N + 1) • y = 0), B.IsPairing (N + 1) x y
        ((t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) /
          (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) := by
      intro hx hy
      refine ⟨hx, hy, b R x y, _, _, ?_, ?_, rfl⟩
      · rw [frame_nsmul1 B (b R) (t₁ R) (h₁ R), transport_left_smul_frame, frame_zero1 B (b R) (t₁ R) (h₁ R),
          ← B.mul_smul, mul_comm]
      · rw [frame_nsmul2 B (b R) (t₂ R) (h₂ R), transport_right_smul_frame, frame_zero2 B (b R) (t₂ R) (h₂ R),
          ← B.mul_smul, mul_comm]
    constructor
    · intro h
      exact ⟨h.1, h.2.1, B.pairing_unique _ _ _ _ _ h (key h.1 h.2.1)⟩
    · rintro ⟨hx, hy, rfl⟩
      exact key hx hy
  · refine ⟨⟨a, a', fun {R} s x z => (frameEquiv B (b R (a.f s x) z)).symm.trans
      (frameEquiv B (B.smul (u s x z)⁻¹ (b R x (a'.f s z)))), ?_, ?_, ?_⟩, rfl, rfl⟩
    · intro R s x z l v
      obtain ⟨m, rfl, -⟩ := B.trans (b R (a.f s x) z) v
      rw [← B.mul_smul, frameEquiv_trans, frameEquiv_trans, B.mul_smul]
    · intro R s x x' z v v'
      obtain ⟨m, rfl, -⟩ := B.trans (b R (a.f s x) z) v
      obtain ⟨m', rfl, -⟩ := B.trans (b R (a.f s x') z) v'
      rw [B.addFst_smul, h₁, ← B.mul_smul, transport_left_smul_frame, frameEquiv_trans, frameEquiv_trans,
        frameEquiv_trans, B.addFst_smul, B.addFst_smul, h₁, ← B.mul_smul, ← B.mul_smul, ← B.mul_smul]
      congr 1
      have := hu₁ s x x' z
      exact coboundary_rearrange _ _ _ _ _ _ _ this
    · intro R s x z z' v v'
      obtain ⟨m, rfl, -⟩ := B.trans (b R (a.f s x) z) v
      obtain ⟨m', rfl, -⟩ := B.trans (b R (a.f s x) z') v'
      rw [B.addSnd_smul, h₂, ← B.mul_smul, frameEquiv_trans, frameEquiv_trans,
        frameEquiv_trans, B.addSnd_smul, B.addSnd_smul, h₂, ← B.mul_smul, ← B.mul_smul, ← B.mul_smul,
        transport_right_smul_frame]
      congr 1
      have := hu₂ s x z z'
      exact coboundary_rearrange _ _ _ _ _ _ _ this

end GlobalTheory
end
