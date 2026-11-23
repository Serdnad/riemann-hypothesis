module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.WpPairing

variable {O : Type} [CommRing O] (N : NumD O)


open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.WpPairing.s_nsmul (g : N.Gt) (n : ℕ) (y : N.X) : g.s (n • y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ n 1 (N.c y) g.b = g.s y ^ n := by
  induction n with
  | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, _root_.GlobalTheory.Ex.NumD.Gt.s_zero]
  | succ n ih =>
    have hm := g.mult (n • y) y
    rw [succ_nsmul, pow_succ, ← ih]
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, Finset.prod_range_succ, one_mul]
    rw [← N.c_nsmul, ← mul_assoc, mul_right_comm, hm]
    exact mul_right_comm _ _ _

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in
private lemma cubN_one_mul_mul_pow_eq {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
    (hθ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub θ) (n : ℕ) (b b' m : A) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN θ n 1 (b * b') m * θ b b' m ^ n =
      θ (b ^ n) (b' ^ n) m * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN θ n 1 b m * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN θ n 1 b' m := by
  induction n with
  | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, hθ.face]
  | succ n ih =>
    have c1 := hθ.coc (b ^ n * b' ^ n) b b' m
    have c2 := hθ.coc (b ^ n * b) (b' ^ n) b' m
    have c3 := hθ.coc (b ^ n) (b' ^ n) b m
    have c4 := hθ.coc (b ^ n) b (b' ^ n) m
    rw [mul_right_comm (b ^ n) b (b' ^ n)] at c2
    rw [mul_comm b (b' ^ n), hθ.s01 b (b' ^ n) m] at c4
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, Finset.prod_range_succ, one_mul, mul_pow, pow_succ] at ih ⊢
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c1' := congrArg Additive.ofMul c1
    have c2' := congrArg Additive.ofMul c2
    have c3' := congrArg Additive.ofMul c3
    have c4' := congrArg Additive.ofMul c4
    simp only [ofMul_mul, ofMul_pow] at ih' c1' c2' c3' c4' ⊢
    linear_combination (norm := abel) ih' + c2' + c3' - c1' - c4'


open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.WpPairing.wp_mul_left {k : ℕ} (p p' p'' : N.QT k) : N.wp (p * p') p'' = N.wp p p'' * N.wp p' p'' := by
  have hθ := N.cub
  set g := (p : Multiplicative N.X × N.Gt).2 with hg
  set g' := (p' : Multiplicative N.X × N.Gt).2 with hg'
  set h := (p'' : Multiplicative N.X × N.Gt).2 with hh
  set x := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with hx
  set x' := Multiplicative.toAdd (p' : Multiplicative N.X × N.Gt).1 with hx'
  set y := Multiplicative.toAdd (p'' : Multiplicative N.X × N.Gt).1 with hy
  have bp := N.QT_pow_b p
  have bp' := N.QT_pow_b p'
  have bq := N.QT_pow_b p''
  rw [← hg, ← hx] at bp
  rw [← hg', ← hx'] at bp'
  rw [← hh, ← hy] at bq
  have e1 : N.tk (p * p') p'' = g.s y * g'.s y /
      N.θ (N.c y) g.b g'.b *
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b
        (g.b * g'.b) := by
    simp only [_root_.GlobalTheory.Ex.NumD.tk, Subgroup.coe_mul, Prod.snd_mul,
      _root_.GlobalTheory.Ex.NumD.Gt.mul_s,
      _root_.GlobalTheory.Ex.NumD.Gt.mul_b]
    rfl
  have e2 : N.tk p'' (p * p') = h.s (x + x') *
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 (g.b * g'.b)
        h.b := by
    simp only [_root_.GlobalTheory.Ex.NumD.tk, Subgroup.coe_mul, Prod.snd_mul, Prod.fst_mul,
      toAdd_mul, _root_.GlobalTheory.Ex.NumD.Gt.mul_b]
    rfl
  have e3 : N.tk p p'' =
      g.s y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b g.b := rfl
  have e4 : N.tk p' p'' =
      g'.s y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b g'.b := rfl
  have e5 : N.tk p'' p =
      h.s x * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 g.b h.b := rfl
  have e6 : N.tk p'' p' =
      h.s x' * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 g'.b h.b := rfl
  have hm := h.mult x x'
  have hadd := hθ.N_add k 1 h.b g.b g'.b
  have hmid := cubN_one_mul_mul_pow_eq hθ k g.b g'.b
    h.b
  have hsym : N.θ h.b g.b g'.b =
      N.θ g.b g'.b h.b := by
    rw [hθ.s01, hθ.s12]
  rw [hθ.face, one_mul, hsym] at hadd
  rw [← bp, ← bp'] at hm
  rw [← bq] at e1
  simp only [_root_.GlobalTheory.Ex.NumD.wp]
  rw [e1, e2, e3, e4, e5, e6]
  apply Additive.ofMul.injective
  have hm' := congrArg Additive.ofMul hm
  have hadd' := congrArg Additive.ofMul hadd
  have hmid' := congrArg Additive.ofMul hmid
  simp only [ofMul_mul, ofMul_pow, ofMul_div, ofMul_one] at hm' hadd' hmid' ⊢
  linear_combination (norm := abel) hadd' - hmid' - hm'


open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.WpPairing.wp_mul_right {k : ℕ} (p p' p'' : N.QT k) : N.wp p (p' * p'') = N.wp p p' * N.wp p p'' := by
  rw [N.wp_swap (p' * p'') p, _root_.GlobalTheory.Ex.WpPairing.wp_mul_left, mul_inv, ← N.wp_swap p' p, ← N.wp_swap p'' p]

noncomputable def wpHom {k : ℕ} (q : N.QT k) : N.QT k →* Oˣ :=
  MonoidHom.mk' (fun p => N.wp p q) fun p p' => wp_mul_left N p p' q


open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.WpPairing.wp_pow_left {k : ℕ} (p q : N.QT k) (n : ℕ) : N.wp (p ^ n) q = N.wp p q ^ n :=
  map_pow (_root_.GlobalTheory.Ex.WpPairing.wpHom N q) p n


open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.WpPairing.wp_qTriv {k : ℕ} (z : N.X) (q : N.QT k) : N.wp (N.qTriv k z) q = 1 := by
  have hq := N.mem_QT.mp q.2
  have h1 := _root_.GlobalTheory.Ex.WpPairing.s_nsmul N
    (q : Multiplicative N.X × N.Gt).2 k z
  have h2 := _root_.GlobalTheory.Ex.NumD.Gt.pow_s
    (q : Multiplicative N.X × N.Gt).2 k z
  rw [hq, _root_.GlobalTheory.Ex.NumD.io_s, _root_.GlobalTheory.Ex.NumD.τ_symm] at h2
  simp only [_root_.GlobalTheory.Ex.NumD.wp, _root_.GlobalTheory.Ex.NumD.tk,
    _root_.GlobalTheory.Ex.NumD.qTriv, _root_.GlobalTheory.Ex.NumD.io_s,
    _root_.GlobalTheory.Ex.NumD.io_b, toAdd_ofAdd, div_eq_one]
  rw [h1, h2]


open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.WpPairing.wp_congr_left {k : ℕ} {p p' : N.QT k} (h : N.QEq p p') (q : N.QT k) : N.wp p q = N.wp p' q := by
  obtain ⟨z, rfl⟩ := (N.qEq_iff p p').mp h
  rw [_root_.GlobalTheory.Ex.WpPairing.wp_mul_left, _root_.GlobalTheory.Ex.WpPairing.wp_qTriv, mul_one]


open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.WpPairing.wp_pairing : ∀ (O : Type) [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O), ∀ (k : ℕ) (p p' p'' : N.QT k), N.wp (p * p') p'' = N.wp p p'' * N.wp p' p'' ∧ N.wp p p = 1 ∧ N.wp p p' * N.wp p' p = 1 ∧ N.wp p p' ^ k = 1 ∧ (N.QEq p p' → N.wp p p'' = N.wp p' p'') ∧ (p.1.1 = 1 → p.1.2.b = 1 → N.wp p p' = p.1.2.s p'.1.1.toAdd) ∧ (p.1.1 = 1 → p'.1.1 = 1 → N.wp p p' = N.weil k p.1.2.b p'.1.2.b) := by
  intro O _ N k p p' p''
  refine ⟨_root_.GlobalTheory.Ex.WpPairing.wp_mul_left N p p' p'', N.wp_self p, ?_, ?_,
    fun h => _root_.GlobalTheory.Ex.WpPairing.wp_congr_left N h p'', ?_,
    fun h1 h2 => N.wp_of_eq_zero p p' (by simp [h1]) (by simp [h2])⟩
  · rw [N.wp_swap p p', mul_inv_cancel]
  · have hp : p ^ k = N.qTriv k
        (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1) := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, _root_.GlobalTheory.Ex.NumD.qTriv]
      refine Prod.ext ?_ ?_
      · simp
      · simpa using N.mem_QT.mp p.2
    rw [← _root_.GlobalTheory.Ex.WpPairing.wp_pow_left, hp, _root_.GlobalTheory.Ex.WpPairing.wp_qTriv]
  · intro h1 hb
    obtain ⟨t, ht⟩ := (N.exists_tor_iff _).mpr hb
    have hk := N.mem_QT.mp p.2
    rw [h1, toAdd_one, N.io_zero] at hk
    have htk : t ^ k = 1 := N.tor_injective (by rw [N.tor_pow, ht, N.tor_one, hk])
    have hp : p = N.qTor t htk := by
      apply Subtype.ext
      simp only [_root_.GlobalTheory.Ex.NumD.qTor]
      exact Prod.ext h1 ht.symm
    calc N.wp p p' =
          N.wp (N.qTor t htk) p' := by
          rw [← hp]
      _ = t (p' : Multiplicative N.X × N.Gt).1 := N.wp_qTor t htk p'
      _ = _ := by rw [← ht, N.torus_generator_apply, ofAdd_toAdd]

end GlobalTheory.Ex.WpPairing
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.PhiOp

section Cube
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem cub_four (u v u' v' x : A) :
    θ (u * v) (u' * v') x * θ u' v' x * θ u v x = θ (u * u') (v * v') x * θ u u' x * θ v v' x := by
  have a := h.coc (u * v) u' v' x
  have b := h.coc v u u' x
  have c := h.coc (u * u') v v' x
  rw [mul_comm v u, h.s01 v u, h.s01 v (u * u')] at b
  rw [mul_right_comm u u' v] at c
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  have c' := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a' b' c' ⊢
  linear_combination (norm := abel) b' + c' - a'

theorem cubN_mul (k : ℕ) (b b' x : A) :
    cubN θ k 1 (b * b') x * θ b b' x ^ k = θ (b ^ k) (b' ^ k) x * cubN θ k 1 b x * cubN θ k 1 b' x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := cub_four h (b ^ k) (b' ^ k) b b' x
    simp only [cubN, Finset.prod_range_succ, one_mul] at ih ⊢
    rw [mul_pow b b' k, pow_succ b, pow_succ b', pow_succ (θ b b' x)]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

theorem factor_comp (k : ℕ) (a b b' x : A) :
    cubN θ k (a * b' ^ k) b x / θ (a * b' ^ k) x b * (cubN θ k a b' (x * b) / θ a (x * b) b') * θ a b b' =
      cubN θ k a (b * b') x / θ a x (b * b') * (θ a (b' ^ k) b * cubN θ k 1 b' b) := by
  have e₁ := h.N_add k a b' x b
  have e₂ := h.N_split k (a * b' ^ k) b x
  have e₃ := h.N_split k a b' x
  have e₄ := h.N_split k a (b * b') x
  have e₅ := h.N_split k a b' b
  have e₆ := cubN_mul h k b b' x
  have e₇ := h.coc a (b' ^ k) (b ^ k) x
  have e₈ := h.coc x b b' a
  have r : ∀ u v, θ u v a = θ a u v := fun u v => by rw [h.s12, h.s01]
  simp only [r] at e₈
  rw [mul_comm (b' ^ k), ← mul_pow, h.s01 (b' ^ k)] at e₇
  rw [h.s12 b' x b, h.s01 b' b x] at e₁
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have a₈ := E e₈
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃ - a₄ + a₅ - a₆ + a₇ - a₈

end Cube

variable {O : Type} [CommRing O] (N : NumD O)

theorem s_nsmul (g : N.Gt) (k : ℕ) (y : N.X) : g.s (k • y) * cubN N.θ k 1 (N.c y) g.b = g.s y ^ k := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    have m := g.mult (k • y) y
    rw [N.c_nsmul] at m
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, one_mul, succ_nsmul, pow_succ, ← ih, ← mul_assoc, mul_right_comm, m,
      mul_right_comm]

theorem phi_phi {k : ℕ} (p p' : N.QT k) (w w' : Oˣ) (s : N.X → N.A → O) :
    N.phi p w (N.phi p' w' s) = N.phi (p * p') (w * w' * N.tk p p') s := by
  funext α x
  obtain ⟨β, rfl⟩ : ∃ β, α = β + p'.1.1.toAdd + p.1.1.toAdd :=
    ⟨α - p.1.1.toAdd - p'.1.1.toAdd, by abel⟩
  have y : (p * p').1.1.toAdd = p.1.1.toAdd + p'.1.1.toAdd := rfl
  have g : (p * p').1.2 = p.1.2 * p'.1.2 := rfl
  have e : β + p'.1.1.toAdd + p.1.1.toAdd - (p.1.1.toAdd + p'.1.1.toAdd) = β := by abel
  simp only [NumD.phi, y, g, e, add_sub_cancel_right, NumD.Gt.mul_b]
  rw [← mul_assoc, ← Units.val_mul, mul_assoc x]
  congr 2
  have m := p.1.2.mult β p'.1.1.toAdd
  have f := factor_comp N.cub k (N.c β) p.1.2.b p'.1.2.b x
  rw [← N.QT_pow_b p'] at m
  rw [NumD.Gt.mul_s, NumD.tk, N.c_add, ← N.QT_pow_b p', NumB.uV, NumB.uV, NumB.uV]
  have m' := congrArg Additive.ofMul m
  have f' := congrArg Additive.ofMul f
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at m' f' ⊢
  linear_combination (norm := abel) m' + f'

theorem phi_mul {k : ℕ} (p : N.QT k) (u w : Oˣ) (s : N.X → N.A → O) :
    N.phi p (u * w) s = (u : O) • N.phi p w s := by
  funext α x
  simp only [NumD.phi, Pi.smul_apply, smul_eq_mul, Units.val_mul]
  ring

theorem phi_comm {k : ℕ} (p p' : N.QT k) (w w' : Oˣ) (s : N.X → N.A → O) :
    N.phi p w (N.phi p' w' s) = (N.wp p p' : O) • N.phi p' w' (N.phi p w s) := by
  rw [phi_phi, phi_phi, ← phi_mul, mul_comm p' p, NumD.wp]
  congr 1
  rw [mul_comm w' w, mul_left_comm, div_mul_cancel]

theorem phi_triv {k : ℕ} (p : N.QT k) (s : N.X → N.A → O) (z : N.X) (hs : N.FE k s) (h₁ : p.1.1.toAdd = k • z)
    (h₂ : p.1.2 = N.io z) : N.phi p (N.ψ z ^ k) s = s := by
  funext α x
  have := hs z (α - k • z) x
  rw [sub_add_cancel] at this
  rw [this]
  simp only [NumD.phi, h₁, h₂, NumD.io_b, NumD.io_s]
  rw [mul_right_comm]

theorem fe_of_phi_triv {k : ℕ} (s : N.X → N.A → O) (h : ∀ z, N.phi (N.qTriv k z) (N.ψ z ^ k) s = s) :
    N.FE k s := by
  intro μ α x
  have := congrFun (congrFun (h μ) (α + k • μ)) x
  rw [← this]
  simp only [NumD.phi, NumD.qTriv, toAdd_ofAdd, add_sub_cancel_right, NumD.io_b, NumD.io_s]
  rw [mul_right_comm]

theorem wp_qTriv {k : ℕ} (z : N.X) (p : N.QT k) : N.wp (N.qTriv k z) p = 1 := by
  have a := NumD.Gt.pow_s p.1.2 k z
  rw [N.mem_QT.1 p.2, NumD.io_s, N.τ_symm] at a
  have b := s_nsmul N p.1.2 k z
  rw [NumD.wp, div_eq_one]
  exact a.trans b.symm

theorem fe_phi {k : ℕ} (p : N.QT k) (w : Oˣ) (s : N.X → N.A → O) (hs : N.FE k s) : N.FE k (N.phi p w s) :=
  fe_of_phi_triv N _ fun z => by
    rw [phi_comm, wp_qTriv, phi_triv N _ s z hs rfl rfl, Units.val_one, one_smul]

theorem phi_main : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (p p' : N.QT k) (w w' : Oˣ) (s : N.X → N.A → O), (N.FE k s → N.FE k (N.phi p w s)) ∧ N.phi p w (N.phi p' w' s) = N.phi (p * p') (w * w' * N.tk p p') s ∧ N.phi p w (N.phi p' w' s) = (N.wp p p' : O) • N.phi p' w' (N.phi p w s) ∧ ∀ z : N.X, N.FE k s → p.1.1.toAdd = k • z → p.1.2 = N.io z → N.phi p (N.ψ z ^ k) s = s :=
  fun _ _ N _ p p' w w' s =>
    ⟨fe_phi N p w s, phi_phi N p p' w w' s, phi_comm N p p' w w' s, fun z => phi_triv N p s z⟩

end GlobalTheory.Ex.PhiOp
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.existsUnique_rigidified_generator_extend_normal : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], IsNormalScheme S → ∀ (U H HU X : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  first | exact @GlobalTheory.GenExtendNormal.existsUnique_gen_extend | exact GlobalTheory.GenExtendNormal.existsUnique_gen_extend | (intros; apply GlobalTheory.GenExtendNormal.existsUnique_gen_extend <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.SelfCmp

theorem isGrpPullback_of_eq_id {S : Scheme.{0}} (G : Over S) [GrpObj G] {f : S ⟶ S} (hf : f = 𝟙 S) :
    IsGrpPullback G G f (𝟙 G.left) := by
  subst hf
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.LN.SelfCmp
end
end
