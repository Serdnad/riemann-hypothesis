module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle004
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch
noncomputable section
namespace GlobalTheory.Ex.Arch.Wp

variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}

theorem ex_nsmul (d : Dict N B) (i : ℕ) (z : Fin B.gB → ℂ) : d.ex (i • z) = d.ex z ^ i := by
  induction i with
  | zero =>
    rw [zero_smul, pow_zero]
    exact (d.ab.2.2.1 0).2 (zero_mem _)
  | succ i ih => rw [succ_nsmul, d.ab.1, ih, pow_succ]

theorem cubN_frame (d : Dict N B) (k : ℕ) (x' x : Fin B.gB → ℂ) :
    cubN N.θ k 1 (d.ex x') (d.ex x) * d.fr (k • x') * d.fr x * d.fr (x' + x) ^ k =
      d.fr (k • x' + x) * (d.fr x' * d.fr x) ^ k := by
  induction k with
  | zero => simp [cubN, d.ab.2.2.2.1]
  | succ k ih =>
    have h := d.ab.2.2.2.2.2.1 (k • x') x' x
    rw [ex_nsmul] at h
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, succ_nsmul, _root_.one_mul (d.ex x' ^ k)]
    replace h := congrArg Additive.ofMul h
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [pow_succ, ofMul_mul] at h ih ⊢
    linear_combination (norm := abel) h + ih

theorem tk_frame (d : Dict N B) {k : ℕ} (hk : 0 < k) {la la' : B.La} {p p' : N.QT k} (h : d.Rep k la p)
    (h' : d.Rep k la' p') :
    (N.tk p p' : ℂ) * (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2) : ℂ) ^ k =
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) *
        ((d.fr ((k : ℂ)⁻¹ • B.P0 la').2 : ℂ) * d.fr ((k : ℂ)⁻¹ • B.P0 la).2) ^ k := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set x := ((k : ℂ)⁻¹ • B.P0 la).2 with hx
  set x' := ((k : ℂ)⁻¹ • B.P0 la').2 with hx'
  have e : k • x' = B.ct la'.y + la'.l := by
    rw [hx', Prod.smul_snd, AnArc.degeneratingTori_basePeriodMap_snd, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk', one_smul]
  have c := congrArg (Units.val : ℂˣ → ℂ) (cubN_frame d k x' x)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c
  have s := h.2.2 la'.y
  have f1 := d.ab.2.2.2.2.1 la'.l (B.ct la'.y + x)
  have f2 := d.ab.2.2.2.2.1 la'.l (B.ct la'.y)
  rw [AnArc.ah_add, add_right_comm, ← e] at f1
  rw [← e] at f2
  rw [← hx, f1, f2, eTwoPi] at s
  rw [NumD.tk, h'.1, h.2.1, h'.2.1, Units.val_mul, Complex.exp_sub, ← hx, ← hx']
  have n1 := B.ah_ne_zero la'.l (B.ct la'.y)
  have n2 := (d.fr (k • x')).ne_zero
  have n3 := (d.fr x).ne_zero
  have n4 := (d.fr (k • x' + x)).ne_zero
  have n5 := Complex.exp_ne_zero (Real.pi * B.H x la'.l)
  rw [div_mul_eq_mul_div, eq_div_iff n5]
  apply mul_left_cancel₀ (mul_ne_zero n1 (mul_ne_zero n2 (mul_ne_zero n3 n4)))
  linear_combination (B.ah la'.l (B.ct la'.y) * Complex.exp (Real.pi * B.H x la'.l) * (d.fr (k • x' + x) : ℂ) *
    (p.1.2.s (d.eX la'.y) : ℂ)) * c + (((d.fr x' : ℂ) * d.fr x) ^ k * (d.fr (k • x' + x) : ℂ)) * s

theorem wp_eq : WpSt := by
  intro O _ _ N B d k hk la la' p p' h h'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have a := tk_frame d hk h h'
  have b := tk_frame d hk h' h
  rw [add_comm, mul_comm (d.fr _ : ℂ)] at b
  have n1 := pow_ne_zero k (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2)).ne_zero
  have E : (B.Ef la.l la'.l : ℂ) = ((B.H la.l la'.l).im : ℂ) := by
    rw [← B.Ef_eq_im]; simp
  have C := Complex.sub_conj (B.H la.l la'.l)
  rw [B.H_conj] at C
  have key : Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (B.EF la la' : ℂ) / k) *
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la').1 la.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la').2 la.l) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply, AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.degeneratingTori_basePeriodMap_snd,
      AnArc.H_smul_left, AnArc.H_add_left, smul_eq_mul, AnArc.EF_apply, B.T_symm la'.y la.y]
    push_cast at C ⊢
    rw [E]
    have hI := Complex.I_ne_zero
    field_simp
    linear_combination (-1 : ℂ) * C
  rw [NumD.wp, Units.val_div_eq_div_val, div_eq_iff (N.tk p' p).ne_zero]
  apply mul_right_cancel₀ n1
  rw [a, key, _root_.mul_assoc _ (N.tk p' p : ℂ), b, _root_.mul_assoc]

end GlobalTheory.Ex.Arch.Wp
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

theorem period_constantPart_eq_zero_injective {O : Type} [CommRing O] [StarRing O] (B : AnArc O) (la : B.La) (hy : la.y = 0)
    (h : B.P0 la = 0) : la = 0 := by
  have hl : la.l = 0 := by
    have := congrArg Prod.snd h
    rw [AnArc.degeneratingTori_basePeriodMap_snd, hy, map_zero, zero_add] at this
    exact Subtype.ext this
  refine AnArc.La.ext hy (AddMonoidHom.ext fun x => ?_) hl
  have : (B.P0 la).1 x = 0 := by rw [h]; rfl
  rw [AnArc.degeneratingTori_basePeriodMap_fst_apply, hy, hl] at this
  simpa using this

theorem qkSt_of_ptSt : PtSt → QkSt := by
  intro hP O _ _ N B d k hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP O N B d
  choose E hE hU using h1
  have hiff : ∀ v g, d.IsPt v g ↔ g = E v := fun v g => ⟨hU v g, fun h => h ▸ hE v⟩
  have hadd : ∀ v v', E (v + v') = E v * E v' := fun v v' => (hU _ _ (h3 _ _ _ _ (hE v) (hE v'))).symm
  have hzero : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hpow : ∀ (n : ℕ) v, E (n • v) = E v ^ n := fun n v => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hper : ∀ la : B.La, E (B.P0 la) = N.io (d.eX la.y) := fun la => (hU _ _ (h5 la)).symm
  have hker : ∀ v v', E v = E v' → ∃ la : B.La, la.y = 0 ∧ v = v' + B.P0 la := fun v v' h => by
    have e : E (v - v') * E v' = E v' := by rw [← hadd, sub_add_cancel, h]
    obtain ⟨la, hy, hl⟩ := (h4 (v - v')).1 ((hiff _ _).2 (mul_eq_right.1 e).symm)
    exact ⟨la, hy, by rw [← hl, add_sub_cancel]⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hc1 : ∀ v : B.V, (k : ℂ)⁻¹ • (k • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hc2 : ∀ v : B.V, k • ((k : ℂ)⁻¹ • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  have hrep : ∀ (la : B.La) (p : N.QT k), d.Rep k la p ↔
      p.1.1.toAdd = d.eX la.y ∧ p.1.2 = E ((k : ℂ)⁻¹ • B.P0 la) := fun la p => and_congr Iff.rfl (hiff _ _)
  refine ⟨fun p => ?_, fun la => ?_, fun la la' p p' h h' => ?_, fun la la' p p' h h' => ?_⟩
  · obtain ⟨v, hv⟩ := h2 p.1.2
    have hv' := (hiff _ _).1 hv
    have e : E (k • v) = E (B.P0 (AnArc.La.mk (d.eX.symm p.1.1.toAdd) 0 0)) := by
      rw [hpow, hper, ← hv', AnArc.La.mk_y, AddEquiv.apply_symm_apply]
      exact N.mem_QT.1 p.2
    obtain ⟨la, hy, hl⟩ := hker _ _ e
    refine ⟨AnArc.La.mk (d.eX.symm p.1.1.toAdd) 0 0 + la, (hrep _ _).2 ⟨?_, ?_⟩⟩
    · rw [AnArc.La.add_y, hy, add_zero, AnArc.La.mk_y, AddEquiv.apply_symm_apply]
    · rw [map_add (f := _), ← hl, hc1, hv']
  · refine ⟨⟨(Multiplicative.ofAdd (d.eX la.y), E ((k : ℂ)⁻¹ • B.P0 la)), ?_⟩, (hrep _ _).2 ⟨rfl, rfl⟩, fun p hp => ?_⟩
    · rw [NumD.mem_QT, ← hpow, hc2, hper]
      rfl
    · obtain ⟨a, b⟩ := (hrep _ _).1 hp
      exact Subtype.ext (Prod.ext a b)
  · obtain ⟨a, b⟩ := (hrep _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _).1 h'
    refine (hrep _ _).2 ⟨?_, ?_⟩
    · rw [AnArc.La.add_y, map_add (f := _), ← a, ← a']
      rfl
    · rw [map_add (f := _), smul_add, hadd, ← b, ← b']
      rfl
  · obtain ⟨a, b⟩ := (hrep _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _).1 h'
    constructor
    · rintro ⟨z, c, c'⟩
      set z₀ : B.La := AnArc.La.mk (d.eX.symm z) 0 0 with hz₀
      have hz : d.eX z₀.y = z := by rw [hz₀, AnArc.La.mk_y, AddEquiv.apply_symm_apply]
      have e : E ((k : ℂ)⁻¹ • B.P0 la') = E ((k : ℂ)⁻¹ • B.P0 la + B.P0 z₀) := by
        rw [hadd, hper, hz, ← b, ← b', c']
      obtain ⟨e₀, hy, hl⟩ := hker _ _ e
      refine ⟨z₀ + e₀, sub_eq_zero.1 (period_constantPart_eq_zero_injective B _ ?_ ?_)⟩
      · apply d.eX.injective
        rw [AnArc.La.sub_y, AnArc.La.add_y, AnArc.La.nsmul_y, AnArc.La.add_y, hy, add_zero, map_sub, map_add (f := _),
          map_nsmul, hz, ← a, ← a', c, sub_self, map_zero]
      · rw [map_sub, map_add (f := _), map_nsmul, map_add (f := _), ← hc2 (B.P0 la'), hl, add_assoc, smul_add, hc2, sub_self]
    · rintro ⟨e, rfl⟩
      refine ⟨d.eX e.y, ?_, ?_⟩
      · rw [a, a', AnArc.La.add_y, AnArc.La.nsmul_y, map_add (f := _), map_nsmul]
      · rw [b, b', map_add (f := _), map_nsmul, smul_add, hc1, hadd, hper]

end GlobalTheory.Ex.Arch
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem exists_symm_bilin_ext {L V : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] [AddCommGroup V]
    [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] (P : L →+ V) (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (hr : Module.finrank ℤ L = Module.finrank ℝ V) (b : L →+ (V →ₗ[ℂ] ℂ)) (hb : ∀ a c, b a (P c) = b c (P a)) :
    ∃ Bs : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ u v, Bs u v = Bs v u) ∧ ∀ a v, Bs (P a) v = b a v := by
  classical
  let e := Module.Free.chooseBasis ℤ L
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => P (e i)) := by
    rw [← hP, Submodule.span_le]
    rintro _ ⟨a, rfl⟩

    rw [← e.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => P (e i)) i)) _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℝ V := by
    rw [← hr, Module.finrank_eq_card_chooseBasisIndex]
  let β := basisOfTopLeSpanOfCardEqFinrank _ htop hcard
  have hβ : ∀ i, β i = P (e i) := fun i => by simp [β]
  let f : V →ₗ[ℝ] (V →ₗ[ℂ] ℂ) := β.constr ℝ fun i => b (e i)
  have hf : ∀ a, f (P a) = b a := fun a => by
    rw [← e.sum_repr a]

    simp only [map_sum, map_zsmul, ← hβ, f, Module.Basis.constr_basis]
  have hs : ∀ u v, f u v = f v u := by
    let F : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun u v => f u v) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    have : F = F.flip := β.ext fun i => β.ext fun j => by
      change f (β i) (β j) = f (β j) (β i)
      rw [hβ, hβ, hf, hf, hb]
    exact fun u v => LinearMap.congr_fun₂ this u v
  refine ⟨LinearMap.mk₂ ℂ (fun u v => f u v) (fun _ _ _ => by simp) (fun c u v => ?_) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp), hs, fun a v => ?_⟩
  · rw [hs, map_smul, hs]
  · exact congrArg (fun g => g v) (hf a)

theorem hermForm_sub_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm z w - hermForm Hm w z = 2 * Complex.I * (hermForm Hm z w).im := by
  have h : ∀ i k, starRingEnd ℂ (Hm i k) = Hm k i := fun i k => hH.apply k i
  have hc : starRingEnd ℂ (hermForm Hm z w) = hermForm Hm w z := by

    simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [← hc, Complex.sub_conj]
  push_cast; ring

variable {O : Type} [CommRing O] [StarRing O] (B : AnArc O)

theorem lin_period (w : ℂ) (a c : B.La) : lin B a (B.Pw w c) =
    -(2 * Real.pi * Complex.I) * (B.T c.y a.y + c.n a.y + w * B.be c.y a.y) +
      Real.pi * (B.H (B.ct a.y) c.l + B.H (B.ct c.y) a.l + B.H c.l a.l) := by
  have := Complex.I_ne_zero
  rw [lin, AnArc.Pw_fst_apply, AnArc.Pw_snd, AnArc.H_add_left]
  field_simp
  ring

theorem lin_period_sub (w : ℂ) (a c : B.La) :
    lin B a (B.Pw w c) - lin B c (B.Pw w a) = -(2 * Real.pi * Complex.I) * B.EF a c := by
  have h := hermForm_sub_swap B.Hm_herm a.l c.l
  rw [← B.Ef_eq, ← B.H_def, ← B.H_def] at h
  rw [lin_period, lin_period, B.T_symm c.y, B.be_symm c.y, AnArc.EF_apply]
  push_cast at h ⊢
  linear_combination (-Real.pi : ℂ) * h

theorem perFactor_of_isPrim {w₀ : O} (hp : IsPrim B w₀) (w : ℂ) (a : B.La) (v : B.V) :
    B.perFactor w a v = (-1) ^ B.EF a (w₀ • a) * Complex.exp (lin B a v + lin B a (B.Pw w a) / 2) := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hy : w₀ • a.y + star w₀ • a.y = a.y := by rw [← add_smul, h1, one_smul]
  have hT : B.T a.y a.y = 2 * B.T a.y (w₀ • a.y) := by
    have := congrArg (B.T a.y) hy
    rw [map_add (f := _), ← B.T_adj, B.T_symm (w₀ • a.y)] at this
    rw [← this]; ring
  have hE : B.EF a (w₀ • a) = B.Ef a.l (B.FLam w₀ a.l) + (a.n a.y + 2 * (-a.n (w₀ • a.y))) := by
    have := congrArg a.n hy
    rw [map_add (f := _)] at this
    rw [AnArc.EF_apply, AnArc.La.smul_n_apply, AnArc.La.smul_y, AnArc.La.smul_l]
    omega
  have hq : (B.be a.y a.y : ℂ) = 2 * B.q a.y := by rw [← B.two_mul_q]; push_cast; ring
  have hs : ((-1 : ℂ)) ^ (a.n a.y + 2 * (-a.n (w₀ • a.y))) = Complex.exp (Real.pi * Complex.I * a.n a.y) := by
    rw [zpow_add₀ (by norm_num), zpow_mul, mul_comm _ (a.n a.y : ℂ), Complex.exp_int_mul, Complex.exp_pi_mul_I]
    norm_num
  rw [hE, zpow_add₀ (by norm_num), hs, AnArc.perFactor, AnArc.ah, h2, h3, lin_period, hT, hq, lin, AnArc.H_add_left,
    ← AnArc.e_add, ← AnArc.e_add, eTwoPi, ← Complex.exp_neg, mul_assoc (_ ^ _), mul_assoc (_ ^ _), ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  ring

theorem theta_sum_appellHumbert : ThetaSt := by
  intro O _ _ B w₀ hp th hth w hS g h Hm hH hsp hE
  let b : B.La →+ (B.V →ₗ[ℂ] ℂ) := AddMonoidHom.mk' (fun a =>
    { toFun := fun v => lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a))
      map_add' := fun v v' => by
        simp only [lin, hermForm, map_add (f := _), add_dotProduct, Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply,
          AnArc.H_add_left]
        ring
      map_smul' := fun c v => by
        simp only [lin, hermForm, map_smul, smul_dotProduct, Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply,
          AnArc.H_smul_left, smul_eq_mul, RingHom.id_apply]
        ring }) fun a a' => LinearMap.ext fun v => by
      simp only [lin, hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, AnArc.La.add_y, AnArc.La.add_l,
        Submodule.coe_add, AnArc.H_add_right, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
      ring
  have hb : ∀ a v, b a v = lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a)) := fun _ _ => rfl
  obtain ⟨Bs, hs, hB⟩ := exists_symm_bilin_ext (B.Pw w) hsp B.finrank_La b fun a c => by
    have h1 := hermForm_sub_swap hH (h (B.Pw w a)) (h (B.Pw w c))
    rw [hE] at h1
    push_cast at h1
    rw [hb, hb]
    linear_combination lin_period_sub B w a c + (Real.pi : ℂ) * h1
  refine ⟨fun z => Complex.exp (-(Bs (h.symm z) (h.symm z) / 2)) * B.Sum 1 0 th w (h.symm z), ?_, fun v => ?_,
    fun a z => ?_, fun a m hm => ?_⟩
  · have hd : Differentiable ℂ fun z => h.symm z := h.symm.toContinuousLinearEquiv.differentiable
    let Bc : B.V →L[ℂ] B.V →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (B.V →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ Bs)
    have hq : Differentiable ℂ fun v : B.V => Bs v v := Bc.differentiable.clm_apply differentiable_id
    have hq' : Differentiable ℂ fun z => Bs (h.symm z) (h.symm z) := hq.comp hd
    have hq'' : Differentiable ℂ fun z => -(Bs (h.symm z) (h.symm z) / 2) := by
      simp only [div_eq_mul_inv]
      exact (hq'.mul_const _).neg
    exact hq''.cexp.mul (hS.comp hd)
  · simp only [h.symm_apply_apply, mul_eq_zero, Complex.exp_ne_zero, false_or]
  · obtain ⟨v, rfl⟩ := h.surjective z
    simp only [← map_add (f := _), h.symm_apply_apply]
    rw [B.Sum_add_period hth, pow_one, perFactor_of_isPrim B hp]
    simp only [map_add (f := _), LinearMap.add_apply, hs v (B.Pw w a), hB, hb]
    have e : ∀ s x y x' y' S : ℂ, x + y = x' + y' →
        Complex.exp x * (s * Complex.exp y * S) = s * Complex.exp x' * (Complex.exp y' * S) := fun s x y x' y' S e => by
      have := congrArg Complex.exp e
      rw [Complex.exp_add, Complex.exp_add] at this
      linear_combination s * S * this
    exact e _ _ _ _ _ _ (by ring)
  · have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    simp only [← map_smul, h.symm_apply_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hB, hb]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    field_simp
    ring

end GlobalTheory.Ex.Arch
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem val_iso_chart {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL' : L'.IsLB) {F : X' ⟶ X}
    {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (x : Sp ℂ ⟶ X') (j j' : L.ι) (i : L'.ι)
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j') (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    valAt' x _ (w.s (fun _ => j, i)).val =
      valAt' (x ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * valAt' x _ (w.s (fun _ => j', i)).val := by
  have a : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => F) (fun _ => j) := (le_preimage_wchart x L _ _).2 fun _ => hj
  have a' : ⊤ ≤ x ⁻¹ᵁ L.wchart (fun _ : PUnit => F) (fun _ => j') := (le_preimage_wchart x L _ _).2 fun _ => hj'
  have b := (le_preimage_inf x _ _).2 ⟨a, hi⟩
  have b' := (le_preimage_inf x _ _).2 ⟨a', hi⟩
  have c := (le_preimage_inf x _ _).2 ⟨b, b'⟩
  refine (val_sec x (genSec w hw) (fun _ => j, i) (fun _ => j', i) b b').trans (congrArg₂ (· * ·) ?_ rfl)
  have e₁ := val_linComb x valueRules L (fun _ : PUnit => F) (fun _ => 1) (fun _ => j) (fun _ => j') a a'
  rw [Fintype.prod_unique, zpow_one] at e₁
  have e₂ : valAt' x (L'.U i ⊓ L'.U i) (L'.g i i).val = 1 := by
    obtain ⟨e, he⟩ := (valueRules X' x).2.1 _ hi
    rw [← val_res x valueRules (le_inf le_rfl le_rfl) hi, hL'.g_self i, he]
    exact map_one e
  obtain ⟨e, he⟩ := (valueRules X' x).2.1 _ c
  refine (val_unit_mul x valueRules c _ _).trans ?_
  refine (congrArg₂ (· * ·) ((val_res x valueRules _ c _).trans e₁) ((he _).trans ((map_units_inv e _).trans
    (congrArg (·⁻¹) ((he _).symm.trans ((val_res x valueRules _ c _).trans e₂)))))).trans ?_
  simp

theorem fibSec : FibSecSt := by
  intro R _ _ _ D J g Λ Hm χ ex fr h s
  obtain ⟨hJ, P', φ, w, u, hΛ, -, hw, -, -, -, -, hex, hfr⟩ := h
  refine ⟨fun z => sF s (ex z).left J / fr z, fun z₀ => ?_, fun z => (div_mul_cancel₀ _ (fr z).ne_zero).symm⟩
  obtain ⟨i, hi⟩ : ∃ i, ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ P'.L.U i := ⟨_, le_chartAt P'.isLB _⟩
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex z₀).left ≫ φ) ⁻¹ᵁ D.P.L.U j := ⟨_, hJ _⟩
  have ch : ∀ (y : Sp ℂ ⟶ D.P.A.left) (k : D.P.L.ι), ⊤ ≤ y ⁻¹ᵁ D.P.L.U k →
      ⊤ ≤ y ⁻¹ᵁ D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => k) := fun y k hk =>
    (le_preimage_wchart y _ _ _).2 fun _ => by rwa [Category.comp_id]
  have a : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ (D.P.L.wchart (fun _ : PUnit => φ) (fun _ => j) ⊓ P'.L.U i) :=
    (le_preimage_inf _ _ _).2 ⟨(le_preimage_wchart _ _ _ _).2 fun _ => hj, hi⟩
  obtain ⟨o₁, d₁⟩ := u.hol (φ ⁻¹ᵁ D.P.L.wchart (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => j))
    ((φ.app _).hom (s.f fun _ => j))
  obtain ⟨o₂, d₂⟩ := u.hol _ (w.s (fun _ => j, i)).val
  have n₂ := o₂.mem_nhds a
  have d := (d₁.differentiableAt (o₁.mem_nhds (ch _ j hj))).fun_mul (((d₂.differentiableAt n₂).fun_mul
    ((u.fr_hol i).differentiableAt ((u.hol _ 0).1.mem_nhds hi))).fun_inv
    (mul_ne_zero (val_unit_ne_zero _ valueRules a _) (u.fr_ne i _ hi)))
  refine d.congr_of_eventuallyEq ?_
  filter_upwards [n₂] with z hz
  obtain ⟨h₁, h₂⟩ := (le_preimage_inf _ _ _).1 hz
  have h₃ := (le_preimage_wchart _ _ _ _).1 h₁ PUnit.unit
  have e₀ : sF s (ex z).left J = valAt' (ex z).left _ (s.f fun _ => J (ex z).left) := by
    rfl
  have e₁ := val_sec (ex z).left s (fun _ => J (ex z).left) (fun _ => j) (ch _ _ (hJ _)) (ch _ _ (hex z ▸ h₃))
  have e₂ := val_linComb (ex z).left valueRules D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => ((1 : ℕ) : ℤ))
    (fun _ => J (ex z).left) (fun _ => j) (ch _ _ (hJ _)) (ch _ _ (hex z ▸ h₃))
  rw [Fintype.prod_unique, Nat.cast_one, zpow_one, Category.comp_id] at e₂
  have e₃ := val_iso_chart P'.isLB hw (u.ex z).left (J (ex z).left) j i (hex z ▸ hJ _) h₃ h₂
  have n := val_unit_ne_zero (ex z).left valueRules ((le_preimage_inf _ _ _).2 ⟨hJ _, hex z ▸ h₃⟩)
    (D.P.L.g (J (ex z).left) j)
  have e₄ := (valueRules _ (u.ex z).left).2.2.2.1 _ φ _ (s.f fun _ => j)
  rw [← hex z] at e₃ e₄
  rw [e₀, e₁, hfr z i h₂, e₃, _root_.mul_assoc]
  exact (congrArg (fun q => q * _ / _) e₂).trans ((mul_div_mul_left _ _ n).trans ((div_eq_mul_inv _ _).trans
    (congrArg₂ (· * ·) e₄.symm rfl)))

end GlobalTheory.Ex.Arch
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.exists_integrally_closed_extension_of_adjoin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (s : AlgebraicClosure (FractionRing R)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R →+* R₂) (h' : FractionRing R →+* FractionRing R₂) (e : FractionRing R₂ →+* AlgebraicClosure (FractionRing R)), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R _ r) = algebraMap R₂ _ (h r)) ∧ e.comp h' = algebraMap _ _ ∧ (∃ s₂, e s₂ = s) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (g : FractionRing R₂ →+* F), ∃ g' : AlgebraicClosure (FractionRing R) →+* F, g'.comp e = g := by
  first | exact @GlobalTheory.exists_finite_normal_adjoin_algebraic | exact GlobalTheory.exists_finite_normal_adjoin_algebraic | (intros; apply GlobalTheory.exists_finite_normal_adjoin_algebraic <;> assumption)
end
