module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle815
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem cube_corr {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (xi xj yi yj ui uj : A) (sji sij tji tij : U) :
    sji * tji / θ xi yj uj * (sij * tij / θ xj yi ui) /
        (θ xj (yj * uj) xi * θ xj (yj * uj) (yi * ui) * θ xi (yi * ui) (xj * (yj * uj))) *
      (θ (xi * xj) (yi * yj) (ui * uj) / (θ xi yi ui * θ xj yj uj)) =
    sji * sij / (θ xj yj xi * θ xj yj yi * θ xi yi (xj * yj)) *
      (tji * tij / (θ xj uj xi * θ xj uj ui * θ xi ui (xj * uj))) := by
  have hp : ∀ x y z, θ x y z = θ y x z ∧ θ x y z = θ x z y ∧ θ x y z = θ z x y ∧ θ x y z = θ y z x ∧
      θ x y z = θ z y x := fun x y z =>
    ⟨h.s01 x y z, h.s12 x y z, (h.s12 x y z).trans (h.s01 x z y), (h.s01 x y z).trans (h.s12 y x z),
      ((h.s01 x y z).trans (h.s12 y x z)).trans (h.s01 y z x)⟩
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have c0 := E (show θ (xi * xj) (yi * yj) (ui * uj) * θ xi xj (ui * uj) = θ xi (xj * yi * yj) (ui * uj) * θ xj (yi * yj) (ui * uj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * yj) (ui * uj))
  have c1 := E (show θ (xj * ui) uj (yi * yj) * θ xj ui (yi * yj) = θ xj (ui * uj) (yi * yj) * θ ui uj (yi * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj ui uj (yi * yj))
  have c2 := E (show θ (xj * ui) (yi * yj) uj * θ xj ui uj = θ xj (yi * yj * ui) uj * θ ui (yi * yj) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj ui (yi * yj) uj)
  have c3 := E (show θ (xj * yj) uj (yi * ui) * θ xj yj (yi * ui) = θ xj (yj * uj) (yi * ui) * θ yj uj (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yj uj (yi * ui))
  have c4 := E (show θ (xj * yj) (yi * ui) uj * θ xj yj uj = θ xj (yi * yj * ui) uj * θ yj (yi * ui) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yj (yi * ui) uj)
  have c5 := E (show θ (xj * yi) ui yj * θ xj yi yj = θ xj (yi * ui) yj * θ yi ui yj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yi ui yj)
  have c6 := E (show θ (xj * yi) yj ui * θ xj yi ui = θ xj (yi * yj) ui * θ yi yj ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yi yj ui)
  have c7 := E (show θ (xi * xj) (yj * uj) (yi * ui) * θ xi xj (yi * ui) = θ xi (xj * yj * uj) (yi * ui) * θ xj (yj * uj) (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yj * uj) (yi * ui))
  have c8 := E (show θ (xi * xj) (yi * ui) (yj * uj) * θ xi xj (yj * uj) = θ xi (xj * yi * ui) (yj * uj) * θ xj (yi * ui) (yj * uj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * ui) (yj * uj))
  have c9 := E (show θ (xi * ui) uj (xj * yi * yj) * θ xi ui (xj * yi * yj) = θ xi (ui * uj) (xj * yi * yj) * θ ui uj (xj * yi * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui uj (xj * yi * yj))
  have c10 := E (show θ (xi * ui) (xj * yi * yj) uj * θ xi ui uj = θ xi (xj * yi * yj * ui) uj * θ ui (xj * yi * yj) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui (xj * yi * yj) uj)
  have c11 := E (show θ (xi * yj) uj (xj * yi * ui) * θ xi yj (xj * yi * ui) = θ xi (yj * uj) (xj * yi * ui) * θ yj uj (xj * yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yj uj (xj * yi * ui))
  have c12 := E (show θ (xi * yj) (xj * yi * ui) uj * θ xi yj uj = θ xi (xj * yi * yj * ui) uj * θ yj (xj * yi * ui) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yj (xj * yi * ui) uj)
  have c13 := E (show θ (xi * ui) uj xj * θ xi ui xj = θ xi (ui * uj) xj * θ ui uj xj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui uj xj)
  have c14 := E (show θ (xi * ui) xj uj * θ xi ui uj = θ xi (xj * ui) uj * θ ui xj uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui xj uj)
  have c15 := E (show θ (xi * xj) uj ui * θ xi xj ui = θ xi (xj * uj) ui * θ xj uj ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj uj ui)
  have c16 := E (show θ (xi * xj) ui uj * θ xi xj uj = θ xi (xj * ui) uj * θ xj ui uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj ui uj)
  have c17 := E (show θ (xi * yi) ui (xj * yj) * θ xi yi (xj * yj) = θ xi (yi * ui) (xj * yj) * θ yi ui (xj * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yi ui (xj * yj))
  have c18 := E (show θ (xi * yi) (xj * yj) ui * θ xi yi ui = θ xi (xj * yi * yj) ui * θ yi (xj * yj) ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yi (xj * yj) ui)
  have c19 := E (show θ (xi * xj) (yi * ui) yj * θ xi xj yj = θ xi (xj * yi * ui) yj * θ xj (yi * ui) yj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * ui) yj)
  have c20 := E (show θ (xi * xj) yj (yi * ui) * θ xi xj (yi * ui) = θ xi (xj * yj) (yi * ui) * θ xj yj (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj yj (yi * ui))
  have p0 := E (hp xj (yj * uj) xi).2.2.1
  have p1 := E (hp xj yj xi).2.2.1
  have p2 := E (hp xj yj yi).2.1
  have p3 := E (hp xj uj xi).2.2.1
  have p4 := E (hp (xj * ui) uj (yi * yj)).2.2.1
  have p5 := E (hp xj ui (yi * yj)).2.1
  have p6 := E (hp xj (ui * uj) (yi * yj)).2.1
  have p7 := E (hp ui uj (yi * yj)).2.2.1
  have p8 := E (hp (xj * ui) (yi * yj) uj).1
  have p9 := E (hp ui (yi * yj) uj).1
  have p10 := E (hp (xj * yj) uj (yi * ui)).2.1
  have p11 := E (hp yj uj (yi * ui)).2.1
  have p12 := E (hp (xj * yi) ui yj).2.1
  have p13 := E (hp xj (yi * ui) yj).2.1
  have p14 := E (hp yi ui yj).2.1
  have p15 := E (hp (xi * xj) (yj * uj) (yi * ui)).2.1
  have p16 := E (hp xi (xj * yj * uj) (yi * ui)).2.1
  have p17 := E (hp xj (yj * uj) (yi * ui)).2.1
  have p18 := E (hp (xi * ui) uj (xj * yi * yj)).2.2.1
  have p19 := E (hp xi ui (xj * yi * yj)).2.1
  have p20 := E (hp xi (ui * uj) (xj * yi * yj)).2.1
  have p21 := E (hp ui uj (xj * yi * yj)).2.2.1
  have p22 := E (hp (xi * ui) (xj * yi * yj) uj).1
  have p23 := E (hp ui (xj * yi * yj) uj).1
  have p24 := E (hp (xi * yj) uj (xj * yi * ui)).2.1
  have p25 := E (hp xi (yj * uj) (xj * yi * ui)).2.1
  have p26 := E (hp yj uj (xj * yi * ui)).2.1
  have p27 := E (hp (xi * ui) uj xj).2.2.1
  have p28 := E (hp xi ui xj).2.1
  have p29 := E (hp xi (ui * uj) xj).2.1
  have p30 := E (hp ui uj xj).2.2.1
  have p31 := E (hp (xi * ui) xj uj).1
  have p32 := E (hp ui xj uj).1
  have p33 := E (hp (xi * xj) uj ui).2.1
  have p34 := E (hp xi (xj * uj) ui).2.1
  have p35 := E (hp (xi * yi) ui (xj * yj)).2.1
  have p36 := E (hp xi (yi * ui) (xj * yj)).2.1
  have p37 := E (hp yi ui (xj * yj)).2.1
  have p38 := E (hp (xi * xj) (yi * ui) yj).2.1
  have p39 := E (hp xi (xj * yi * ui) yj).2.1
  rw [← mul_assoc xj yj uj]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at *
  linear_combination (norm := abel) c0 - c1 + c2 + c3 - c4 + c5 - c6 + c7 - c8 - c9 + c10 + c11 - c12 + c13 - c14 - c15 + c16 + c17 - c18 + c19 - c20 - p0 + p1 + p2 + p3 + p4 + p5 - p6 - p7 - p8 + p9 - p10 + p11 - p12 + 2 • p13 + p14 - p15 + p16 + p17 + p18 + p19 - p20 - p21 - p22 + p23 - p24 + p25 + p26 - p27 - p28 + p29 + p30 + p31 - p32 + p33 - p34 - p35 + p36 + p37 - p38 + p39

end GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem vmul_comb {U : Type} [CommGroup U] (s1 s2 t P1 P2 P Q wc wb wb' wcb wcb' wbb' wcbb' w1 : U)
    (h1 : s1 * wc * wb = P1 * wcb * w1) (h2 : s2 * wc * wb' = P2 * wcb' * w1)
    (h3 : t * wcbb' * wc * wb * wb' = Q * wcb * wcb' * wbb' * w1) (h4 : P * Q = P1 * P2) :
    s1 * s2 / t * wc * wbb' = P * wcbb' * w1 := by
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a1 := E h1; have a2 := E h2; have a3 := E h3; have a4 := E h4
  simp only [ofMul_mul, ofMul_div] at *
  linear_combination (norm := abel) a1 + a2 - a3 - a4

theorem gtRelV_mul : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv →
    ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us →
      GtRelV W φ e wv (v' * u') (vs * us) := by
  intro F _ N N' r W φ e wv hT v' u' vs us hv hu
  obtain ⟨hφ, -, -, -, hφc, hw0, hcub, -⟩ := hT
  refine ⟨fun j => ?_, fun χ' => ?_⟩
  · show φ (v'.b * u'.b) j = (vs j).b * (us j).b
    rw [hφ, hv.1, hu.1]
  · let w : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
    let Pf : (Fin r → N.Gt) → Fˣ := fun g => ∏ i, ∏ j, ((g j).s (e χ' i) * (g i).s (e χ' j) /
      (N.θ (N.c (e χ' j)) (g j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (g j).b (g i).b *
        N.θ (N.c (e χ' i)) (g i).b (N.c (e χ' j) * (g j).b))) ^ W i j
    let Qf : Fˣ := ∏ i, ∏ j, (N.θ (N.c (e χ' i) * N.c (e χ' j)) ((vs i).b * (vs j).b) ((us i).b * (us j).b) /
      (N.θ (N.c (e χ' i)) (vs i).b (us i).b * N.θ (N.c (e χ' j)) (vs j).b (us j).b)) ^ W i j
    have h1 : v'.s χ' * w (N'.c χ') * w v'.b = Pf vs * w (N'.c χ' * v'.b) * w 1 := Units.ext (hv.2 χ')
    have h2 : u'.s χ' * w (N'.c χ') * w u'.b = Pf us * w (N'.c χ' * u'.b) * w 1 := Units.ext (hu.2 χ')
    have h3 := hcub (N'.c χ') v'.b u'.b
    rw [mul_assoc (N'.c χ') v'.b u'.b] at h3
    simp only [hφc, hv.1, hu.1] at h3
    have h3' : N'.θ (N'.c χ') v'.b u'.b * w (N'.c χ' * (v'.b * u'.b)) * w (N'.c χ') * w v'.b * w u'.b =
        Qf * w (N'.c χ' * v'.b) * w (N'.c χ' * u'.b) * w (v'.b * u'.b) * w 1 := Units.ext h3
    have h4 : Pf (vs * us) * Qf = Pf vs * Pf us := by
      simp only [Pf, Qf]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← mul_zpow, ← mul_zpow]
      exact congrArg (· ^ W i j) (cube_corr N.cub (N.c (e χ' i)) (N.c (e χ' j)) (vs i).b (vs j).b (us i).b (us j).b
        ((vs j).s (e χ' i)) ((vs i).s (e χ' j)) ((us j).s (e χ' i)) ((us i).s (e χ' j)))
    exact congrArg Units.val (vmul_comb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3' h4)

end GlobalTheory.Mum.TensTor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.Vonto

theorem sum_sym_inv {G : Type} [AddCommGroup G] {r : ℕ} (W C : Matrix (Fin r) (Fin r) ℤ)
    (h : (W + W.transpose) * C = 1) (a : Fin r → Fin r → G) :
    ∑ i, ∑ j, W i j • ((∑ k, C j k • a i k) + ∑ k, C i k • a j k) = ∑ i, a i i := by
  have e3 : ∀ i k, ∑ j, (W i j + W j i) * C j k = if i = k then 1 else 0 := fun i k => by
    have := congrFun (congrFun h i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa using this
  have e1 : ∀ i, ∑ j, W i j • ((∑ k, C j k • a i k) + ∑ k, C i k • a j k) =
      ∑ j, W i j • ∑ k, C j k • a i k + ∑ j, W i j • ∑ k, C i k • a j k := fun i => by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => smul_add _ _ _
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib]
  rw [show (∑ i, ∑ j, W i j • ∑ k, C i k • a j k) = ∑ i, ∑ j, W j i • ∑ k, C j k • a i k from Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_smul, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, e3, ite_smul, one_smul, zero_smul]
  simp

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

section Split

variable {X U : Type} [AddCommGroup X] [CommGroup U]

@[ext] structure ExtPt (f : X → X → U) where

  a : X

  u : U

instance (f : X → X → U) : Add (ExtPt f) := ⟨fun p q => ⟨p.a + q.a, p.u * q.u / f p.a q.a⟩⟩

instance (f : X → X → U) : Zero (ExtPt f) := ⟨⟨0, 1⟩⟩

instance (f : X → X → U) : Neg (ExtPt f) := ⟨fun p => ⟨-p.a, f p.a (-p.a) / p.u⟩⟩

def extGroup (f : X → X → U) (f0 : ∀ a, f 0 a = 1) (fs : ∀ a b, f a b = f b a)
    (fc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) : AddCommGroup (ExtPt f) where
  add_assoc p q w := by
    refine ExtPt.ext (add_assoc p.a q.a w.a) ?_
    change p.u * q.u / f p.a q.a * w.u / f (p.a + q.a) w.a = p.u * (q.u * w.u / f q.a w.a) / f p.a (q.a + w.a)
    have h := congrArg Additive.ofMul (fc p.a q.a w.a)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at h ⊢
    linear_combination (norm := abel) -h
  zero_add p := by
    refine ExtPt.ext (zero_add p.a) ?_
    change 1 * p.u / f 0 p.a = p.u
    rw [f0, _root_.one_mul, div_one]
  add_zero p := by
    refine ExtPt.ext (add_zero p.a) ?_
    change p.u * 1 / f p.a 0 = p.u
    rw [fs, f0, _root_.mul_one, div_one]
  neg_add_cancel p := by
    refine ExtPt.ext (neg_add_cancel p.a) ?_
    change f p.a (-p.a) / p.u * p.u / f (-p.a) p.a = 1
    rw [fs (-p.a), div_mul_cancel, div_self']
  add_comm p q := by
    refine ExtPt.ext (add_comm p.a q.a) ?_
    change p.u * q.u / f p.a q.a = q.u * p.u / f q.a p.a
    rw [mul_comm p.u, fs]
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem exists_split [Module.Free ℤ X] (f : X → X → U) (f0 : ∀ a, f 0 a = 1) (fs : ∀ a b, f a b = f b a)
    (fc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) :
    ∃ s : X → U, ∀ a b, s (a + b) * f a b = s a * s b := by
  letI := extGroup f f0 fs fc
  let bX := Module.Free.chooseBasis ℤ X
  let h : X →ₗ[ℤ] ExtPt f := bX.constr ℤ fun i => ⟨bX i, 1⟩
  let p : ExtPt f →ₗ[ℤ] X := AddMonoidHom.toIntLinearMap ⟨⟨ExtPt.a, rfl⟩, fun _ _ => rfl⟩
  have hp : p ∘ₗ h = LinearMap.id := bX.ext fun i => by
    change (h (bX i)).a = bX i
    simp only [h, bX.constr_basis]
  have ha : ∀ x, (h x).a = x := fun x => LinearMap.congr_fun hp x
  refine ⟨fun x => (h x).u, fun a b => ?_⟩
  have e : (h (a + b)).u = (h a).u * (h b).u / f (h a).a (h b).a := congrArg ExtPt.u (map_add h a b)
  show (h (a + b)).u * f a b = (h a).u * (h b).u
  rw [e, ha, ha, div_mul_cancel]

end Split

theorem exists_gt_over {F : Type} [Field F] (N : NumD F) (b : N.A) : ∃ g : N.Gt, g.b = b := by
  obtain ⟨s, hs⟩ := exists_split (fun χ χ' => N.θ (N.c χ) (N.c χ') b)
    (fun a => by rw [N.c_zero, N.cub.face]) (fun a a' => N.cub.s01 _ _ _)
    (fun a a' a'' => by simp only [N.c_add]; exact N.cub.coc _ _ _ _)
  exact ⟨⟨b, s, hs⟩, rfl⟩

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem tor_rel (hT : TensFacts W φ e wv) (hdet : IsUnit (W + W.transpose).det) (t' : Multiplicative N'.X →* Fˣ) :
    ∃ ts : Fin r → (Multiplicative N.X →* Fˣ), GtRelV W φ e wv (N'.tor t') fun j => N.tor (ts j) := by
  obtain ⟨hφm, -, hem, heb, -, -, -, -⟩ := hT
  have hBC : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  let E : N'.X ≃+ (Fin r → N.X) := AddEquiv.ofBijective (AddMonoidHom.mk' e fun a b => funext (hem a b)) heb
  let sH : Fin r → Multiplicative N.X →* Fˣ := fun k =>
    t'.comp (AddMonoidHom.toMultiplicative ((E.symm : (Fin r → N.X) →+ N'.X).comp (AddMonoidHom.single (fun _ : Fin r => N.X) k)))
  let C : Fin r → Fin r → ℤ := ((W + W.transpose)⁻¹ : Matrix (Fin r) (Fin r) ℤ)
  let M : Fin r → Fin r → ℤ := W
  refine ⟨fun j => ∏ k, sH k ^ C j k, fun j => ?_, fun χ' => ?_⟩
  · have h1 := hφm 1 1 j
    rw [_root_.mul_one] at h1
    exact mul_eq_left.1 h1.symm
  · have hχ : χ' = ∑ i, E.symm (Pi.single i (e χ' i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.univ_sum_single]; exact (E.symm_apply_apply χ').symm
    have ht : t' (Multiplicative.ofAdd χ') = ∏ i, sH i (Multiplicative.ofAdd (e χ' i)) := by
      conv_lhs => rw [hχ]
      rw [ofAdd_sum, map_prod]
      rfl
    simp only [NumD.torus_generator_apply, NumD.tor_b, N.cub.face₂, N.cub.face₃, _root_.mul_one, div_one]
    congr 2
    congr 1
    rw [ht]
    change (∏ i, sH i (Multiplicative.ofAdd (e χ' i))) =
      ∏ i, ∏ j, ((∏ k, sH k ^ C j k) (Multiplicative.ofAdd (e χ' i)) *
        (∏ k, sH k ^ C i k) (Multiplicative.ofAdd (e χ' j))) ^ M i j
    have hp (f : Fin r → (Multiplicative N.X →* Fˣ)) (x : Multiplicative N.X) :
        (∏ k, f k) x = ∏ k, f k x := by
      exact map_prod (MonoidHom.eval x) _ _
    simp only [hp, MonoidHom.zpow_apply]
    apply Additive.ofMul.injective
    simp only [ofMul_prod, ofMul_zpow, ofMul_mul]
    exact (sum_sym_inv W C hBC fun i k => Additive.ofMul (sH k (Multiplicative.ofAdd (e χ' i)))).symm

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem of_exist_mul (hT : TensFacts W φ e wv) (hdet : IsUnit (W + W.transpose).det)
    (hex : ∀ vs : Fin r → N.Gt, ∃ v' : N'.Gt, GtRelV W φ e wv v' vs)
    (hmul : ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us →
      GtRelV W φ e wv (v' * u') (vs * us))
    (v' : N'.Gt) : ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs := by
  choose g hg using fun j => exists_gt_over N (φ v'.b j)
  obtain ⟨u', hu'⟩ := hex g
  have hb : u'.b = v'.b := hT.2.1.1 (funext fun j => (hu'.1 j).trans (hg j))
  obtain ⟨t', ht'⟩ := (N'.exists_tor_iff (u'⁻¹ * v')).2 (by rw [NumD.Gt.mul_b, NumD.Gt.inv_b, hb, inv_mul_cancel])
  obtain ⟨ts, hts⟩ := tor_rel hT hdet t'
  have h := hmul u' (N'.tor t') g (fun j => N.tor (ts j)) hu' hts
  rw [ht', mul_inv_cancel_left] at h
  exact ⟨_, h⟩

end GlobalTheory.Mum.TensTor.Vonto
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

def chartPullPerm {X Y Y' : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ' : K' → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε' : K' → ℤ) (ε : K → ℤ) (h : Y' ⟶ Y) (e : K' ≃ K)
    (hc : ∀ k, φ' (e.symm k) = h ≫ φ k) (hε : ∀ k, ε' (e.symm k) = ε k) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) h :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j (e.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy (e.symm k)
      rw [hc] at this
      exact this
  { idx := fun j k => j (e.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y') y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      refine (Fintype.prod_equiv e.symm _ _ fun k => ?_).symm
      rw [Category.id_comp, hc, hε] }

theorem psum_perm {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (I : Finset (Fin n)) : psum G x' I = h ≫ psum G x (I.map σ.toEmbedding) := by
  rw [CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.comp_prod, Finset.prod_map]
  exact Finset.prod_congr rfl fun i _ => hx i

def chartPullCube {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (L : LB G.left) : ChartPull (cubeLB G x' L) (cubeLB G x L) h.left :=
  chartPullPerm L _ _ _ _ h.left (Equiv.ulift.trans ((Equiv.finsetCongr σ).trans Equiv.ulift.symm))
    (fun k => by
      show (psum G x' ((Equiv.finsetCongr σ).symm k.down)).left = h.left ≫ (psum G x k.down).left
      rw [psum_perm G h x x' σ hx, Over.comp_left]
      congr 3
      exact (Equiv.finsetCongr σ).apply_symm_apply k.down)
    (fun k => by
      show (-1 : ℤ) ^ (n - ((Equiv.finsetCongr σ).symm k.down).card) = (-1) ^ (n - k.down.card)
      simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply])

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem gAdj_swap {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} (H : GAdj L₁ L₂ u u') : GAdj L₂ L₁ u' u :=
  LBIso.chartPull
    (chartPullCube G₁ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂, snd G₁ G₂ ≫ u'] ![fst G₂ G₁ ≫ u', snd G₂ G₁]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₁)
    (chartPullCube G₂ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂ ≫ u, snd G₁ G₂] ![fst G₂ G₁, snd G₂ G₁ ≫ u]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₂)
    (LBIso.symm H)

theorem gAdj_comp {S : Scheme.{0}} {G₁ G₂ G₃ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    [GrpObj G₃] [IsCommMonObj G₃] {L₁ : LB G₁.left} {L₂ : LB G₂.left} {L₃ : LB G₃.left} (hL₁ : L₁.IsLB)
    (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} {v : G₂ ⟶ G₃} {v' : G₃ ⟶ G₂}
    (H : GAdj L₁ L₂ u u') (H' : GAdj L₂ L₃ v v') : GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  LBIso.trans (LB.isLB_linComb hL₃ _ _) (LB.isLB_linComb hL₂ _ _) (LB.isLB_linComb hL₁ _ _)
    (LBIso.chartPull
      (chartPullCube G₃ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃ ≫ v, snd G₂ G₃]
        ![fst G₁ G₃ ≫ u ≫ v, snd G₁ G₃] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₃)
      (chartPullCube G₂ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃, snd G₂ G₃ ≫ v']
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂) H')
    (LBIso.chartPull
      (chartPullCube G₂ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂ ≫ u, snd G₁ G₂]
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂)
      (chartPullCube G₁ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂, snd G₁ G₂ ≫ u']
        ![fst G₁ G₃, snd G₁ G₃ ≫ v' ≫ u'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₁) H)

theorem gAdj_swap_comp :
    (∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : LB G₁.left)
      (L₂ : LB G₂.left), L₁.IsLB → L₂.IsLB → ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), GAdj L₁ L₂ u u' → GAdj L₂ L₁ u' u) ∧
    ∀ (S : Scheme.{0}) (G₁ G₂ G₃ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃]
      [IsCommMonObj G₃] (L₁ : LB G₁.left) (L₂ : LB G₂.left) (L₃ : LB G₃.left), L₁.IsLB → L₂.IsLB → L₃.IsLB →
      ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁) (v : G₂ ⟶ G₃) (v' : G₃ ⟶ G₂), GAdj L₁ L₂ u u' → GAdj L₂ L₃ v v' →
        GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ H => gAdj_swap H,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ _ _ _ _ H H' => gAdj_comp h₁ h₂ h₃ H H'⟩

end GlobalTheory.MumFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_complete_dvr_values_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V) V → (∀ x : FractionRing V, ‖algebraMap (FractionRing V) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
  ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsDiscreteValuationRing V₂) (_ : Algebra (FractionRing V₂) (PadicAlgCl p)), IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ ∧ (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) ∧
    ∃ σ : FractionRing V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing V) (PadicAlgCl p) ∧
      ∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ (algebraMap (FractionRing V₂) (PadicAlgCl p)).range := by
  intro E _ _ _ H Dw l Xo cf C X₁ D p _ z₁ c y h V _ _ _ _ hc hV
  obtain ⟨R, _, hR, y₀, hval⟩ := GlobalTheory.ValField.exists_fg_values D.X.M (gPt p ≫ y)
  let κ : FractionRing V →+* PadicAlgCl p := algebraMap (FractionRing V) (PadicAlgCl p)
  haveI : CharZero V := RingHom.charZero (κ.comp (algebraMap V (FractionRing V)))
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV
  obtain ⟨W₂, i₁, i₂, i₃, hcW, -, fV, fK, κ', -, -, -, -, hκ', hunit, hy⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ R y₀
  letI : Algebra (FractionRing W₂) (PadicAlgCl p) := κ'.toAlgebra
  refine ⟨W₂, i₁, i₂, i₃, κ'.toAlgebra, hcW, hunit, fK, hκ', fun a ha => ?_⟩
  have hm := hval κ'.fieldRange (fun r => by obtain ⟨x, hx⟩ := hy r; exact ⟨x, hx⟩) a ha
  obtain ⟨x, hx⟩ := hm
  exact ⟨x, hx⟩

end GlobalTheory.UPoinc
end
