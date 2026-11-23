module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.LevEps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

structure Tower.PsPair (T : Tower D) {c' : Coef l} (h : c.O ≤ c'.O) (k : Type) [Field k] [Algebra c'.O k]
    (Q : PD T.ι (G T.F Ω) (PowerSeries k)) : Prop where
  loc : ∀ a ∈ maximalIdeal c'.O, algebraMap c'.O k a = 0
  pair : (T.fr ∅).IsPair ((algebraMap c'.O (PowerSeries k)).comp (inc h)) Q
  cont : Q.Cont (maximalIdeal (PowerSeries k))
  cp : ∀ g, (Q.r g).charpoly.map (PowerSeries.constantCoeff : PowerSeries k →+* k) =
    ∏ i, (X - C (algebraMap c'.O k (inc h (chi D T.pr i (resQ T.F g)))))
  psi : ∀ v i, ∀ s ∈ Dec (F := T.F) (T.pl v),
    PowerSeries.constantCoeff (Q.ψ v i s) = algebraMap c'.O k (inc h (chi D T.pr i (resQ T.F s)))

namespace Link

variable {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) {R : Type} [CommRing R] [Algebra c'.O R]

def IsRho (ρ : K.V.frame.G₀ →* GL (Fin 4) R) (Q : PD T.ι (G T.F Ω) R) : Prop :=
  ∀ g : G T.L Ω, W.mat ρ (K.V.pr g) = algebraMap c'.O R (K.κ g) • Q.r (resLe T.F_le g)

def IsPsi (ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ) (Q : PD T.ι (G T.F Ω) R) : Prop :=
  ∀ (v : W.Vl l T.L) (i : Fin 4) (g : Dec (F := T.L) (K.s.A v)),
    ((ψ v i g : Rˣ) : R) = algebraMap c'.O R (K.κ g) * Q.ψ (K.e v) i (resLe T.F_le g)

end Link

end UpperTheory.V.Ws

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp


theorem UpperTheory.V.Ws.P1.condC :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (η : K.V.frame.G₀ →* (ResidueField c'.O)ˣ), η ^ 2 = 1 → (K.V.frame.eps c'.O (ResidueField c'.O)).ker ≤ η.ker →
          (∀ i, ∃ j, η * K.r.chib i = K.r.chib j) → η = 1 := by
  intro Ω _ _ _ l _ c D T hfit _ c' h K η hη2 hker hperm
  obtain ⟨hrange, hinj, -, -, hres, -⟩ := P1.towerGal D T
  haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h
  have hgood : D.Good := by
    rcases hfit.2 with ⟨h2, -⟩ | ⟨h3, -⟩
    exacts [h2.1, h3.1]
  have hlev := P1.levEps K.V
  have hsurj := (phiKer K.V).1
  have hφ : Function.Injective (ResidueField.map (inc h)) := (ResidueField.map (inc h)).injective
  have hη2' : η * η = 1 := by rw [← pow_two]; exact hη2
  have hE2 : ∀ x, ((η (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O) * η (K.V.pr x) = 1 := fun x =>
    congrArg (fun θ => ((θ (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O)) hη2'
  have hpm : ∀ x, ∃ y : ResidueField c.O, ResidueField.map (inc h) y = η (K.V.pr x) := by
    intro x
    rcases mul_self_eq_one_iff.mp (hE2 x) with e | e
    · exact ⟨1, by rw [map_one, e]⟩
    · exact ⟨-1, by rw [map_neg, map_one, e]⟩
  choose f hf using hpm
  have hff : ∀ x, f x * f x = 1 := fun x => hφ (by rw [map_mul, hf, map_one, hE2])
  have hfmul : ∀ a b, f (a * b) = f a * f b := fun a b =>
    hφ (by rw [map_mul, hf, hf, hf]; exact congrArg Units.val ((η.comp K.V.pr).map_mul a b))
  have hf1 : f 1 = 1 := hφ (by rw [hf, map_one]; exact congrArg Units.val (η.comp K.V.pr).map_one)
  let F' : G T.L Ω →* (ResidueField c.O)ˣ :=
    { toFun := fun x => ⟨f x, f x, hff x, hff x⟩
      map_one' := Units.ext hf1
      map_mul' := fun a b => Units.ext (hfmul a b) }
  let e := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let η' : T.GalL →* (ResidueField c.O)ˣ := F'.comp e.symm.toMonoidHom
  have hxg : ∀ g : T.GalL, resLe (Tower.F_le T) (e.symm g) = (g : G T.F Ω) := fun g =>
    congrArg Subtype.val (e.apply_symm_apply g)
  have hmain : η' = 1 := by
    refine hfit.1.g3' η' ?_ ?_ ?_
    · rw [pow_two]
      refine MonoidHom.ext fun g => ?_
      exact Units.ext (hff _)
    · intro g hom
      have hq : resQ T.F (g : G T.F Ω) = resQ T.L (e.symm g) := by rw [← hxg]; exact (hres _).1
      rw [hq] at hom
      have hb := hgood.om_bar (resQ T.L (e.symm g))
      simp only [Raw.bar, hom, Units.val_one, map_one] at hb
      have heps : K.V.frame.eps c'.O (ResidueField c'.O) (K.V.pr (e.symm g)) = 1 := by
        apply Units.ext
        rw [hlev.2.2.2 c'.O (ResidueField c'.O) (e.symm g), Units.val_one]
        have hc : (cycZ (↥T.L) Ω l) (e.symm g) = cycZ ℚ Ω l (resQ T.L (e.symm g)) := ((hres _).2.2).symm
        have key : algebraMap ℤ_[l] c'.O ↑(cycZ ℚ Ω l (resQ T.L (e.symm g))) =
            inc h (algebraMap ℤ_[l] c.O ↑(cycZ ℚ Ω l (resQ T.L (e.symm g)))) :=
          ((Subalgebra.inclusion h).commutes _).symm
        show residue c'.O (algebraMap ℤ_[l] c'.O ↑(cycZ (↥T.L) Ω l (e.symm g))) = 1
        rw [hc, key, ← ResidueField.map_residue]
        have hb' : residue c.O (algebraMap ℤ_[l] c.O ↑(cycZ ℚ Ω l (resQ T.L (e.symm g)))) = 1 := by
          first | exact hb | exact hb.symm
        rw [hb', map_one]
      have hη1 : η (K.V.pr (e.symm g)) = 1 := hker heps
      apply Units.ext
      show f (e.symm g) = 1
      exact hφ (by rw [hf, hη1]; simp)
    · intro i
      obtain ⟨j, hj⟩ := hperm i
      refine ⟨j, fun g => ?_⟩
      have hq : resQ T.F (g : G T.F Ω) = resQ T.L (e.symm g) := by rw [← hxg]; exact (hres _).1
      show f (e.symm g) * residue c.O ↑(chi D T.pr i (resQ T.F ↑g)) = residue c.O ↑(chi D T.pr j (resQ T.F ↑g))
      rw [hq]
      generalize e.symm g = x
      have hc' : ((η (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O) *
          (K.r.chib i (K.V.pr x) : ResidueField c'.O) = K.r.chib j (K.V.pr x) :=
        congrArg (fun θ => ((θ (K.V.pr x) : (ResidueField c'.O)ˣ) : ResidueField c'.O)) hj
      rw [K.chib i x, K.chib j x, map_mul (residue c'.O), map_mul (residue c'.O)] at hc'
      have hκ : residue c'.O (K.κ x : c'.O) ≠ 0 := ((K.κ x).isUnit.map (residue _)).ne_zero
      apply hφ
      rw [map_mul, ResidueField.map_residue (inc h), ResidueField.map_residue (inc h), hf x]
      apply mul_left_cancel₀ hκ
      linear_combination hc'
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  have h1 : f x = 1 := by
    have hm := congrArg (fun θ => ((θ (e x) : (ResidueField c.O)ˣ) : ResidueField c.O)) hmain
    rw [show f x = f (e.symm (e x)) by rw [e.symm_apply_apply]]
    exact hm
  apply Units.ext
  rw [← hf x, h1, map_one]
  rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.P1.condD_roots : ∀ w ∈ roots, ∃ i j : Fin 4, w = wt i j := by
  decide

private theorem UpperTheory.V.Ws.P1.condD_rt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    rw [← h, mul_comm (Φ.χ 0 g) (Φ.χ 3 g), mul_inv_cancel_right]
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hd] <;>
    (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)

theorem UpperTheory.V.Ws.P1.condD :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h), ∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (K.r.chib i / K.r.chib j) ^ n ≠ 1 := by
  intro Ω _ _ _ l _ c D T hfit _ c' h K
  obtain ⟨w, hw, hord⟩ := hfit.1.ord
  obtain ⟨i, j, rfl⟩ := condD_roots w hw
  refine ⟨i, j, fun n hn hn4 heq => ?_⟩
  obtain ⟨g, hgL, hne⟩ := hord n hn hn4
  obtain ⟨hrange, -, -, -, hres, -⟩ := P1.towerGal D T
  rw [← hrange] at hgL
  obtain ⟨g', hg'⟩ := hgL
  haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h
  have hΦ : (T.fr ∅).χ 0 g * (T.fr ∅).χ 3 g = (T.fr ∅).χ 1 g * (T.fr ∅).χ 2 g := by
    simp only [Tower.fr, chi, lab]
    cases T.pr <;> simp [Raw.ps, Raw.th, mul_comm]
  have hrt := condD_rt (T.fr ∅) g hΦ i j
  have hq : resQ T.F g = resQ T.L g' := by rw [← hg']; exact (hres g').1
  have hA : (T.fr ∅).χ i g = chi D T.pr i (resQ T.L g') := by rw [← hq]; rfl
  have hB : (T.fr ∅).χ j g = chi D T.pr j (resQ T.L g') := by rw [← hq]; rfl
  rw [hA, hB] at hrt
  have hAval : ((chi D T.pr i (resQ T.L g') : (c.O)ˣ) : c.O) =
      (((T.fr ∅).rt (wt i j) g : (c.O)ˣ) : c.O) * (chi D T.pr j (resQ T.L g') : c.O) := by
    rw [← hrt, Units.val_mul]
  have hx : (K.r.chib i (K.V.pr g') / K.r.chib j (K.V.pr g')) ^ n = 1 :=
    DFunLike.congr_fun heq (K.V.pr g')
  have hx' := congrArg (fun u : (ResidueField c'.O)ˣ => (u : ResidueField c'.O)) hx
  simp only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_one] at hx'
  rw [K.chib i g', K.chib j g', hAval] at hx'
  have hκ : residue c'.O (K.κ g' : c'.O) ≠ 0 := ((K.κ g').isUnit.map (residue _)).ne_zero
  have hBn : residue c'.O (inc h (chi D T.pr j (resQ T.L g') : c.O)) ≠ 0 :=
    (((chi D T.pr j (resQ T.L g')).isUnit.map (inc h)).map (residue _)).ne_zero
  simp only [map_mul] at hx'
  rw [mul_div_mul_left _ _ hκ, mul_div_cancel_right₀ _ hBn] at hx'
  apply hne
  show (residue c.O (((T.fr ∅).rt (wt i j) g : (c.O)ˣ) : c.O)) ^ n = 1
  apply (ResidueField.map (inc h)).injective
  rw [map_pow, map_one, ResidueField.map_residue]
  exact hx'
end
