module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.CoefAlg

theorem pow_frobenius_truncated {B : Type} [CommRing B] (δ : B) (p : ℕ) [Fact p.Prime]
    (hp0 : (p : B) = 0) (hδ : δ ^ (p + 1) = 0) (a : Fin (p + 1) → B) (ha0 : a 0 = 1)
    (h1 : 1 < p + 1) :
    (∑ i, a i * δ ^ (i : ℕ)) ^ p = 1 + a ⟨1, h1⟩ ^ p * δ ^ p := by
  have hpp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hpp.two_le
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact Subsingleton.elim _ _
  haveI : CharP B p := by
    have h := CharP.ringChar_of_prime_eq_zero hpp hp0
    rw [← h]
    exact ringChar.charP B
  rw [sum_pow_char p]
  have hterm : ∀ i : Fin (p + 1), (a i * δ ^ (i : ℕ)) ^ p =
      (if i = 0 then 1 else 0) + (if i = ⟨1, h1⟩ then a ⟨1, h1⟩ ^ p * δ ^ p else 0) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      have : (0 : Fin (p + 1)) ≠ ⟨1, h1⟩ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [ha0, this]
    by_cases hi1 : i = ⟨1, h1⟩
    · subst hi1
      have : (⟨1, h1⟩ : Fin (p + 1)) ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [this, mul_pow]
    · have hv0 : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
      have hv1 : (i : ℕ) ≠ 1 := fun h => hi1 (Fin.ext h)
      have hv : 2 ≤ (i : ℕ) := by omega
      have hle : p + 1 ≤ (i : ℕ) * p := by nlinarith
      have hz : δ ^ ((i : ℕ) * p) = 0 := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
        rw [hk, pow_add, hδ, zero_mul]
      simp [hi0, hi1, mul_pow, ← pow_mul, hz]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem delta_pow_mul_truncated {B : Type} [CommRing B] (δ : B) (p : ℕ)
    (hδ : δ ^ (p + 1) = 0) (b : Fin (p + 1) → B) (hb0 : b 0 = 1) :
    δ ^ p * ∑ i, b i * δ ^ (i : ℕ) = δ ^ p := by
  rw [Fin.sum_univ_succ, mul_add, Finset.mul_sum]
  have hz : ∀ i : Fin p, δ ^ p * (b i.succ * δ ^ ((i.succ : Fin (p + 1)) : ℕ)) = 0 := by
    intro i
    have : δ ^ p * (b i.succ * δ ^ ((i.succ : Fin (p + 1)) : ℕ)) =
        b i.succ * (δ ^ (p + 1) * δ ^ (i : ℕ)) := by
      simp only [Fin.val_succ]
      ring
    rw [this, hδ]
    simp
  rw [Finset.sum_eq_zero (fun i _ => hz i)]
  simp [hb0]

theorem coeff_comparison : ∀ (A B : Type) [CommRing A] [CommRing B] (π : A →+* B) (δ : B) (p : ℕ) [Fact p.Prime], (p : B) = 0 → δ ^ (p + 1) = 0 → (∀ c c' : Fin (p + 1) → A, ∑ i, π (c i) * δ ^ (i : ℕ) = ∑ i, π (c' i) * δ ^ (i : ℕ) → c = c') → ∀ (u c₁ c₂ : Fin (p + 1) → A), u 0 = 1 → c₁ 0 = 1 → c₂ 0 = 1 → ∑ i, π (c₁ i) * δ ^ (i : ℕ) = (∑ i, π (u i) * δ ^ (i : ℕ)) ^ p * ∑ i, π (c₂ i) * δ ^ (i : ℕ) → c₁ (Fin.last p) = c₂ (Fin.last p) + u ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩ ^ p := by
  intro A B _ _ π δ p _ hp0 hδ huniq u c₁ c₂ hu0 hc₁ hc₂ hmain
  have h1 : 1 < p + 1 := Nat.succ_lt_succ (Nat.Prime.pos Fact.out)
  have hfrob := pow_frobenius_truncated δ p hp0 hδ (fun i => π (u i)) (by simp [hu0]) h1
  have hdel := delta_pow_mul_truncated δ p hδ (fun i => π (c₂ i)) (by simp [hc₂])
  have hlast : ∀ i : Fin (p + 1),
      π (Function.update c₂ (Fin.last p) (c₂ (Fin.last p) + u ⟨1, h1⟩ ^ p) i) * δ ^ (i : ℕ) =
        π (c₂ i) * δ ^ (i : ℕ) +
          (if i = Fin.last p then π (u ⟨1, h1⟩) ^ p * δ ^ p else 0) := by
    intro i
    by_cases hi : i = Fin.last p
    · subst hi
      simp [add_mul]
    · simp [Function.update_of_ne hi, hi]
  have hsum : ∑ i, π (c₁ i) * δ ^ (i : ℕ) = ∑ i,
      π (Function.update c₂ (Fin.last p) (c₂ (Fin.last p) + u ⟨1, h1⟩ ^ p) i) * δ ^ (i : ℕ) := by
    simp only [hlast, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hmain, hfrob, add_mul, _root_.one_mul, _root_.mul_assoc, hdel]
  have := huniq _ _ hsum
  rw [this]
  simp

end GlobalTheory.CompanionTheory.Ar.CoefAlg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem gm_appLE {X Y : Scheme.{0}} (a : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ a ⁻¹ᵁ U) (u : Γ(X, U)ˣ)
    {x : Y} (hx : x ∈ V) :
    gm (𝟙 Y) x V (Units.map (a.appLE U V h).hom.toMonoidHom u) = gm a x U u := by
  have e : Units.map (a.appLE U V h).hom.toMonoidHom u = res h (pullU a U u) := by
    apply Units.ext
    simp [res, pullU, Scheme.Hom.appLE]
  rw [e, gm_res _ x h hx, gm_pull (𝟙 Y) a x U (h hx) u, Category.id_comp]

theorem cob_group {G : Type} [CommGroup G] (p q r u v B T : G) (h₁ : p * q = v) (h₂ : r * u = v) :
    p * (q * B⁻¹ * T) = r * B⁻¹ * (u * T) := by
  calc p * (q * B⁻¹ * T) = p * q * (B⁻¹ * T) := by simp only [_root_.mul_assoc]
    _ = r * u * (B⁻¹ * T) := by rw [h₁, h₂]
    _ = r * B⁻¹ * (u * T) := mul_mul_mul_comm r u B⁻¹ T

theorem exists_gen_of_units (X Y : Scheme.{0}) (L : LB X) (hL : L.IsLB) (a b : Y ⟶ X) (hab : ∀ y, a y = b y)
    (t : ∀ j, Γ(Y, b ⁻¹ᵁ L.U j)ˣ)
    (ht : ∀ (j j' : L.ι) (h : b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')),
      res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j from fun _ hy => hy.1) (t j) =
        Units.map (a.appLE _ _ h).hom.toMonoidHom (L.g j j') * (pullU b _ (L.g j j'))⁻¹ *
          res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j' from fun _ hy => hy.2) (t j')) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]), c.IsGen := by
  have hA : ∀ i : Fin 2 → L.ι, ∀ y ∈ LB.wchart L ![a, b] i, a y ∈ L.U (i 0) := fun i y hy =>
    Set.mem_iInter.1 hy 0
  have hB : ∀ i : Fin 2 → L.ι, ∀ y ∈ LB.wchart L ![a, b] i, b y ∈ L.U (i 1) := fun i y hy =>
    Set.mem_iInter.1 hy 1
  have hle : ∀ i : Fin 2 → L.ι, LB.wchart L ![a, b] i ≤ a ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i 1)) := fun i y hy =>
    ⟨hA i y hy, by
      show a y ∈ L.U (i 1)
      rw [hab y]; exact hB i y hy⟩
  have hle' : ∀ i : Fin 2 → L.ι, LB.wchart L ![a, b] i ≤ b ⁻¹ᵁ L.U (i 1) := fun i y hy => hB i y hy
  let s : ∀ i : Fin 2 → L.ι, Γ(Y, LB.wchart L ![a, b] i)ˣ := fun i =>
    res (hle i) (pullU a _ (L.g (i 0) (i 1))) * res (hle' i) (t (i 1))
  have hs : ∀ (i : Fin 2 → L.ι) (x : Y), x ∈ LB.wchart L ![a, b] i →
      gm (𝟙 Y) x _ (s i) = gm a x _ (L.g (i 0) (i 1)) * gm (𝟙 Y) x _ (t (i 1)) := by
    intro i x hx
    have h₁ : gm (𝟙 Y) x _ (res (hle i) (pullU a _ (L.g (i 0) (i 1)))) = gm a x _ (L.g (i 0) (i 1)) := by
      rw [gm_res _ x _ hx, gm_pull (𝟙 Y) a x _ (hle i hx), Category.id_comp]
    rw [map_mul, h₁, gm_res _ x _ hx]
  refine ⟨⟨s⟩, fun i i' => unit_ext fun x hx => ?_⟩
  have hmem : b x ∈ L.U (i 1) ⊓ L.U (i' 1) := ⟨hB i x hx.1, hB i' x hx.2⟩
  have hh : b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) ≤ a ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) := fun y hy => by
    show a y ∈ L.U (i 1) ⊓ L.U (i' 1)
    rw [hab y]; exact hy
  have e := congrArg (gm (𝟙 Y) x (b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)))) (ht (i 1) (i' 1) hh)
  have hmem' : x ∈ b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) := hmem
  rw [map_mul, map_mul, map_inv, gm_res (𝟙 Y) x _ hmem', gm_res (𝟙 Y) x _ hmem', gm_appLE a hh _ hmem',
    gm_pull (𝟙 Y) b x _ hmem, Category.id_comp] at e
  have c₁ := gm_cocycle hL a x (hA i x hx.1) (show a x ∈ L.U (i 1) from (hle i hx.1).2)
    (show a x ∈ L.U (i' 1) from (hle i' hx.2).2)
  have c₂ := gm_cocycle hL a x (hA i x hx.1) (hA i' x hx.2) (show a x ∈ L.U (i' 1) from (hle i' hx.2).2)
  have hg := gm_linComb L ![a, b] ![1, -1] (𝟙 Y) x i i' hx.1 hx.2
  rw [gm_res _ x _ hx, map_mul, gm_res _ x _ hx]
  show gm (𝟙 Y) x (LB.wchart L ![a, b] i) (s i) =
    gm (𝟙 Y) x (LB.wchart L ![a, b] i ⊓ LB.wchart L ![a, b] i') ((LB.LinComb L ![a, b] ![1, -1]).g i i') *
      gm (𝟙 Y) x (LB.wchart L ![a, b] i') (s i')
  rw [hg, hs i x hx.1, hs i' x hx.2, e, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp, zpow_one, zpow_neg]
  exact cob_group _ _ _ _ _ _ _ c₁ c₂

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.line_bundle_cocycle_pullback_transform : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (a b : Y ⟶ X), (∀ y, a y = b y) → ∀ (t : ∀ j, Γ(Y, b ⁻¹ᵁ L.U j)ˣ), (∀ (j j' : L.ι) (h : b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')), res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j from fun _ hy => hy.1) (t j) = Units.map (a.appLE _ _ h).hom.toMonoidHom (L.g j j') * (pullU b _ (L.g j j'))⁻¹ * res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j' from fun _ hy => hy.2) (t j')) → ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]), c.IsGen := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units | exact GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units <;> assumption)

end
end
