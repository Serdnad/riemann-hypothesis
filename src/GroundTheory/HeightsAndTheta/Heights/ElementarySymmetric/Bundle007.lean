module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorSubInsertion
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle006
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqCech
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle006
import Mathlib.Algebra.MvPolynomial.Nilpotent
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

universe u w

section Combinatorics

end Combinatorics

section Snoc

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

end Snoc

section Dim

end Dim

theorem InterNumCut.proof (hF : CycleSplit.Filt.Statement.{u, w}) (hA : CutRestrLenExact.Statement.{u, w})
    (hB : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} :=
  _root_.UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.proof hF hA hB

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagonalFibreFubini

def wordCoef (i : ℕ) : ℕ → Fin 2 → ℝ := fun n =>
  if n = 0 then ![1, -1] else if n = 1 then ![0, 1] else if n < 2 + 2 * i then ![1, 0] else ![0, 1]

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem linProd_word (k i : ℕ) (hik : i < k) :
    wwLinProd k (wordCoef i) = (X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * k = 2 + 2 * i + r := ⟨2 * k - 2 - 2 * i, by omega⟩
  rw [wwLinProd, hr, Finset.prod_range_add, Finset.prod_range_add]
  have h1 : ∏ x ∈ Finset.range 2, (C (wordCoef i x 0) * X 0 + C (wordCoef i x 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
      (X 0 - X 1) * X 1 := by
    simp [Finset.prod_range_succ, wordCoef]
    ring
  have h2 : ∏ x ∈ Finset.range (2 * i),
      (C (wordCoef i (2 + x) 0) * X 0 + C (wordCoef i (2 + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) = X 0 ^ (2 * i) := by
    rw [← Finset.card_range (2 * i), ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x hx => ?_
    have hx' : x < 2 * i := Finset.mem_range.1 hx
    simp [wordCoef, show 2 + x ≠ 1 by omega, show 2 + x < 2 + 2 * i by omega]
  have h3 : ∏ x ∈ Finset.range r,
      (C (wordCoef i (2 + 2 * i + x) 0) * X 0 + C (wordCoef i (2 + 2 * i + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
        X 1 ^ r := by
    rw [← Finset.card_range r, ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x _ => ?_
    simp [wordCoef, show 2 + 2 * i + x ≠ 1 by omega,
      show ¬ 2 + 2 * i + x < 2 + 2 * i by omega]
  rw [h1, h2, h3, show 2 + 2 * i + r - 1 - 2 * i = r + 1 by omega, pow_succ]
  ring

end DiagonalFibreFubini


end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Monoid

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

abbrev twistMonoid : CommMonoid (SubSystem S x Ω) where
  mul F Q := F.twist Q
  one := twistSys S x 0
  mul_assoc F P Q := SubSystem.twist_assoc F P Q
  one_mul F := twistSys_zero_twist F
  mul_one F := SubSystem.twist_twistSys_zero F
  mul_comm F Q := SubSystem.twist_comm F Q

attribute [local instance] twistMonoid

theorem foldl_twist_eq_mul {n : ℕ} (L : Fin n → SubSystem S x Ω) (l : List (Fin n)) (F : SubSystem S x Ω) :
    l.foldl (fun F i => F.twist (L i)) F = F * (l.map L).prod := by
  induction l generalizing F with
  | nil => exact (mul_one F).symm
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc]
    rfl

theorem prod_map_filter {α M : Type*} [CommMonoid M] (p : α → Bool) (f : α → M) (l : List α) :
    ((l.filter p).map f).prod = (l.map fun a => if p a then f a else 1).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ih]
    · simp [h, ih]

theorem tensorSub_eq_prod {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = ∏ j ∈ T, L j := by
  unfold tensorSub
  rw [foldl_twist_eq_mul]
  change 1 * _ = _
  rw [one_mul, prod_map_filter, ← Fin.prod_univ_def, ← Finset.prod_filter]
  congr 1
  ext j
  simp

end Monoid

section MixDiff

theorem powerset_map_emb {α β : Type*} (e : α ↪ β) (s : Finset α) :
    (s.map e).powerset = s.powerset.map (Finset.mapEmbedding e).toEmbedding := by
  ext T
  simp only [Finset.mem_powerset, Finset.mem_map, Finset.subset_map_iff, RelEmbedding.coe_toEmbedding,
    Finset.mapEmbedding_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

variable {G : Type*} [CommMonoid G]

def mixDiff (f : G → ℤ) {n : ℕ} (L : Fin n → G) : ℤ :=
  ∑ T : Finset (Fin n), (-1) ^ (n - T.card) * f (∏ j ∈ T, L j)

theorem mixDiff_snoc (f : G → ℤ) {m : ℕ} (L : Fin m → G) (X : G) :
    mixDiff f (Fin.snoc (α := fun _ => G) L X) = mixDiff (fun g => f (X * g)) L - mixDiff f L := by
  classical
  unfold mixDiff
  rw [← Finset.powerset_univ, ← Finset.powerset_univ, Fin.univ_castSuccEmb, Finset.cons_eq_insert,
    Finset.sum_powerset_insert (by simp), powerset_map_emb, Finset.sum_map, Finset.sum_map,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun U _ => ?_
  have hU : U.card ≤ m := by simpa using U.card_le_univ
  have hlast : Fin.last m ∉ U.map Fin.castSuccEmb := by simp [Fin.castSucc_ne_last]
  have hp : ∏ j ∈ U.map Fin.castSuccEmb, Fin.snoc (α := fun _ => G) L X j = ∏ j ∈ U, L j := by
    rw [Finset.prod_map]
    simp
  simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply, Finset.card_insert_of_notMem hlast,
    Finset.card_map, Finset.prod_insert hlast, hp, Fin.snoc_last]
  rw [show m + 1 - U.card = m - U.card + 1 by omega, show m + 1 - (U.card + 1) = m - U.card by omega, pow_succ]
  ring

theorem mixDiff_snoc_mul (f : G → ℤ) {m : ℕ} (L : Fin m → G) (X Y : G) :
    mixDiff f (Fin.snoc (α := fun _ => G) L (X * Y)) =
      mixDiff f (Fin.snoc (α := fun _ => G) L X) + mixDiff f (Fin.snoc (α := fun _ => G) L Y) +
        mixDiff f (Fin.snoc (α := fun _ => G) (Fin.snoc (α := fun _ => G) L X) Y) := by
  simp only [mixDiff_snoc]
  have h : mixDiff (fun g => f (Y * (X * g))) L = mixDiff (fun g => f (X * Y * g)) L := by
    congr 1
    funext g
    rw [mul_left_comm, mul_assoc]
  simp only [h]
  ring

end MixDiff

section Main

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

attribute [local instance] twistMonoid

theorem interSum_eq_mixDiff (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω) (c : ℕ) :
    interSum pp L c = mixDiff (fun F => restrLen pp (F.twist (twistSys S x (c : ℤ)))) L := by
  unfold interSum mixDiff
  simp only [tensorSub_eq_prod]

end Main

attribute [local instance] twistMonoid

theorem InterNumAdditive.proof (hE : InterNumEventual.Statement.{u, w})
    (hZ : InterSumTopVanish.Statement.{u, w}) : InterNumAdditive.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L i L' L'' hW
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  set σ := Equiv.swap i (Fin.last m) with hσ
  set L₀ : Fin m → LineBundle k x := fun j => L (σ (Fin.castSucc j)) with hL₀

  have hfam : ∀ B : LineBundle k x, Function.update (fun j => (L j).toSubSystem) i B.toSubSystem =
      fun j => (Function.update L i B j).toSubSystem := fun B => by
    funext j
    exact (Function.apply_update (fun _ B => B.toSubSystem) L i B j).symm

  have hmove : ∀ (Y : SubSystem k x Ω) (c : ℕ),
      interSum pp (Function.update (fun j => (L j).toSubSystem) i Y) c =
        interSum pp (Fin.snoc (α := fun _ => SubSystem k x Ω) (fun j => (L₀ j).toSubSystem) Y) c := by
    intro Y c
    rw [← interSum_comp_perm pp _ σ c]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [hσ]
    · have hne : σ (Fin.castSucc j) ≠ i := by
        rw [hσ, Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
        exact Fin.castSucc_ne_last j
      simp [Function.update_of_ne hne, hL₀]

  have hev : ∀ B : LineBundle k x, ∀ᶠ c : ℕ in atTop,
      interSum pp (Function.update (fun j => (L j).toSubSystem) i B.toSubSystem) c =
        interNum pp (Function.update (fun j => (L j).toSubSystem) i B.toSubSystem) := fun B => by
    obtain ⟨a, ha⟩ := hE k Ω N x (m + 1) pp (Function.update L i B) hW
    rw [hfam B]
    exact interSum_eventually_eq_interNum pp _ ha
  have hz := hZ k Ω N x (m + 1) pp
    (Fin.snoc (α := fun _ => LineBundle k x) (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L'') hW
  obtain ⟨c, h1, h2, h3, h4⟩ :=
    ((hev (L'.tensorProd L'')).and ((hev L').and ((hev L'').and hz))).exists
  have hs : (fun j => (Fin.snoc (α := fun _ => LineBundle k x)
      (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L'' j).toSubSystem) =
      Fin.snoc (α := fun _ => SubSystem k x Ω) (Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun j => (L₀ j).toSubSystem) L'.toSubSystem) L''.toSubSystem := by
    have e1 := Fin.comp_snoc (fun B : LineBundle k x => B.toSubSystem)
      (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L''
    have e2 := Fin.comp_snoc (fun B : LineBundle k x => B.toSubSystem) L₀ L'
    simp only [Function.comp_def] at e1 e2
    rw [e1, e2]
  have key := mixDiff_snoc_mul (fun F => restrLen pp (F.twist (twistSys k x (c : ℤ))))
    (fun j => (L₀ j).toSubSystem) L'.toSubSystem L''.toSubSystem
  rw [← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← hs, h4,
    add_zero, ← hmove, ← hmove, ← hmove] at key
  have e : (L'.tensorProd L'').toSubSystem = L'.toSubSystem.twist L''.toSubSystem := rfl
  rw [e] at h1
  rw [← h1, ← h2, ← h3]
  exact key

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem GradedCech.proof : GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof

end GroundTheory.Heights₂.Heights.Swarm
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def RestrLenEuler.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (qq : Ideal (Poly k N)), (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) →
    primeOf (S := k) x ≤ qq → ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∀ᶠ c : ℤ in atTop,
        restrLen qq (((twistSys k x 0).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          pieceChar k qq 0 L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

def subsetDiff (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ) (m : ℕ) (c : ℤ) : ℚ :=
  ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) *
    f (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m) c

def SubsetDiffConst.Statement : Prop :=
  ∀ (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ), IsNumPolyLT (n + 1) (n + 1) f →
    (∀ (m m' : ℕ) (c c' : ℤ), subsetDiff n f m c = subsetDiff n f m' c') ∧
      (IsNumPolyLT (n + 1) n f → ∀ (m : ℕ) (c : ℤ), subsetDiff n f m c = 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace BoundedSectionTransfer

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_C (r : ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h0
  · subst h0; simp
  · exact absurd rfl hm

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hg]
  refine ⟨fun h ↦ C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right
    (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_ne_zero k))), fun h ↦ by rw [h, C_0, zero_mul]⟩

theorem aeval_xpow [DecidableEq K] {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ) :
    aeval y (ArakelovGeometry.xpow c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [ArakelovGeometry.xpow, map_prod]

end BoundedSectionTransfer

end

end GroundTheory.Heights₂.Heights.Targets
end
