module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanPrism
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Bundle002
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

@[expose] public section

section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

open PrismSpan

variable {P Q : Type} [Group P] [Group Q]

theorem ru_eq (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
    {a b : ℕ} {F : Bi P Q a b} (hF : PInv pr F) : Ru u F = Tc (s u) (Rt (s u)⁻¹ F) := by
  funext x y
  unfold PInv at hF
  have h := hF (s u)⁻¹ (fun i => x i * u) y
  simp only [map_inv, hs] at h
  show F (fun i => x i * u) y = F x (fun j => (s u)⁻¹ * y j * s u * (s u)⁻¹)
  rw [← h]
  congr 1
  · funext i
    rw [hu (x i), inv_mul_cancel_left]
  · funext j
    group

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral

namespace EvaluationCoboundary

open PositivityTheory.KB

theorem ev_eq {G : Type} [Group G] {m : ℕ} (F : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    ev (MonoidHom.id G) F 1 z =
      Finsupp.linearCombination ℝ (fun g : Fin m → G => F fun i => (MonoidHom.id G) (Fin.partialProd g i) • (1 : G)) z := by
  rw [Finsupp.linearCombination_apply]
  rfl

theorem key {G : Type} [Group G] (j : ℕ) (e : (Fin (j + 1) → G) → ℝ) (he : Inv (MonoidHom.id G) e)
    (g : Fin (j + 1) → G) :
    dC e (fun i => (MonoidHom.id G) (Fin.partialProd g i) • (1 : G)) =
      ev (MonoidHom.id G) e 1 (bd G j (Finsupp.single g 1)) := by

  rw [ev_eq, bd, Finsupp.linearCombination_single, one_smul, map_add (f := _), map_sum,
  Finsupp.linearCombination_single, dC, Fin.sum_univ_succ]
  simp only [MonoidHom.id_apply, smul_eq_mul, mul_one, Fin.succAbove_zero, one_smul,
    Fin.val_zero, pow_zero, one_mul, map_smul, Finsupp.linearCombination_single, Fin.val_succ]
  congr 1
  · have h := he (g 0) fun i => Fin.partialProd (fun i => g i.succ) i
    simp only [MonoidHom.id_apply, smul_eq_mul] at h
    rw [← h]
    congr 1
    funext i
    rw [Fin.partialProd_succ']
    rfl
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fin.partialProd_contractNth]
    rfl

end EvaluationCoboundary

theorem evCob : EvCob := by
  intro G _ j e he z hz
  have h : ∀ w : Chn G (j + 1), ev (MonoidHom.id G) (dC e) 1 w =
      ev (MonoidHom.id G) e 1 (bd G j w) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp [ev]
    | add a b ha hb =>
      rw [map_add (f := _), EvaluationCoboundary.ev_eq, map_add (f := _), ← EvaluationCoboundary.ev_eq, ← EvaluationCoboundary.ev_eq, ha, hb,
        EvaluationCoboundary.ev_eq, EvaluationCoboundary.ev_eq e (bd G j b), ← map_add, ← EvaluationCoboundary.ev_eq]
    | single g r =>
      rw [EvaluationCoboundary.ev_eq, Finsupp.linearCombination_single, EvaluationCoboundary.key j e he g,
        ← Finsupp.smul_single_one, map_smul, EvaluationCoboundary.ev_eq, EvaluationCoboundary.ev_eq, map_smul]
      rw [one_smul, ← map_smul, ← map_smul, Finsupp.smul_single_one]
  rw [h, hz]
  simp [ev]

end PositivityTheory.KB.SplitAffineSpectral

end
end

section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

def SplitA : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (q : ℕ) (b : (Fin (q + 2) → Q) → ℝ), dc b = 0 →
    Wtop pr b = dv (zz pr b 1 (q + 1))

def SplitS : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (p q : ℕ) (b : (Fin (p + q + 3) → Q) → ℝ), dc b = 0 →
    dh (zz pr b (p + 1) (q + 2)) = (-1 : ℝ) ^ (p + 1) • dv (zz pr b (p + 2) (q + 1))

def SplitB : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (N : ℕ) (b : (Fin (N + 2) → Q) → ℝ), dc b = 0 →
    dh (zz pr b (N + 1) 1) = (-1 : ℝ) ^ (N + 1) • (fun x _ => b x : Bi P Q (N + 2) 1)

def ZInv : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (n a c : ℕ) (b : (Fin n → Q) → ℝ), a + c = n →
    (∀ (g : Q) x, b (fun i => g * x i) = b x) → PInv pr (zz pr b a c)

def E2VanishingFirstColumn : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ u : Q, (∀ g, g * u = u * g) → ∀ m : ℕ, ColPoly pr s u m → ∀ q : ℕ, q + 1 ≤ m →
    ∀ x : Bi P Q 1 (q + 2), PInv pr x → dv x = 0 → dh x = 0 →
      ∃ e : Bi P Q 1 (q + 1), PInv pr e ∧ x = dv e

def E2VanishingOtherColumns : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ u : Q, (∀ g, g * u = u * g) → ∀ m : ℕ, ColPoly pr s u m → ∀ p q : ℕ, q + 1 ≤ m →
    ∀ x : Bi P Q (p + 2) (q + 2), PInv pr x → dv x = 0 → dh x = 0 →
      ∃ (w : Bi P Q (p + 1) (q + 2)) (e : Bi P Q (p + 2) (q + 1)),
        PInv pr w ∧ dv w = 0 ∧ PInv pr e ∧ x = dh w + dv e

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

structure WData (G P : Type) [Group G] [Group P] where
  ι : G →* P
  ρ : P →* G
  ℓ : Additive P →+ ℤ
  t : P
  ρι : ∀ g, ρ (ι g) = g
  ρt : ρ t = 1
  ℓι : ∀ g, ℓ (Additive.ofMul (ι g)) = 0
  ℓt : ℓ (Additive.ofMul t) = 1
  tc : ∀ z, t * z = z * t
  dec : ∀ p, p = ι (ρ p) * t ^ (ℓ (Additive.ofMul p))

variable {G P : Type} [Group G] [Group P] (W : WData G P)

def WData.pr (z : P) : P := W.ι (W.ρ z)

def WData.ps (z : P) : P := W.t⁻¹ * W.ι (W.ρ z)

theorem WData.comm_range (g : P) (_hg : g ∈ Set.range W.ι) : g * W.t = W.t * g := (W.tc g).symm

theorem WData.pr_mul (g : P) (hg : g ∈ Set.range W.ι) (z : P) : W.pr (g * z) = g * W.pr z := by
  obtain ⟨g', rfl⟩ := hg
  simp [WData.pr, W.ρι]

theorem WData.inv_univ {n : ℕ} (F : (Fin n → P) → ℝ) (hS : InvS (Set.range W.ι) F)
    (ht : ∀ y, F (fun i => W.t * y i) = F y) : InvS Set.univ F := by
  have hk : ∀ k : ℤ, ∀ y, F (fun i => W.t ^ k * y i) = F y := by
    intro k
    induction k using Int.induction_on with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [← ih y, ← ht (fun i => W.t ^ (k : ℤ) * y i)]
      congr 1; funext i
      rw [← mul_assoc, ← zpow_one_add, add_comm]
    | pred k ih =>
      intro y
      rw [← ih y, ← ht (fun i => W.t ^ (-(k : ℤ) - 1) * y i)]
      congr 1; funext i
      rw [← mul_assoc, ← zpow_one_add]; congr 2; ring
  intro p _ y
  have : (fun i => p * y i) = fun i => W.ι (W.ρ p) * (W.t ^ (W.ℓ (Additive.ofMul p)) * y i) := by
    funext i; rw [← mul_assoc, ← W.dec p]
  rw [this, hS _ ⟨_, rfl⟩, hk]

theorem WData.vanish_range {n : ℕ} (F : (Fin n → P) → ℝ) (hF : ∀ g : Fin n → G, F (fun i => W.ι (g i)) = 0)
    (z : Fin n → P) (hz : ∀ i, z i ∈ Set.range W.ι) : F z = 0 := by
  choose g hg using hz
  have : z = fun i => W.ι (g i) := by funext i; exact (hg i).symm
  rw [this, hF]

theorem dc_one {Y : Type} (F : (Fin 1 → Y) → ℝ) (a : Y) (y : Fin 1 → Y) :
    dc F (Fin.cons a y) = F y - F (fun _ => a) := by
  simp [dc, Fin.sum_univ_succ]
  have h1 : (fun j : Fin 1 => (Fin.cons a y : Fin 2 → Y) (Fin.succAbove 1 j)) = fun _ => a := by
    funext j; fin_cases j; rfl
  rw [h1]
  ring

theorem WData.inj (m : ℕ) (c : (Fin (m + 2) → P) → ℝ) (hc : InvS Set.univ c) (hdc : dc c = 0)
    (hres : ∀ g : Fin (m + 2) → G, c (fun i => W.ι (g i)) = 0)
    (hsl : ∀ g : Fin (m + 1) → G, prism W.ps c (fun i => W.ι (g i)) = 0) :
    ∃ e : (Fin (m + 1) → P) → ℝ, InvS Set.univ e ∧ c = dc e := by
  set S := Set.range W.ι with hSdef
  have hcS : InvS S c := fun g _ y => hc g trivial y
  have hprS : ∀ z ∈ S, W.pr z ∈ S := fun z _ => ⟨_, rfl⟩
  set x := prism W.pr c with hxdef
  have hxS : InvS S x := prism_inv W.pr S W.pr_mul c hcS
  have hdx : dc x = -c := by
    funext y
    have h := prism_dc W.pr m c y
    rw [hdc, prism_zero] at h
    have h0 : c (fun i => W.pr (y i)) = 0 := hres (fun i => W.ρ (y i))
    simp only [Pi.zero_apply, add_zero, h0, zero_sub] at h
    simpa using h
  have hx0 : ∀ g : Fin (m + 1) → G, x (fun i => W.ι (g i)) = 0 := fun g =>
    prism_eq_zero_of_set W.pr S hprS c _ (W.vanish_range c hres) (fun i => ⟨_, rfl⟩)
  have hxt : ∀ g : Fin (m + 1) → G, x (fun i => W.t * W.ι (g i)) = 0 := by
    intro g
    rw [hxdef, prism_mul]
    have e1 : (fun z => W.t⁻¹ * W.pr (W.t * z)) = W.ps := by
      funext z; simp [WData.pr, WData.ps, W.ρt]
    have e2 : (fun z : Fin (m + 2) → P => c (fun i => W.t * z i)) = c := by
      funext z; exact hc _ trivial z
    rw [e1, e2]
    exact hsl g
  have hv0 : ∀ g : Fin (m + 1) → G, x (fun i => W.t * W.ι (g i)) - x (fun i => W.ι (g i)) = 0 := by
    intro g; rw [hxt, hx0, sub_zero]
  have hdv : dc ((fun y => x (fun i => W.t * y i)) - x) = 0 := by
    rw [dc_sub]; funext z
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [dc_comp x (fun p => W.t * p) z, hdx]
    simp only [Pi.neg_apply]
    rw [hc _ trivial z]; ring
  have hvS : InvS S ((fun y => x (fun i => W.t * y i)) - x) := by
    intro g hg y
    simp only [Pi.sub_apply]
    have : (fun i => W.t * (g * y i)) = fun i => g * (W.t * y i) := by
      funext i; rw [← mul_assoc, ← mul_assoc, W.comm_range g hg]
    rw [this, hxS g hg, hxS g hg]
  cases m with
  | zero =>
    have hvz : ∀ y : Fin 1 → P, x (fun i => W.t * y i) = x y := by
      intro y
      have h := congrFun hdv (Fin.cons (W.ι 1) y)
      rw [dc_one] at h
      have h1 := hv0 (fun _ => 1)
      simp only [Pi.sub_apply, Pi.zero_apply] at h h1
      linarith
    refine ⟨-x, ?_, ?_⟩
    · have hx := W.inv_univ x hxS hvz
      intro g hg y; simp only [Pi.neg_apply]; rw [hx g hg y]
    · rw [dc_neg, hdx, neg_neg]
  | succ m' =>
    set v := (fun y => x (fun i => W.t * y i)) - x with hvdef
    set w := -prism W.pr v with hwdef
    have hdw : dc w = v := by
      funext y
      have h := prism_dc W.pr m' v y
      rw [hdv, prism_zero] at h
      have h0 : v (fun i => W.pr (y i)) = 0 := hv0 (fun i => W.ρ (y i))
      simp only [Pi.zero_apply, add_zero, h0, zero_sub] at h
      rw [hwdef, dc_neg, Pi.neg_apply, h, neg_neg]
    have hwS : InvS S w := by
      intro g hg y
      simp only [hwdef, Pi.neg_apply]
      rw [prism_inv W.pr S W.pr_mul v hvS g hg y]
    set lev : P → ℤ := fun z => W.ℓ (Additive.ofMul z) with hlevdef
    have hlev : ∀ z, lev (W.t * z) = lev z + 1 := by
      intro z; simp only [hlevdef, ofMul_mul, map_add (f := _), W.ℓt]; ring
    have hlevS : ∀ g ∈ S, ∀ z, lev (g * z) = lev z := by
      rintro g ⟨g', rfl⟩ z; simp only [hlevdef, ofMul_mul, map_add (f := _), W.ℓι, zero_add]
    set w' := levSum W.t lev w with hw'def
    have hw'S : InvS S w' := levSum_inv W.t lev S hlevS W.comm_range w hwS
    have hw'w : (fun y => w' (fun i => W.t * y i)) - w' = w := by
      funext y; exact levSum_spec W.t lev hlev w y
    set e0 := x - dc w' with he0def
    have he0S : InvS S e0 := by
      intro g hg y
      simp only [he0def, Pi.sub_apply]
      rw [hxS g hg y, dc_inv S w' hw'S g hg y]
    have he0t : ∀ y, e0 (fun i => W.t * y i) = e0 y := by
      intro y
      have h1 : dc ((fun y => w' (fun i => W.t * y i)) - w') y = v y := by rw [hw'w, hdw]
      rw [dc_sub] at h1
      simp only [Pi.sub_apply] at h1
      rw [dc_comp w' (fun p => W.t * p) y] at h1
      simp only [he0def, Pi.sub_apply, hvdef] at h1 ⊢
      linarith
    have he0 := W.inv_univ e0 he0S he0t
    refine ⟨-e0, ?_, ?_⟩
    · intro g hg y; simp only [Pi.neg_apply]; rw [he0 g hg y]
    · rw [dc_neg, he0def, dc_sub, dc_dc, sub_zero, hdx, neg_neg]

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
end
