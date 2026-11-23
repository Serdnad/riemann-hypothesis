module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
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
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Generic
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem apow_zpow (x : kˣ) (n : ℤ) (z : ℂ) : apow (x ^ n) z = apow x (n * z) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [_root_.zpow_add_one, apow_mul, ih, ← apow_add]; push_cast; ring_nf
  | pred n ih =>
    rw [_root_.zpow_sub_one, apow_mul, ih, apow_inv, ← apow_add]; push_cast; ring_nf

theorem prod_apow_list (ϖ : kˣ) {α : Type*} (l : List α) (f : α → ℂ) :
    (l.map fun b => apow ϖ (f b)).prod = apow ϖ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.map_cons, List.prod_cons, ih, ← apow_add]; simp

theorem prod_apow_finset (ϖ : kˣ) {α : Type*} (s : Finset α) (f : α → ℂ) :
    ∏ i ∈ s, apow ϖ (f i) = apow ϖ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← apow_add]

end Generic
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Vol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem setOf_le_eq_preimage (u : kˣ) :
    {x : k | valuation k x ≤ valuation k (u : k)} = (fun x => ((u⁻¹ : kˣ) : k) * x) ⁻¹' (𝒪[k] : Set k) := by
  ext x
  have h0 : 0 < valuation k (u : k) := zero_lt_iff.2 (by simp)
  simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff, map_mul,
    Units.val_inv_eq_inv_val, map_inv₀]
  rw [inv_mul_le_one₀ h0]

variable [MeasurableSpace k] [BorelSpace k]

theorem measurableSet_setOf_le (u : kˣ) : MeasurableSet {x : k | valuation k x ≤ valuation k (u : k)} := by
  rw [setOf_le_eq_preimage]
  exact (Model.isOpen_int.preimage (continuous_const.mul continuous_id)).measurableSet

theorem vol_setOf_le (ν : Measure k) (hν : IsUnitVol ν) (u : kˣ) :
    ν {x : k | valuation k x ≤ valuation k (u : k)} = ENNReal.ofReal (nabs k u) := by
  rw [← Model.nabs_vol ν hν u, setOf_le_eq_preimage]
  congr 1
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rfl

theorem measurableSet_box (G : Grid k) (ϖ : kˣ) (a a' : ℤ) : MeasurableSet (box G ϖ a a') :=
  MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_setOf_le _

open Classical in
theorem vol_box (G : Grid k) (ν : Measure k) (hν : IsUnitVol ν) (ϖ : kˣ) (a a' : ℤ) :
    (varsVol G ν (box G ϖ a a')).toReal = ∏ j, ∏ v, nabs k (ϖ ^ boxExp G a a' j v) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have := hν.1
  rw [varsVol, box, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [vol_setOf_le ν hν, ENNReal.toReal_ofReal (Model.nabs_pos _).le]

end Vol
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Expo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_zpow_units {α : Type*} (ϖ : kˣ) (s : Finset α) (f : α → ℤ) : ∏ i ∈ s, ϖ ^ f i = ϖ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, _root_.zpow_add]

variable (G : Grid k)

def vtxDet (a a' : ℤ) (X : ℕ × ℕ) : ℤ :=
  if X.1 = G.m then ∑ x : Fin (G.rank (G.m, X.2)), vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x else 0


open Classical in
def expo (a a' : ℤ) : ℤ :=
  ((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum -
    2 * ∑ j, ∑ v, boxExp G a a' j v

variable {G}

theorem gdet_eq (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j)
    (hg' : ∀ i j, i ≠ G.m → g (i, j) = 1) (X : ℕ × ℕ) : gdet (g X) = ϖ ^ vtxDet G a a' X := by
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · rw [show (i, j) = (G.m, j) by rw [hi], hg, vtxDet, if_pos rfl, colDiag, gdet, det_diagGL, prod_zpow_units]
  · rw [hg' i j hi, vtxDet, if_neg hi]
    simp

end Expo
end GlobalTheory.OriginBox
end
end

section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.OriginBoxVac

section Alg
variable {k : Type} [Field k] [ValuativeRel k]

theorem unit_mul_mem_integer_iff (u : kˣ) (x : k) :
    (u : k) * x ∈ 𝒪[k] ↔ valuation k x ≤ valuation k ((u⁻¹ : kˣ) : k) := by
  have hu : valuation k (u : k) ≠ 0 := by simp
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    ← one_mul (valuation k (u : k))⁻¹, le_mul_inv_iff₀ (zero_lt_iff.2 hu), mul_comm]

theorem scale_eq (ϖ : kˣ) (a A B : ℤ) (x : k) :
    (((ϖ ^ a)⁻¹ : kˣ) : k) * (((ϖ ^ A : kˣ) : k) * x * (((ϖ ^ B)⁻¹ : kˣ) : k)) =
      ((ϖ ^ (A - B - a) : kˣ) : k) * x := by
  have h : ϖ ^ (A - B - a) = (ϖ ^ a)⁻¹ * ϖ ^ A * (ϖ ^ B)⁻¹ := by
    rw [_root_.zpow_sub, _root_.zpow_sub]; group
  rw [h, Units.val_mul, Units.val_mul]; ring

theorem scaled_mem_iff (ϖ : kˣ) (a A B : ℤ) (x : k) :
    (((ϖ ^ a)⁻¹ : kˣ) : k) * (((ϖ ^ A : kˣ) : k) * x * (((ϖ ^ B)⁻¹ : kˣ) : k)) ∈ 𝒪[k] ↔
      valuation k x ≤ valuation k ((ϖ ^ (a - A + B) : kˣ) : k) := by
  rw [scale_eq, unit_mul_mem_integer_iff, ← _root_.zpow_neg, show -(A - B - a) = a - A + B by ring]

end Alg

theorem basePt_zero_of_var {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) :
    basePt c (0 : Matrix n n' k) r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp [basePt, Free, Kept] at h ⊢ <;> omega

end GlobalTheory.OriginBoxVac

namespace GlobalTheory.OriginBoxVac

theorem moveArgs_one_entry {k : Type} [Field k] (G : Grid k) (g : G.VertexGroup) (z : G.Args) (b : Edge)
    (dt : Fin (G.rank b.tgt) → kˣ) (ds : Fin (G.rank b.src) → kˣ) (ht : g b.tgt = diagGL dt)
    (hsrc : g b.src = diagGL ds) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    G.moveArgs .one g z b r s = (dt r : k) * z b r s * ((ds s)⁻¹ : kˣ) := by
  have h1 : ((g b.src)⁻¹).val = diagonal fun i => (((ds i)⁻¹ : kˣ) : k) := by rw [hsrc]; rfl
  simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val]
  rw [h1, ht, diagGL_val, diagonal_transpose, diagonal_transpose, mul_diagonal, diagonal_mul]

end GlobalTheory.OriginBoxVac

namespace GlobalTheory.OriginBox
open GlobalTheory.OriginBoxVac

theorem indicator_moveArgs_origin {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup)
    (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) (e : Vars G) :
    Set.indicator {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}
      (1 : G.Args → ℂ) (G.moveArgs .one g (fill hs 0 0 e)) = (box G ϖ a a').indicator (1 : Vars G → ℂ) e := by
  classical
  set M := G.moveArgs .one g (fill hs 0 0 e) with hMdef
  have hM : ∀ (j : ℕ) (r : Fin (G.rank (G.m, j))) (s : Fin (G.rank (G.m, j + 1))), M (.theta G.m j) r s =
      ((ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) r : kˣ) : k) * downMap hs 0 e j s r *
        (((ϖ ^ vtxExp a a' (G.m - 1 - (j + 1)) (topRank G (j + 1)) s)⁻¹ : kˣ) : k) := by
    intro j r s
    rw [hMdef, moveArgs_one_entry G g _ (.theta G.m j)
      (fun x => ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) x)
      (fun x => ϖ ^ vtxExp a a' (G.m - 1 - (j + 1)) (topRank G (j + 1)) x) (hg j) (hg (j + 1)),
      fill_theta, transpose_apply]
  have hE : ∀ (j : ℕ) (hj : j < G.m - 1) (r' : Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1))
      (s' : Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)),
      M (.theta G.m j) (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega) r')
        (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega) s') =
      ((ϖ ^ auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) r' : kˣ) : k) * stepPt ((0 : ColArgs G) j) (e ⟨j, hj⟩) s' r' *
        (((ϖ ^ auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) s')⁻¹ : kˣ) : k) := by
    intro j hj r' s'
    rw [hM, show G.m - 1 - j = G.m - 2 - j + 1 by omega, vtxExp_frame,
      show G.m - 1 - (j + 1) = G.m - 2 - j by omega, vtxExp_frame]
    congr 2
    simp only [downMap, dif_pos hj, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]

  have hbox : ∀ (j : ℕ) (hj : j < G.m - 1) (r' : Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1))
      (s' : Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)) (hv : Free ((G.m - 2 - j) / 2 + 1) (s', r') ∨ Kept (s', r')),
      (((ϖ ^ a)⁻¹ : kˣ) : k) * M (.theta G.m j) (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega) r')
        (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega) s') ∈ 𝒪[k] ↔
      valuation k (e ⟨j, hj⟩ ⟨(s', r'), hv⟩) ≤ valuation k ((ϖ ^ boxExp G a a' ⟨j, hj⟩ ⟨(s', r'), hv⟩ : kˣ) : k) := by
    intro j hj r' s' hv
    rw [hE, scaled_mem_iff]
    simp only [stepPt, Matrix.add_apply, of_apply, dif_pos hv, Pi.zero_apply, basePt_zero_of_var s' r' hv, zero_add]
    rfl
  have key : (∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * M b i j ∈ 𝒪[k]) ↔ e ∈ box G ϖ a a' := by
    constructor
    · intro H j _ v _
      have hb : Edge.theta G.m j ∈ oppositePath G.m := by have := j.2; simp [oppositePath]; omega
      exact (hbox j j.2 v.1.2 v.1.1 v.2).1 (H _ hb _ _)
    · intro he b hb r s
      simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
      rcases hb with ⟨i, -, rfl⟩ | ⟨j, hj, rfl⟩
      · have h0 : M (.ex i G.m) = 0 := by
          simp only [hMdef, Grid.moveArgs, fill_ex, Pi.zero_apply, transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
        simp [h0]
      · rcases Nat.lt_or_ge j (G.m - 1) with hj' | hj'
        · obtain ⟨r', rfl⟩ := (frame (a := topRank G j) (c := G.m - 2 - j + 1) (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega)).surjective r
          obtain ⟨s', rfl⟩ := (frame (a := topRank G (j + 1)) (c := G.m - 2 - j) (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega)).surjective s
          by_cases hv : Free ((G.m - 2 - j) / 2 + 1) (s', r') ∨ Kept (s', r')
          · exact (hbox j hj' r' s' hv).2 (he ⟨j, hj'⟩ trivial ⟨(s', r'), hv⟩ trivial)
          · rw [hE j hj', scale_eq]
            simp only [stepPt, Matrix.add_apply, of_apply, dif_neg hv, add_zero, Pi.zero_apply]
            rcases s' with s' | l <;> rcases r' with r' | i
            · simp [basePt]
            · simp [basePt]
            · simp [basePt]
            · simp only [basePt, fromBlocks_apply₂₂, of_apply]
              split_ifs with hli
              · have h0 : auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) (Sum.inr i : Fin (topRank G j) ⊕ _) -
                    auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) (Sum.inr l : Fin (topRank G (j + 1)) ⊕ _) - a = 0 := by
                  simp only [auxiliaryVectorUniformizerExponent, hli]; push_cast; ring
                rw [h0]; simp
              · simp
        · have hjm : j + 1 = G.m := by omega
          have h0 : M (.theta G.m j) r s = 0 := by
            rw [hM]; simp [downMap, show ¬ j < G.m - 1 by omega, hjm]
          simp [h0]
  by_cases he : e ∈ box G ϖ a a'
  · rw [Set.indicator_of_mem he]
    exact Set.indicator_of_mem (s := {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}) (key.2 he) _
  · rw [Set.indicator_of_notMem he]
    exact Set.indicator_of_notMem (s := {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}) (fun h => he (key.1 h)) _

end GlobalTheory.OriginBox
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh
  GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

namespace GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem resThk_pt (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    spMap ((RingHom.id (Sec (algStr R T.obj.B) p.1.1.1)).comp
      (Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) : Sec (algStr R T.obj.B) q.1.1.1 →+* Sec (algStr R T.obj.B) p.1.1.1)) ≫
      (affPt (algStr R T.obj.B) q.1.1 ≫ pt T) = affPt (algStr R T.obj.B) p.1.1 ≫ pt T := by
  rw [RingHom.id_comp, ← Category.assoc, affPt_res]

def resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) : thk T q ⟶ thk T p :=
  ⟨Thick.trivHom (T := (thk T p).obj) (Sec.res (algStr R T.obj.B) (Pair.le_fst hpq)) (resThk_pt T hpq)⟩

theorem bM_resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    bM T q ≫ resThk T hpq = bM T p :=
  ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext fun b ↦
    res_toSec R T.obj.B (homOfLE (Pair.le_fst hpq)).op b))

theorem aM_resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    aM T q ≫ resThk T hpq = (affF s).map (homOfLE (Pair.le_snd hpq)).op ≫ aM T p :=
  ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext fun u ↦
    (congrArg (fun t ↦ t.hom u) ((pt T).appLE_map q.2 (homOfLE (Pair.le_fst hpq)).op)).trans
      (congrArg (fun t ↦ t.hom u) ((pt T).map_appLE p.2 (homOfLE (Pair.le_snd hpq)).op)).symm))

theorem hSec_res (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s))
    (hg : ∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a))
    (T : TT s) (p q : Pair (pt T)) (hpq : p ≤ q) :
    Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) (hSec f g T q) = hSec f g T p := by
  set ρ := Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) with hρ
  let d : op q.1.2 ⟶ op p.1.2 := (homOfLE (Pair.le_snd hpq)).op
  have e1 : fv f (bM T p) = ρ (fv f (bM T q)) + fv f (resThk T hpq) := by
    rw [← bM_resThk T hpq]; exact f.2 _ _
  have e2 : ρ (fv f (aM T q)) + fv f (resThk T hpq) =
      secPullA T p (fv f ((affF s).map d)) + fv f (aM T p) := by
    have k := f.2 (aM T q) (resThk T hpq)
    rw [aM_resThk] at k
    exact k.symm.trans (f.2 ((affF s).map d) (aM T p))
  have e3 : g (op p.1.2) = Sec.res s (Pair.le_snd hpq) (g (op q.1.2)) +
      (show Sec s p.1.2.1 from fv f ((affF s).map d)) :=
    sub_eq_iff_eq_add'.1 (hg d)
  have e4 : ∀ u, secPullA T p (Sec.res s (Pair.le_snd hpq) u) = ρ (secPullA T q u) := fun u ↦
    (congrArg (fun m ↦ m.hom.φ u) (aM_resThk T hpq)).symm
  change ρ (secPullA T q (g (op q.1.2)) + fv f (aM T q) - fv f (bM T q)) =
    secPullA T p (g (op p.1.2)) + fv f (aM T p) - fv f (bM T p)
  rw [map_sub, map_add (f := _), e1, e3, map_add (f := _), e4]
  linear_combination e2

end GlobalTheory.CechDR.AffLoc
end
end

section

open MeasureTheory ValuativeRel GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.UnfoldLoss

namespace GlobalTheory.UnfoldLoss.LatVol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem varLat_eq_pi (G : Grid k) (ϖ : kˣ) (n : ℕ) :
    (varLat G ϖ n : Set (Vars G)) = Set.univ.pi fun _ => Set.univ.pi fun _ => cball (ϖ ^ n) := by
  ext e
  exact ⟨fun h j _ r _ => h j r, fun h j r => h j trivial r trivial⟩

theorem eventually_cball_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {U : Set k} (hU : U ∈ nhds (0 : k)) :
    ∀ᶠ n : ℕ in Filter.atTop, cball (ϖ ^ n) ⊆ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  haveI : MulArchimedean (ValueGroupWithZero k) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 γ
  refine Filter.eventually_atTop.2 ⟨N, fun n hn z hz => hγ ?_⟩
  have hz' : valuation k z ≤ valuation k ((ϖ ^ n : kˣ) : k) := hz
  rw [Units.val_pow_eq_pow_val, map_pow] at hz'
  exact (hz'.trans (pow_le_pow_of_le_one zero_le h1.le hn)).trans_lt hN

theorem varLat_basis_open_vol : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (G : Grid k) (ν : Measure k), IsUnitVol ν → ∀ ϖ : kˣ, IsUnif ϖ →
    (∀ s ∈ nhds (0 : Vars G), ∃ n : ℕ, (varLat G ϖ n : Set (Vars G)) ⊆ s) ∧
    ∀ n : ℕ, IsOpen (varLat G ϖ n : Set (Vars G)) ∧ varsVol G ν (varLat G ϖ n : Set (Vars G)) ≠ ⊤ ∧
      (varsVol G ν).real (varLat G ϖ n : Set (Vars G)) = ((resCard k : ℝ)⁻¹) ^ (n * varCount G) := by
  intro k _ _ _ _ _ _ G ν hν ϖ hϖ
  classical
  refine ⟨fun s hs => ?_, fun n => ?_⟩
  · rw [nhds_pi, Filter.mem_pi'] at hs
    obtain ⟨I, t, ht, hts⟩ := hs
    have key : ∀ j, ∀ᶠ n : ℕ in Filter.atTop, (Set.univ.pi fun _ => cball (ϖ ^ n)) ⊆ t j := fun j => by
      have hj := ht j
      rw [nhds_pi, Filter.mem_pi'] at hj
      obtain ⟨J, u, hu, hut⟩ := hj
      filter_upwards [Filter.eventually_all.2 fun r => eventually_cball_subset hϖ (hu r)] with n hn e he
      exact hut fun r _ => hn r (he r trivial)
    obtain ⟨n, hn⟩ := (Filter.eventually_all.2 key).exists
    refine ⟨n, fun e he => hts fun j _ => hn j fun r _ => he j r⟩
  · haveI := hν.1
    haveI := secondCountable k
    have h1 : ((distribHaarChar k ϖ : NNReal) : ℝ) = (resCard k : ℝ)⁻¹ :=
      nabs_uniformiser hϖ.irreducible rfl
    have hv : varsVol G ν (varLat G ϖ n : Set (Vars G)) =
        ((distribHaarChar k ϖ ^ (n * varCount G) : NNReal) : ENNReal) := by
      rw [varLat_eq_pi, varsVol, Measure.pi_pi]
      simp only [Measure.pi_pi, measure_cball, hν.2, mul_one, Finset.prod_const, Finset.card_univ, map_pow,
        varCount, ← Nat.card_eq_fintype_card, ENNReal.coe_pow, ← pow_mul, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
    refine ⟨?_, ?_, ?_⟩
    · rw [varLat_eq_pi]
      exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball _
    · rw [hv]; exact ENNReal.coe_ne_top
    · rw [Measure.real, hv, ENNReal.coe_toReal, NNReal.coe_pow, h1]

end GlobalTheory.UnfoldLoss.LatVol
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem isFirstMax_eventually (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    IsFirstMax Y J → ∀ᶠ Y' in nhds Y, IsFirstMax Y' J := by
  rintro ⟨h0, hle⟩
  have hm : valuation k (minor Y J) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hc : ∀ J' : Fin a ↪ Fin d, Continuous fun Y' : Matrix (Fin a) (Fin d) k => minor Y' J' := fun J' =>
    (continuous_id.matrix_submatrix id J').matrix_det
  have key : ∀ J' : Fin a ↪ Fin d, ∀ᶠ Y' in nhds Y,
      valuation k (minor Y' J') = valuation k (minor Y J') ∨
        (minor Y J' = 0 ∧ valuation k (minor Y' J') < valuation k (minor Y J)) := by
    intro J'
    by_cases hz : minor Y J' = 0
    · have hn : {x : k | valuation k x < ((Units.mk0 _ hm : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)}
          ∈ nhds (0 : k) := (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hm, subset_rfl⟩
      have hca := (hc J').continuousAt (x := Y)
      rw [ContinuousAt, hz] at hca
      filter_upwards [hca hn] with Y' hY'
      exact Or.inr ⟨hz, hY'⟩
    · have hne : valuation k (minor Y J') ≠ 0 := (Valuation.ne_zero_iff _).2 hz
      filter_upwards [(hc J').continuousAt (x := Y) ((valuation k).locally_const hne)] with Y' hY'
      exact Or.inl hY'
  have hall := Filter.eventually_all.2 key
  filter_upwards [hall] with Y' hY'
  have hJ : valuation k (minor Y' J) = valuation k (minor Y J) := by
    rcases hY' J with h | ⟨h, -⟩
    · exact h
    · exact absurd h h0
  refine ⟨(Valuation.ne_zero_iff _).1 (hJ ▸ hm), fun J' => ?_⟩
  rw [hJ]
  rcases hY' J' with h | ⟨-, h⟩
  · rw [h]; exact hle J'
  · exact ⟨h.le, fun _ => h⟩

end GlobalTheory.RankFibreKer
end

section

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

theorem _root_.GlobalTheory.T.partial_operator_fderiv_formula : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ),
    Differentiable ℝ (qOp P f) ∧ ∀ (s v : κ ⊕ κ₁' → V),
      fderiv ℝ (qOp P f) s v = qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s := by
  first | exact @GlobalTheory.SliceOp.differentiable_qOp_and_fderiv | exact GlobalTheory.SliceOp.differentiable_qOp_and_fderiv | (intros; apply GlobalTheory.SliceOp.differentiable_qOp_and_fderiv <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.twoCocycle_coboundary_on_unitLocus_piece : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (p : C') (v : T ⟶ G.obj p), (∀ (S : C) (u : T ⟶ S), IsUnit (mp F u e) → Nonempty (G.obj p ⟶ S)) → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece <;> assumption)
end
