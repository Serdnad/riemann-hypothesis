module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle527
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

theorem cls_LL_add (F : FlagMod.Frames Y π) (e e' : Ix Dw → ℤ) :
    GlobalTheory.CechPic.cls (F.LL (e + e')) (F.isLB_LL _) =
      GlobalTheory.CechPic.cls (F.LL e) (F.isLB_LL _) + GlobalTheory.CechPic.cls (F.LL e') (F.isLB_LL _) := by
  have h := GlobalTheory.CechPic.isLB_tens (F.isLB_LL e) (F.isLB_LL e')
  refine ((GlobalTheory.CechPic.cls_eq_iff (F.isLB_LL (e + e')) h).2 (GlobalTheory.CechPic.iso_of_chart h ⟨fun k => (k, k), fun _ _ h => ⟨h, h⟩, ?_⟩)).trans
    (GlobalTheory.CechPic.cls_tens _ _ h)
  intro y p q hp hq
  refine Eq.trans ?_ (GlobalTheory.CechPic.gm_tens (F.LL e) (F.LL e') (𝟙 Z) y (p, p) (q, q) ⟨hp, hp⟩ ⟨hq, hq⟩).symm
  exact (congrArg (gm (𝟙 Z) y _) (F.LL_add_g e e' p q)).trans (map_mul _ _ _)

def clsLLHom (F : FlagMod.Frames Y π) : (Ix Dw → ℤ) →+ GlobalTheory.CechPic.Pic Z :=
  AddMonoidHom.mk' (fun e => GlobalTheory.CechPic.cls (F.LL e) (F.isLB_LL _)) (cls_LL_add F)

theorem cls_LL_sum (F : FlagMod.Frames Y π) {ι : Type} (s : Finset ι) (e : ι → Ix Dw → ℤ) :
    GlobalTheory.CechPic.cls (F.LL (∑ i ∈ s, e i)) (F.isLB_LL _) = ∑ i ∈ s, GlobalTheory.CechPic.cls (F.LL (e i)) (F.isLB_LL _) :=
  map_sum (clsLLHom F) e s

end GlobalTheory.FlagPlucker
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FunObj.FlatSupp

open GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_inv_pow {ϖ : kˣ} (n : ℕ) :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) = (valuation k (ϖ : k) ^ n)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]

theorem val_inv_pow_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {n n' : ℕ} (h : n ≤ n') :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) ≤ valuation k (((ϖ ^ n')⁻¹ : kˣ) : k) := by
  rw [val_inv_pow, val_inv_pow]
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  exact inv_anti₀ (pow_pos (zero_lt_iff.2 h0) _) (pow_le_pow_of_le_one zero_le' h1 h)

theorem exists_le {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : k) :
    ∃ n : ℕ, valuation k a ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  have hv : valuation k a ≠ 0 := by simpa using ha
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (hϖ ▸ uniformizer_lt_one : valuation k (ϖ : k) < 1) (Units.mk0 _ hv)⁻¹
  refine ⟨n, ?_⟩
  rw [val_inv_pow]
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at hn
  have := le_of_lt hn
  rwa [le_inv_comm₀ (pow_pos (zero_lt_iff.2 h0) _) (zero_lt_iff.2 hv)] at this

theorem exists_bound_conj {ϖ : kˣ} (hϖ : IsUnif ϖ) {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : GL m k) (B : GL n k) :
    ∃ N : ℕ, ∀ Z : Matrix m n k, (∀ r s, ((A⁻¹ : GL m k).val * Z * B.val) r s ∈ 𝒪[k]) →
      ∀ r s, valuation k (Z r s) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) := by
  classical
  choose nA hnA using fun p : m × m => exists_le hϖ (A.val p.1 p.2)
  choose nB hnB using fun p : n × n => exists_le hϖ ((B⁻¹ : GL n k).val p.1 p.2)
  set N0 := Finset.univ.sup nA ⊔ Finset.univ.sup nB
  have hc : valuation k (((ϖ ^ (N0 + N0))⁻¹ : kˣ) : k) =
      valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k) * valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k) := by
    rw [val_inv_pow, val_inv_pow, pow_add, mul_inv]
  set c := valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k)
  have hA : ∀ r a, valuation k (A.val r a) ≤ c := fun r a =>
    (hnA (r, a)).trans (val_inv_pow_mono hϖ (le_sup_left.trans' (Finset.le_sup (f := nA) (Finset.mem_univ (r, a)))))
  have hB : ∀ b s, valuation k ((B⁻¹ : GL n k).val b s) ≤ c := fun b s =>
    (hnB (b, s)).trans (val_inv_pow_mono hϖ (le_sup_right.trans' (Finset.le_sup (f := nB) (Finset.mem_univ (b, s)))))
  refine ⟨N0 + N0, fun Z hZ r s => ?_⟩
  have hZ' : Z = A.val * ((A⁻¹ : GL m k).val * Z * B.val) * (B⁻¹ : GL n k).val := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul]
  rw [hZ', hc]
  set W := (A⁻¹ : GL m k).val * Z * B.val
  simp only [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun b _ => ?_
  rw [map_mul]
  refine mul_le_mul' (Valuation.map_sum_le _ fun a _ => ?_) (hB b s)
  rw [map_mul]
  simpa using mul_le_mul' (hA r a) (show valuation k (W a b) ≤ 1 from hZ a b)


open Matrix in
theorem flatTensor_support : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → (∀ j, j < G.m → ∀ r s, (j + 1 = G.m → r ≠ topLast G (j + 1)) → valuation k (x j r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  classical
  intro k _ _ _ _ _ _ G hs ψ ν ϖ e T keep g hϖ hT
  choose N hN using fun b : Edge => exists_bound_conj hϖ (Assignment.one.read (g b.tgt)) (Assignment.one.read (g b.src))
  refine ⟨(oppositePath G.m).toFinset.sup N, fun x y hne => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, flatIntegrand hs ψ (moved G keep g T) x y v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    unfold flatTensor
    simp [h]
  have hT0 : T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    intro h0
    apply hv
    simp [flatIntegrand, moved, Grid.pathAct, h0]
  have key : ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (fill hs x y v b r s) ≤
      valuation k (((ϖ ^ (oppositePath G.m).toFinset.sup N)⁻¹ : kˣ) : k) := by
    intro b hb r s
    refine le_trans (hN b _ (fun r s => ?_) r s)
      (val_inv_pow_mono hϖ (Finset.le_sup (f := N) (List.mem_toFinset.2 hb)))
    have hm : (G.moveArgs .one g (fill hs x y v)) b ∈ matLat _ (GlobalTheory.SplitFlip.stdLat k _) := by
      by_contra h
      exact hT0 (hT.2.1 _ b hb h)
    exact mem_matLat_stdLat.1 hm r s
  refine ⟨fun j hj r s hr => ?_, fun i hi r s => ?_⟩
  · have hmem : Edge.theta G.m j ∈ oppositePath G.m := by simp [oppositePath]; omega
    by_cases hj' : j < G.m - 1
    · have h := key _ hmem (frame (b := G.rank (G.m, j)) (c := G.m - 2 - j + 1) (by have := topRank_add hs j; omega) (Sum.inl s))
        (frame (b := G.rank (G.m, j + 1)) (c := G.m - 2 - j) (by have := topRank_add hs (j + 1); omega) (Sum.inl r))
      rw [fill_theta, transpose_apply, downMap, dite_eq_left hj'] at h
      simpa [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, stepPt, basePt, Free, Kept] using h
    · have hjm : j + 1 = G.m := by omega
      have hrk := topRank_add hs (j + 1)
      have hrk' := topRank_add hs j
      have hr' : r.val < G.rank (G.m, j + 1) := by
        have := hr hjm
        have h2 : (topLast G (j + 1)).val = topRank G (j + 1) - 1 := rfl
        rw [Ne, Fin.ext_iff, h2] at this
        have := r.2
        omega
      have h := key _ hmem (show Fin (G.rank (G.m, j)) from ⟨s.val, by have := s.2; omega⟩)
        (show Fin (G.rank (G.m, j + 1)) from ⟨r.val, hr'⟩)
      rw [fill_theta, transpose_apply, downMap, dite_eq_right hj', dite_eq_left hjm] at h
      simpa using h
  · have hmem : Edge.ex i G.m ∈ oppositePath G.m := by simp [oppositePath]; omega
    have h := key _ hmem s r
    rwa [fill_ex, transpose_apply] at h

end GlobalTheory.FunObj.FlatSupp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

namespace GlobalTheory.MovedBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_le_inv_pow {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : k) :
    ∃ n : ℕ, valuation k x ≤ (valuation k (ϖ : k) ^ n)⁻¹ := by
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hv : (valuation k x)⁻¹ ≠ 0 := by simp [hx]
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hv)
  have hu : 0 < valuation k (ϖ : k) ^ m := by
    rw [pos_iff_ne_zero]; simp
  refine ⟨m, ?_⟩
  have hx0 : 0 < valuation k x := by rw [pos_iff_ne_zero]; simp [hx]
  exact (le_inv_comm₀ hu hx0).1 (by simpa using hm.le)

theorem inv_pow_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {n N : ℕ} (h : n ≤ N) :
    (valuation k (ϖ : k) ^ n)⁻¹ ≤ (valuation k (ϖ : k) ^ N)⁻¹ := by
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu : 0 < valuation k (ϖ : k) ^ N := by rw [pos_iff_ne_zero]; simp
  exact inv_anti₀ hu (pow_le_pow_right_of_le_one' h1.le h)

theorem exists_uniform {α : Type*} (s : Finset α) (P : α → ℕ → Prop)
    (hP : ∀ a n N, n ≤ N → P a n → P a N) (h : ∀ a ∈ s, ∃ n, P a n) : ∃ n, ∀ a ∈ s, P a n := by
  classical
  choose f hf using h
  exact ⟨s.attach.sup fun a => f a.1 a.2, fun a ha =>
    hP _ _ _ (Finset.le_sup (f := fun a : s => f a.1 a.2) (Finset.mem_attach s ⟨a, ha⟩)) (hf a ha)⟩

theorem exists_matrix_bound {ϖ : kˣ} (hϖ : IsUnif ϖ) {m n : Type*} [Fintype m] [Fintype n] (P : Matrix m n k) :
    ∃ N : ℕ, ∀ r s, valuation k (P r s) ≤ (valuation k (ϖ : k) ^ N)⁻¹ := by
  obtain ⟨N, hN⟩ := exists_uniform (Finset.univ : Finset (m × n))
    (fun rs N => valuation k (P rs.1 rs.2) ≤ (valuation k (ϖ : k) ^ N)⁻¹)
    (fun _ _ _ h h' => h'.trans (inv_pow_mono hϖ h)) (fun rs _ => exists_le_inv_pow hϖ _)
  exact ⟨N, fun r s => hN (r, s) (Finset.mem_univ _)⟩

theorem val_mul_mul_le {a b c d : Type*} [Fintype b] [Fintype c] (P : Matrix a b k) (X : Matrix b c k)
    (Q : Matrix c d k) (p x q : ValueGroupWithZero k) (hP : ∀ r s, valuation k (P r s) ≤ p)
    (hX : ∀ r s, valuation k (X r s) ≤ x) (hQ : ∀ r s, valuation k (Q r s) ≤ q) (r : a) (s : d) :
    valuation k ((P * X * Q) r s) ≤ p * x * q := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, Matrix.mul_apply]
  refine mul_le_mul' (Valuation.map_sum_le _ fun i _ => ?_) (hQ _ _)
  rw [map_mul]
  exact mul_le_mul' (hP _ _) (hX _ _)

end GlobalTheory.MovedBound

namespace GlobalTheory.MovedBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unitsPow_inv (ϖ : kˣ) (n : ℕ) :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) = (valuation k (ϖ : k) ^ n)⁻¹ := by
  simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]

theorem val_unitsPow (ϖ : kˣ) (n : ℕ) :
    valuation k ((ϖ ^ n : kˣ) : k) = valuation k (ϖ : k) ^ n := by
  simp [Units.val_pow_eq_pow_val, map_pow]

end GlobalTheory.MovedBound


open GlobalTheory.MovedBound in
theorem GlobalTheory.MovedBound.moved_bounded_locConst : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, (∀ z : G.Args, moved G keep g T z ≠ 0 → ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (z b r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ z δ : G.Args, (∀ b ∈ oppositePath G.m, ∀ r s, valuation k (δ b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → moved G keep g T (z + δ) = moved G keep g T z := by
  intro k _ _ _ _ G ϖ e T keep g hϖ hT
  classical
  set u := valuation k (ϖ : k) with hu_def
  have hu0 : u ≠ 0 := by simp [u]
  have hu1 : u ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  let A : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k := fun b => ((Assignment.one.read (g b.tgt))⁻¹).val
  let Ai : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k := fun b => (Assignment.one.read (g b.tgt)).val
  let B : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k := fun b => (Assignment.one.read (g b.src)).val
  let Bi : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k := fun b => ((Assignment.one.read (g b.src))⁻¹).val
  obtain ⟨n0, hn0⟩ := exists_uniform (oppositePath G.m).toFinset
    (fun b N => (∀ r s, valuation k (A b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Ai b r s) ≤ (u ^ N)⁻¹) ∧
      (∀ r s, valuation k (B b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Bi b r s) ≤ (u ^ N)⁻¹))
    (fun _ _ _ h ⟨h1, h2, h3, h4⟩ => ⟨fun r s => (h1 r s).trans (inv_pow_mono hϖ h),
      fun r s => (h2 r s).trans (inv_pow_mono hϖ h), fun r s => (h3 r s).trans (inv_pow_mono hϖ h),
      fun r s => (h4 r s).trans (inv_pow_mono hϖ h)⟩)
    (fun b _ => by
      obtain ⟨n1, h1⟩ := exists_matrix_bound hϖ (A b)
      obtain ⟨n2, h2⟩ := exists_matrix_bound hϖ (Ai b)
      obtain ⟨n3, h3⟩ := exists_matrix_bound hϖ (B b)
      obtain ⟨n4, h4⟩ := exists_matrix_bound hϖ (Bi b)
      refine ⟨n1 + n2 + n3 + n4, fun r s => (h1 r s).trans (inv_pow_mono hϖ (by omega)),
        fun r s => (h2 r s).trans (inv_pow_mono hϖ (by omega)), fun r s => (h3 r s).trans (inv_pow_mono hϖ (by omega)),
        fun r s => (h4 r s).trans (inv_pow_mono hϖ (by omega))⟩)
  have hmv : ∀ x : G.Args, ∀ b, G.moveArgs .one g x b = A b * x b * B b := fun _ _ => rfl
  refine ⟨2 * n0 + e, ?_, ?_⟩
  · intro z hz b hb r s
    have hT0 : T (G.moveArgs .one g z) ≠ 0 := by
      intro h0; apply hz; simp [moved, Grid.pathAct, h0]
    have hint : G.moveArgs .one g z b ∈ matLat _ (stdLat k _) := by
      by_contra hc; exact hT0 (hT.2.1 _ b hb hc)
    have hint' := mem_matLat_stdLat.1 hint
    have hz' : z b = Ai b * G.moveArgs .one g z b * Bi b := by
      simp [hmv, A, Ai, B, Bi, ← Matrix.mul_assoc]
    obtain ⟨-, h2, -, h4⟩ := hn0 b (List.mem_toFinset.2 hb)
    rw [hz', val_unitsPow_inv]
    refine (val_mul_mul_le _ _ _ _ 1 _ h2 (fun r s => (hint' r s)) h4 r s).trans ?_
    rw [mul_one, ← mul_inv, ← pow_add]
    exact inv_pow_mono hϖ (by omega)
  · intro z δ hδ
    let δ' : G.Args := fun b => if b ∈ oppositePath G.m then G.moveArgs .one g δ b else 0
    have h1 : T (G.moveArgs .one g (z + δ)) = T (G.moveArgs .one g z + δ') := by
      refine hT.1 fun b hb => ?_
      simp only [Set.mem_setOf_eq] at hb
      simp [δ', hb, hmv, Matrix.mul_add, Matrix.add_mul]
    have h2 : T (G.moveArgs .one g z + δ') = T (G.moveArgs .one g z) := by
      refine hT.2.2 _ _ fun b => ?_
      by_cases hb : b ∈ oppositePath G.m
      · simp only [δ', hb, if_true]
        obtain ⟨h1, -, h3, -⟩ := hn0 b (List.mem_toFinset.2 hb)
        have hd : ∀ r s, valuation k (δ b r s) ≤ u ^ (2 * n0 + e) := fun r s => by
          rw [← val_unitsPow]; exact hδ b hb r s
        have hbd : ∀ r s, valuation k (G.moveArgs .one g δ b r s) ≤ u ^ e := fun r s => by
          rw [hmv]
          refine (val_mul_mul_le _ _ _ _ _ _ h1 hd h3 r s).trans (le_of_eq ?_)
          rw [show 2 * n0 + e = n0 + (n0 + e) by ring, pow_add, pow_add]
          field_simp
        rw [mem_matLat]
        intro i
        rw [mem_smul_lat, mem_stdLat]
        intro j
        rw [Valuation.mem_integer_iff]
        simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
        rw [map_mul, val_unitsPow_inv]
        calc (u ^ e)⁻¹ * valuation k (G.moveArgs .one g δ b i j) ≤ (u ^ e)⁻¹ * u ^ e := mul_le_mul' le_rfl (hbd i j)
          _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hu0)
      · simp only [δ', hb, if_false]
        exact zero_mem _
    simp only [moved, Grid.pathAct, h1, h2]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (exact GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen <;> assumption)
end

section

noncomputable section

open Formalism.REAL (UJ KG toM inG Jm)
open GlobalTheory.PsCo.Pc1
open scoped Matrix

namespace GlobalTheory.PsCo.Pc3

variable {n : ℕ}

theorem pB_conjTranspose (ε : Fin n → Bool) (B : Mode ε → ℂ) : (pB ε B)ᴴ = pB ε B := by
  ext a b
  simp only [Matrix.conjTranspose_apply]
  cases ha : ε a <;> cases hb : ε b <;> simp [pB, ha, hb]

theorem pB_ne (ε : Fin n → Bool) (B : Mode ε → ℂ) (a b : Fin n) (h : ε a = ε b) : pB ε B a b = 0 := by
  simp only [pB]
  rw [dite_eq_right (by rintro ⟨h1, h2⟩; rw [h, h2] at h1; simp at h1),
    dite_eq_right (by rintro ⟨h1, h2⟩; rw [← h, h2] at h1; simp at h1)]

theorem pB_inG (ε : Fin n → Bool) (B : Mode ε → ℂ) : inG ε (pB ε B) := by
  unfold inG
  rw [pB_conjTranspose]
  ext a b
  simp only [Matrix.add_apply, Matrix.zero_apply, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ε a = ε b
  · rw [pB_ne ε B a b h]; simp
  · cases ha : ε a <;> cases hb : ε b <;> simp_all

theorem continuous_pB (ε : Fin n → Bool) : Continuous (pB ε) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [pB]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).star
  · exact continuous_const

theorem pB_zero (ε : Fin n → Bool) : pB ε 0 = 0 := by
  ext a b; simp only [pB]; split_ifs <;> simp

theorem toM_eB (ε : Fin n → Bool) (B : Mode ε → ℂ) : toM (eB ε B) = NormedSpace.exp (pB ε B) := by
  rw [eB, Formalism.REAL.toM_expG ε _ 1 (pB_inG ε B)]; simp

theorem toM_inv (ε : Fin n → Bool) (g : UJ ε) : toM g⁻¹ = (toM g)⁻¹ := by
  show (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
  rw [Matrix.coe_units_inv]

theorem stEB : StEB := by
  intro n ε
  refine ⟨?_, ?_, fun B => ⟨toM_eB ε B, ?_⟩⟩
  · rw [(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.continuous_iff]
    change Continuous fun B => toM (eB ε B)
    simp_rw [toM_eB]
    have hc : Continuous (NormedSpace.exp : Mat n → Mat n) := by
      letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
      letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℚ) (α := ℂ)
      exact @NormedSpace.exp_continuous (Matrix (Fin n) (Fin n) ℂ) _ _
        (inferInstanceAs (CompleteSpace (Fin n → Fin n → ℂ)))
    exact hc.comp (continuous_pB ε)
  · apply Subtype.ext; apply Units.ext
    change toM (eB ε 0) = 1
    rw [toM_eB, pB_zero, NormedSpace.exp_zero]
  · rw [toM_inv, toM_eB]
    rw [Matrix.exp_neg]

end GlobalTheory.PsCo.Pc3
end
end

section

open MeasureTheory GlobalTheory.Orb

namespace GlobalTheory.PsCo.Pc1

theorem stOrbCpt : GlobalTheory.PsCo.Pc1.StOrbCpt := by
  intro n ε μ _ s hs hT dt _ _ y f hf hc
  haveI : μ.IsMulRightInvariant := GlobalTheory.haar_UJ_isMulRightInvariant n ε μ
  exact GlobalTheory.hasOrbInt_of_isCompact_cent_conj _ μ s hT dt (isProperOrbit_realUJ hs) y f hf hc

end GlobalTheory.PsCo.Pc1
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_restrictedProduct_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v, {q : DoubleCoset.Quotient (twCent (θv v) (pf v δ) : Set (Y v)) (K v : Set (Y v)) | ∃ k ∈ K v, fv v ((Quotient.out q * k)⁻¹ * pf v δ * θv v (Quotient.out q * k)) ≠ 0}.Finite) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v ∧ ∀ y, y⁻¹ * pf v δ * θv v y ∈ K v → ∃ t ∈ twCent (θv v) (pf v δ), ∃ k ∈ K v, y = t * k) → twOrb θ (⨅ v, (K v).comap (pf v)) δ f = ∏ᶠ v, twOrb (θv v) (K v) (pf v δ) (fv v) := by
  first | exact @GlobalTheory.EulerAbs.twOrb_restr_eq_finprod | exact GlobalTheory.EulerAbs.twOrb_restr_eq_finprod | (intros; apply GlobalTheory.EulerAbs.twOrb_restr_eq_finprod <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.kappaOrbitalIntegral_congruence_inert_latticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), a + b = n → Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → (1 + algebraMap K.O B₁.A t * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A t * B₁.g) = 1 → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (1 + algebraMap K.O B₂.A t * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A t * B₂.g) = 1 → kapOrb n w Q₁ Q₂ ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) = ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum | exact GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum | (intros; apply GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum <;> assumption)
end
