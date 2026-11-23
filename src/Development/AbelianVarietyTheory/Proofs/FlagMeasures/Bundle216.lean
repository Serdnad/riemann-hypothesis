module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle009
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle201
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle197
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle202
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.DetMap

section General

variable {R K U V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup U] [Module K U] [Module R U] [IsScalarTower R K U]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem length_quot_map (f : U →ₗ[R] V) (hf : Function.Injective f) (A B : Submodule R U) :
    Module.length R ((A.map f) ⧸ (B.map f).comap (A.map f).subtype) =
      Module.length R (A ⧸ B.comap A.subtype) := by
  let e : A ≃ₗ[R] A.map f := Submodule.equivMapOfInjective f hf A
  have he : (B.comap A.subtype).map (e : A →ₗ[R] A.map f) = (B.map f).comap (A.map f).subtype := by
    ext z
    constructor
    · rintro ⟨⟨a, ha⟩, haB, rfl⟩
      exact ⟨a, haB, rfl⟩
    · intro hz
      obtain ⟨b, hb, hbz⟩ := hz
      obtain ⟨a, ha, haz⟩ := z.2
      obtain rfl : a = b := hf (haz.trans hbz.symm)
      exact ⟨⟨a, ha⟩, hb, Subtype.ext haz⟩
  exact (Submodule.Quotient.equiv _ _ e he).length_eq.symm

theorem localization_map₂ (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A : Submodule R U) :
    Formalism.HermitianLatticesTheory.localization₂ p (A.map (i.restrictScalars R)) = (Formalism.HermitianLatticesTheory.localization₂ p A).map (i.restrictScalars R) := by
  ext x
  constructor
  · rintro ⟨s, hs, a, ha, hax⟩
    have hs0 : algebraMap R K s ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := hRK (by rw [h0, map_zero])
      rw [this]
      exact p.zero_mem
    refine ⟨(algebraMap R K s)⁻¹ • a, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s ((algebraMap R K s)⁻¹ • a), smul_smul, mul_inv_cancel₀ hs0, one_smul]
      exact ha
    · rw [LinearMap.restrictScalars_apply] at hax ⊢
      rw [map_smul, hax, ← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hsy⟩, rfl⟩
    exact ⟨s, hs, s • y, hsy, LinearMap.map_smul _ s y⟩

theorem locLen_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.locLen p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.locLen p A B := by
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [localization_map₂ hRK i hi p A, localization_map₂ hRK i hi p B,
    length_quot_map (i.restrictScalars R) (by simpa using hi)]

theorem lidx_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.lidx p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.lidx p A B := by
  have hi' : Function.Injective (i.restrictScalars R) := by simpa using hi
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [← Submodule.map_inf _ hi', locLen_map hRK i hi, locLen_map hRK i hi]

end General

section NumberField

variable {K U V : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem genIdxH_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    genIdxH (A.map (i.restrictScalars (𝓞 K))) (B.map (i.restrictScalars (𝓞 K))) = genIdxH A B := by
  have hRK : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  unfold genIdxH
  refine finprod_congr fun P => ?_
  haveI := P.isPrime
  rw [lidx_map hRK i hi]

theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem dualInH_map (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V)
    (hiso : ∀ x y, hV (i x) (i y) = hU x y) (N : Submodule (𝓞 K) U) :
    dualInH hV (N.map (i.restrictScalars (𝓞 K))) =
      (dualInH hU N).map (i.restrictScalars (𝓞 K)) := by
  have hspan : (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) =
      (Submodule.span K (N : Set U)).map i := by
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]
  ext x
  simp only [dualInH, Submodule.mem_inf, Submodule.restrictScalars_mem, hspan, mem_dual,
    Submodule.mem_map, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    refine ⟨y, ⟨fun n hn => ?_, hy⟩, rfl⟩
    rw [← hiso]
    exact hx (i n) ⟨n, hn, rfl⟩
  · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
    refine ⟨?_, y, hys, rfl⟩
    rintro _ ⟨n, hn, rfl⟩
    rw [hiso]
    exact hy n hn

end NumberField

theorem latDetH_map : ∀ (K U V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V), Function.Injective i → (∀ x y, hV (i x) (i y) = hU x y) → ∀ N : Submodule (𝓞 K) U, latDetH hV (N.map (i.restrictScalars (𝓞 K))) = latDetH hU N := by
  intro K U V _ _ _ _ _ _ _ _ _ _ _ hU hV i hi hiso N
  unfold latDetH
  rw [dualInH_map hU hV i hiso, genIdxH_map i hi]

end GlobalTheory.LoopC.DetMap
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.PtMinor

noncomputable def minor (bs : List (ℂ × ℕ)) (m : ℕ) : ℂ := (Matrix.of fun a b : Fin m => ptEntry bs a b).det

def ends (c : ℕ) (bs : List (ℂ × ℕ)) : List ℕ := ((bs.map Prod.snd).scanl (· + ·) c).tail

theorem ends_nil (c : ℕ) : ends c [] = [] := by simp [ends]

theorem ends_cons (c : ℕ) (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) :
    ends c ((t, s) :: bs) = (c + s) :: ends (c + s) bs := by
  cases bs <;> simp [ends]

theorem det_anti (t : ℂ) (ht : t ≠ 0) (s : ℕ) :
    (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det ≠ 0 := by
  have : (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0) =
      (Matrix.diagonal fun _ : Fin s => t).submatrix (Fin.revPerm : Equiv.Perm (Fin s)) id := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, Fin.revPerm_apply, id, Fin.ext_iff,
      Fin.val_rev]
    have := a.2
    exact if_congr (by omega) rfl rfl
  rw [this, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h | h <;> simp [h, ht]

theorem minor_cons (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (m : ℕ) :
    minor ((t, s) :: bs) (s + m) =
      (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det * minor bs m := by
  unfold minor
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (0 : Matrix (Fin s) (Fin m) ℂ),
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [ptEntry]

theorem minor_lt (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (m : ℕ) (h1 : 1 ≤ m) (h2 : m < s) :
    minor ((t, s) :: bs) m = 0 := by
  unfold minor
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, h1⟩ fun j => ?_
  have := j.2
  simp only [Matrix.of_apply, ptEntry]
  split_ifs <;> first | rfl | omega

theorem ends_bd (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c : ℕ) :
    (∀ x ∈ ends c bs, c < x ∧ x ≤ c + (bs.map Prod.snd).sum) ∧ (ends c bs).Nodup ∧
      (bs ≠ [] → c + (bs.map Prod.snd).sum ∈ ends c bs) := by
  induction bs generalizing c with
  | nil => simp [ends_nil]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    have hs : 1 ≤ s := (h (t, s) (by simp)).2
    obtain ⟨i1, i2, i3⟩ := ih (fun b hb => h b (by simp [hb])) (c + s)
    rw [ends_cons]
    simp only [List.map_cons, List.sum_cons, List.mem_cons, List.nodup_cons]
    refine ⟨?_, ⟨fun hm => ?_, i2⟩, fun _ => ?_⟩
    · rintro x (rfl | hx)
      · omega
      · have := i1 x hx
        omega
    · have := i1 _ hm
      omega
    · by_cases hb : bs = []
      · subst hb; simp
      · right
        rw [← add_assoc]
        exact i3 hb

theorem minor_ne_iff (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c l : ℕ) (hl : 1 ≤ l) :
    minor bs l ≠ 0 ↔ c + l ∈ ends c bs := by
  induction bs generalizing c l with
  | nil =>
    have : minor [] l = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨0, hl⟩ fun j => by simp [ptEntry]
    simp [this, ends_nil]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    have h' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b hb => h b (by simp [hb])
    have hb := (ends_bd bs h' (c + s)).1
    rw [ends_cons, List.mem_cons]
    rcases lt_or_ge l s with hls | hls
    · rw [minor_lt t s bs l hl hls]
      refine ⟨fun h0 => absurd rfl h0, ?_⟩
      rintro (h1 | h1)
      · omega
      · have := hb _ h1
        omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hls
      rw [minor_cons, mul_ne_zero_iff, and_iff_right (det_anti t ht s)]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [minor]
      · rw [ih h' (c + s) m hm, add_assoc]
        refine ⟨Or.inr, ?_⟩
        rintro (h1 | h1)
        · omega
        · exact h1

theorem one_le_max_inv (x : ℝ) (hx : 0 < x) : 1 ≤ max x x⁻¹ := by
  rcases le_total 1 x with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hx).2 h)

theorem list_prod (L : List ℕ) (f : ℕ → ℝ) (hf : ∀ l ∈ L, 1 ≤ f l) (a a' : ℝ) (ha : 0 ≤ a) (ha' : a ≤ a') :
    1 ≤ (L.map fun l => f l ^ a).prod ∧ (L.map fun l => f l ^ a).prod ≤ (L.map fun l => f l ^ a').prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨i1, i2⟩ := ih fun l hl => hf l (by simp [hl])
    have hx : 1 ≤ f x := hf x (by simp)
    have h1 := Real.one_le_rpow hx ha
    have h2 := Real.rpow_le_rpow_of_exponent_le hx ha'
    simp only [List.map_cons, List.prod_cons]
    exact ⟨one_le_mul_of_one_le_of_one_le h1 i1, mul_le_mul h2 i2 (by linarith) (by linarith)⟩

theorem one_le_foldr (L : List ℝ) : 1 ≤ L.foldr max 1 := by
  induction L with
  | nil => simp
  | cons x L ih => exact le_max_of_le_right ih

theorem blockEnds_minors : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → RelPt D z z' γ p → (∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p)) ∧ (ptBlockEnds p).Nodup ∧ (∀ l ∈ ptBlockEnds p, 1 ≤ l ∧ l ≤ D.R.rS + 1) ∧ D.R.rS + 1 ∈ ptBlockEnds p ∧ DminN z z' γ 0 = 1 ∧ 0 < Gf D.R.k D.R.rS z z' γ ∧ Gf D.R.k D.R.rS z z' γ ≤ ‖DminN z z' γ (D.R.rS + 1)‖ ^ 2 ∧ ∀ b C C₂ : ℝ, 1 ≤ b → 0 ≤ C → C ≤ C₂ → 1 ≤ lossV b C D.R.m z z' γ p ∧ lossV b C D.R.m z z' γ p ≤ lossV b C₂ D.R.m z z' γ p ∧ 1 ≤ lossP b C D.R.m z z' γ p ∧ lossP b C D.R.m z z' γ p ≤ lossP b C₂ D.R.m z z' γ p := by
  intro D z z' γ p hz hz' hT hT' hRel
  obtain ⟨hU, ⟨L, U, hL, hU', hZ⟩, hG⟩ := hRel
  have hp := p.2.1
  have hsum := p.2.2
  obtain ⟨e1, e2, e3⟩ := ends_bd p.1 hp 0
  rw [zero_add, hsum] at e1 e3
  have key : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Complex.normSq (DminN z z' γ l) = Complex.normSq (minor p.1 l) := by
    intro l hl
    have h1 := Formalism.MainNotions.S.Bridge.normSq_leadMinor_ZhatO D.R.k D.R.rS z z' γ l hl
    rw [hZ, Formalism.MainNotions.S.Bridge.leadMinor_cell L (ptMat p) U hL hU' l hl] at h1
    rw [DminN, dite_eq_left (Nat.lt_succ_of_le hl)]
    exact h1.symm
  have hiff : ∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p) := by
    intro l hl
    by_cases hl' : l ≤ D.R.rS + 1
    · have h2 := minor_ne_iff p.1 hp 0 l hl
      rw [zero_add] at h2
      rw [Ne, ← Complex.normSq_eq_zero, key l hl', Complex.normSq_eq_zero]
      exact h2
    · rw [DminN, dite_eq_right (by omega)]
      exact ⟨fun h0 => absurd rfl h0, fun hm => absurd (e1 l hm).2 hl'⟩
  have hG0 : 0 < Gf D.R.k D.R.rS z z' γ :=
    lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS z z' hz hz' hT hT' γ hU) (Ne.symm hG)
  refine ⟨hiff, e2, fun l hl => e1 l hl, e3 fun h0 => ?_, ?_, hG0, ?_, fun b C C₂ hb hC hC2 => ?_⟩
  · rw [h0] at hsum
    simp at hsum
  · simp [DminN, Formalism.QuantumDeterminants.Dmin]
  · rw [DminN, dite_eq_left (by omega), ← Complex.normSq_eq_norm_sq]
    have := mul_nonneg (mul_pos hT hT').le
      (Complex.normSq_nonneg (Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' γ ⟨D.R.rS, by omega⟩))
    exact sub_le_self _ this
  · have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have ex : ∀ x : ℝ, 0 ≤ x → 0 ≤ C * x ∧ C * x ≤ C₂ * x := fun x hx =>
      ⟨mul_nonneg hC hx, mul_le_mul_of_nonneg_right hC2 hx⟩
    obtain ⟨p1, p2⟩ := list_prod (ptBlockEnds p) (fun l => max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹)
      (fun l hl => one_le_max_inv _ (norm_pos_iff.2 ((hiff l (e1 l hl).1).2 hl))) _ _ (ex _ hm).1 (ex _ hm).2
    have g := one_le_max_inv _ hG0
    have a1 := Real.one_le_rpow hb (ex _ (pow_nonneg hm 4)).1
    have a2 := Real.rpow_le_rpow_of_exponent_le hb (ex _ (pow_nonneg hm 4)).2
    have g1 := Real.one_le_rpow g (ex _ (pow_nonneg hm 2)).1
    have g2 := Real.rpow_le_rpow_of_exponent_le g (ex _ (pow_nonneg hm 2)).2
    have c1 := Real.one_le_rpow hb (ex _ hm).1
    have c2 := Real.rpow_le_rpow_of_exponent_le hb (ex _ hm).2
    have f := one_le_foldr ((ptBlockEnds p).map fun l => max 1 ‖DminN z z' γ l‖⁻¹)
    have q1 := one_le_mul_of_one_le_of_one_le c1 f
    have q2 := mul_le_mul_of_nonneg_right c2 (zero_le_one.trans f)
    refine ⟨one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le a1 g1) p1, ?_,
      Real.one_le_rpow q1 (ex _ (pow_nonneg hr 3)).1, ?_⟩
    · exact mul_le_mul (mul_le_mul a2 g2 (by linarith) (by linarith)) p2 (by linarith)
        (mul_nonneg (by linarith) (by linarith))
    · exact (Real.rpow_le_rpow (by linarith) q2 (ex _ (pow_nonneg hr 3)).1).trans
        (Real.rpow_le_rpow_of_exponent_le (q1.trans q2) (ex _ (pow_nonneg hr 3)).2)

end GlobalTheory.Amp.PtMinor
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory.TypedPlacesProduct

theorem finite_over {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((n : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hn
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem finprod_over {K : Type*} [Field K] [NumberField K] {n f : ℕ} (hn : n ≠ 0) (φ : ℝ → ℝ)
    (hc : Nat.card {v : HeightOneSpectrum (𝓞 K) // ((n : ℕ) : 𝓞 K) ∈ v.asIdeal} = f)
    (hq : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal →
      Nat.card (𝓞 K ⧸ v.asIdeal) = n) :
    (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal : ℝ)) = φ n ^ f := by
  have hs := finite_over (K := K) hn
  have hnorm : ∀ p ∈ {p : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ p.asIdeal},
      φ (Ideal.absNorm p.asIdeal : ℝ) = φ n := by
    intro p hp
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq p hp]
  rw [finprod_mem_congr rfl hnorm, finprod_mem_eq_finite_toFinset_prod _ hs, Finset.prod_const,
    ← Nat.card_eq_card_finite_toFinset hs]
  exact congrArg _ hc

private lemma disjoint_primes_dvd_of_coprime {K : Type*} [Field K] [NumberField K] {a b : ℕ} (hab : Nat.Coprime a b) :
    Disjoint {p : HeightOneSpectrum (𝓞 K) | ((a : ℕ) : 𝓞 K) ∈ p.asIdeal}
      {p : HeightOneSpectrum (𝓞 K) | ((b : ℕ) : 𝓞 K) ∈ p.asIdeal} := by
  rw [Set.disjoint_left]
  intro p ha hb
  obtain ⟨u, w, huw⟩ := (Nat.isCoprime_iff_coprime.mpr hab).map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ p.asIdeal := by
    rw [← huw]
    simp only [eq_intCast, Int.cast_natCast]
    exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ ha) (p.asIdeal.mul_mem_left _ hb)
  exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem finprod_typed_places : ∀ (D : D7) (φ : ℝ → ℝ), (∀ i, StandardLattice.SplitsF D (D.host.g i)) → (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, φ (Ideal.absNorm p.asIdeal : ℝ)) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  intro D φ hs
  have hp := D.host.g_prime
  have hne : D.host.g 0 ≠ D.host.g 1 := D.host.g_ne
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) := (Nat.coprime_primes (hp 0) (hp 1)).mpr hne
  rw [Set.setOf_or, finprod_mem_union (disjoint_primes_dvd_of_coprime hcop) (finite_over (hp 0).ne_zero)
    (finite_over (hp 1).ne_zero), finprod_over (hp 0).ne_zero φ (hs 0).1 (hs 0).2,
    finprod_over (hp 1).ne_zero φ (hs 1).1 (hs 1).2]

end GlobalTheory.TypedPlacesProduct
end

section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem first_type_prime_large_of_record (D : D7) : StandardLattice.GBig D := by
  refine ⟨0, ?_⟩
  have hc := D.ntypes.g_cond 0
  have hg := (D.host.g_prime 0).two_le
  have h3 : D.host.QS * D.host.q * D.host.d ≤ D.host.g 0 := by
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega)] at hc
    omega
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hf : D.R.f ≤ D.R.k := D.R.f_le_k
  have hm := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have h4 : D.R.f * D.R.k ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr
  have hQ : 1 ≤ D.host.QS := D.host.QS_pos
  have h5 : D.host.q ≤ D.host.QS * D.host.q * D.host.d :=
    calc D.host.q = 1 * D.host.q * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hQ) (by omega)
  rw [mul_assoc] at hq ⊢
  omega

end GlobalTheory
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.card_sublattices_quotient_prod_degree_one_primes : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), Submodule.IsFullLattice K M → ∀ (T : ℕ) (s : Finset (Ideal (𝓞 K))), T.Prime → (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) → {L : Submodule (𝓞 K) V | L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))}.encard = (((∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  first
  | exact @GlobalTheory.SublatCount.main
  | intro K V _ _ _ _ _ _ _ M hM T s hT hs
    exact GlobalTheory.SublatCount.main K V M hM.toIsLattice T s hT hs
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.zlattice_covolume_eq_of_coprime_scalars : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (A B : Submodule ℤ (ι → κ → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A] [DiscreteTopology B] [IsZLattice ℝ B], (∀ p : ℕ, p.Prime → ∃ (d : ι → ℝ) (N : ℕ), ¬ p ∣ N ∧ ∏ v, d v ^ 2 = N ∧ (∀ y ∈ A, (fun v i => d v * y v i) ∈ B) ∧ ∀ y ∈ B, (fun v i => d v * y v i) ∈ A) → ZLattice.covolume A volume = ZLattice.covolume B volume := by
  first | exact @GlobalTheory.CovScal.covolume_eq_of_scalars | exact GlobalTheory.CovScal.covolume_eq_of_scalars | (intros; apply GlobalTheory.CovScal.covolume_eq_of_scalars <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.covolume_pi_lattice_unitary_coordinates : ∀ (ι κ β : Type) [Fintype ι] [Fintype κ] [Fintype β] (r s : β → ℕ) (Φ : ι → ((κ → ℂ) ≃ₗ[ℂ] (∀ b : β, Fin (r b) → Fin (s b) → ℂ))), (∀ v z, ∑ b, ∑ p, ∑ q, ‖Φ v z b p q‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) → ∀ (M : ∀ b : β, Submodule ℤ (ι → Fin (r b) → Fin (s b) → ℂ)), (∀ b, ∃ _ : DiscreteTopology (M b), IsZLattice ℝ (M b)) → ∀ L : Submodule ℤ (ι → κ → ℂ), (∀ z, z ∈ L ↔ ∀ b, (fun v => Φ v (z v) b) ∈ M b) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = ∏ b, ZLattice.covolume (M b) volume := by
  first | exact @GlobalTheory.CovPi.covolume_pi_unitary | exact GlobalTheory.CovPi.covolume_pi_unitary | (intros; apply GlobalTheory.CovPi.covolume_pi_unitary <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.conjStable_lattice_real_imag_covolume_le : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (L : Submodule ℤ (ι → κ → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L], (∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) → ∀ A B : Submodule ℤ (ι → κ → ℝ), (∀ y, y ∈ A ↔ (fun v i => (y v i : ℂ)) ∈ L) → (∀ y, y ∈ B ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L) → (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧ ZLattice.covolume A volume * ZLattice.covolume B volume ≤ 2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume := by
  first | exact @GlobalTheory.ReImLattice.real_imag_covolume_le | exact GlobalTheory.ReImLattice.real_imag_covolume_le | (intros; apply GlobalTheory.ReImLattice.real_imag_covolume_le <;> assumption)
end
