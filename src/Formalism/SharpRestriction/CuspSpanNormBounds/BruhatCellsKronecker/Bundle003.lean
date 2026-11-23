module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle002
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ClauseAOfIdentityFlag
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
public import Formalism.FlagUnipotentLattices.Bundle002
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle005

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField

theorem l_theta : IntegralTraceSurjective := by
  intro E _ _ _ h
  obtain ⟨_, _, hun⟩ := h
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = star (x : E) := fun x => rfl
  have hσσ : ∀ x, σ (σ x) = x := fun x => RingOfIntegers.ext (by rw [hσ, hσ, star_star])
  let J : Ideal (𝓞 E) := Ideal.span {t | ∃ x, t = x + σ x}
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨θ, t, ht, hnot⟩ := hun P hP
    have htσ : t = σ θ := RingOfIntegers.ext (by rw [hσ]; exact ht)
    apply hnot
    have h1 : θ + σ θ ∈ P := hle (Ideal.subset_span ⟨θ, rfl⟩)
    have h2 : (1 : 𝓞 E) + σ 1 ∈ P := hle (Ideal.subset_span ⟨1, rfl⟩)
    rw [map_one] at h2
    have h3 : θ - t = (θ + σ θ) - (1 + 1) * σ θ := by rw [htσ]; ring
    rw [h3]
    exact P.sub_mem h1 (P.mul_mem_right _ h2)
  have key : ∀ y ∈ J, ∃ x, y * σ y = x + σ x := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, rfl⟩ := ht
      exact ⟨(x + σ x) * x, by simp only [map_add (f := _), map_mul, hσσ]; ring⟩
    | zero => exact ⟨0, by simp⟩
    | add y y' _ _ ih ih' =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨x', hx'⟩ := ih'
      exact ⟨x + x' + y * σ y', by simp only [map_add (f := _), map_mul, hσσ]; linear_combination hx + hx'⟩
    | smul a y _ ih =>
      obtain ⟨x, hx⟩ := ih
      exact ⟨a * σ a * x, by simp only [smul_eq_mul, map_mul, hσσ]; linear_combination (a * σ a) * hx⟩
  obtain ⟨x, hx⟩ := key 1 (by rw [hJ]; exact Submodule.mem_top)
  refine ⟨x, ?_⟩
  rw [map_one, mul_one] at hx
  have h4 := congrArg (fun z : 𝓞 E => (z : E)) hx
  simp only [map_add (f := _), map_one] at h4
  rw [← hσ]
  exact h4.symm

end Formalism.MainNotions.BridgeLemma

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module IsDedekindDomain

theorem liso_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} (Λ : Submodule (𝓞 E) S.V)
    (o : 𝓞 E) {v : S.V} (hv : v ∈ Λ) : (o : E) • v ∈ Λ := by
  have h : (o : E) • v = o • v := algebraMap_smul E o v
  rw [h]
  exact Λ.smul_mem o hv

theorem l_iso (h1 : IntegralAdjointUnimodular) (h2 : IntegralRetraction) (h3 : IntegralTraceSurjective) : IsotropicIntegralRetraction := by
  intro E _ _ _ S Λ X hcm hlat huni hiso
  obtain ⟨P0, hid, hX, hint⟩ := h2 E S Λ X hlat
  obtain ⟨P0', hadj, hint'⟩ := h1 E S Λ huni P0 hint
  obtain ⟨θ, hθ⟩ := h3 E hcm
  have hbar : star (θ : E) = ((1 - θ : 𝓞 E) : E) := by
    have : ((1 - θ : 𝓞 E) : E) = 1 - (θ : E) := by simp
    rw [this]
    linear_combination hθ

  have hrev : ∀ x y, S.hT (P0' x) y = S.hT x (P0 y) := by
    intro x y
    rw [← S.herm.eq y (P0' x), ← hadj y x, S.herm.eq]
  have hHX : ∀ y, P0 (P0' y) ∈ X := fun y => hX _
  have hHH : ∀ x y, S.hT (P0 (P0' x)) y = S.hT x (P0 (P0' y)) := by
    intro x y
    rw [hadj, hrev]
  have hzero : ∀ x ∈ X, P0' x = 0 := by
    intro x hx
    refine S.nondeg.2 _ (fun w => ?_)
    rw [← hadj]
    exact hiso _ (hX w) _ hx
  refine ⟨P0 - (θ : E) • (P0 ∘ₗ P0'), P0' - star (θ : E) • (P0 ∘ₗ P0'), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smulₛₗ,
      smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    rw [hadj, hHH]
  · intro x hx
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hzero x hx, map_zero, smul_zero, sub_zero, hid x hx]
  · intro y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    exact X.sub_mem (hX y) (X.smul_mem _ (hHX y))
  · intro l hl
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    exact Λ.sub_mem (hint l hl) (liso_smul_mem Λ θ (hint _ (hint' l hl)))
  · intro l hl
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hbar]
    exact Λ.sub_mem (hint' l hl) (liso_smul_mem Λ (1 - θ) (hint _ (hint' l hl)))
  · intro w y
    have e1 : S.hT (P0' w) (P0' y) = S.hT w (P0 (P0' y)) := hrev _ _
    have e2 : S.hT (P0' w) (P0 (P0' y)) = S.hT w (P0 (P0' y)) := by
      rw [hrev, hid _ (hHX y)]
    have e3 : S.hT (P0 (P0' w)) (P0' y) = S.hT w (P0 (P0' y)) := by
      rw [← hadj, hid _ (hHX w), hHH]
    have e4 : S.hT (P0 (P0' w)) (P0 (P0' y)) = 0 := hiso _ (hHX w) _ (hHX y)
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_smulₛₗ,
      smul_eq_mul, starRingEnd_apply, star_star, RingHom.id_apply]
    rw [e1, e2, e3, e4]
    linear_combination (-(S.hT w (P0 (P0' y)))) * hθ

end Formalism.MainNotions.BridgeLemma

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module

section

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

def ladjG : Matrix (Fin S.rank) (Fin S.rank) E := fun i k => S.hT (S.frame i) (S.frame k)

theorem ladj_ext (y : S.V) (h : ∀ i, S.hT (S.frame i) y = 0) : y = 0 := by
  apply S.nondeg.2 y
  intro x
  have : S.hT.flip y = 0 := S.frame.ext (fun i => by simpa using h i)
  have h2 := LinearMap.congr_fun this x
  simpa using h2

theorem ladj_det : (ladjG S).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  have hy : ∑ k, v k • S.frame k = 0 := by
    apply ladj_ext S
    intro i

    rw [map_sum]
    have := congrFun hmul i
    simp only [Matrix.mulVec, dotProduct, ladjG, Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]
  funext k
  exact Fintype.linearIndependent_iff.1 S.frame.linearIndependent v hy k

def ladjOp (B : S.V →ₗ[E] S.V) : S.V →ₗ[E] S.V :=
  ∑ i, (∑ k, ((ladjG S)⁻¹ i k) • S.hT (B (S.frame k))).smulRight (S.frame i)

theorem ladj_frame (B : S.V →ₗ[E] S.V) (l : Fin S.rank) (y : S.V) :
    S.hT (S.frame l) (ladjOp S B y) = S.hT (B (S.frame l)) y := by
  have hu : IsUnit (ladjG S).det := isUnit_iff_ne_zero.2 (ladj_det S)

  simp only [ladjOp, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, map_sum, map_smul,
  smul_eq_mul]
  have h1 : ∀ i : Fin S.rank, (∑ k, (ladjG S)⁻¹ i k * S.hT (B (S.frame k)) y) * S.hT (S.frame l) (S.frame i) =
      ∑ k, (ladjG S l i * (ladjG S)⁻¹ i k) * S.hT (B (S.frame k)) y := by
    intro i
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [ladjG]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
  have h2 : ∀ k : Fin S.rank, ∑ i, (ladjG S l i * (ladjG S)⁻¹ i k) * S.hT (B (S.frame k)) y =
      ((1 : Matrix (Fin S.rank) (Fin S.rank) E) l k) * S.hT (B (S.frame k)) y := by
    intro k
    rw [← Finset.sum_mul, ← Matrix.mul_nonsing_inv _ hu, Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun k _ => h2 k)]
  simp [Matrix.one_apply]

theorem ladj_adj (B : S.V →ₗ[E] S.V) : LAdj S B (ladjOp S B) := by
  intro x y
  have : (S.hT.flip y).comp B = S.hT.flip (ladjOp S B y) :=
    S.frame.ext (fun i => by simpa using (ladj_frame S B i y).symm)
  have h2 := LinearMap.congr_fun this x
  simpa using h2

end

theorem l_adj : IntegralAdjointUnimodular := by
  intro E _ _ _ S Λ hU B hB
  refine ⟨ladjOp S B, ladj_adj S B, fun l hl => ?_⟩
  have hd : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
  rw [← hd, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  intro y hy
  rw [← ladj_adj S B y l]
  have hl' : l ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hd]; exact hl
  exact (Formalism.HermitianLatticesTheory.dualBasic_mem_dual S.hT Λ l).1 hl' _ (hB y hy)

end Formalism.MainNotions.BridgeLemma

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module IsDedekindDomain

section

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem lframe_mem_locP {P : Ideal (𝓞 E)} [P.IsPrime] {M : Submodule (𝓞 E) S.V} {y : S.V} :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ P M ↔ ∃ s : 𝓞 E, s ∉ P ∧ s • y ∈ M := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, h⟩

theorem lframe_local_global (M : Submodule (𝓞 E) S.V) (y : S.V)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M) : y ∈ M := by
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) S.V y)
  have hI : ∀ s, s ∈ I ↔ s • y ∈ M := fun s => by
    simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  by_cases htop : I = ⊤
  · have h1 : (1 : 𝓞 E) ∈ I := by rw [htop]; trivial
    simpa using (hI 1).1 h1
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I htop
    have hne : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
    obtain ⟨s, hs, hsy⟩ := h ⟨m, hm.isPrime, hne⟩
    exact absurd (hle ((hI s).2 hsy)) hs

theorem lframe_dual {r : ℕ} {T : E} (F : FlagG S r T) (a : Fin r) :
    ∃ φ : S.V →ₗ[E] E, ∀ b, φ (F.e b) = if b = a then 1 else 0 := by
  let B := Basis.span F.e_indep
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (B.coord a)
  refine ⟨φ, fun b => ?_⟩
  have h1 : F.e b = ((B b : Submodule.span E (Set.range F.e)) : S.V) := (congrArg Subtype.val (Basis.span_apply F.e_indep b)).symm
  have h2 : φ ((B b : Submodule.span E (Set.range F.e)) : S.V) = B.coord a (B b) := by
    rw [← hφ]
    rfl
  rw [h1, h2, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

end

theorem l_frame : UnitriangularFrameIntegral := by
  intro E _ _ _ S r T Λ g F F' hF hF' he U hU x hxΛ hxX
  have hXa := tie_Xa_eq F.fl F'.fl he
  have hX : F'.fl.X = F.fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa, hXa]
  have hXL : XLam Λ F' = XLam Λ F := by
    unfold XLam
    rw [show Xsp F' = Xsp F from hX]
  apply lframe_local_global
  intro P
  have := P.isPrime
  have h1P : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  obtain ⟨c, _, _, hc⟩ := hF.1 P
  obtain ⟨c', _, _, hc'⟩ := hF'.1 P
  have hA : ∀ a, c a • F'.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') := by
    intro a
    have h1 : c a • F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') := by
      rw [hXL, hc]
      exact lframe_mem_locP.2 ⟨1, h1P, by rw [one_smul]; exact Submodule.subset_span ⟨a, rfl⟩⟩
    rw [hc'] at h1 ⊢
    obtain ⟨t, ht, h2⟩ := lframe_mem_locP.1 h1
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 h2
    obtain ⟨φ, hφ⟩ := lframe_dual F'.fl a
    have hφ0 : ∀ w ∈ F'.fl.Xa a.val, φ w = 0 := by
      have hle : F'.fl.Xa a.val ≤ LinearMap.ker φ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, hi, rfl⟩
        show φ (F'.fl.e i) = 0
        rw [hφ, if_neg]
        intro h
        subst h
        exact lt_irrefl i.val hi
      exact fun w hw => hle hw
    have hea : φ (F.fl.e a) = 1 := by
      have h3 : F.fl.e a = F'.fl.e a - (F'.fl.e a - F.fl.e a) := by abel
      rw [h3, map_sub, hφ, if_pos rfl, hφ0 _ (by rw [hXa]; exact he a), sub_zero]
    have key : algebraMap (𝓞 E) E t * c a = algebraMap (𝓞 E) E (o a) * c' a := by
      have h4 := congrArg φ ho

      simp only [map_sum, LinearMap.map_smul_of_tower, map_smul, hφ, hea, smul_eq_mul, Algebra.smul_def, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h4
      exact h4.symm
    refine lframe_mem_locP.2 ⟨t, ht, ?_⟩
    have h5 : t • (c a • F'.fl.e a) = o a • (c' a • F'.fl.e a) := by
      rw [← algebraMap_smul E t, ← algebraMap_smul E (o a), smul_smul, smul_smul, key]
    rw [h5]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hx1 : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) :=
    lframe_mem_locP.2 ⟨1, h1P, by rw [one_smul]; exact ⟨hxΛ, hxX⟩⟩
  rw [hc] at hx1
  obtain ⟨s, hs, h3⟩ := lframe_mem_locP.1 hx1
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 h3
  have hU1 : s • U x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') := by

    rw [← LinearMap.map_smul_of_tower, ← ho, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smul_of_tower, map_smul, hU]
    exact Submodule.smul_mem _ _ (hA a)
  obtain ⟨t, ht, h4⟩ := lframe_mem_locP.1 hU1
  exact ⟨t * s, fun h => (P.isPrime.mem_or_mem h).elim ht hs, by rw [mul_smul]; exact h4.1⟩

end Formalism.MainNotions.BridgeLemma

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

structure CData : Type 1 where
  I : AutInst
  b : ℝ
  lam : InfinitePlace I.F → Fin I.n → ℝ
  g : ℕ
  g₀ : ℕ
  e : I.Gf → ℂ
  H : InfinitePlace I.F → Type
  [hN : ∀ v, NormedAddCommGroup (H v)]
  [hI : ∀ v, InnerProductSpace ℂ (H v)]
  [hC : ∀ v, CompleteSpace (H v)]
  σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)
  w : ∀ v, H v
  Hs : Type
  [sN : NormedAddCommGroup Hs]
  [sI : InnerProductSpace ℂ Hs]
  [sC : CompleteSpace Hs]
  σs : I.Ginf → (Hs →L[ℂ] Hs)
  tens : (∀ v, H v) → Hs
  μf : Measure I.Gf
  [sf : SigmaFinite μf]
  fund : Set I.GA
  R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)
  Re : I.L2 μf fund →L[ℂ] I.L2 μf fund
  h : ℝ

attribute [instance] CData.hN CData.hI CData.hC CData.sN CData.sI CData.sC CData.sf

namespace CData

variable (X : CData)

abbrev L2 : Type := X.I.L2 X.μf X.fund


end CData

namespace CData

variable (X : CData)

end CData

namespace CData

variable (X : CData)


end CData

def cartanDistance {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : ℝ :=
  sInf {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
    umat g = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)}

namespace CData

variable (X : CData)




end CData

namespace CData

variable (X : CData)

end CData

namespace CData

variable (X : CData)


end CData

section Numbers

open Formalism.HermitianLatticeCounting.S7 (Ydat epsN)

end Numbers

namespace CData

variable (X : CData)

end CData


namespace CData

variable (X : CData)

end CData

end Formalism.MainNotions.BridgeLemma

end
end
