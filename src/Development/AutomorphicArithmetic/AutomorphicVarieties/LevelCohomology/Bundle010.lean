module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle006
public import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UrCard
import Mathlib.FieldTheory.Finiteness
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle006

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

section
variable (O : Type) [CommRing O] (k : Type) [Field k] [Algebra O k]

private theorem spDim_JR : (form O).JR k = J4 k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Alg.FormData.JR, form, J4]

private theorem spDim_mem (j : ℤ × ℤ) (Y : M4 k) : Y ∈ (form O).gw k j ↔
    (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) ∧
      ∀ a b, wt a b ≠ j → Y a b = 0 := by
  have e : Y ∈ (form O).gw k j ↔ (Y.transpose * (form O).JR k + (form O).JR k * Y = 0 ∧
      ∀ a b, (form O).blk a ≠ (form O).blk b → Y a b = 0) ∧ ∀ a b, wt a b ≠ j → Y a b = 0 := Iff.rfl
  rw [e, spDim_JR]
  refine and_congr_left fun _ => ⟨fun ⟨h, _⟩ => ?_, fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨?_, fun a b h => absurd rfl h⟩⟩
  · have h1 := congrFun (congrFun h 0) 1
    have h2 := congrFun (congrFun h 0) 2
    have h3 := congrFun (congrFun h 0) 3
    have h4 := congrFun (congrFun h 1) 2
    have h5 := congrFun (congrFun h 1) 3
    have h6 := congrFun (congrFun h 2) 3
    simp [J4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four] at h1 h2 h3 h4 h5 h6
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination h1
    · linear_combination h2
    · linear_combination h3
    · linear_combination h4
    · linear_combination h5
    · linear_combination -h6
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [J4, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, h1, h2, h3, h4, h5, h6]

private theorem spDim_one (j : ℤ × ℤ) (B : M4 k) (a b : Fin 4) (hB : B ∈ (form O).gw k j) (hab : B a b = 1)
    (h : ∀ Y ∈ (form O).gw k j, Y a b = 0 → Y = 0) : finrank k ((form O).gw k j) = 1 := by
  refine finrank_eq_one (⟨B, hB⟩ : (form O).gw k j) ?_ ?_
  · intro e
    have : B = 0 := congrArg Subtype.val e
    rw [this] at hab
    simp at hab
  · intro Y
    refine ⟨Y.1 a b, Subtype.ext ?_⟩
    have := h (Y.1 a b • B - Y.1) (Submodule.sub_mem _ (Submodule.smul_mem _ _ hB) Y.2) (by simp [hab])
    exact sub_eq_zero.mp this

private theorem spDim_root (j : ℤ × ℤ) (B : M4 k) (a b : Fin 4) (hj : wt a b = j)
    (hB : B ∈ (form O).gw k (wt a b)) (hab : B a b = 1)
    (h : ∀ Y : M4 k, (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) →
      Y a b = 0 → Y b.rev a.rev = 0)
    (h' : ∀ c d, wt c d = wt a b → (c = a ∧ d = b) ∨ (c = b.rev ∧ d = a.rev)) :
    finrank k ((form O).gw k j) = 1 := by
  subst hj
  refine spDim_one O k _ B a b hB hab fun Y hY h0 => ?_
  obtain ⟨y1, y2⟩ := (spDim_mem O k _ Y).1 hY
  ext c d
  by_cases e : wt c d = wt a b
  · rcases h' c d e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h0
    · exact h Y y1 h0
  · exact y2 c d e

private theorem spDim_zero : finrank k ((form O).gw k 0) = 2 := by
  let f : (form O).gw k 0 →ₗ[k] k × k :=
    { toFun := fun Y => (Y.1 0 0, Y.1 1 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro Y hY
      have h0 : Y.1 0 0 = 0 := congrArg Prod.fst hY
      have h1 : Y.1 1 1 = 0 := congrArg Prod.snd hY
      obtain ⟨⟨-, -, y3, y4, -, -⟩, y2⟩ := (spDim_mem O k _ Y.1).1 Y.2
      ext c d
      by_cases e : c = d
      · subst e
        fin_cases c <;> simp [h0, h1, y3, y4]
      · exact y2 c d fun n => e ((wt_eq_zero c d).1 n)
    · rintro ⟨x, y⟩
      refine ⟨⟨Matrix.diagonal ![x, y, -y, -x], (spDim_mem O k _ _).2 ⟨by simp, fun a b h => ?_⟩⟩, ?_⟩
      · exact Matrix.diagonal_apply_ne _ fun n => h ((wt_eq_zero a b).2 n)
      · rfl
  rw [(LinearEquiv.ofBijective f hf).finrank_eq]
  simp

private theorem spDim_B (a b : Fin 4) (B : M4 k)
    (h : B 3 1 = B 2 0 ∧ B 3 2 = -B 1 0 ∧ B 3 3 = -B 0 0 ∧ B 2 2 = -B 1 1 ∧ B 2 3 = -B 0 1 ∧ B 1 3 = B 0 2)
    (h' : ∀ c d, ¬ (c = a ∧ d = b) → ¬ (c = b.rev ∧ d = a.rev) → B c d = 0) : B ∈ (form O).gw k (wt a b) := by
  refine (spDim_mem O k _ _).2 ⟨h, fun c d e => h' c d ?_ ?_⟩
  · rintro ⟨rfl, rfl⟩; exact e rfl
  · rintro ⟨rfl, rfl⟩; exact e (wt_rev _ _)

end

theorem UpperTheory.V.X.spDim :
    ∀ (O : Type) [CommRing O] (k : Type) [Field k] [Algebra O k] (j : ℤ × ℤ), finrank k ((form O).gw k j) = dimP j := by
  intro O _ k _ _ j
  unfold dimP
  split_ifs with h0 hw
  · subst h0; exact spDim_zero O k
  · have key : ∀ (a b : Fin 4) (B : M4 k), wt a b = j → B a b = 1 →
        (B 3 1 = B 2 0 ∧ B 3 2 = -B 1 0 ∧ B 3 3 = -B 0 0 ∧ B 2 2 = -B 1 1 ∧ B 2 3 = -B 0 1 ∧ B 1 3 = B 0 2) →
        (∀ c d, ¬ (c = a ∧ d = b) → ¬ (c = b.rev ∧ d = a.rev) → B c d = 0) →
        (∀ Y : M4 k, (Y 3 1 = Y 2 0 ∧ Y 3 2 = -Y 1 0 ∧ Y 3 3 = -Y 0 0 ∧ Y 2 2 = -Y 1 1 ∧ Y 2 3 = -Y 0 1 ∧ Y 1 3 = Y 0 2) →
          Y a b = 0 → Y b.rev a.rev = 0) →
        (∀ c d, wt c d = wt a b → (c = a ∧ d = b) ∨ (c = b.rev ∧ d = a.rev)) → finrank k ((form O).gw k j) = 1 :=
      fun a b B e h1 h2 h3 h4 h5 => spDim_root O k j B a b e (spDim_B O k a b B h2 h3) h1 h4 h5
    simp only [wts, oddRoots, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl
    · refine key 0 1 !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 2 3 = 0
        simp [*]
    · refine key 1 0 !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 2 = 0
        simp [*]
    · refine key 1 2 !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 1 2 = 0
        simp [*]
    · refine key 2 1 !![0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 2 1 = 0
        simp [*]
    · refine key 0 3 !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 0 3 = 0
        simp [*]
    · refine key 3 0 !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 0 = 0
        simp [*]
    · refine key 0 2 !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 1 3 = 0
        simp [*]
    · refine key 2 0 !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 0] (by decide) rfl (by simp) ?_ ?_ (by decide)
      · intro c d h1 h2
        fin_cases c <;> fin_cases d <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h1 | exact absurd ⟨rfl, rfl⟩ h2
      · rintro Y ⟨y1, y2, y3, y4, y5, y6⟩ h
        change Y 3 1 = 0
        simp [*]
    · exact absurd rfl h0
  · rw [Submodule.finrank_eq_zero, eq_bot_iff]
    intro Y hY
    obtain ⟨-, y2⟩ := (spDim_mem O k _ Y).1 hY
    ext c d
    exact y2 c d fun n => hw (n ▸ wt_mem c d)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.urAbs :
    ∀ {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M), ContAction ρ → ∀ (I : Subgroup D) [I.Normal] (φ : D), (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ → (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) → finrank k (H1ur ρ I) = finrank k (H0 ρ) := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ hρ I _ φ hcl hd
  have hcard := UpperTheory.V.Ws.Bl.urCard k D M ρ hρ I φ hcl hd
  let _ : Finite (H1ur ρ I) :=
    Nat.finite_of_card_ne_zero (hcard ▸ (Nat.card_pos (α := H0 ρ)).ne')
  rcases subsingleton_or_nontrivial M with hM | hM
  · let _ : Subsingleton (H1ur ρ I) := Nat.card_eq_one_iff_unique.1
      (hcard.trans (Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩)) |>.1
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    let _ : Finite k := Finite.of_injective (fun a : k => a • v) (smul_left_injective k hv)
    rw [Module.natCard_eq_pow_finrank (K := k) (V := H1ur ρ I),
      Module.natCard_eq_pow_finrank (K := k) (V := H0 ρ)] at hcard
    let _ := Fintype.ofFinite k
    apply Nat.pow_right_injective _ hcard
    change 1 < Nat.card k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
end
