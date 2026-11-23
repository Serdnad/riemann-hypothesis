module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.GroupTheory.PGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem comap_max {B Q : Type} [CommRing B] [IsLocalRing B] [CommGroup Q] [Finite Q]
    (M : Ideal (MonoidAlgebra B Q)) [M.IsMaximal] :
    M.comap (algebraMap B (MonoidAlgebra B Q)) = maximalIdeal B :=
  eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) M)

private theorem single_sub_mem {l : ℕ} (hl : l.Prime) {B Q : Type} [CommRing B] [IsLocalRing B]
    [CommGroup Q] [Finite Q] (hB : ((l : ℕ) : B) ∈ maximalIdeal B) (hQ : IsPGroup l Q)
    (M : Ideal (MonoidAlgebra B Q)) [hM : M.IsMaximal] (z : Q) :
    (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ M := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨k, hk⟩ := hQ z
  have hlM : ((l : ℕ) : MonoidAlgebra B Q) ∈ M := by
    have h1 : ((l : ℕ) : B) ∈ M.comap (algebraMap B (MonoidAlgebra B Q)) := by
      rw [comap_max M]
      exact hB
    rw [Ideal.mem_comap, map_natCast] at h1
    exact h1
  letI : Field (MonoidAlgebra B Q ⧸ M) := Ideal.Quotient.field M
  have hlK : ((l : ℕ) : MonoidAlgebra B Q ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
    exact hlM
  haveI : CharP (MonoidAlgebra B Q ⧸ M) l := by
    rcases hl.eq_one_or_self_of_dvd _ (ringChar.dvd hlK) with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one)
    · rw [← h1]
      exact ringChar.charP _
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : (Ideal.Quotient.mk M (MonoidAlgebra.single z 1 - 1)) ^ l ^ k = 0 := by
    rw [map_sub, map_one, sub_pow_char_pow, one_pow, ← map_pow, MonoidAlgebra.single_pow, one_pow, hk,
      ← MonoidAlgebra.one_def, map_one, sub_self]
  exact (pow_eq_zero_iff (pow_ne_zero k hl.ne_zero)).mp h0

private theorem sub_aug_mem {B Q : Type} [CommRing B] [CommGroup Q]
    (M : Ideal (MonoidAlgebra B Q))
    (h : ∀ z : Q, (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ M) (x : MonoidAlgebra B Q) :
    x - algebraMap B (MonoidAlgebra B Q) (MonoidAlgebra.lift B B Q 1 x) ∈ M := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact M.add_mem hx hy
  | single g b =>
    have e : MonoidAlgebra.single g b - algebraMap B (MonoidAlgebra B Q) (MonoidAlgebra.lift B B Q 1 (MonoidAlgebra.single g b)) =
        algebraMap B (MonoidAlgebra B Q) b * (MonoidAlgebra.single g 1 - 1) := by
      rw [MonoidAlgebra.lift_single]
      simp [mul_sub, MonoidAlgebra.single_mul_single, MonoidAlgebra.one_def]
    rw [e]
    exact M.mul_mem_left _ (h g)

theorem UpperTheory.V.Ws.H5.grpCO :
    ∀ (l : ℕ) [Fact l.Prime] (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [IsCO O B], ((l : ℕ) : B) ∈ maximalIdeal B → ∀ (Q : Type) [CommGroup Q] [Finite Q], IsPGroup l Q → ∃ _ : IsCO O (MonoidAlgebra B Q), ∀ z : Q, (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ maximalIdeal (MonoidAlgebra B Q) := by
  intro l _ O B _ _ _ _ _ hB Q _ _ hQ
  have hl : l.Prime := Fact.out
  let aug : MonoidAlgebra B Q →+* B := (MonoidAlgebra.lift B B Q 1).toRingHom
  let φ : MonoidAlgebra B Q →+* ResidueField B := (residue B).comp aug
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    refine ⟨algebraMap B _ b, ?_⟩
    simp [φ, aug]
  have hM0 := RingHom.ker_isMaximal_of_surjective φ hφ
  have hle : ∀ (M : Ideal (MonoidAlgebra B Q)), M.IsMaximal → RingHom.ker φ ≤ M := by
    intro M hM x hx
    have h1 : aug x ∈ maximalIdeal B := by
      rw [RingHom.mem_ker] at hx
      exact (residue_eq_zero_iff _).mp hx
    have h2 : algebraMap B _ (aug x) ∈ M := by
      have : aug x ∈ M.comap (algebraMap B _) := by
        rw [comap_max M]
        exact h1
      exact this
    have h3 : x - algebraMap B _ (aug x) ∈ M := sub_aug_mem M (single_sub_mem hl hB hQ M) x
    have := M.add_mem h3 h2
    rwa [sub_add_cancel] at this
  haveI : IsLocalRing (MonoidAlgebra B Q) := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨RingHom.ker φ, hM0, fun M hM => ?_⟩
    exact (hM0.eq_of_le hM.ne_top (hle M hM)).symm
  have hres : ∀ x : MonoidAlgebra B Q, ∃ a : O, x - algebraMap O _ a ∈ maximalIdeal (MonoidAlgebra B Q) := by
    intro x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (aug x)
    refine ⟨a, ?_⟩
    have h3 : x - algebraMap B _ (aug x) ∈ maximalIdeal (MonoidAlgebra B Q) :=
      sub_aug_mem _ (single_sub_mem hl hB hQ _) x
    have h4 : algebraMap B (MonoidAlgebra B Q) (aug x - algebraMap O B a) ∈ maximalIdeal (MonoidAlgebra B Q) := by
      have : aug x - algebraMap O B a ∈ (maximalIdeal (MonoidAlgebra B Q)).comap (algebraMap B _) := by
        rw [comap_max]
        exact ha
      exact this
    have := (maximalIdeal _).add_mem h3 h4
    rw [IsScalarTower.algebraMap_apply O B (MonoidAlgebra B Q)]
    rwa [map_sub, sub_add_sub_cancel] at this
  exact ⟨co_finite O B (MonoidAlgebra B Q) hres, fun z => single_sub_mem hl hB hQ _ z⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.H5.prFacts :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} (V : s.Lev), Topology.IsQuotientMap V.pr ∧ (∀ g : G L Ω, ∃ g' : G L Ω, resP L Ω g' = s.c * resP L Ω g * s.c⁻¹ ∧ V.frame.conj (V.pr g) = V.pr g') ∧ ∀ H : Subgroup (G L Ω), H.Normal → IsClosed (H : Set (G L Ω)) → (∀ g g' : G L Ω, resP L Ω g' = s.c * resP L Ω g * s.c⁻¹ → g ∈ H → g' ∈ H) → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := L) A ≤ H) → V.pr.ker ≤ H := by
  intro l _ L Ω _ _ _ _ _ _ s V
  refine ⟨(phiKer V).2.1, ?_, ?_⟩
  · intro g
    have hin : s.c * resP L Ω g * s.c⁻¹ ∈ (resP L Ω).range := by
      rw [← V.hη]
      have h1 : V.η (toGS Ω V.S' (resP L Ω g)) = 1 := (V.hη _).mpr ⟨g, rfl⟩
      simp only [map_mul, map_inv, h1, mul_one, mul_inv_cancel]
    obtain ⟨g', hg'⟩ := hin
    refine ⟨g', hg', ?_⟩
    have e1 : toGS Ω V.S' (s.c * resP L Ω g * s.c⁻¹) =
        toGS Ω V.S' s.c * ((V.pr g : V.η.ker) : GS Ω V.S') * (toGS Ω V.S' s.c)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      all_goals rfl
    apply Subtype.ext
    show toGS Ω V.S' s.c * ((V.pr g : V.η.ker) : GS Ω V.S') * (toGS Ω V.S' s.c)⁻¹ =
      ((V.pr g' : V.η.ker) : GS Ω V.S')
    rw [← e1, ← hg']
    all_goals rfl
  · intro H _ hcl _ hine
    apply (phiKer V).2.2 H hcl
    intro A v hAv hv
    apply hine A
    intro hlt
    apply hv
    apply V.sub
    have hmem := (hAv (l : 𝓞 (Lp L))).mp (by simpa using hlt)
    exact Or.inl (by simpa using hmem)
end
