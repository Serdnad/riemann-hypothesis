module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.SelfTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.MonomialRed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.Bundle001
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem quadratic_twist_charpoly_eq {K G : Type} [Field K] [Group G] (h2 : (2 : K) ≠ 0)
    (r : G →* Matrix (Fin 4) (Fin 4) K) (S : Subgroup G) (φ : G →* Kˣ)
    (e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (h1 : φ ≠ 1) (hS : S ≤ φ.ker) (hsq : ∀ g, φ g * φ g = 1)
    (he : ∀ g v, r g *ᵥ e v = (φ g : K) • e (r g *ᵥ v)) :
    ∃ η : G →* ℤˣ, η ≠ 1 ∧ S ≤ η.ker ∧
      ∀ g, (r g).charpoly = ((((η g : ℤˣ) : ℤ) : K) • r g).charpoly := by
  classical
  let ι : ℤˣ →* Kˣ := Units.map (Int.castRingHom K).toMonoidHom
  have hι : ∀ u : ℤˣ, ((ι u : Kˣ) : K) = ((u : ℤ) : K) := fun u => rfl
  have hneg : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro u hu
    rcases Int.units_eq_one_or u with h | h
    · exact h
    · exfalso
      have := congrArg Units.val hu
      rw [hι, h] at this
      apply hneg
      simpa using this
  have hex : ∀ g, ∃ u : ℤˣ, ι u = φ g := by
    intro g
    have h : (φ g : K) * (φ g : K) = 1 := by
      rw [← Units.val_mul, hsq, Units.val_one]
    rcases mul_self_eq_one_iff.mp h with h | h
    · exact ⟨1, Units.ext (by rw [hι, h]; simp)⟩
    · exact ⟨-1, Units.ext (by rw [hι, h]; simp)⟩
  choose η hη using hex
  let η' : G →* ℤˣ := MonoidHom.mk' η (fun a b => hinj (by rw [map_mul, hη, hη, hη, map_mul]))
  have hη' : ∀ g, η' g = η g := fun g => rfl
  refine ⟨η', ?_, ?_, ?_⟩
  · intro h
    apply h1
    ext1 g
    rw [← hη, ← hη', h]
    simp
  · intro g hg
    rw [MonoidHom.mem_ker]
    apply hinj
    rw [hη', hη, map_one]
    exact hS hg
  · intro g
    rw [hη', ← hι, hη]
    have hc : e.conj (Matrix.toLin' ((φ g : K) • r g)) = Matrix.toLin' (r g) := by
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := e.surjective v
      rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply, Matrix.toLin'_apply,
        Matrix.toLin'_apply, he, Matrix.smul_mulVec, map_smul]
    rw [← Matrix.charpoly_toLin', ← hc, LinearEquiv.charpoly_conj, Matrix.charpoly_toLin']

theorem UpperTheory.V.Ws.exists_sign_twist_charpoly_of_not_irreducible_restriction :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G], (2 : K) ≠ 0 → ∀ r : G →* Matrix (Fin 4) (Fin 4) K, U3.MatIrr ⊤ r →
      ∀ S : Subgroup G, commutator G ≤ S → S.index ∣ 4 → ¬ U3.MatIrr S r →
      ∃ η : G →* ℤˣ, η ≠ 1 ∧ S ≤ η.ker ∧ ∀ g, (r g).charpoly = ((((η g : ℤˣ) : ℤ) : K) • r g).charpoly := by
  intro K G _ _ _ h2 r hirr S hcomm hidx hred
  have hab : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S := fun a b =>
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  haveI hN : S.Normal := ⟨fun n hn g => by
    have := S.mul_mem (hab g n) hn
    simpa using this⟩
  have h4 : ((4 : ℕ) : K) ≠ 0 := by
    have : ((4 : ℕ) : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  obtain ⟨m, hm⟩ := hidx
  have hiK : (S.index : K) ≠ 0 := by
    intro h
    apply h4
    rw [hm, Nat.cast_mul, h, zero_mul]
  have hfi : S.FiniteIndex := ⟨fun h => hiK (by rw [h, Nat.cast_zero])⟩
  let ρ : Representation K G (Fin 4 → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin 4)).toMonoidHom.comp r
  have hρ : ∀ g v, ρ g v = r g *ᵥ v := fun g v => Matrix.toLinAlgEquiv'_apply _ _
  unfold U3.MatIrr at hirr hred
  push Not at hred
  obtain ⟨φ, e, h1, hS, he⟩ := UpperTheory.V.Pr.T.selfTwist ρ S hfi hiK hab
    (fun W hW => hirr W (fun g _ v hv => hρ g v ▸ hW g v hv))
    (by
      obtain ⟨W, hW, hb, ht⟩ := hred
      exact ⟨W, fun g hg v hv => (hρ g v).symm ▸ hW g hg v hv, hb, ht⟩)
  simp only [hρ] at he
  by_cases hsq : ∀ g, φ g * φ g = 1
  · exact quadratic_twist_charpoly_eq h2 r S φ e h1 hS hsq he
  · refine quadratic_twist_charpoly_eq h2 r S (φ * φ) (e.trans e) ?_ ?_ ?_ ?_
    · intro h
      apply hsq
      intro g
      exact DFunLike.congr_fun h g
    · intro g hg
      have : φ g = 1 := hS hg
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, this, one_mul]
    · intro g
      have h : φ (g ^ S.index) = 1 := hS (S.pow_index_mem g)
      have h' : φ g ^ 4 = 1 := by rw [hm, pow_mul, ← map_pow, h, one_pow]
      rw [MonoidHom.mul_apply, ← h']
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    · intro g v
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he, he, map_smul, smul_smul,
        MonoidHom.mul_apply, Units.val_mul]
end

section

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.exists_noncommuting_images_in_finiteIndex_normal_subgroup :
    ∀ (K k B G : Type) [Field K] [IsAlgClosed K] [Field k] [CommRing B] [Group G] (r : G →* Matrix (Fin 4) (Fin 4) K)
      (j : B →+* K) (φ : B →+* k) (χ : Fin 4 → G →* kˣ), Function.Injective j →
      (∀ g, ∃ p : B[X], p.map j = (r g).charpoly ∧ p.map φ = ∏ i, (X - C (χ i g : k))) →
      Submodule.span K (Set.range r) = ⊤ → (∃ s t, ∀ n : ℕ, 0 < n → n ≤ 4 → (χ s / χ t) ^ n ≠ 1) →
      ∀ (Z : Subgroup G) [Z.Normal] (u : G), u ∈ Z → (∀ d : ℕ, 0 < d → (r u ^ d).charpoly.Separable) →
      ∀ N : Subgroup Z, N.Normal → N.FiniteIndex → ∃ g ∈ N, ∃ h ∈ N, r g * r h ≠ r h * r g := by
  intro K k B G _ _ _ _ _ r j φ χ hj hpoly hspan hst Z _ u huZ hsep N hN hfi
  haveI := hN
  by_contra hcon
  push_neg at hcon
  have hd0 : 0 < N.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  let N' : Subgroup G := N.map Z.subtype
  have hcore : u ^ N.index ∈ N'.normalCore := by
    show ∀ c : G, c * u ^ N.index * c⁻¹ ∈ N'
    intro c
    have hz : c * u * c⁻¹ ∈ Z := ‹Z.Normal›.conj_mem u huZ c
    have hp := N.pow_index_mem ⟨c * u * c⁻¹, hz⟩
    refine ⟨_, hp, ?_⟩
    simp [conj_pow]
  have hcomm : ∀ g ∈ N'.normalCore, ∀ h ∈ N'.normalCore, r g * r h = r h * r g := by
    intro g hg h hh
    obtain ⟨g', hg', rfl⟩ := N'.normalCore_le hg
    obtain ⟨h', hh', rfl⟩ := N'.normalCore_le hh
    exact hcon g' hg' h' hh'
  obtain ⟨b, π, _, hmono, htrans⟩ := AlgebraTools.monomialOfComm K G 4 r hspan N'.normalCore hcomm
    ⟨u ^ N.index, hcore, by rw [map_pow]; exact hsep _ hd0⟩
  have hred := AlgebraTools.monomialRed K k B G 4 r j φ χ hj hpoly b π hmono htrans
  obtain ⟨s, t, hst'⟩ := hst
  have hle : π.ker ≤ (χ s / χ t).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    simp [hred g hg s t]
  obtain ⟨h1, h2⟩ := AlgebraTools.permChar G k π (χ s / χ t) hle
  exact hst' _ h1 h2 (pow_orderOf_eq_one _)
end
