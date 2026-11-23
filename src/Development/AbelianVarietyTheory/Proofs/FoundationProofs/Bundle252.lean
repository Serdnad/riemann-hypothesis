module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle247
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle249
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle001
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle241
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle156
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle154
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle242
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle244
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle243
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
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_coords_of_mem_LaB (D : D7) (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : VC D N N') (hy : y ∈ LaB D T b) :
    ∃ w : Fin r → ℂ, (∀ j, w j ∈ T.abelian₂) ∧ y = ∑ j, w j • embV D T (b j) := by
  apply GlobalTheory.OrthoProdTheta.exists_coord <;> assumption

theorem adpB_lattices : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → (∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ M ∧ wpD (lamOf D cc δ) t ∈ M) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ n : ℕ, 0 < n → (∀ x x' y y', AdpB D (tor0 D cc δ) M ρ b n x x' → AdpB D (tor0 D cc δ) M ρ b n y y' → AdpB D (tor0 D cc δ) M ρ b n (x - y) (x' - y')) ∧ (∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → ∃ t', AdpB D (tor0 D cc δ) M ρ b n t t') ∧ ∀ (k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D (tor0 D cc δ) Y, ∃ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ (∀ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, ∃ x ∈ LaS D (tor0 D cc δ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ ∀ x x', AdpB D (tor0 D cc δ) M ρ b n x x' → (x ∈ LaS D (tor0 D cc δ) Y ↔ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y) := by
  intro D hG hS cc δ hc M ρ hK hD hM N N' r b hb n hn
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := hS cc δ hc M ρ hK hD.2.1 hD.2.2
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hneg : ∀ t t', StarPt M ρ (lamOf D cc δ) t t' → StarPt M ρ (lamOf D cc δ) (-t) (-t') := by
    intro t t' h
    have := h5 (-1) t t' h
    simpa using this
  have hsub : ∀ t t' u u', StarPt M ρ (lamOf D cc δ) t t' → StarPt M ρ (lamOf D cc δ) u u' →
      StarPt M ρ (lamOf D cc δ) (t - u) (t' - u') := by
    intro t t' u u' h h'
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact h4 _ _ _ _ h (hneg _ _ h')
  have hone : ∀ t t', StarPt M ρ (lamOf D cc δ) t t' →
      (t ∈ lamOf D cc δ ↔ t' ∈ lamConj M ρ (lamOf D cc δ)) := by
    intro t t' h
    simpa using h6 1 t t' h
  have hex : ∀ t, InRationalLattice (lamOf D cc δ) t → ∃ t', StarPt M ρ (lamOf D cc δ) t t' := by
    intro t hq
    refine h1 _ hq ?_
    by_cases h : t ∈ lamOf D cc δ
    · exact Or.inl h
    · exact Or.inr (hM _ hq h)
  have hex' : ∀ t', InRationalLattice (lamConj M ρ (lamOf D cc δ)) t' → ∃ t, StarPt M ρ (lamOf D cc δ) t t' := by
    rintro t' ⟨m, hm, ht'⟩
    obtain ⟨t, -, ht⟩ := h7 m hm (fun t h h' => hM t ⟨m, hm, h⟩ h') t' ht'
    exact ⟨t, ht⟩
  have hst : ∀ a : 𝓞 D.host.K, ∀ w ∈ lamOf D cc δ,
      D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
    intro a w hw
    have := h5 a w 0 (Or.inl ⟨hw, zero_mem _⟩)
    rw [hone _ _ this, mul_zero]; exact zero_mem _
  have hst' : ∀ a : 𝓞 D.host.K, ∀ w ∈ lamConj M ρ (lamOf D cc δ),
      D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamConj M ρ (lamOf D cc δ) := by
    intro a w hw
    have := h5 a 0 w (Or.inl ⟨zero_mem _, hw⟩)
    rw [← hone _ _ this, mul_zero]; exact zero_mem _
  have hT := isTraceCompatibleTorusEmbedding_standardTorus D hG cc δ
  have hT' := good_torConj D hG cc δ M ρ hK hD
  refine ⟨?_, ?_, ?_⟩
  · rintro _ _ _ _ ⟨c, c', hc, rfl, rfl, hcc⟩ ⟨d, d', hd, rfl, rfl, hdd⟩
    refine ⟨c - d, c' - d', fun j => ?_, ?_, ?_, fun j => ?_⟩
    · obtain ⟨m, hm, h⟩ := hc j
      obtain ⟨m', hm', h'⟩ := hd j
      refine ⟨m * m', Nat.mul_pos hm hm', ?_⟩
      have : ((m * m' : ℕ) : ℂ) * (c - d) j = m' • ((m : ℂ) * c j) - m • ((m' : ℂ) * d j) := by
        simp only [nsmul_eq_mul, Pi.sub_apply]; push_cast; ring
      rw [this]
      exact sub_mem (AddSubgroup.nsmul_mem _ h _) (AddSubgroup.nsmul_mem _ h' _)
    · simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    · simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    · show StarPt M ρ (lamOf D cc δ) ((c j - d j) / n) ((c' j - d' j) / n)
      rw [sub_div, sub_div]
      exact hsub _ _ _ _ (hcc j) (hdd j)
  · intro x m hm hmx
    obtain ⟨w, hw, hsum⟩ := exists_coords_of_mem_LaB D _ b _ hmx
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hq : ∀ j, ∃ t', StarPt M ρ (lamOf D cc δ) (w j / m / n) t' := by
      intro j
      refine hex _ ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      have : ((m * n : ℕ) : ℂ) * (w j / m / n) = w j := by push_cast; field_simp
      rw [this]; exact hw j
    choose t' ht' using hq
    refine ⟨_, fun j => w j / m, fun j => (n : ℂ) * t' j, ?_, ?_, rfl, ?_⟩
    · intro j
      refine ⟨m, hm, ?_⟩
      have : (m : ℂ) * (w j / m) = w j := by field_simp
      rw [this]; exact hw j
    · have hx : x = (m : ℂ)⁻¹ • (m • x) := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
      rw [hx, hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← div_eq_inv_mul]
    · intro j
      have : (n : ℂ) * t' j / n = t' j := by field_simp
      show StarPt M ρ (lamOf D cc δ) (w j / m / n) ((n : ℂ) * t' j / n)
      rw [this]; exact ht' j
  · intro k Y hk hkn hY
    obtain ⟨A1, A2⟩ := GlobalTheory.T.okLinear_torsionCorrespondence_maps_lattice D (tor0 D cc δ) (torConj D (tor0 D cc δ) M ρ) hT hT' hst N N' r b hb.1
      (StarPt M ρ (lamOf D cc δ)) hex (fun t t₁ t₂ h h' => (h2 t t₁ t₂ h).1 h') h4 h5
      (fun m t t' h => (h6 m t t' h).1) n k Y hn hk hkn hY
    obtain ⟨B1, B2⟩ := GlobalTheory.T.okLinear_torsionCorrespondence_maps_lattice D (torConj D (tor0 D cc δ) M ρ) (tor0 D cc δ) hT' hT hst' N N' r b hb.1
      (fun t' t => StarPt M ρ (lamOf D cc δ) t t') hex'
      (fun t t₁ t₂ h h' => (hone _ _ (hsub _ _ _ _ h h')).2 (by rw [sub_self]; exact zero_mem _))
      (fun t t' u u' h h' => h4 _ _ _ _ h h') (fun a t t' h => h5 a _ _ h)
      (fun m t t' h => (h6 m _ _ h).2) n k Y hn hk hkn hY
    refine ⟨fun x hx => ?_, fun x' hx' => ?_, ?_⟩
    · obtain ⟨c, c', hc, hxc, hcc, hmem⟩ := A1 x hx
      exact ⟨_, hmem, c, c', hc, hxc, rfl, hcc⟩
    · obtain ⟨c', c, hc', hxc, hcc, hmem⟩ := B1 x' hx'
      refine ⟨_, hmem, c, c', fun j => ?_, rfl, hxc, hcc⟩
      obtain ⟨m, hm, h⟩ := hc' j
      refine ⟨m, hm, ?_⟩
      have h' := (h6 (m * n) _ _ (hcc j)).2 (by
        have : ((m * n : ℕ) : ℂ) * (c' j / n) = m * c' j := by push_cast; field_simp
        rw [this]; exact h)
      have : ((m * n : ℕ) : ℂ) * (c j / n) = m * c j := by push_cast; field_simp
      rw [this] at h'; exact h'
    · rintro _ _ ⟨c, c', -, rfl, rfl, hcc⟩
      exact ⟨A2 c c' hcc, B2 c' c hcc⟩

end GlobalTheory.ThetaConj
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem lv_galois_conj : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ),
    (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d →
        QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  intro g E N _ d w f hE hZ hf
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set F : ℍ → ℂ := fun τ => DD τ ^ w * f τ with hFdef
  have hsl : ∀ (h : ℍ → ℂ) (γ : SL(2, ℤ)),
      ((fun τ => DD τ ^ w * h τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * h (γ • τ) :=
    fun h γ => GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul w h γ
  have hev : Even (12 * w) := ⟨6 * w, by ring⟩
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∣[((12 * w : ℕ) : ℤ)] γ = F := by
    intro γ hγ
    rw [hFdef, hsl]
    funext τ
    rw [hf.1 γ hγ τ]
  have hq : ∀ γ : SL(2, ℤ), ∃ a, HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) a := by
    intro γ
    obtain ⟨a, ha, -⟩ := hf.2 γ
    exact ⟨a, by rw [hFdef, hsl]; exact ha⟩
  obtain ⟨F', hF'inv, hF'c⟩ := GlobalTheory.T.shimuraReciprocity_conjugate_form_level g N d (12 * w) F hZ hev hinv hq
  refine ⟨fun τ => F' τ / DD τ ^ w, ?_, ?_⟩
  · have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * (F' (γ • τ) / DD (γ • τ) ^ w)) =
        F' ∣[((12 * w : ℕ) : ℤ)] γ := by
      intro γ
      have := hsl (fun τ => F' τ / DD τ ^ w) γ
      rw [hF'eq] at this
      exact this.symm
    refine ⟨fun γ hγ τ => ?_, fun γ' => ?_⟩
    · have h1 := congrFun (key γ) τ
      rw [hF'inv γ hγ] at h1
      have h2 := congrFun hF'eq τ
      have hne := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      exact mul_left_cancel₀ hne (h1.trans h2.symm)
    · obtain ⟨γ, hγ⟩ := (GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod N d).2 γ'
      obtain ⟨a, ha, ha'⟩ := hF'c γ γ' hγ
      obtain ⟨b, hb, hbE⟩ := hf.2 γ
      have hb' : HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) b := by rw [hFdef, hsl]; exact hb
      have hab : a = b := GlobalTheory.QFam.hasQ_unique_both.1 N _ a b hN ha hb'
      refine ⟨fun n => g (a n), ?_, fun n => ?_⟩
      · rw [key γ']; exact ha'
      · rw [hab]; exact hE _ (hbE n)
  · intro γ γ' hγ
    have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w)) = F' ∣[((12 * w : ℕ) : ℤ)] γ' := by
      have := hsl (fun τ => F' τ / DD τ ^ w) γ'
      rw [hF'eq] at this
      exact this.symm
    have kf : (fun τ => DD τ ^ w * f (γ • τ)) = F ∣[((12 * w : ℕ) : ℤ)] γ := by rw [hFdef, hsl]
    show QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w))
    rw [key, kf]
    exact hF'c γ γ' hγ

end GlobalTheory.FN
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lam_add' (B : ℕ) (c a b : ℕ → ℂ) : lam B c (a + b) = lam B c a + lam B c b := by
  simp only [lam, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem lam_smul' (B : ℕ) (c a : ℕ → ℂ) (z : ℂ) : lam B c (z • a) = z * lam B c a := by
  simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem slz_add' (k : ℕ) (δ : M2) (f g : ℍ → ℂ) : slz k δ (f + g) = slz k δ f + slz k δ g := by
  funext τ; simp only [slz, Pi.add_apply]; ring

theorem slz_smul' (k : ℕ) (δ : M2) (z : ℂ) (f : ℍ → ℂ) : slz k δ (z • f) = z • slz k δ f := by
  funext τ; simp only [slz, Pi.smul_apply, smul_eq_mul]; ring

theorem eigAll_of_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ)
    (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N →
    EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c → ∃ (B' : ℕ) (c' : ℕ → ℂ), EigAll k N l χ g (χ l * α) B' c' ∧
    ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' →
      qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a' := by
  intro k N l χ g α B c a₀ b₀ c₀ d₀ hdet hk hN hl hlN hE
  set δ : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hδ
  have hL : 0 < N * l := Nat.mul_pos hN hl.pos
  obtain ⟨hz1, hadd1, hsm1, -, -, -⟩ := mf_linear k (N * l) (ch χ)
  obtain ⟨hz2, hadd2, hsm2, -, -, -⟩ := mf_linear k (N * l) (ch χ⁻¹)

  have uniq : ∀ x y, MF k (N * l) (ch χ⁻¹) x → MF k (N * l) (ch χ⁻¹) y → qs x = qs y → x = y :=
    fun x y hx hy h => qs_injective x y hx.1 hy.1 h
  let S : Set (ℕ → ℂ) := {a | MF k (N * l) (ch χ) a}
  classical
  let φ : (ℕ → ℂ) → ℂ := fun a =>
    if h : ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) then lam B c h.choose else 0
  have hφ : ∀ a a', MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k δ (qs a) → φ a = lam B c a' := by
    intro a a' h1 h2
    have h : ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) := ⟨a', h1, h2⟩
    simp only [φ, dif_pos h]
    rw [uniq _ _ h.choose_spec.1 h1 (h.choose_spec.2.trans h2.symm)]
  have hex : ∀ a, MF k (N * l) (ch χ) a → ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) :=
    fun a ha => GlobalTheory.T.atkinLehner_slash_isModularFormCoeffSeq k N l χ a a₀ b₀ c₀ d₀ hdet hk hN ha
  obtain ⟨B₀, hB₀⟩ := sturm_coef_zero k (N * l) N χ hL (dvd_mul_right N l)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.func_eq_lam S B₀ φ hz1
    (by
      intro a ha b hb
      obtain ⟨a', ha', ea⟩ := hex a ha
      obtain ⟨b', hb', eb⟩ := hex b hb
      obtain ⟨hab, hqab⟩ := hadd1 a b ha hb
      obtain ⟨hab', hqab'⟩ := hadd2 a' b' ha' hb'
      refine ⟨hab, ?_⟩
      rw [hφ a a' ha' ea, hφ b b' hb' eb, hφ (a + b) (a' + b') hab' (by rw [hqab', hqab, slz_add', ea, eb]),
        lam_add'])
    (by
      intro z a ha
      obtain ⟨a', ha', ea⟩ := hex a ha
      obtain ⟨hza, hqza⟩ := hsm1 z a ha
      obtain ⟨hza', hqza'⟩ := hsm2 z a' ha'
      refine ⟨hza, ?_⟩
      rw [hφ a a' ha' ea, hφ (z • a) (z • a') hza' (by rw [hqza', hqza, slz_smul', ea]), lam_smul'])
    (fun a ha h => hB₀ a ha h)
  obtain ⟨B', c', hagree, hkill⟩ := GlobalTheory.T.exists_lam_eq_and_vanishes_off_character k (N * l) N χ B₀ c₁ hL (dvd_mul_right N l)
  have key : ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k δ (qs a) →
      lam B' c' a = lam B c a' := by
    intro a a' ha ha' e
    rw [hagree a ha, ← hc₁ a ha, hφ a a' ha' e]
  refine ⟨B', c', ⟨⟨?_, ?_⟩, hkill⟩, key⟩
  · intro a ha q hq hqNl
    obtain ⟨a', ha', ea⟩ := hex a ha
    have hqN : ¬ q ∣ N := fun h => hqNl (dvd_mul_of_dvd_left h l)
    obtain ⟨hT, -⟩ := GlobalTheory.T.atkinLehner_intertwines_hecke_operators k N l χ a a' a₀ b₀ c₀ d₀ hdet hk hN hl hlN ha ha' ea
    have hTa : MF k (N * l) (ch χ) (To k (ch χ q) q a) :=
      GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ a hk (dvd_mul_right N l) hq hqNl ha
    have hTa' : MF k (N * l) (ch χ⁻¹) (To k (ch χ⁻¹ q) q a') :=
      GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ⁻¹ a' hk (dvd_mul_right N l) hq hqNl ha'
    obtain ⟨hs, hqs⟩ := hsm2 (ch χ q) _ hTa'
    rw [key _ _ hTa hs (by rw [hqs, hT q hq hqNl]), lam_smul', hE.T a' ha' q hq hqNl, key a a' ha ha' ea]
    have hunit : IsUnit ((q : ℕ) : ZMod N) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
    have h1 : χ (q : ZMod N) * χ⁻¹ (q : ZMod N) = 1 := by
      rw [show χ (q : ZMod N) * χ⁻¹ (q : ZMod N) = (χ * χ⁻¹) (q : ZMod N) by rw [MulChar.coeToFun_mul]; rfl,
        mul_inv_cancel, MulChar.one_apply hunit]
    simp only [ch, Int.cast_natCast]
    linear_combination (g q * lam B c a') * h1
  · intro a ha
    obtain ⟨a', ha', ea⟩ := hex a ha
    obtain ⟨-, hU⟩ := GlobalTheory.T.atkinLehner_intertwines_hecke_operators k N l χ a a' a₀ b₀ c₀ d₀ hdet hk hN hl hlN ha ha' ea
    have hper : ∀ (ε : DirichletCharacter ℂ N) (d : ℤ), ch ε (d + (N * l : ℕ)) = ch ε d := by
      intro ε d
      simp [ch]
    have hUa := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ) a hk hl (dvd_mul_left l N) (hper χ) ha).1
    have hUa' := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ⁻¹) a' hk hl (dvd_mul_left l N) (hper χ⁻¹) ha').1
    obtain ⟨hs, hqs⟩ := hsm2 (ch χ l) _ hUa'
    rw [key _ _ hUa hs (by rw [hqs, hU]), lam_smul', hE.U a' ha', key a a' ha ha' ea]
    simp only [ch, Int.cast_natCast]
    ring

end GlobalTheory.EisM
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.heckeTq_semisimple_cuspForms_gamma1 : ∀ (N k q : ℕ) (σ : SL(2, ℤ)), 5 ≤ N → 3 ≤ k → q.Prime → ¬ q ∣ N → IsDiam N 1 (q : ZMod N) σ → ∀ (f : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ), (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne.tq_semisimple | exact GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne.tq_semisimple | (intros; apply GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne.tq_semisimple <;> assumption)
end

section

open Polynomial

namespace GlobalTheory

theorem classGroup_ringOfIntegers_divisible : GlobalTheory.NeedB.ClDiv := by
  intro k K _ _ _ _ _ _ _ _ N hN c
  rcases Nat.lt_or_ge N 2 with h | h
  · have : N = 1 := by omega
    subst this
    exact ⟨c, (pow_one c).symm⟩
  set A := FunctionField.ringOfIntegers k K
  have : Algebra.IsSeparable (RatFunc k) K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  have : Module.Free k[X] A := IsIntegralClosure.module_free k[X] (RatFunc k) K _
  have : Module.Finite k[X] A := IsIntegralClosure.finite k[X] (RatFunc k) K _
  have : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) K _
  letI : Algebra k A := ((algebraMap k[X] A).comp (algebraMap k k[X])).toAlgebra
  have : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨f, hf0, hf⟩ := GlobalTheory.exists_integral_norm_natDegree_mod_eq_one k K N hN
  have hdim : Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
    rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hf0]
    exact hf
  exact GlobalTheory.T.classGroup_nthPower_of_congruent_points_mod k A N hN (GlobalTheory.T.function_field_class_group_powers k A N h) ⟨f, hf0, hdim⟩ c

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.integrableOn_strip_unfolded_rankin_integrand : ∀ (k e L N : ℕ) (ε : DirichletCharacter ℂ N) (h b : ℕ → ℂ) (s : ℝ), k = 2 * e + 1 → 1 ≤ e → 0 < s → 0 < L → N ∣ L → CF k L (ch ε) h → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) strip := by
  first | exact @GlobalTheory.EisM.strip_integrable_rankin | exact GlobalTheory.EisM.strip_integrable_rankin | (intros; apply GlobalTheory.EisM.strip_integrable_rankin <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.integrable_petersson_integrand_moderateGrowth : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (ρ : ℍ → ℝ) (F : ℍ → ℂ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → CF k L' (ch ε) a → AEStronglyMeasurable F → Mod F → Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs a τ) * F τ * (τ.im : ℂ) ^ k)) := by
  first | exact @GlobalTheory.EisM.integrable_pet_integrand | exact GlobalTheory.EisM.integrable_pet_integrand | (intros; apply GlobalTheory.EisM.integrable_pet_integrand <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_theta_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  intro k _ _ _ _ n ψ hs ho
  have hoc := GlobalTheory.T.principalSeriesCongruenceSubgroup_isOpen_isCompact k n ψ hs
  have hnear := GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k n ψ hs
  have hone : (1 : GL (Fin n) k) ∈ grp ψ := by
    refine ⟨(KO k (Fin n)).one_mem, fun i j hij => ?_⟩
    have h0 : (1 : GL (Fin n) k).val i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
  refine ⟨⟨hone, GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ ho, GlobalTheory.T.principalSeriesCongruenceSubgroup_inv_mem k n ψ ho, hoc.2, hnear.1,
    GlobalTheory.T.principalSeriesTypeCharacter_mul k n ψ ho, ?_⟩, hoc.1⟩
  obtain ⟨U, hU, hUt⟩ := hnear.2
  exact ⟨U, hU, fun g hg _ => hUt g hg⟩

end GlobalTheory.PsType
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eisenstein_periodic_weights_isModularForm : ∀ (j L₁ L₂ : ℕ) (a b χ₁ χ₂ : ℤ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → a 0 = 0 → (∀ x, a (x + L₁) = a x) → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ x, a (x * d) = χ₁ d * a x) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c a b) := by
  first | exact @GlobalTheory.eis_periodic_weights | exact GlobalTheory.eis_periodic_weights | (intros; apply GlobalTheory.eis_periodic_weights <;> assumption)
end

section

open GlobalTheory.DualWeyl MvPolynomial NumberField

theorem _root_.GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one : ∀ (N : ℕ) (la : Fin N → ℕ), Antitone la → (∀ f ∈ nabla la ℂ, form la f (extremal la ℂ) = evalAt 1 f) ∧ normSq la (extremal la ℂ) = 1 := by
  first | exact @GlobalTheory.DualWeyl.Repro.extremal_reproducing | exact GlobalTheory.DualWeyl.Repro.extremal_reproducing | (intros; apply GlobalTheory.DualWeyl.Repro.extremal_reproducing <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.pairing_normalising_constant_log_le_bound : ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∃ s : ℕ, 0 < s ∧ extNorm K lam = (s : K) ∧ Real.log s ≤ bound (Fintype.card ι) n R := by
  first | exact @GlobalTheory.extNorm_eq_nat_log_le_bound | exact GlobalTheory.extNorm_eq_nat_log_le_bound | (intros; apply GlobalTheory.extNorm_eq_nat_log_le_bound <;> assumption)
end
