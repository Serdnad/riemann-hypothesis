module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelevantBruhatCellsLevelDatum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WhittakerTranslatesCornerLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueTowerPowersLinearIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle123
public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle125
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009

@[expose] public section

section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_tower_powers_linearIndependent : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ E : Subfield Ω, Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) →
  (∀ y ∈ E, IsInt (p := p) y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω))) →
  ∀ (T : Tower p Ω) (N : ℕ) (d : ℕ → Ω), (∀ j < p ^ N, d j ∈ E ∧ IsInt (p := p) (d j)) →
  (∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j) ^ m / (p : Ω))) →
  ∀ j < p ^ N, ∃ m : ℕ, 0 < m ∧ IsInt (p := p) (d j ^ m / (p : Ω)) := by
  intro p hp Ω _ _ h E hE hq T N d hd hs
  classical
  have := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have mem_rad_iff (x : integralClosure (O0 p) Ω) :
      x ∈ (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical ↔
        ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((x : Ω) ^ m / (p : Ω)) := by
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hn
      refine ⟨n + 1, n.succ_pos, ?_⟩
      have h1 : (z : Ω) * p = (x : Ω) ^ n := by exact_mod_cast congrArg Subtype.val hz
      have h2 : (x : Ω) ^ (n + 1) / p = ((z * x : integralClosure (O0 p) Ω) : Ω) := by
        rw [pow_succ, ← h1]; push_cast; field_simp
      rw [h2]
      exact (z * x).2
    · rintro ⟨m, -, hm⟩
      refine ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hm⟩, Subtype.ext ?_⟩⟩
      push_cast
      field_simp
  have isInt_inv (x : Ω) (hx0 : x ≠ 0)
      (hx : ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) (x ^ m / (p : Ω))) :
      IsInt (p := p) x⁻¹ := by
    obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) :=
      hmax ▸ o0_isAdicComplete_span_p p
    have : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj
    let : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
    have : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
      FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
    have : Algebra.IsAlgebraic (O0 p) Ω := h.alg
    have : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
      Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
    obtain ⟨a, b, hb, h1, h2⟩ :=
      exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p) hirr x hx0
    rw [map_natCast] at h1 h2
    have hpi : IsIntegral (O0 p) (p : Ω) := by
      exact_mod_cast Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    by_cases ha : 0 < a
    · exfalso
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = (n + 1 : ℕ) := ⟨(a - 1).toNat, by push_cast; omega⟩
      refine hx ⟨b, hb, ?_⟩
      have : x ^ b / (p : Ω) = x ^ b / (p : Ω) ^ ((n + 1 : ℕ) : ℤ) * (p : Ω) ^ n := by
        rw [zpow_natCast]; field_simp; ring
      rw [this]
      exact h1.mul (hpi.pow n)
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -(n : ℤ) := ⟨(-a).toNat, by omega⟩
      refine IsIntegral.of_pow hb ?_
      have : x⁻¹ ^ b = (p : Ω) ^ (-(n : ℤ)) / x ^ b * (p : Ω) ^ n := by
        rw [zpow_neg, zpow_natCast, inv_pow]; field_simp
      rw [this]
      exact h2.mul (hpi.pow n)
  set M := (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical with hM
  have hmem : ∀ x : integralClosure (O0 p) Ω, Ideal.Quotient.mk M x = 0 ↔
      ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((x : Ω) ^ m / (p : Ω)) := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hM, mem_rad_iff]
  have : M.IsMaximal := ResidueIndep.rad_isMaximal h
  let : Field (integralClosure (O0 p) Ω ⧸ M) := Ideal.Quotient.field M
  have : CharP (integralClosure (O0 p) Ω ⧸ M) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk M),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
  let K : Subfield (integralClosure (O0 p) Ω ⧸ M) :=
    { (E.toSubring.comap (integralClosure (O0 p) Ω).val.toRingHom).map (Ideal.Quotient.mk M) with
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases h0 : Ideal.Quotient.mk M y = 0
        · exact ⟨0, E.zero_mem, by rw [h0, inv_zero, map_zero]⟩
        · have h1 : (y : Ω) ≠ 0 := by
            intro hy0
            have : y = 0 := Subtype.ext hy0
            exact h0 (by rw [this, map_zero])
          have h2 := isInt_inv (y : Ω) h1 (fun hh => h0 ((hmem y).2 hh))
          refine ⟨⟨_, h2⟩, E.inv_mem hy, ?_⟩
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← map_mul, ← map_one (Ideal.Quotient.mk M)]
          congr 1
          exact Subtype.ext (inv_mul_cancel₀ h1) }
  have hqi : IsIntegral (O0 p) (T.qq N) :=
    IsIntegral.of_pow (pow_pos hp.out.pos N) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : integralClosure (O0 p) Ω := ⟨_, hqi⟩
  have ht : ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) = algebraMap (O0 p) Ω (qO p) := by
    rw [← Basic.qq_pow T N]; rfl
  let d' : ℕ → integralClosure (O0 p) Ω := fun j => if hj : j < p ^ N then ⟨d j, (hd j hj).2⟩ else 0
  have hd' : ∀ j < p ^ N, (d' j : Ω) = d j := fun j hj => by simp only [d', dite_eq_left hj]
  have key := ResidueIndep.field_indep p K N (Ideal.Quotient.mk M t)
    ⟨t ^ p ^ N, by
      show ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) ∈ E
      rw [ht]; exact hE ⟨_, rfl⟩, map_pow _ _ _⟩
    (by
      rintro _ ⟨y, hy, rfl⟩ hb
      refine hq y hy y.2 ?_
      rw [← ht]
      have hz : Ideal.Quotient.mk M (y ^ p - t ^ p ^ N) = 0 := by
        rw [RingHom.map_sub, RingHom.map_pow, RingHom.map_pow, hb, sub_self]
      have := (hmem (y ^ p - t ^ p ^ N)).1 hz
      exact this)
    (fun j => Ideal.Quotient.mk M (d' j))
    (fun j hj => ⟨d' j, by
      show (d' j : Ω) ∈ E
      rw [hd' j hj]; exact (hd j hj).1, rfl⟩)
    (by
      have e : ((∑ j ∈ Finset.range (p ^ N), d' j * t ^ j : integralClosure (O0 p) Ω) : Ω) =
          ∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j := by
        push_cast
        exact Finset.sum_congr rfl fun j hj => by rw [hd' j (Finset.mem_range.1 hj)]
      have := (hmem _).2 (e ▸ hs)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, map_mul, map_pow] using this)
  intro j hj
  rw [← hd' j hj]
  exact (hmem _).1 (key j hj)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.subgroupCharacterIdempotent_properties : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (S : G → Prop) (χ : G → ℂ), S 1 → (∀ u v, S u → S v → S (u * v)) → χ 1 = 1 → (∀ u v, S u → S v → χ (u * v) = χ u * χ v) → IsProj (eps S χ) ∧ eps S χ 1 = ((Nat.card {u // S u} : ℂ))⁻¹ ∧ (∀ x : M, x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x) ∧ ∀ (n : ℕ) (x : Fin n → M), LinearIndependent ℂ x → (∀ i u, S u → ρ u (x i) = χ u • x i) → n ≤ rk ρ (eps S χ) := by
  first | exact @GlobalTheory.BadShare.EpsProj.eps_spec | exact GlobalTheory.BadShare.EpsProj.eps_spec | (intros; apply GlobalTheory.BadShare.EpsProj.eps_spec <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.monomial_eq_of_upperUnipotent_double_coset : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (w w' u u' : GG g N), (∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) → (∃ σ : Equiv.Perm (Fin N), ∀ a b, w'.val a b ≠ 0 → a = σ b) → IsUp g N u → IsUp g N u' → u * w = w' * u' → w = w' := by
  first | exact @GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset | exact GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset | (intros; apply GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = L'.sharp → L.s = L'.s → L.k = L'.k → rk ρ L.e = rk ρ L'.e := by
  first | exact @GlobalTheory.BadShare.CoDiag.rk_e_eq | exact GlobalTheory.BadShare.CoDiag.rk_e_eq | (intros; apply GlobalTheory.BadShare.CoDiag.rk_e_eq <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.exists_relevant_bruhat_cells_levelDatum : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N), L.sharp = false → (∀ a, L.co a = 1) → ∀ k : ℕ, 0 < k → k < N → ∃ R : Finset (GG g N), (g - 1) * g ^ (k - 1) ≤ R.card ∧ (∀ w ∈ R, (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (w : GG g N).val a b = if a = b then 1 else 0) ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) ∧ ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0) → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u' : GG g N).val a b = if a = b then 1 else 0) → u * w = w * u' → L.chi u = L.chi u' := by
  first | exact @GlobalTheory.BadShare.Cells.relevant_cells | exact GlobalTheory.BadShare.Cells.relevant_cells | (intros; apply GlobalTheory.BadShare.Cells.relevant_cells <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.whittaker_translates_corner_linearIndependent : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ (L : Lev g N), L.sharp = false → ∀ (x : M), x ≠ 0 → (∀ u, IsUp g N u → ρ u x = L.chi u • x) → ∀ k : ℕ, k < N → ∀ φ : GG g N → ℂ, (∀ h, φ h ≠ 0 → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (h : GG g N).val a b = if a = b then 1 else 0)) → ∑ h, φ h • ρ h x = 0 → ∀ h₀ : GG g N, ∑ u ∈ Finset.univ.filter (fun u : GG g N => IsUp g N u ∧ (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0)), φ (h₀ * u) * L.chi u = 0 := by
  first | exact @GlobalTheory.BadShare.Indep.translates_independent | exact GlobalTheory.BadShare.Indep.translates_independent | (intros; apply GlobalTheory.BadShare.Indep.translates_independent <;> assumption)
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem idx_congr_of_inf_eq {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    {A B C : Submodule R X} (h : A ⊓ C = B ⊓ C) : idx A C = idx B C := by
  unfold idx
  rw [← AddSubgroup.inf_relIndex_right A.toAddSubgroup, ← AddSubgroup.inf_relIndex_right B.toAddSubgroup]
  have : A.toAddSubgroup ⊓ C.toAddSubgroup = B.toAddSubgroup ⊓ C.toAddSubgroup := by
    ext x
    have := SetLike.ext_iff.1 h x
    simpa using this
  rw [this]

theorem normOp_comp_of_adj : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hl A B C hA hB hC hadj hAC v hv
  obtain ⟨x, hx, P, hP, hfin, hann, hle⟩ := id hadj
  obtain ⟨hAB, hBA, -, hsB, hsA⟩ := GlobalTheory.T.adjacent_selfDual_lattices_index_simple h A B hA hB x hx P hP hfin hann hle
  have hn : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB0 : idx A B ≠ 0 := hAB ▸ hn
  have hBA0 : idx B A ≠ 0 := hBA ▸ hn
  have hBC0 : idx B C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hBA0 hAC
  have hsq : lam (idx A B) ^ 2 = (idx A B : ℂ) := by
    rw [hAB]; exact (hl.2 P hP hfin).1
  have lAB := hl.1 _ hAB0
  have lBC := hl.1 _ hBC0
  have lAC := hl.1 _ hAC
  have homBC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h B C hC).2.1 hBC0).2.2
  have homAC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A C hC).2.1 hAC).2.2
  have fixB := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A B hB).2.1 hAB0).2.1 v hv
  unfold normOp
  rw [homBC, smul_smul]
  by_cases h1 : B ⊓ C ≤ A
  · by_cases h2 : A ⊓ C ≤ B
    · have he : A ⊓ C = B ⊓ C :=
        le_antisymm (le_inf h2 inf_le_right) (le_inf h1 inf_le_right)
      rw [GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq h lam hl A B C hA hB hC hadj hAC he v hv, smul_smul, ← idx_congr_of_inf_eq he]
      congr 1
      field_simp
    · have hT : A ⊓ B ⊔ A ⊓ C = A := by
        rcases hsA (A ⊓ B ⊔ A ⊓ C) le_sup_left (sup_le inf_le_left inf_le_left) with h3 | h3
        · exact absurd (le_sup_right.trans h3) h2
        · exact h3
      obtain ⟨hi, hs⟩ := GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h B A C hB hA hC hBA0 hAC hT.ge
      rw [← hs _ fixB, (GlobalTheory.T.heisenberg_intertwining_sums_comp_eq_index h A B hA hB hAB0).2 v hv, homAC, smul_smul, hi,
        hBA.trans hAB.symm, map_mul, ← hsq]
      congr 1
      field_simp
  · have hT : A ⊓ B ⊔ B ⊓ C = B := by
      rcases hsB (A ⊓ B ⊔ B ⊓ C) le_sup_left (sup_le inf_le_right inf_le_left) with h3 | h3
      · exact absurd (le_sup_right.trans h3) h1
      · exact h3
    obtain ⟨hi, hs⟩ := GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h A B C hA hB hC hAB0 hBC0 (by rw [inf_comm B A]; exact hT.ge)
    rw [hs v hv, hi, map_mul]
    congr 1
    field_simp

end GlobalTheory.FinWeil
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

theorem _root_.GlobalTheory.T.exists_combination_mul_eq_reparametrization_image : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ N : Ω, GlobalTheory.GeoFix.InR ψ N → N ≠ 0 → ∃ (N' : Ω) (D : O0 p), GlobalTheory.GeoFix.InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
  first | exact @GlobalTheory.GeoFix.exists_inR_mul_eq_psi | exact GlobalTheory.GeoFix.exists_inR_mul_eq_psi | (intros; apply GlobalTheory.GeoFix.exists_inR_mul_eq_psi <;> assumption)
end

section

namespace GlobalTheory.TestLat

theorem weyl_rowAct_mem_of_isUnit_det :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
      ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g.det →
        ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν,
          Formalism.GradedWeylDivisibility.rowAct R g f ∈ Formalism.GradedWeylDivisibility.weyl R n n (le_refl n) ν := by
  intro R _ _ n ν _ g hg f hf
  exact Formalism.UG.P.wlocal_main (le_refl n) ν n 0 (by omega) g g⁻¹ (Matrix.nonsing_inv_mul g hg)
    (fun _ _ hj => absurd hj (Nat.not_lt_zero _)) f hf

end GlobalTheory.TestLat
end

section

noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem TWact_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (g : G) (r : RW) (y : TW RW T) :
    TWact f T g (r • y) = f r • TWact f T g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWact, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem TWmap_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (r : RW) (y : TW RW T) :
    TWmap f T (r • y) = f r • TWmap f T y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem unit_cancel (hO : Function.Injective (algebraMap O LL)) :
    ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      ∀ r r' : RW, r • ((1 : RW) ⊗ₜ[O] e₀) = r' • ((1 : RW) ⊗ₜ[O] e₀) → r = r' := by
  obtain ⟨e, e₀, h1, h2, -⟩ := E.one_e
  obtain ⟨x, hx, hT⟩ := W.one_line
  have h0 : (e₀ : W.one.V) ≠ 0 := by
    intro h
    have hm : (⟨x, by rw [hT]; exact Submodule.mem_span_singleton_self x⟩ : ↥W.one.L.T) ∈
        Submodule.span O {e₀} := by rw [h1]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have := congrArg Subtype.val hc
    simp only [SetLike.val_smul, h, smul_zero] at this
    exact hx this.symm
  have hb : Function.Bijective (LinearMap.toSpanSingleton O _ e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc => ?_, ?_⟩
    · have := congrArg Subtype.val hc
      simp only [LinearMap.toSpanSingleton_apply, SetLike.val_smul, ZeroMemClass.coe_zero] at this
      rw [← algebraMap_smul LL, smul_eq_zero] at this
      exact hO (by rw [this.resolve_right h0, map_zero])
    · rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, h1]
  let lam := (LinearEquiv.ofBijective _ hb).symm
  have hl : lam e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]; simp
  refine ⟨e, e₀, h2, fun r r' h => ?_⟩
  have := congrArg (fun y => TensorProduct.rid O RW (LinearMap.lTensor RW lam.toLinearMap y)) h
  simpa [TensorProduct.smul_tmul', hl] using this

theorem ioE_φ (hO : Function.Injective (algebraMap O LL)) (a : W.EE) :
    E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h1, h2⟩ := unit_cancel E hO
  have h3 : TWmap φR W.one ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWmap]
  have := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, TWmap_smul, h1, h3] at this
  exact h2 _ _ this

theorem ioE_γ (hO : Function.Injective (algebraMap O LL)) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h1, h2⟩ := unit_cancel E hO
  have h4 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
  have h3 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWact, h4]
  have := E.jD_act W.one g (a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, TWact_smul, h1, h3] at this
  exact h2 _ _ this

def sc : LetA O n →ₐ[O] RW := inclR.comp E.io

theorem sc_φ (hO : Function.Injective (algebraMap O LL)) (a : LetA O n) :
    sc E (W.φA a) = φR (sc E a) := by
  have := ioE_φ E hO (algebraMap _ _ a)
  rwa [W.φE_ext, E.ioE_ext, E.ioE_ext] at this

def cst (c : ZMod n → O) : LetA O n := fun i => PowerSeries.C (c i)

theorem φA_cst (c : ZMod n → O) : W.φA (cst c) = cst fun i => c (i - 1) := by
  funext i
  exact W.φ₀.commutes (c (i - 1))

theorem iter_sc_cst (hO : Function.Injective (algebraMap O LL)) (c : ZMod n → O) (k : ℕ) :
    φR^[k] (sc E (cst c)) = sc E (cst fun i => c (i - k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← sc_φ E hO, φA_cst]
    congr 2
    funext i
    congr 1
    push_cast
    ring

end Generic

section Comp

variable {Z O R R' : Type} [CommRing Z] [CommRing O] [CommRing R] [CommRing R'] [Algebra Z O]
  [Algebra Z R] [Algebra Z R']

def cf (lam : O →ₗ[Z] Z) : O ⊗[Z] R →ₗ[Z] R :=
  (TensorProduct.lid Z R).toLinearMap ∘ₗ lam.rTensor R

end Comp

section Situation

open GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

variable {l : ℕ} [Fact l.Prime]

theorem inclW_frob (a : Ainf l) : inclW l (WittVector.frobenius a) = frobW l (inclW l a) := by
  ext n
  change ((WittVector.map _ _ : WCb l)).coeff n = (WittVector.map (frobenius (Cb l) l) (inclW l a)).coeff n
  simp [inclW, WittVector.map_coeff, frobenius_def]

theorem tmul_iter (LL : FinExt l) (k : ℕ) (x : WCb l) :
    (φRW LL)^[k] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (frobW l)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
  (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l (x ^ l) := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

end Situation

end GlobalTheory.TorsionBoundCompare
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.exists_joint_genEigenspace_idempotent_poly : ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (Z B : Submodule K V) (ι : Type) (S : ι → Prop) (T : ι → Module.End K V) (lam : ι → K), B ≤ Z → FiniteDimensional K Z → (∀ t, S t → ∀ z ∈ Z, T t z ∈ Z) → (∀ t, S t → ∀ z ∈ B, T t z ∈ B) → (∀ t t', S t → S t' → ∀ z ∈ Z, T t (T t' z) - T t' (T t z) ∈ B) → (∀ z ∈ Z, ∀ n : ℕ, (∀ t, S t → ((T t - lam t • 1) ^ n) z ∈ B) → ∀ t, S t → (T t - lam t • 1) z ∈ B) → ∃ P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}), FreeAlgebra.lift K lam P = 1 ∧ ∀ z ∈ Z, ∀ t, S t → (T t - lam t • 1) (FreeAlgebra.lift K T P z) ∈ B := by
  first | exact @GlobalTheory.exists_genEig_idem_poly | exact GlobalTheory.exists_genEig_idem_poly | (intros; apply GlobalTheory.exists_genEig_idem_poly <;> assumption)
end
