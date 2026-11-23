module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle004
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

def compoundRep {G : Type} [Group G] {n : ℕ} (j : ℕ) (ρ : G →* GL (Fin n) ℂ) :
    Representation ℂ G (Set.powersetCard (Fin n) j → ℂ) where
  toFun g := Matrix.toLin' (GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ))
  map_one' := by
    rw [map_one, Units.val_one, GlobalTheory.compoundMatrix_one, Matrix.toLin'_one]; rfl
  map_mul' a b := by
    rw [map_mul, Units.val_mul, GlobalTheory.compoundMatrix_mul, Matrix.toLin'_mul]; rfl

open Polynomial in
private lemma det_submatrix_subsetEnum_eq_det_submatrix_val {n j : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (S : Set.powersetCard (Fin n) j) :
    (A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S)).det =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).det := by
  have hmem : ∀ i, _root_.GlobalTheory.subsetEnum S i ∈ S.1 := fun i => by
    have : _root_.GlobalTheory.subsetEnum S i ∈ Set.range (_root_.GlobalTheory.subsetEnum S) :=
      ⟨i, rfl⟩
    rw [_root_.GlobalTheory.range_subsetEnum] at this
    exact_mod_cast this
  let σ : Fin j ≃ {x // x ∈ S.1} := Equiv.ofBijective
    (fun i => ⟨_root_.GlobalTheory.subsetEnum S i, hmem i⟩)
    ⟨fun a b hab => _root_.GlobalTheory.subsetEnum_injective S (congrArg Subtype.val hab),
      fun x => by
        have hx : x.1 ∈ ((S.1 : Finset (Fin n)) : Set (Fin n)) := x.2
        rw [← _root_.GlobalTheory.range_subsetEnum] at hx
        obtain ⟨i, hi⟩ := hx
        exact ⟨i, Subtype.ext hi⟩⟩
  have hsub : A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S) =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).submatrix σ σ := rfl
  rw [hsub, Matrix.det_submatrix_equiv_self]

open Polynomial in
private lemma trace_compoundMatrix_eq_sum_principal_minors {n : ℕ} (j : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (_root_.GlobalTheory.compoundMatrix j A).trace = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (A.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  rw [Finset.sum_subtype (p := fun s : Finset (Fin n) => s ∈ Set.powersetCard (Fin n) j) _
    (fun s => by simp [Finset.mem_powersetCard, Set.powersetCard])]
  unfold _root_.GlobalTheory.compoundMatrix
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  exact Finset.sum_congr rfl fun S _ => det_submatrix_subsetEnum_eq_det_submatrix_val A S

open Polynomial in
private lemma esymm_roots_charpoly_eq_sum_principal_minors {n : ℕ} (j : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.roots.esymm j = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (M.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcard : M.charpoly.roots.card = M.charpoly.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits _)
  rcases le_or_gt j n with hj | hj
  · have h1 := coeff_eq_esymm_roots_of_card hcard (k := n - j) (by omega)
    have h2 := M.charpoly_coeff_eq_sum_minors j (by simp [hj])
    rw [hdeg, Nat.sub_sub_self hj, M.charpoly_monic.leadingCoeff, one_mul] at h1
    rw [Fintype.card_fin, h1] at h2
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h2
  · rw [Finset.powersetCard_eq_empty.mpr (by simp [hj]), Finset.sum_empty, Multiset.esymm,
      Multiset.powersetCard_eq_empty _ (by omega)]
    simp


open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_esymm_roots_charpoly :
    ∀ (G : Type) [Group G] (n j : ℕ) (ρ : G →* GL (Fin n) ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ
      (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) := by
  intro G _ n j ρ
  have h := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (_root_.GlobalTheory.BI.compoundRep j ρ)).1
  have heq : (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) =
      fun g => algebraMap ℂ ℂ ((_root_.GlobalTheory.BI.compoundRep j ρ).character g) := by
    funext g
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    change _ = LinearMap.trace ℂ _
      (Matrix.toLin' (_root_.GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ)))
    rw [Matrix.trace_toLin'_eq, trace_compoundMatrix_eq_sum_principal_minors, esymm_roots_charpoly_eq_sum_principal_minors]
  rw [heq]
  exact h

end GlobalTheory.BI
end
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.commute_image_abelianByPrimePower_of_normal_central : ∀ (G : Type) [Group G] [Finite G] (M : Type) [Monoid M] (φ : G →* M), AbByP G → (∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, φ a * φ b = φ b * φ a) → ∀ b ∈ B, ∀ g : G, φ b * φ g = φ g * φ b) → ∀ a b : G, φ a * φ b = φ b * φ a := by
  first | exact @GlobalTheory.BI.commute_all | exact GlobalTheory.BI.commute_all | (intros; apply GlobalTheory.BI.commute_all <;> assumption)
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ a b c : G → L, pair (a + b) c = pair a c + pair b c) ∧ (∀ a b : G → L, IsChar K L a → IsChar K L b → ∃ n : ℕ, pair a b = (n : L)) ∧ (∀ φ : G → L, IsIrrChar K L φ → ∃ n : ℕ, 0 < n ∧ pair φ φ = (n : L)) ∧ ∀ a b : G → L, pair a b = pair b a := by
  first | exact @GlobalTheory.BI.pair_add_nat_pos_symm | exact GlobalTheory.BI.pair_add_nat_pos_symm | (intros; apply GlobalTheory.BI.pair_add_nat_pos_symm <;> assumption)
end

section

open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

theorem out_conj_mem_iff_smul_eq {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    q.out⁻¹ * g * q.out ∈ H ↔ g • q = q := by
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, ← H.inv_mem_iff]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem ind_restrict_eq_card_fixedBy_mul : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by
  intro L _ _ G _ _ H χ hχ g
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hψ : ∀ h x : H, (fun h : H => χ h) (x⁻¹ * h * x) = (fun h : H => χ h) h := by
    intro h x
    simpa using hχ h x
  have hterm : ∀ q : G ⧸ H, ext0 H (fun h : H => χ h) (q.out⁻¹ * g * q.out)
      = (if g • q = q then (1 : L) else 0) * χ g := by
    intro q
    unfold ext0
    by_cases hq : g • q = q
    · have hm := (out_conj_mem_iff_smul_eq H g q).2 hq
      rw [dite_eq_left hm, if_pos hq, one_mul]
      exact hχ g q.out
    · have hm : q.out⁻¹ * g * q.out ∉ H := fun h => hq ((out_conj_mem_iff_smul_eq H g q).1 h)
      rw [dite_eq_right hm, if_neg hq, zero_mul]
  rw [ind_eq_finsum_cosets L G H _ hψ g, finsum_eq_sum_of_fintype]
  simp_rw [hterm]
  rw [← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end GlobalTheory.BI
end
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.inducedClassFunctionFromSubgroup_eq_finsum_cosets : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), (∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) → ∀ g : G, ind H ψ g = ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) := by
  first | exact @GlobalTheory.BI.ind_eq_finsum_cosets | exact GlobalTheory.BI.ind_eq_finsum_cosets | (intros; apply GlobalTheory.BI.ind_eq_finsum_cosets <;> assumption)
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isAbelianByPrimePowerGroup_subgroup : ∀ (G : Type) [Group G] (T : Subgroup G), AbByP G → AbByP T := by
  first | exact @GlobalTheory.BI.AbByP.subgroup | exact GlobalTheory.BI.AbByP.subgroup | (intros; apply GlobalTheory.BI.AbByP.subgroup <;> assumption)
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_of_representation : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V), IsChar K L (fun g => algebraMap K L (ρ.character g)) ∧ (ρ.IsIrreducible → IsIrrChar K L (fun g => algebraMap K L (ρ.character g))) := by
  first | exact @GlobalTheory.BI.isChar_and_isIrrChar_of_rep | exact GlobalTheory.BI.isChar_and_isIrrChar_of_rep | (intros; apply GlobalTheory.BI.isChar_and_isIrrChar_of_rep <;> assumption)
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_restrict_classFunction_one : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (χ : G → L), IsChar K L χ → (∀ (H : Type) [Group H] (f : H →* G), IsChar K L (fun h => χ (f h))) ∧ (∀ g x : G, χ (x⁻¹ * g * x) = χ g) ∧ ∃ n : ℕ, χ 1 = (n : L) ∧ (n = 0 → χ = 0) := by
  first | exact @GlobalTheory.isChar_restrict_conj_one | exact GlobalTheory.isChar_restrict_conj_one | (intros; apply GlobalTheory.isChar_restrict_conj_one <;> assumption)
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_zero_and_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G], IsChar K L (0 : G → L) ∧ ∀ a b : G → L, IsChar K L a → IsChar K L b → IsChar K L (a + b) := by
  first | exact @GlobalTheory.BI.isChar_zero_and_add | exact GlobalTheory.BI.isChar_zero_and_add | (intros; apply GlobalTheory.BI.isChar_zero_and_add <;> assumption)
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_character_eq_finrank_intertwining : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W), pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g)) = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  first | exact @GlobalTheory.BI.pair_character_eq_finrank | exact GlobalTheory.BI.pair_character_eq_finrank | (intros; apply GlobalTheory.BI.pair_character_eq_finrank <;> assumption)
end

section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_abelianByPrimePower_not_dvd_card_fixedBy₂ :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime →
      ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by
  intro G _ _ x p hp
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_coprime_orderOf_pow_prime_pow' G x p hp
  obtain ⟨H, hCH, hnorm, hpow, hidx⟩ := GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex G (Subgroup.zpowers (x ^ p ^ k)) p hp
  have hN : ∀ g : G, g ∈ Subgroup.normalizer ((Subgroup.zpowers (x ^ p ^ k) : Subgroup G) : Set G) ↔
      ∀ d ∈ Subgroup.zpowers (x ^ p ^ k), g * d * g⁻¹ ∈ Subgroup.zpowers (x ^ p ^ k) := by
    intro g
    constructor
    · intro hg d hd
      exact (Subgroup.mem_normalizer_iff.1 hg d).1 hd
    · intro h
      exact Subgroup.mem_normalizer_fintype h
  refine ⟨H, ⟨p, hp, (Subgroup.zpowers (x ^ p ^ k)).subgroupOf H, ⟨?_⟩, ?_, ?_⟩, ?_⟩
  · intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn
  · intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hm, ← hn]
    exact (Commute.refl _).zpow_zpow m n
  · intro g
    obtain ⟨j, hj⟩ := hpow g g.2
    exact ⟨j, by rw [Subgroup.mem_subgroupOf]; simpa using hj⟩
  · intro hd
    haveI : Finite (G ⧸ H) := inferInstance
    have h1 := GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime G (x ^ p ^ k) p H _ hk hCH hpow hN
    have h2 := GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy G (G ⧸ H) x p k hp
    apply hidx _ hN
    rw [← h1]
    exact (h2.dvd_iff dvd_rfl).2 hd

end GlobalTheory.BI
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.character_coset_sum_eq_zero_of_subgroup_sum : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), IsChar ℂ ℂ χ → ∀ H : Subgroup G, ∑ᶠ u : H, χ u = 0 → ∀ g : G, ∑ᶠ u : H, χ (g * u) = 0 := by
  first | exact @GlobalTheory.BI.char_coset_sum_eq_zero | exact GlobalTheory.BI.char_coset_sum_eq_zero | (intros; apply GlobalTheory.BI.char_coset_sum_eq_zero <;> assumption)
end
