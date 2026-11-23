module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle017
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle005
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle020
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL

theorem exists_linearEquiv_mem_iff_of_finrank_eq {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A B : Submodule F V) (h : Module.finrank F A = Module.finrank F B) :
    ∃ e : V ≃ₗ[F] V, ∀ x, e x ∈ B ↔ x ∈ A := by
  obtain ⟨A', hA⟩ := A.exists_isCompl
  obtain ⟨B', hB⟩ := B.exists_isCompl
  have h' : Module.finrank F A' = Module.finrank F B' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hA
    have h2 := Submodule.finrank_add_eq_of_isCompl hB
    omega
  let e1 := LinearEquiv.ofFinrankEq A B h
  let e2 := LinearEquiv.ofFinrankEq A' B' h'
  refine ⟨(Submodule.prodEquivOfIsCompl A A' hA).symm ≪≫ₗ (e1.prodCongr e2) ≪≫ₗ
    Submodule.prodEquivOfIsCompl B B' hB, fun x => ?_⟩
  obtain ⟨⟨a, a'⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A A' hA).surjective x
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  simp only [LinearEquiv.prodCongr_apply, Submodule.coe_prodEquivOfIsCompl']
  rw [B.add_mem_iff_right (e1 a).2, A.add_mem_iff_right a.2,
    Submodule.mem_left_iff_eq_zero_of_disjoint hB.disjoint,
    Submodule.mem_left_iff_eq_zero_of_disjoint hA.disjoint]
  simp

theorem finsum_nilRad_extZero_eq_zero (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ)
    (hχ : IsChar ℂ ℂ χ) (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F))
    (hb : Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1)
      (H : Set (GL (Fin d) F)) (nilRad A))
    (h0 : ∑ᶠ u ∈ (H : Set (GL (Fin d) F)), χ u = 0)
    (g : Module.End F (Fin d → F)) (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ h ∈ nilRad A, extZero χ (g + h) = 0 := by
  obtain ⟨e1, e2, -, -⟩ := GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ
  by_cases hu : IsUnit g
  · have hm : IsUnit (LinearMap.toMatrix' g) := by
      have := hu.map (LinearMap.toMatrixAlgEquiv' (R := F) (n := Fin d))
      exact this
    obtain ⟨x, hx⟩ := hm
    have hgx : Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g := by
      rw [hx, Matrix.toLin'_toMatrix']
    have : Finite (Module.End F (Fin d → F)) := Module.finite_of_finite F
    have hb2 : Set.BijOn (fun h : Module.End F (Fin d → F) => g * h) (nilRad A) (nilRad A) := by
      refine ((Set.toFinite _).injOn_iff_bijOn_of_mapsTo ?_).1 ?_
      · intro h hh
        exact ⟨fun y => hg _ (hh.1 y), fun y hy => by simp [hh.2 y hy]⟩
      · intro a _ b _ hab
        exact hu.mul_left_cancel hab
    have h1 := GlobalTheory.T.character_coset_sum_eq_zero_of_subgroup_sum _ χ hχ H
      ((finsum_set_coe_eq_finsum_mem (f := χ) (H : Set (GL (Fin d) F))).trans h0) x
    have h2 := (finsum_set_coe_eq_finsum_mem (f := fun u => χ (x * u)) (H : Set (GL (Fin d) F))).symm.trans h1
    rw [← h2]
    symm
    refine finsum_mem_eq_of_bijOn _ (hb2.comp hb) fun u _ => ?_
    rw [← e1]
    congr 1
    simp only [Function.comp, Units.val_mul, Matrix.toLin'_mul, hgx, mul_sub, mul_one]
    rw [add_sub_cancel]
    rfl
  · refine finsum_mem_of_eqOn_zero fun h hh => ?_
    refine e2 _ fun hu' => hu ?_
    have hc := (GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F _ A g hg).2 h hh
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff] at hu' ⊢
    rwa [hc] at hu'

theorem isPrimitive_extZero_of_sum_unipotent : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), IsChar ℂ ℂ χ → (∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, χ u = 0) → IsPrimitive (extZero χ) := by
  intro F _ _ d χ hχ hs A hA0 hA1 g hg
  have ha0 : 0 < Module.finrank F A := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => hA0 (Submodule.finrank_eq_zero.1 h)
  have ha1 : Module.finrank F A < d := by
    have := Submodule.finrank_lt hA1
    simpa using this
  obtain ⟨B, H, hB, hH, hb⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F d _ ha1.le
  have h0 := hs _ ha0 ha1
  rw [← hH] at h0
  obtain ⟨e, he⟩ := exists_linearEquiv_mem_iff_of_finrank_eq A B hB.symm
  have hcl := (GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ).2.2.2 (GlobalTheory.isChar_restrict_conj_one ℂ ℂ _ χ hχ).2.1
  have key := finsum_nilRad_extZero_eq_zero F d χ hχ B H hb h0 (e.conj g) (fun x hx => by
    rw [LinearEquiv.conj_apply_apply, he]
    apply hg
    rw [← he]
    simpa using hx)
  rw [← key]
  refine finsum_mem_eq_of_bijOn (fun h => e.conj h) ⟨fun h hh => ⟨fun y => ?_, fun y hy => ?_⟩,
    e.conj.injective.injOn, fun h hh => ⟨e.symm.conj h, ⟨fun y => ?_, fun y hy => ?_⟩, by ext y; simp [LinearEquiv.conj_apply_apply]⟩⟩ fun h _ => ?_
  · rw [LinearEquiv.conj_apply_apply, he]
    exact hh.1 _
  · rw [LinearEquiv.conj_apply_apply, hh.2 _ (by rw [← he]; simpa using hy), map_zero]
  · rw [← he, LinearEquiv.conj_apply_apply]
    simpa using hh.1 _
  · rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, hh.2 _ ((he y).2 hy), map_zero]
  · rw [← map_add (f := _), hcl]

end GlobalTheory.CuspGL
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_abelianByPrimePower_not_dvd_card_fixedBy : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by
  first | exact @GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ | exact GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ | (intros; apply GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ <;> assumption)
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.ind_restrict_eq_card_fixedBy_mul_of_classFn : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by
  first | exact @GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul | exact GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul | (intros; apply GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul <;> assumption)
end

section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem mem_virt_iff_sub (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L) :
    f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by
  obtain ⟨h0, hadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G
  unfold Virt
  constructor
  · intro hf
    induction hf using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨x, 0, hx, h0, (sub_zero x).symm⟩
    | zero => exact ⟨0, 0, h0, h0, (sub_zero 0).symm⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ihx
      obtain ⟨c, d, hc, hd, rfl⟩ := ihy
      exact ⟨a + c, b + d, hadd a c ha hc, hadd b d hb hd, by abel⟩
    | neg x _ ih =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ih
      exact ⟨b, a, hb, ha, by abel⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure ha) (AddSubgroup.subset_closure hb)
end GlobalTheory.BI
end

section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_isChar_eq_add_of_injective : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W) (f : Representation.IntertwiningMap σ ρ), Function.Injective f → ∃ c : G → L, IsChar K L c ∧ ∀ g, algebraMap K L (ρ.character g) = algebraMap K L (σ.character g) + c g := by
  intro K L _ _ _ G _ V _ _ _ W _ _ _ ρ σ f hf
  have hcomm : ∀ g, ρ g ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ σ g := fun g =>
    (f.isIntertwining' g).symm
  have hle : ∀ g, LinearMap.range f.toLinearMap ≤ (LinearMap.range f.toLinearMap).comap (ρ g) := by
    rintro g _ ⟨w, rfl⟩
    exact ⟨σ g w, (LinearMap.congr_fun (hcomm g) w).symm⟩
  refine ⟨fun g => algebraMap K L ((ρ.quotient _ hle).character g),
    (GlobalTheory.T.isCharacterOverSubfield_of_representation K L G _ (ρ.quotient _ hle)).1, fun g => ?_⟩
  rw [← map_add (f := _)]
  congr 1
  refine GlobalTheory.T.linear_map_short_exact_commute K W V _ f.toLinearMap (LinearMap.range f.toLinearMap).mkQ (σ g) (ρ g)
    (ρ.quotient _ hle g) hf (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm (hcomm g) ?_
  ext v
  rfl
end GlobalTheory.BI
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacter_finsum_conj_subgroupFunctionExtendByZero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by
  first | exact @GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar | exact GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar | (intros; apply GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar <;> assumption)
end

section

open GlobalTheory.BI

namespace GlobalTheory.BI

theorem character_eq_ind_of_imprimitive :
    ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V) (T : Subgroup G) (e : Module.End L V), ρ.IsIrreducible → e ≠ 0 → e * e = e → (∀ t ∈ T, ρ t * e = e * ρ t) → (∀ g ∉ T, e * ρ g * e = 0) → ∃ ψ : T → L, IsChar L L ψ ∧ ∀ g, ρ.character g = ind T ψ g := by
  intro L _ _ G _ _ V _ _ _ ρ T e hirr he0 hee hT hoff
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨fun t => LinearMap.trace L V (ρ t * e), ?_, ?_⟩
  · exact isChar_trace_mul_idempotent L T V (ρ.comp T.subtype) e hee (fun t => hT t t.2)
  · intro g
    have hsum := GlobalTheory.sum_conj_idempotent_eq_card_smul L G V ρ T e hirr he0 hee hT hoff
    have hcard : (Nat.card T : L) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := T)).ne'
    have hkey : ∀ h : G, LinearMap.trace L V (ρ h * e)
        = ext0 T (fun t : T => LinearMap.trace L V (ρ t * e)) h := by
      intro h
      unfold ext0
      split_ifs with hh
      · rfl
      · have h2 : ρ h * e = ρ h * e * e := by rw [mul_assoc, hee]
        rw [h2, LinearMap.trace_mul_comm, ← mul_assoc, hoff h hh, map_zero]
    have hterm : ∀ x : G, LinearMap.trace L V (ρ g * (ρ x * e * ρ x⁻¹))
        = LinearMap.trace L V (ρ (x⁻¹ * g * x) * e) := by
      intro x
      rw [show ρ g * (ρ x * e * ρ x⁻¹) = (ρ g * ρ x * e) * ρ x⁻¹ by simp only [mul_assoc],
        LinearMap.trace_mul_comm]
      simp only [map_mul, mul_assoc]
    have htr : (Nat.card T : L) * LinearMap.trace L V (ρ g)
        = ∑ x : G, LinearMap.trace L V (ρ (x⁻¹ * g * x) * e) := by
      have h3 : (Nat.card T : L) * LinearMap.trace L V (ρ g)
          = LinearMap.trace L V (ρ g * ∑ x : G, ρ x * e * ρ x⁻¹) := by
        rw [hsum, mul_smul_comm, mul_one, map_smul, smul_eq_mul]

      rw [h3, Finset.mul_sum, map_sum]
      exact Finset.sum_congr rfl (fun x _ => hterm x)
    rw [Representation.character, ind, finsum_eq_sum_of_fintype]
    simp only [← hkey]
    rw [← htr, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end GlobalTheory.BI
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (g : Module.End F V), s (LinearMap.charpoly g) = ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by
  first | exact @GlobalTheory.CuspGL.charpoly_eq_finsum_psi | exact GlobalTheory.CuspGL.charpoly_eq_finsum_psi | (intros; apply GlobalTheory.CuspGL.charpoly_eq_finsum_psi <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ g : Module.End F V, (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ LinearMap.charpoly g = f ^ m) → φ g = 0 := by
  first | exact @GlobalTheory.CuspGL.eq_zero_of_not_primary | exact GlobalTheory.CuspGL.eq_zero_of_not_primary | (intros; apply GlobalTheory.CuspGL.eq_zero_of_not_primary <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem card_GL_eq_prod_range (F : Type) [Field F] [Finite F] (n : ℕ) :
    Nat.card (GL (Fin n) F) = ∏ i ∈ Finset.range n, (Nat.card F ^ n - Nat.card F ^ i) := by
  classical
  haveI := Fintype.ofFinite F
  rw [Matrix.card_GL_field, Nat.card_eq_fintype_card,
    ← Fin.prod_univ_eq_prod_range (fun i => Fintype.card F ^ n - Fintype.card F ^ i)]

theorem card_subspaces_mul_glCard : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * (Nat.card F : ℂ) ^ (a * (Module.finrank F V - a)) * glCard F a * glCard F (Module.finrank F V - a) = glCard F (Module.finrank F V) := by
  intro F _ _ V _ _ _ a ha
  have h := GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases F V a ha
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le ha
  have hb' : Module.finrank F V - a = b := by omega
  rw [hb']
  rw [hb] at h ⊢
  unfold glCard
  rw [card_GL_eq_prod_range, card_GL_eq_prod_range, card_GL_eq_prod_range]
  have key : Nat.card {W : Submodule F V // Module.finrank F W = a} * Nat.card F ^ (a * b) *
      (∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i)) *
      (∏ i ∈ Finset.range b, (Nat.card F ^ b - Nat.card F ^ i)) =
      ∏ i ∈ Finset.range (a + b), (Nat.card F ^ (a + b) - Nat.card F ^ i) := by
    rw [Finset.prod_range_add, ← h]
    have h2 : ∏ i ∈ Finset.range b, (Nat.card F ^ (a + b) - Nat.card F ^ (a + i)) =
        Nat.card F ^ (a * b) * ∏ i ∈ Finset.range b, (Nat.card F ^ b - Nat.card F ^ i) := by
      simp only [pow_add, ← Nat.mul_sub, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_range, pow_mul]
    rw [h2]
    ring
  exact_mod_cast key

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

noncomputable def oneValue (q a : ℕ) : ℂ :=
  if a = 0 then 0 else ∏ i ∈ Finset.Ico 1 a, (1 - (q : ℂ) ^ i)

theorem sum_oneValue_finrank (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Fintype (Submodule F V)] :
    ∑ W : Submodule F V, oneValue (Nat.card F) (Module.finrank F W) = (Module.finrank F V : ℂ) := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h := GlobalTheory.QBinomialSum.sum_gaussian_mul_prod (Nat.card F) (Module.finrank F V)
    (fun a => Nat.card {W : Submodule F V // Module.finrank F W = a}) hq
    (fun a ha => GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases F V a ha)
  rw [← h, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.Icc 0 (Module.finrank F V))
    (g := fun W : Submodule F V => Module.finrank F W)
    (fun W _ => Finset.mem_Icc.2 ⟨Nat.zero_le _, W.finrank_le⟩)]
  have h2 : ∀ a : ℕ, ∑ W ∈ Finset.univ.filter (fun W : Submodule F V => Module.finrank F W = a),
      oneValue (Nat.card F) (Module.finrank F W) =
      (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * oneValue (Nat.card F) a := by
    intro a
    rw [Finset.sum_congr rfl (g := fun _ => oneValue (Nat.card F) a)
      (fun W hW => by rw [(Finset.mem_filter.1 hW).2]), Finset.sum_const, nsmul_eq_mul,
      Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = a}), Fintype.card_subtype]
  simp only [h2]
  symm
  refine Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) ?_ ?_
  · intro a ha
    have : a = 0 := by
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at ha
      omega
    simp [this, oneValue]
  · intro a ha
    have : a ≠ 0 := by
      simp only [Finset.mem_Icc] at ha
      omega
    simp [this, oneValue]

theorem psi_one_eq_oneValue (F : Type) [Field F] [Finite F] (s : F[X] → ℂ)
    (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.finrank F V = n →
      psi s V 1 = oneValue (Nat.card F) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hn
    classical
    haveI : Finite V := Module.finite_of_finite F
    haveI : Fintype (Submodule F V) := Fintype.ofFinite _
    have hc : LinearMap.charpoly (1 : Module.End F V) = (X - C 1) ^ n := by
      rw [LinearMap.charpoly_one, hn, C_1]
    rw [psi_eq, hc, hs]
    have h1 : ∀ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, (1 : Module.End F V) x ∈ W},
        psi s W.1 ((1 : Module.End F V).restrict W.2.2) = oneValue (Nat.card F) (Module.finrank F W.1) := by
      intro W
      have : (1 : Module.End F V).restrict W.2.2 = (1 : Module.End F W.1) := by
        ext x
        rfl
      rw [this]
      exact ih _ (hn ▸ Submodule.finrank_lt W.2.1) _ rfl
    rw [finsum_congr h1, finsum_eq_sum_of_fintype,
      ← Finset.sum_subtype (Finset.univ.erase (⊤ : Submodule F V)) (by intro W; simp)
        (fun W : Submodule F V => oneValue (Nat.card F) (Module.finrank F W))]
    have h2 := sum_oneValue_finrank F V
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⊤ : Submodule F V)), finrank_top, hn] at h2
    rw [← h2]
    ring

theorem psi_one (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (s : F[X] → ℂ) (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (h : 0 < Module.finrank F V) :
    psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by
  rw [psi_one_eq_oneValue F s hs _ V rfl, oneValue, if_neg h.ne']

end GlobalTheory.CuspGL
end

section

open Topology

theorem _root_.GlobalTheory.T.exists_holomorphic_family_of_ringHom_near : ∀ (K A : Type) [Field K] [CharZero K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ) (φ₀ : A →+* ℂ), φ₀.comp (algebraMap K A) = σ → ∃ (m : ℕ) (s : Fin m → A) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (S : Finset A) (ε : ℝ), IsOpen B ∧ 0 < ε ∧ (∀ b ∈ B, (φ b).comp (algebraMap K A) = σ ∧ ∀ i, φ b (s i) = b i) ∧ (∀ a : A, DifferentiableOn ℂ (fun b => φ b a) B) ∧ ∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → (∀ a ∈ S, ‖ψ a - φ₀ a‖ < ε) → (fun i => ψ (s i)) ∈ B ∧ φ (fun i => ψ (s i)) = ψ := by
  first | exact @GlobalTheory.SmoothPointFamily.exists_holomorphic_family | exact GlobalTheory.SmoothPointFamily.exists_holomorphic_family | (intros; apply GlobalTheory.SmoothPointFamily.exists_holomorphic_family <;> assumption)
end
