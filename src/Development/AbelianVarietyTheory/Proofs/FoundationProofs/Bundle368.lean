module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle356
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle351
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

namespace GlobalTheory.InertCoh

theorem fg_map_mkQ_of_ev {R M N : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (Z B Y : Submodule R M) (ev : M →ₗ[R] N) (L : Submodule R N) (hL : L.FG)
    (h1 : ∀ z ∈ Z, ∃ y ∈ Y, z - y ∈ B) (h2 : ∀ y ∈ Y, ev y ∈ L) (h3 : ∀ y ∈ Y, ev y = 0 → y ∈ B) :
    (Z.map B.mkQ).FG := by
  let f : Y →ₗ[R] N := ev ∘ₗ Y.subtype
  let g : Y →ₗ[R] (M ⧸ B) := B.mkQ ∘ₗ Y.subtype
  have hf : (LinearMap.range f).FG := by
    refine hL.of_le ?_
    rintro _ ⟨y, rfl⟩
    exact h2 y y.2
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro y hy
    exact (Submodule.Quotient.mk_eq_zero B).2 (h3 y y.2 hy)
  haveI : Module.Finite R (LinearMap.range f) := Module.Finite.iff_fg.2 hf
  haveI : Module.Finite R (Y ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  have hg : (LinearMap.range g).FG := by
    rw [← Submodule.range_liftQ (LinearMap.ker f) g hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  refine hg.of_le ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hzy⟩ := h1 z hz
  exact ⟨⟨y, hy⟩, ((Submodule.Quotient.eq B).2 hzy).symm⟩

theorem cobound_mem_coc {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {W : R2 Ω l} {c : Coef l}
    (I : Subgroup (G ℚ Ω)) (hW : Continuous W) (hO : ∀ s i j, mat W s i j ∈ c.O) {v : Fin 2 → Qbar l}
    (hv : ∀ i, v i ∈ c.O) : (fun s => mat W s *ᵥ v - v) ∈ coc W c I := by
  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hW
  refine mem_coc.2 ⟨fun i => ?_, fun s i => ?_, fun s _ t _ => ?_⟩
  · exact (continuous_apply i).comp ((hm.matrix_mulVec continuous_const).sub continuous_const)
  · simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
    exact c.O.sub_mem (c.O.sum_mem fun j _ => c.O.mul_mem (hO s i j) (hv j)) (hv i)
  · simp only [mat, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel

theorem fg_coc_mod_cob : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) (P : Set (G ℚ Ω)) (γ : G ℚ Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ z ∈ coc W c I, ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ ∈ P, z σ = mat W σ *ᵥ v - v) → (∀ z ∈ coc W c I, (∀ σ ∈ P, z σ = 0) → z γ = 0 → ∀ s ∈ I, z s = 0) → ((coc W c I).map (cob W c I).mkQ).FG := by
  intro l _ Ω _ _ W c I P γ hW hO hP hγ
  haveI := c.dvr
  haveI : IsNoetherianRing c.O := PrincipalIdealRing.isNoetherianRing
  let Y : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) :=
    coc W c I ⊓ ⨅ σ ∈ P, LinearMap.ker (LinearMap.proj σ : (G ℚ Ω → Fin 2 → Qbar l) →ₗ[c.O] (Fin 2 → Qbar l))
  have hY : ∀ z, z ∈ Y ↔ z ∈ coc W c I ∧ ∀ σ ∈ P, z σ = 0 := by
    intro z
    simp [Y, Submodule.mem_iInf]
  let ι : (Fin 2 → c.O) →ₗ[c.O] (Fin 2 → Qbar l) := (Algebra.linearMap c.O (Qbar l)).compLeft (Fin 2)
  have hL : (LinearMap.range ι).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  refine fg_map_mkQ_of_ev _ _ Y (LinearMap.proj γ) _ hL ?_ ?_ ?_
  · intro z hz
    obtain ⟨v, hv, hzv⟩ := hP z hz
    refine ⟨z - fun s => mat W s *ᵥ v - v, (hY _).2 ⟨Submodule.sub_mem _ hz (cobound_mem_coc I hW hO hv), ?_⟩, ?_⟩
    · intro σ hσ
      simp only [Pi.sub_apply, hzv σ hσ, sub_self]
    · exact mem_cob.2 ⟨v, fun s _ => by simp only [sub_sub_cancel]⟩
  · intro y hy
    exact ⟨fun i => ⟨y γ i, (mem_coc.1 ((hY y).1 hy).1).2.1 γ i⟩, rfl⟩
  · intro y hy h0
    refine mem_cob.2 ⟨0, fun s hs => ?_⟩
    rw [hγ y ((hY y).1 hy).1 ((hY y).1 hy).2 h0 s hs]
    simp

end GlobalTheory.InertCoh
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

theorem divCob_of_resCoc_cohom : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (z z' : G ℚ Ω → Fin 2 → Qbar l) (y y' : Fin 2 → Qbar l),
    VecE c y → VecE c y' → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) →
    (∀ s i, (l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i ∈ c.O) →
    (∃ m : ResPlane c, ∀ s, resCoc c W z y s - resCoc c W z' y' s = resAct c W hO s m - m) →
    z - z' ∈ divCob c W := by
  intro l _ Ω _ _ W c hO z z' y y' hy hy' hz hz' ⟨m, hm⟩

  have hlift : ∀ i, ∃ x : Qbar l, ∃ hx : x ∈ c.O, redL c x = m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (m i : ResL c)
    exact ⟨a.1, a.2, by rw [redL_of_mem c a.2]; exact ha⟩
  choose u hu hum using hlift
  have hl0 : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hWu : ∀ s i, (mat W s *ᵥ u) i ∈ c.O := by
    intro s i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1))
  have hWuR : ∀ s i, redL c ((mat W s *ᵥ u) i) = (resAct c W hO s m) i := by
    intro s i
    rw [resAct_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, wRed]
    rw [redL_add c (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1)),
      redL_mul c (hO _ _ _) (hu 0), redL_mul c (hO _ _ _) (hu 1), hum 0, hum 1]
  have key : ∀ s i, ∃ o ∈ c.O, ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
      ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i) = (l : Qbar l) * o := by
    intro s i
    have h1 := hz s i
    have h2 := hz' s i
    have h3 : (mat W s *ᵥ u) i - u i ∈ c.O := c.O.sub_mem (hWu s i) (hu i)
    have hmem := c.O.sub_mem (c.O.sub_mem h1 h2) h3
    refine (redL_eq_zero_iff c hmem).1 ?_
    have e := congrFun (hm s) i
    rw [redL_sub c (c.O.sub_mem h1 h2) h3, redL_sub c h1 h2, redL_sub c (hWu s i) (hu i), hWuR, hum]
    have e' : redL c ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
        redL c ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) = (resAct c W hO s m) i - m i := e
    rw [e', sub_self]
  choose o ho hoe using key
  refine ⟨(l : Qbar l)⁻¹ • (y - y' + u), ?_, fun s i => ?_⟩
  · obtain ⟨k, hk⟩ := hy
    obtain ⟨k', hk'⟩ := hy'
    refine ⟨k + k' + 1, fun i => ?_⟩
    have e : (l : Qbar l) ^ (k + k' + 1) * ((l : Qbar l)⁻¹ • (y - y' + u)) i =
        (l : Qbar l) ^ k' * ((l : Qbar l) ^ k * y i) - (l : Qbar l) ^ k * ((l : Qbar l) ^ k' * y' i)
          + (l : Qbar l) ^ (k + k') * u i := by
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      rw [pow_succ]; field_simp; ring
    rw [e]
    exact c.O.add_mem (c.O.sub_mem (c.O.mul_mem (natPow_mem c _) (hk i)) (c.O.mul_mem (natPow_mem c _) (hk' i)))
      (c.O.mul_mem (natPow_mem c _) (hu i))
  · have e : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i = o s i := by
      have h := hoe s i
      have e2 : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i =
          (l : Qbar l)⁻¹ * (((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
            ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i)) := by
        simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_sub, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        field_simp; ring
      rw [e2, h, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
    rw [e]; exact ho s i

end GlobalTheory.Ord2
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwCard

variable {l : ℕ} [Fact l.Prime]

theorem natCast_not_isUnit (c : Coef l) : ¬ IsUnit ((l : ℕ) : c.O) := by
  rintro ⟨u, hu⟩
  have h2 : ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ ≤ 1 := CupCob.norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h3 : (((u : c.Oˣ) : c.O) : Qbar l) * (((u⁻¹ : c.Oˣ) : c.O) : Qbar l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have hu' : (((u : c.Oˣ) : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu]; simp
  rw [hu'] at h3
  have hl : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℕ) : ℚ_[l]) := by simp
    rw [e, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have := congrArg norm h3
  rw [norm_mul, norm_one] at this
  have : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hl
  linarith

theorem exists_dvd_pow (c : Coef l) {d : c.O} (hd : d ≠ 0) : ∃ k : ℕ, d ∣ ((l : ℕ) : c.O) ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
  refine ⟨k, ?_⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : c.O => (x : Qbar l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : l.Prime).ne_zero h'
  have hl : ϖ ∣ ((l : ℕ) : c.O) := by
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
    rcases m with _ | m
    · exact absurd (hm.isUnit_iff.2 (by simp)) (natCast_not_isUnit c)
    · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
  exact hk.dvd.trans (pow_dvd_pow_of_dvd hl k)

end GlobalTheory.Ord2.GwCard

noncomputable section

namespace GlobalTheory.Ord2.GwCard

variable {l : ℕ} [Fact l.Prime]

theorem card_ker_eq_index {R : Type} [Ring R] [Finite R] (x : R) :
    Nat.card (AddMonoidHom.mulLeft x).ker = (AddMonoidHom.mulLeft x).range.index := by
  set f := AddMonoidHom.mulLeft x
  have h1 := AddSubgroup.card_mul_index f.ker
  have h2 := AddSubgroup.card_mul_index f.range
  have h3 : f.ker.index = Nat.card f.range := by
    rw [AddSubgroup.index]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  rw [h3] at h1
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have := h1.trans h2.symm
  rw [mul_comm] at this
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem exists_card_ker_pow_le (c : Coef l) (k : ℕ) :
    ∃ B : ℕ, ∀ n : ℕ, Nat.card (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).ker ≤ B := by
  obtain ⟨g, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  refine ⟨Nat.card (Fin g → ZMod (l ^ k)), fun n => ?_⟩
  rw [card_ker_eq_index, AddSubgroup.index]
  set H := (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).range
  refine Nat.card_le_card_of_surjective
    (fun z : Fin g → ZMod (l ^ k) => (QuotientAddGroup.mk (∑ i, (z i).val • red c n (s i)) : Qn c n ⧸ H)) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := red_surjective c n y
  have hx : x ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hx
  refine ⟨fun i => PadicInt.toZModPow k (a i), ?_⟩
  simp only

  rw [QuotientAddGroup.eq, ← ha, map_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[l], a i - (PadicInt.toZModPow k (a i)).val = (l : ℤ_[l]) ^ k * w := by
    have hm : a i - ((PadicInt.toZModPow k (a i)).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hm
    exact ⟨w, by rw [← hw, mul_comm]⟩
  refine ⟨red c n (w • s i), ?_⟩
  have e1 : (PadicInt.toZModPow k (a i)).val • red c n (s i) = red c n ((((PadicInt.toZModPow k (a i)).val : ℕ) : ℤ_[l]) • s i) := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [e1, ← map_neg, ← map_add (f := _), ← neg_smul, ← add_smul, neg_add_eq_sub, hw, mul_smul]
  simp only [AddMonoidHom.coe_mulLeft]
  rw [← map_natCast (red c n), ← map_pow, ← map_mul]
  congr 1
  rw [← Nat.cast_pow (α := ℤ_[l]), Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_pow]

end GlobalTheory.Ord2.GwCard

namespace GlobalTheory.Ord2.GwCard

theorem exists_card_H0_rhoS_le : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1),
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Nat.card (H0 (rhoS c n W hint S hN)) ≤ C := by
  intro l _ Ω _ _ _ e S A W hW c hint hN
  obtain ⟨φ, -, hφ⟩ := GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one (l := l) (Ω := Ω) (e := e) (S := S) (A := A) (W := W) hW
  let M : Matrix (Fin 2) (Fin 2) c.O := Matrix.of fun i j => ⟨mat W φ i j, hint φ i j⟩
  have hM : (c.O.val : c.O →+* Qbar l).mapMatrix (M - 1) = mat W φ - 1 := by
    rw [map_sub, map_one]
    congr 1
  have hd : (M - 1).det ≠ 0 := by
    intro h
    apply hφ
    rw [← hM, ← RingHom.map_det, h, map_zero]
  obtain ⟨k, y, hy⟩ := exists_dvd_pow c hd
  obtain ⟨B, hB⟩ := exists_card_ker_pow_le c k
  refine ⟨B ^ 2, fun n _ => ?_⟩
  set K := (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).ker
  have hred : (red c n).mapMatrix (M - 1) = matQ c n W hint φ - 1 := by
    rw [map_sub, map_one]
    congr 1
  have hmem : ∀ m ∈ H0 (rhoS c n W hint S hN), ∀ i, m i ∈ K := by
    intro m hm i
    have h1 : matQ c n W hint φ *ᵥ m = m := (mem_riemannRochSpace_iff_regularAt_everywhere _ m).1 hm (toGS Ω (S : Set Pl) φ)
    have h2 : (matQ c n W hint φ - 1) *ᵥ m = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    have h3 : (matQ c n W hint φ - 1).det • m = 0 := by
      rw [← Matrix.one_mulVec m, ← Matrix.smul_mulVec, ← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, h2,
        Matrix.mulVec_zero]
    have h4 : red c n (M - 1).det * m i = 0 := by
      rw [RingHom.map_det, hred]
      have := congrFun h3 i
      simpa using this
    show ((l : ℕ) : Qn c n) ^ k * m i = 0
    rw [← map_natCast (red c n), ← map_pow, hy, map_mul, mul_comm (red c n _), mul_assoc, h4, mul_zero]
  let F : H0 (rhoS c n W hint S hN) → (Fin 2 → K) := fun m i => ⟨m.1 i, hmem m.1 m.2 i⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  calc Nat.card (H0 (rhoS c n W hint S hN)) ≤ Nat.card (Fin 2 → K) := Nat.card_le_card_of_injective F hF
    _ = Nat.card K ^ 2 := by simp [Nat.card_fun]
    _ ≤ B ^ 2 := Nat.pow_le_pow_left (hB n) 2

end GlobalTheory.Ord2.GwCard
end
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.GwIneq.Arch

theorem isUnit_two (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (c : Coef l) (n : ℕ) : IsUnit (2 : Qn c n) := by
  have hodd : Odd (l ^ n) := ((Fact.out : l.Prime).odd_of_ne_two hl).pow
  obtain ⟨k, hk⟩ := hodd
  have h0 : ((l ^ n : ℕ) : Qn c n) = 0 := by
    have := kill c n (1 : Qn c n)
    rwa [nsmul_eq_mul, mul_one] at this
  have e : (2 : Qn c n) * ((k + 1 : ℕ) : Qn c n) = ((l ^ n : ℕ) : Qn c n) + 1 := by
    rw [hk]; push_cast; ring
  rw [h0, zero_add] at e
  exact isUnit_iff_exists_inv.mpr ⟨_, e⟩

theorem trace_eq_zero {R : Type} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R) (hXX : X * X = 1)
    (hdet : X.det = -1) : X.trace = 0 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two]
  have e00 := congrFun (congrFun hXX 0) 0
  have e10 := congrFun (congrFun hXX 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  linear_combination (X 0 0 - (X 0 0 + X 1 1)) * e00 + X 0 0 * hdet + X 0 1 * e10

theorem card_fixed_cc (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) (c : Coef l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) (n : ℕ) (w : InfinitePlace ℚ) (s : G ℚ Ω) (hs : IsCCAt w s) :
    Nat.card {v : Mn c n // matQ c n W hint s *ᵥ v = v} = Nat.card (Qn c n) := by
  obtain ⟨j, hj, -⟩ := hs
  have hss : s * s = 1 := by
    ext x
    apply j.injective
    show j (s (s x)) = j x
    rw [hj, hj]; simp
  have hXX : matQ c n W hint s * matQ c n W hint s = 1 := by
    rw [← matQ_mul, hss, matQ_one]
  have hd : (mat W s).det = -1 := by
    have h := hW.odd s ⟨j, hj⟩
    have h2 : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
      simp [dt, mat, Matrix.GeneralLinearGroup.val_det_apply]
    rw [← h2, h]; simp
  have hdet : (matQ c n W hint s).det = -1 := by
    rw [Matrix.det_fin_two] at hd ⊢
    simp only [matQ_apply]
    rw [← map_mul, ← map_mul, ← map_sub, ← map_one (red c n), ← map_neg]
    congr 1
    apply Subtype.ext
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_one]
    exact hd
  exact GlobalTheory.OddInvolution.card_fixed l (Qn c n) _ (isUnit_two l hW.l_odd c n) hXX hdet
    (trace_eq_zero _ hXX hdet)

theorem archimedean_h0_card_eq : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ cc : InfinitePlace ℚ → G ℚ Ω, (∀ w, w.IsReal → IsCCAt w (cc w)) → archH0Card S (rhoS c n W hint S hN) cc = Nat.card (Qn c n) := by
  intro l _ Ω _ _ _ e S A W hW c hint hN n _ cc hcc
  classical
  unfold archH0Card
  have hfil : (Finset.univ.filter (fun w : InfinitePlace ℚ => w.IsReal)) = {Rat.infinitePlace} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun h => h ▸ Rat.isReal_infinitePlace⟩
  rw [IsTotallyReal.nrComplexPlaces_eq_zero ℚ, pow_zero, mul_one]
  convert Finset.prod_singleton (fun w : InfinitePlace ℚ =>
    Nat.card {m : Mn c n // rhoS c n W hint S hN (toGS Ω _ (cc w)) m = m}) Rat.infinitePlace using 1
  · rw [hfil]
  · exact (card_fixed_cc l Ω e S A W hW c hint n _ _ (hcc _ Rat.isReal_infinitePlace)).symm

end GlobalTheory.Ord2.GwIneq.Arch
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Published UpperTheory.V.Af.Bc

namespace GlobalTheory.QuadNormChar

theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [hnorm w, hnorm (w.under (𝓞 K))]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem tendsto_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem fixes_or {F E Ω : Type} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosed Ω] [CharZero F] (h2 : Module.finrank F E = 2) (σ : G F Ω)
    (hσ : ∃ e : E, σ (algebraMap E Ω e) ≠ algebraMap E Ω e) (τ : G F Ω) :
    τ ∈ (res F Ω E).range ∨ σ⁻¹ * τ ∈ (res F Ω E).range := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hfix : ∀ ρ : G F Ω, (∀ e : E, ρ (algebraMap E Ω e) = algebraMap E Ω e) → ρ ∈ (res F Ω E).range :=
    fun ρ hρ => ⟨AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) hρ, AlgEquiv.ext fun _ => rfl⟩
  let f : G F Ω → (E →ₐ[F] Ω) := fun ρ => (ρ : Ω →ₐ[F] Ω).comp (IsScalarTower.toAlgHom F E Ω)
  have hf : ∀ ρ e, f ρ e = ρ (algebraMap E Ω e) := fun _ _ => rfl
  have hcard : Fintype.card (E →ₐ[F] Ω) = 2 := by rw [AlgHom.card, h2]
  obtain ⟨e₀, he₀⟩ := hσ
  have h01 : f 1 ≠ f σ := fun h => he₀ (by have := DFunLike.congr_fun h e₀; rw [hf, hf] at this; exact this.symm)
  by_cases h1 : f τ = f 1
  · left
    exact hfix τ fun e => by have := DFunLike.congr_fun h1 e; rw [hf, hf] at this; exact this
  · by_cases h2' : f τ = f σ
    · right
      refine hfix _ fun e => ?_
      have := DFunLike.congr_fun h2' e
      rw [hf, hf] at this
      rw [AlgEquiv.mul_apply, this]
      exact σ.symm_apply_apply _
    · exfalso
      have : 2 < Fintype.card (E →ₐ[F] Ω) :=
        Fintype.two_lt_card_iff.2 ⟨f 1, f σ, f τ, h01, Ne.symm h1, Ne.symm h2'⟩
      omega

end GlobalTheory.QuadNormChar
end
end
