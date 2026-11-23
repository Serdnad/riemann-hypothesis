module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle371
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionAcrossDenseNonvanishing
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LerayInj

theorem peel (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ)
    (hH : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (N : ℤ) (hN : (n : ℤ) + 1 = N)
    (c : Cochain ((chains R).obj E) (res R F) N)
    (hc : ∀ (p q : ℤ) (hpq : p + N = q), p ≠ -N → c.v p q hpq = 0)
    (β₀ : Cochain ((chains R).obj E) (res R F) n) (h₀ : δ n N β₀ = c) :
    ∀ k : ℕ, k ≤ n → ∃ β : Cochain ((chains R).obj E) (res R F) n, δ n N β = c ∧
      ∀ (p q : ℤ) (hpq : p + n = q), -(k : ℤ) < p → β.v p q hpq = 0 := by
  obtain ⟨cl, -, hcl, hcl0, -⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  obtain ⟨-, -, -, -, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨β₀, h₀, fun p q hpq hp => (hpos E p (by omega)).eq_of_src _ _⟩
  | succ k ih =>
    intro hk
    obtain ⟨β, hβ, hv⟩ := ih (by omega)
    have hqk : (((n - k : ℕ) : ℤ)) = (n : ℤ) - k := by omega
    let t : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X ((n - k : ℕ) : ℤ) :=
      (chainsXIso R E k).inv ≫ β.v (-(k : ℤ)) ((n - k : ℕ) : ℤ) (by omega)
    have ht : t ≫ (res R F).d ((n - k : ℕ) : ℤ) (((n - k : ℕ) : ℤ) + 1) = 0 := by
      have e := Cochain.congr_v hβ (-(k : ℤ)) (((n - k : ℕ) : ℤ) + 1) (by omega)
      rw [δ_v n N hN β (-(k : ℤ)) (((n - k : ℕ) : ℤ) + 1) (by omega) ((n - k : ℕ) : ℤ) (-(k : ℤ) + 1)
        (by omega) rfl, hc _ _ _ (by omega), hv (-(k : ℤ) + 1) (((n - k : ℕ) : ℤ) + 1) (by omega) (by omega),
        comp_zero, smul_zero, add_zero] at e
      simp only [t, Category.assoc, e, comp_zero]
    have h0 : cl _ _ t ht = cl _ _ 0 zero_comp :=
      (hH k (n - k) (by omega) (by omega) _).trans (hcl0 _ _).symm
    obtain ⟨y, hy⟩ := ((hcl _ _ _ _ _ _).1 h0)
    rw [zero_add] at hy
    let γ : Cochain ((chains R).obj E) (res R F) ((n : ℤ) - 1) :=
      Cochain.single (p := -(k : ℤ)) (q := ((n - k : ℕ) : ℤ) - 1) ((chainsXIso R E k).hom ≫ y) ((n : ℤ) - 1)
    refine ⟨β - δ ((n : ℤ) - 1) n γ, ?_, ?_⟩
    · rw [δ_sub, δ_δ, sub_zero, hβ]
    · intro p q hpq hp
      rw [Cochain.sub_v, Cochain.δ_single _ ((n : ℤ) - 1) n (by omega) (-(k : ℤ) - 1) ((n - k : ℕ) : ℤ) (by omega) (by omega),
        Cochain.add_v, Cochain.units_smul_v]
      by_cases hpk : p = -(k : ℤ)
      · subst hpk
        obtain rfl : q = ((n - k : ℕ) : ℤ) := by omega
        rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), smul_zero, add_zero]
        have hb : β.v (-(k : ℤ)) ((n - k : ℕ) : ℤ) hpq = (chainsXIso R E k).hom ≫ t := by
          simp only [t, Iso.hom_inv_id_assoc]
        rw [hb, hy, Category.assoc, sub_self]
      · rw [hv p q hpq (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpk,
          Cochain.single_v_eq_zero _ _ _ _ _ (by omega), smul_zero, add_zero, sub_zero]

end GlobalTheory.EtC.LerayInj

namespace GlobalTheory.EtC

theorem leray_inj : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0) →
    (∀ s : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, IsCls (R := R) (E := E) (n := 0) s 0 → s = 0) ∧
    ∀ s : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ F, IsCls (R := R) (E := E) (n := n + 1) s 0 →
      ∃ t : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd (R := R) (E := E) (n := n) t = s := by
  intro R _ F E n hH
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  constructor
  · rintro s ⟨z, hz0, hz⟩
    rw [CohomologyClass.mk_eq_zero_iff] at hz0
    obtain ⟨m, hm, β, hβ⟩ := hz0
    have e := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) 0 (by simp)
    have h1 : β.v (-((0 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
    have h2 : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0 := (hpos E 1 (by norm_num)).eq_of_tgt _ _
    rw [δ_v m _ hm β _ 0 _ (-1) 1 (by omega) (by omega), h1, h2, zero_comp, zero_comp, smul_zero,
      add_zero] at e
    have e' : (↑z : Cochain ((chains R).obj E) (res R F) ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 (by simp) =
        (chainsXIso R E 0).hom ≫ s ≫ resι R F := by
      rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((0 : ℕ) : ℤ)) = z.1 from rfl, hz, Cochain.single_v]
    rw [e'] at e
    have e2 : s ≫ resι R F = 0 ≫ resι R F := by
      rw [zero_comp]
      exact (cancel_epi (chainsXIso R E 0).hom).1 (by rw [← e, comp_zero])
    exact (cancel_mono (resι R F)).1 e2
  · rintro s ⟨z, hz0, hz⟩
    rw [CohomologyClass.mk_eq_zero_iff] at hz0
    obtain ⟨m, hm, β₀, hβ₀⟩ := hz0
    obtain rfl : m = (n : ℤ) := by push_cast at hm; omega
    have hzv : ∀ (p q : ℤ) (hpq : p + ((n + 1 : ℕ) : ℤ) = q),
        (↑z : Cochain ((chains R).obj E) (res R F) ((n + 1 : ℕ) : ℤ)).v p q hpq =
          (Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
            ((chainsXIso R E (n + 1)).hom ≫ s ≫ resι R F) ((n + 1 : ℕ) : ℤ)).v p q hpq := by
      intro p q hpq
      rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((n + 1 : ℕ) : ℤ)) = z.1 from rfl, hz]
    obtain ⟨β, hβ, hv⟩ := LerayInj.peel R F E n hH ((n + 1 : ℕ) : ℤ) (by push_cast; rfl) z
      (fun p q hpq hp => by rw [hzv, Cochain.single_v_eq_zero _ _ _ _ _ hp]) β₀ hβ₀ n le_rfl

    let b := β.v (-(n : ℤ)) 0 (by omega)
    have hb : b ≫ (res R F).d 0 1 = 0 := by
      have e := Cochain.congr_v hβ (-(n : ℤ)) 1 (by push_cast; omega)
      rw [δ_v (n : ℤ) _ (by push_cast; rfl) β (-(n : ℤ)) 1 _ 0 (-(n : ℤ) + 1) (by omega) rfl,
        hv (-(n : ℤ) + 1) 1 (by omega) (by omega), comp_zero, smul_zero, add_zero, hzv,
        Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
      exact e
    haveI : Mono (ShortComplex.mk _ _ w).f := hmono
    let t' : ((chains R).obj E).X (-(n : ℤ)) ⟶ F := hex.lift b hb
    have ht' : t' ≫ resι R F = b := hex.lift_f b hb

    have e := Cochain.congr_v hβ (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    have h1 : β.v (-((n + 1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
    rw [δ_v (n : ℤ) _ (by push_cast; rfl) β _ 0 _ (-1) (-(n : ℤ)) (by omega) (by push_cast; omega), h1,
      zero_comp, zero_add, hzv, Cochain.single_v] at e
    rw [show β.v (-(n : ℤ)) 0 (by omega) = b from rfl, ← ht'] at e
    have hD : ((chainsN R).obj E).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i) :=
      AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _
    let D : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ (free R).obj (E.obj (op ⦋n⦌)) :=
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
    have hd : ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
        (chainsXIso R E (n + 1)).hom ≫ D ≫ (chainsXIso R E n).inv :=
      (HomologicalComplex.extend_d_eq _ _ rfl rfl).trans
        (congrArg (fun D' => (chainsXIso R E (n + 1)).hom ≫ D' ≫ (chainsXIso R E n).inv) hD)
    rw [hd] at e
    have hs : s = (((n + 1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E n).inv ≫ t') := by
      apply (cancel_epi (chainsXIso R E (n + 1)).hom).1
      apply (cancel_mono (resι R F)).1
      rw [Category.assoc, ← e]
      simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    refine ⟨(((n + 1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E n).inv ≫ t'), ?_⟩
    rw [hs]
    simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
      smul_smul, Category.assoc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]

end GlobalTheory.EtC
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.LeraySurj

variable {R : Type} [CommRing R]

theorem chains_d_eq (E : Spc) (n : ℕ) :
    ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (chainsXIso R E (n + 1)).hom ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫
        (chainsXIso R E n).inv := by
  have h2 : ((chainsN R).obj E).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _
  rw [← h2]
  exact HomologicalComplex.extend_d_eq _ _ rfl rfl

theorem cobd_eq (E : Spc) {F : Shv R} (n : ℕ) (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) :
    cobd s = (chainsXIso R E (n + 1)).inv ≫ ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (chainsXIso R E n).hom ≫ s := by
  rw [chains_d_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, Preadditive.sum_comp, Preadditive.zsmul_comp]
  rfl

theorem step (E : Spc) (F : Shv R) {n : ℤ} (z : Cocycle ((chains R).obj E) (res R F) n) (k : ℕ)
    (hv : ∀ p q (hpq : p + n = q), -(k : ℤ) < p → z.1.v p q hpq = 0)
    (hex : ∀ t : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X (n - k), t ≫ (res R F).d (n - k) (n - k + 1) = 0 →
      ∃ y : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X (n - k - 1), t = y ≫ (res R F).d (n - k - 1) (n - k)) :
    ∃ z' : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z' = CohomologyClass.mk z ∧
      ∀ p q (hpq : p + n = q), -((k + 1 : ℕ) : ℤ) < p → z'.1.v p q hpq = 0 := by
  have hcl : z.1.v (-(k : ℤ)) (n - k) (by omega) ≫ (res R F).d (n - k) (n - k + 1) = 0 := by
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) (-(k : ℤ)) (n - k + 1) (by omega)
    rw [δ_v n (n + 1) rfl _ _ _ _ (n - k) (-(k : ℤ) + 1) (by omega) rfl,
      hv (-(k : ℤ) + 1) _ _ (by omega)] at h
    simpa using h
  obtain ⟨y, hy⟩ := hex ((chainsXIso R E k).inv ≫ z.1.v (-(k : ℤ)) (n - k) (by omega))
    (by rw [Category.assoc, hcl, Limits.comp_zero])
  let β : Cochain ((chains R).obj E) (res R F) (n - 1) :=
    Cochain.single (p := -(k : ℤ)) (q := n - k - 1) ((chainsXIso R E k).hom ≫ y) (n - 1)
  let c : Cocycle ((chains R).obj E) (res R F) n := Cocycle.mk (δ (n - 1) n β) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - c, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨β, rfl⟩
  · intro p q hpq hp
    have hβ1 : β.v (p + 1) q (by omega) = 0 := Cochain.single_v_eq_zero _ _ _ _ _ (by omega)
    have hc : c.1.v p q hpq = β.v p (q - 1) (by omega) ≫ (res R F).d (q - 1) q := by
      change (δ (n - 1) n β).v p q hpq = _
      rw [δ_v (n - 1) n (by omega) _ _ _ _ (q - 1) (p + 1) rfl rfl, hβ1]
      simp
    rw [Cocycle.coe_sub, Cochain.sub_v, hc]
    rcases lt_or_eq_of_le (show -(k : ℤ) ≤ p by omega) with h | h
    · rw [hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp
    · subst h
      obtain rfl : q = n - k := by omega
      rw [Cochain.single_v]
      have hz : z.1.v (-(k : ℤ)) (n - k) hpq = (chainsXIso R E k).hom ≫ ((chainsXIso R E k).inv ≫ z.1.v (-(k : ℤ)) (n - k) hpq) := by
        rw [Iso.hom_inv_id_assoc]
      rw [hz, hy]
      simp

theorem exact_of_vanish (F : Shv R) (P : PSh) (m : ℤ) (h0 : ∀ y : H R (disc.obj P) F m, y = 0)
    (t : (free R).obj P ⟶ (res R F).X m) (ht : t ≫ (res R F).d m (m + 1) = 0) :
    ∃ y : (free R).obj P ⟶ (res R F).X (m - 1), t = y ≫ (res R F).d (m - 1) m := by
  obtain ⟨cl, -, hinj, hzero, -⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  have h : cl P m t ht = cl P m 0 Limits.zero_comp := by rw [hzero]; exact h0 _
  obtain ⟨y, hy⟩ := (hinj P m t ht 0 Limits.zero_comp).1 h
  exact ⟨y, by rw [hy, zero_add]⟩

theorem reduce (F : Shv R) (E : Spc) (n : ℕ)
    (hyp : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (x : H R E F n) (j : ℕ) (hj : j ≤ n) :
    ∃ z : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z = x ∧
      ∀ (p q : ℤ) (hpq : p + n = q), -(j : ℤ) < p → z.1.v p q hpq = 0 := by
  induction j with
  | zero =>
    obtain ⟨z, rfl⟩ := x.mk_surjective
    refine ⟨z, rfl, fun p q hpq hp => ?_⟩
    exact ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F).2.2.2.2.2 E p (by omega)).eq_of_src _ _
  | succ j ih =>
    obtain ⟨z, hz, hv⟩ := ih (by omega)
    obtain ⟨z', hz', hv'⟩ := step E F z j hv (fun t ht => by
      have hm : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
      have h0 := hyp j (n - j) (by omega) (by omega)
      rw [hm] at h0
      have := exact_of_vanish F _ ((n : ℤ) - j) h0 t ht
      exact this)
    exact ⟨z', hz'.trans hz, hv'⟩

theorem main (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ)
    (hyp : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (x : H R E F n) : ∃ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 ∧ IsCls s x := by
  obtain ⟨z, rfl, hv⟩ := reduce F E n hyp x n le_rfl
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, -⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  have hcl : z.1.v (-(n : ℤ)) 0 (by omega) ≫ (res R F).d 0 1 = 0 := by
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-(n : ℤ)) 1 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ 0 (-(n : ℤ) + 1) (by omega) rfl,
      hv (-(n : ℤ) + 1) _ _ (by omega)] at h
    simpa using h
  obtain ⟨u, hu⟩ := hex.lift' ((chainsXIso R E n).inv ≫ z.1.v (-(n : ℤ)) 0 (by omega))
    (by change _ ≫ (res R F).d 0 1 = 0; rw [Category.assoc, hcl, Limits.comp_zero])
  change u ≫ resι R F = _ at hu
  have hz : z.1.v (-(n : ℤ)) 0 (by omega) = (chainsXIso R E n).hom ≫ u ≫ resι R F := by
    rw [hu, Iso.hom_inv_id_assoc]
  refine ⟨u, ?_, z, rfl, ?_⟩
  · rw [cobd_eq]
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ (-1) (-(n : ℤ)) (by omega) (by omega), hz,
      (hneg (-1) (by omega)).eq_of_tgt (z.1.v _ (-1) _) 0] at h
    simp only [Limits.zero_comp, zero_add, Cochain.zero_v] at h
    have h' := (smul_eq_zero_iff_eq _).1 h
    have h'' : (((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (chainsXIso R E n).hom ≫ u) ≫ resι R F =
        0 ≫ resι R F := by
      simpa [Category.assoc] using h'
    rw [cancel_mono] at h''
    rw [h'', Limits.comp_zero]
  · refine Cochain.ext _ _ (fun p q hpq => ?_)
    rcases lt_trichotomy p (-(n : ℤ)) with h | h | h
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · subst h
      obtain rfl : q = 0 := by omega
      rw [Cochain.single_v, hz]
    · rw [hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]

end GlobalTheory.EtC.LeraySurj

theorem GlobalTheory.EtC.leray_surj : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0) → ∀ x : H R E F n, ∃ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 ∧ IsCls s x :=
  fun R _ F E n hyp x => GlobalTheory.EtC.LeraySurj.main R F E n hyp x
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ContAlg

theorem cohomology_filteredColimit_of_descent :
    ∀ (M : CommRingCat.{0} ⥤ AbCx) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∀ n, WExact (term M n) (coAug g)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  intro M F0 ι hF0 hι hneg hloc hdesc
  obtain ⟨N, ε, hN, hiso⟩ := GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType AbCx M
  have hterm := (GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN).1
  have hcontN := (GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN).2
  haveI : EtFF.IsStableUnderComposition := GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties.1.1.toIsStableUnderComposition

  have hNneg : ∀ n : ℤ, n < 0 → ∀ A, IsZero ((N.obj A).X n) := by
    intro n hn A
    obtain ⟨J, _, _, D, ιA, ⟨hc⟩, hft⟩ := GlobalTheory.T.exists_filteredColimit_finiteType_int_rings A
    have hel := ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} (term N n)).1 (hterm n)) J D _ hc
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    constructor
    intro x y
    suffices h : ∀ x : (N.obj A).X n, x = 0 by rw [h x, h y]
    intro x
    obtain ⟨j, w, rfl⟩ := hel.1 x
    have hz : IsZero ((N.obj (D.obj j)).X n) := by
      haveI := hiso (D.obj j) (hft j)
      have e : (N.obj (D.obj j)).X n ≅ (M.obj (D.obj j)).X n :=
        (HomologicalComplex.eval _ _ n).mapIso (asIso (ε.app (D.obj j)))
      exact (hneg n hn (D.obj j)).of_iso e
    have : w = 0 := by
      rw [AddCommGrpCat.isZero_iff_subsingleton] at hz
      exact @Subsingleton.elim _ hz _ _
    subst this
    exact map_zero _
  have hqis := GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent CommRingCat.{0} EtFF N M ε
    ⟨0, fun n hn U => ⟨hNneg n hn U, hneg n hn U⟩⟩
    (GlobalTheory.T.coveringsRefine_of_cechConerve_property CommRingCat.{0} EtFF _ (fun A B g hg n =>
      ⟨GlobalTheory.T.coalternatingExact_of_finiteType_iso_filteredColimits (term N n) (term M n) (Functor.whiskerRight ε (HomologicalComplex.eval _ _ n)) (hterm n)
        (fun A' hA' => by
          haveI := hiso A' hA'
          change IsIso ((HomologicalComplex.eval _ _ n).map (ε.app A'))
          infer_instance)
        (fun A' B' g' hg' => hdesc A' B' g' hg' n) A B g hg,
       hdesc A B g hg n⟩))
    (GlobalTheory.T.locallySurjective_of_iso_on_finiteType_approximation N M ε F0 ι hF0 hι hneg hloc hN hiso)
    (GlobalTheory.T.locallyInjective_of_iso_on_finiteType_rings N M ε F0 ι hF0 hι hneg hloc hN hiso)
  exact GlobalTheory.T.filteredColimitCohomology_transport_quasiIso N M ε hqis hcontN

end GlobalTheory.EtC.ContAlg
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_isSec_extension_of_dense_nz_of_l2 : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ la : La) (τ F : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.IsSecOn la (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq la F y) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec la G ∧ ∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y := by
  first | exact @GlobalTheory.OTY.l2_extension_nz | exact GlobalTheory.OTY.l2_extension_nz | (intros; apply GlobalTheory.OTY.l2_extension_nz <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_comap_loc : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (omB k K (rB k K x I) p).comap (e.restrictScalars k) = (Submodule.span (rA k x I) ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)).restrictScalars k := by
  intro k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e I i hi
  have hloc := GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hx I i hi p
  ext w
  rw [Submodule.restrictScalars_mem, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  constructor
  · intro hw
    obtain ⟨N, hN⟩ := (hloc _).1 hw
    have hg : (∏ j ∈ I, x i / x j) ^ N ∈ rA k x I :=
      Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun j hj =>
        Algebra.subset_adjoin (s := {y | ∃ i ∈ I, ∃ j, y = x j / x i}) ⟨j, hj, i, rfl⟩) N
    have hfg : (∏ j ∈ I, x i / x j) ^ N * (∏ j ∈ I, x j / x i) ^ N = 1 := by
      rw [← mul_pow, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_pow]
      intro j _
      have h1 := hx.pd.ne i
      have h2 := hx.pd.ne j
      field_simp
    have hm : (∏ j ∈ I, x j / x i) ^ N • w ∈
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W) := by
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        ← algebraMap_smul K, map_smul, map_pow]
      exact hN
    have := (Submodule.span (rA k x I) _).smul_mem ⟨_, hg⟩ (Submodule.subset_span hm)
    rwa [Subalgebra.smul_def, smul_smul, hfg, one_smul] at this
  · intro hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      refine (hloc _).2 ⟨0, ?_⟩
      rw [pow_zero, one_smul]
      exact hz
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [Subalgebra.smul_def, ← algebraMap_smul K, map_smul]
      refine ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p p).2.1 _ ha).2.2.2 _ ?_
      exact (integralClosure (rA k x I) K).algebraMap_mem r

end GlobalTheory.PD
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem parFun_mem : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ ∈ SB (Matrix α ν E), parFun c ψ χ Q (mat c p) φ ∈ SB (Matrix α ν E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ _ _ χ _ _ p hp φ hφ
  obtain ⟨-, hring, -, -, hc, -, htr, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨β, hβ, -, -, -, hform⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨hinv, -, -⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  haveI := GlobalTheory.WeilM.nonarch_field F
  set a := (mat c p).toBlocks₁₁ with ha
  set b := (mat c p).toBlocks₁₂ with hb
  set d := (((mat c p).toBlocks₂₂).map c)ᵀ with hd
  have hinv' : d * a = 1 := mul_eq_one_comm.mp hinv
  have hca : Continuous fun x : Matrix α ν E => x * a := continuous_id.matrix_mul continuous_const
  have hcb : Continuous fun x : Matrix α ν E => x * b := continuous_id.matrix_mul continuous_const
  have hcd : Continuous fun x : Matrix α ν E => x * d := continuous_id.matrix_mul continuous_const
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun x => x * a
      invFun := fun x => x * d
      left_inv := fun x => by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]
      continuous_toFun := hca
      continuous_invFun := hcd }
  have hpr : Continuous fun x : Matrix α ν E => (2⁻¹ : F) * pr c Q (x * a) (x * b) := by
    refine continuous_const.mul ?_
    have : (fun x : Matrix α ν E => pr c Q (x * a) (x * b)) = fun x =>
        2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * ((x * a) * ((x * b).map c)ᵀ))) := by
      funext x; rw [← hβ, hform]
    rw [this]
    exact continuous_const.mul (htr.comp (continuous_const.matrix_mul
      (hca.matrix_mul (hcb.matrix_map hc).matrix_transpose)).matrix_trace)
  have h1 := (GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous hpr
  have h2 : IsLocallyConstant (φ ∘ fun x : Matrix α ν E => x * a) := hφ.1.comp_continuous hca
  have h3 : HasCompactSupport (φ ∘ e) := hφ.2.comp_homeomorph e
  refine ⟨(IsLocallyConstant.const _).mul (h1.mul h2), ?_⟩
  exact HasCompactSupport.mul_left (HasCompactSupport.mul_left h3)

end GlobalTheory.KSp
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_frobenius_hodgeTateLattice_ainf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ φ : ∀ G : PDivGroup p O, latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G, (∀ G y t, (φ G y).1 t = WittVector.frobenius (y.1 t)) ∧ ∀ G m, ∃ n, φ G n = (WittVector.frobenius (xi ε) : Ainf p O) • m := by
  first | exact @GlobalTheory.PDivLat.exists_frobenius_latt | exact GlobalTheory.PDivLat.exists_frobenius_latt | (intros; apply GlobalTheory.PDivLat.exists_frobenius_latt <;> assumption)
end
