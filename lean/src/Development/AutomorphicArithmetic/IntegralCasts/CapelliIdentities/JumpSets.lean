import Mathlib

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
open scoped Classical

namespace UpperTheory.Reformulated.B.JumpSetsAlt

noncomputable section

universe u_1

def HypOdd (q d : ℕ) : Prop :=
  q.Prime ∧ d.Prime ∧ q ≠ d ∧ q ≠ 2 ∧ d ≠ 2

variable {L : Type u_1} [Field L] [Algebra ℚ L]

def IsLayer (n q d : ℕ) {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) : Prop :=
  IsPrimitiveRoot ζ (2 ^ n) ∧ a ^ 2 = -(q : L) ∧ b ^ 2 = -(d : L) ∧ ℚ⟮ζ, a, b⟯ = ⊤

def E0 (a b : L) : IntermediateField ℚ L := ℚ⟮a, b⟯

def F1 (ζ : L) : IntermediateField ℚ L := ℚ⟮ζ + ζ⁻¹⟯

def hostE (ζ a b : L) : IntermediateField ℚ L := E0 a b ⊔ F1 ζ

theorem aux6 (L : Type) [Field L] [NumberField L] (ζ a b : L) :
    CharZero (hostE ζ a b) := inferInstance

theorem aux7 (L : Type) [Field L] [NumberField L] : IsScalarTower ℚ ℚ L := inferInstance

@[reducible] def G0 := ℤˣ × ℤˣ

@[reducible] def HGrp (e : ℕ) :=
  (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)

@[reducible] def GG (e : ℕ) := G0 × HGrp e

def sgn (σ : Gal(L/ℚ)) (x : L) : ℤˣ := if σ x = x then 1 else -1

theorem algebra_smulCommClass_complex (ζ a b : L) : a ∈ hostE ζ a b :=
  (le_sup_left : E0 a b ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))

def aE (ζ a b : L) : hostE ζ a b := ⟨a, algebra_smulCommClass_complex ζ a b⟩

theorem sign_action_map_comm (ζ a b : L) : b ∈ hostE ζ a b :=
  (le_sup_left : E0 a b ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))

def bE (ζ a b : L) : hostE ζ a b := ⟨b, sign_action_map_comm ζ a b⟩

theorem complex_normed_instance_compat (ζ a b : L) : ζ + ζ⁻¹ ∈ hostE ζ a b :=
  (le_sup_right : F1 ζ ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))

def thE (ζ a b : L) : hostE ζ a b := ⟨ζ + ζ⁻¹, complex_normed_instance_compat ζ a b⟩

def hcl (e : ℕ) (u : (ZMod (2 ^ (e + 2)))ˣ) : HGrp e := ↑u

/-- The action on the real cyclotomic generator determines the coset of its exponent. -/
def hPart (e : ℕ) (ζ a b : L) (σ : Gal(↥(hostE ζ a b)/ℚ)) : HGrp e :=
  if h : ∃ u : (ZMod (2 ^ (e + 2)))ˣ,
      (σ (thE ζ a b) : L) = ζ ^ (↑u : ZMod (2 ^ (e + 2))).val +
        ζ⁻¹ ^ (↑u : ZMod (2 ^ (e + 2))).val
  then hcl e (Classical.choose h)
  else 1

def galE (e : ℕ) (ζ a b : L) (σ : Gal(↥(hostE ζ a b)/ℚ)) : GG e :=
  ((sgn σ (aE ζ a b), sgn σ (bE ζ a b)), hPart e ζ a b σ)

private abbrev HostProperty
    (P : ∀ (e q d : ℕ) (L : Type) [Field L] [NumberField L] (ζ a b : L),
      IsLayer (e + 2) q d ζ a b → Prop) : Prop :=
  ∀ (e q d : ℕ), HypOdd q d → ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L)
    (h : IsLayer (e + 2) q d ζ a b), P e q d L ζ a b h

def HostGalois : Prop :=
  HostProperty fun e _ _ L _ _ ζ a b _ =>
    IsGalois ℚ (hostE ζ a b) ∧
    Module.finrank ℚ (hostE ζ a b) = 2 ^ (e + 2) ∧
    (∀ σ τ, galE e ζ a b (σ * τ) = galE e ζ a b σ * galE e ζ a b τ) ∧
    Function.Bijective (galE e ζ a b)

@[reducible] def GalL (n : ℕ) := (ZMod (2 ^ n))ˣ × ℤˣ × ℤˣ

def galMap {n : ℕ} {L : Type u_1} [Field L] [Algebra ℚ L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (a b : L) (σ : Gal(L/ℚ)) : GalL n :=
  (IsPrimitiveRoot.autToPow ℚ hζ σ, sgn σ a, sgn σ b)

theorem glEmbMat_one_eq_one (e q d : ℕ) (L : Type) [Field L] [NumberField L]
    (ζ a b : L) (h : IsLayer (e + 2) q d ζ a b) : IsPrimitiveRoot ζ (2 ^ (e + 2)) := h.1

def HostGalSpec : Prop :=
  HostProperty fun e q d L _ _ ζ a b h =>
    ∀ σ : Gal(↥(hostE ζ a b)/ℚ),
      (σ (aE ζ a b) : L) = ((galE e ζ a b σ).1.1 : ℤ) * a ∧
      (σ (bE ζ a b) : L) = ((galE e ζ a b σ).1.2 : ℤ) * b ∧
      (∀ u : (ZMod (2 ^ (e + 2)))ˣ, (galE e ζ a b σ).2 = hcl e u ↔
        (σ (thE ζ a b) : L) = ζ ^ (↑u : ZMod (2 ^ (e + 2))).val +
          ζ⁻¹ ^ (↑u : ZMod (2 ^ (e + 2))).val) ∧
      ∀ τ : Gal(L/ℚ),
        (∀ x : hostE ζ a b, (σ x : L) = τ (x : L)) →
        let g := galMap (glEmbMat_one_eq_one e q d L ζ a b h) a b τ
        galE e ζ a b σ = ((g.2.1, g.2.2), hcl e g.1)

def c0 : G0 := (-1, -1)

def cc (e : ℕ) : GG e := (c0, 1)

def HostConj : Prop :=
  HostProperty fun e _ _ L _ _ ζ a b _ =>
    NumberField.IsCMField (hostE ζ a b) ∧
    ∀ (φ : hostE ζ a b →+* ℂ) (σ : Gal(↥(hostE ζ a b)/ℚ)),
      (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galE e ζ a b σ = cc e

@[reducible] def hostF (ζ a b : L) : Subfield (hostE ζ a b) :=
  NumberField.maximalRealSubfield (hostE ζ a b)

def HostReal : Prop :=
  HostProperty fun e _ _ L _ _ ζ a b _ =>
    Module.finrank ℚ (hostF ζ a b) = 2 ^ (e + 1) ∧
    ∀ x : hostE ζ a b,
      (x ∈ hostF ζ a b ↔ ∀ σ : Gal(↥(hostE ζ a b)/ℚ), galE e ζ a b σ = cc e → σ x = x) ∧
      (x ∈ hostF ζ a b ↔ (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯)

theorem hostReal_of :
    HostGalois → HostGalSpec → HostConj → HostReal := by
  intro hG hS hC e q d hqd L _ _ ζ a b hL
  obtain ⟨hgal, hfin, hmul, hbij⟩ := hG e q d hqd L ζ a b hL
  obtain ⟨hCM, hconj⟩ := hC e q d hqd L ζ a b hL
  have hspec := hS e q d hqd L ζ a b hL
  obtain ⟨σ₀, hσ₀⟩ := hbij.2 (cc e)
  have hone : galE e ζ a b 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hfix : ∀ x : ↥(hostE ζ a b), x ∈ hostF ζ a b ↔ σ₀ x = x := by
    intro x
    rw [NumberField.mem_maximalRealSubfield_iff]
    constructor
    · intro hx
      obtain ⟨φ⟩ : Nonempty (↥(hostE ζ a b) →+* ℂ) := inferInstance
      apply φ.injective
      rw [(hconj φ σ₀).mpr hσ₀ x]
      exact hx φ
    · intro hx φ
      have h := (hconj φ σ₀).mpr hσ₀ x
      rw [hx] at h
      exact h.symm
  have hval : ((1 : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val = 1 := by
    haveI : Fact (1 < 2 ^ (e + 2)) := ⟨Nat.one_lt_two_pow (by omega)⟩
    rw [Units.val_one, ZMod.val_one]
  have hth : ∀ σ : Gal(↥(hostE ζ a b)/ℚ), (galE e ζ a b σ).2 = 1 ↔
      σ (thE ζ a b) = thE ζ a b := by
    intro σ
    have h := (hspec σ).2.2.1 1
    rw [hval, pow_one, pow_one] at h
    exact h.trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hab : ∀ σ : Gal(↥(hostE ζ a b)/ℚ),
      ((σ (aE ζ a b * bE ζ a b) : ↥(hostE ζ a b)) : L) =
        ((((galE e ζ a b σ).1.1 * (galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * (a * b) := by
    intro σ
    rw [map_mul, IntermediateField.coe_mul, (hspec σ).1, (hspec σ).2.1]
    push_cast
    ring
  have ha : a ≠ 0 := by
    rintro rfl
    have h := hL.2.1
    have hq : (q : L) ≠ 0 := Nat.cast_ne_zero.mpr hqd.1.ne_zero
    exact hq (by simpa using h)
  have hb : b ≠ 0 := by
    rintro rfl
    have h := hL.2.2.1
    have hd : (d : L) ≠ 0 := Nat.cast_ne_zero.mpr hqd.2.1.ne_zero
    exact hd (by simpa using h)
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · have h := Module.finrank_mul_finrank ℚ ↥(hostF ζ a b) ↥(hostE ζ a b)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two ↥(hostF ζ a b) ↥(hostE ζ a b),
      hfin, show 2 ^ (e + 2) = 2 ^ (e + 1) * 2 from pow_succ 2 (e + 1)] at h
    exact Nat.eq_of_mul_eq_mul_right two_pos h
  · rw [hfix]
    exact ⟨fun hx σ hσ => by rw [hbij.1 (hσ.trans hσ₀.symm)]; exact hx, fun hx => hx σ₀ hσ₀⟩
  · set K : IntermediateField ℚ ↥(hostE ζ a b) :=
      ℚ⟮aE ζ a b * bE ζ a b, thE ζ a b⟯ with hK
    have hlift : (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯ ↔ x ∈ K := by
      have h1 := IntermediateField.lift_adjoin ℚ (hostE ζ a b)
        {aE ζ a b * bE ζ a b, thE ζ a b}
      rw [Set.image_pair] at h1
      have h2 := IntermediateField.mem_lift (F := hostE ζ a b)
        (E := ℚ⟮aE ζ a b * bE ζ a b, thE ζ a b⟯) x
      exact (SetLike.ext_iff.mp h1 (x : L)).symm.trans h2
    rw [hlift, hfix]
    constructor
    · intro hx
      rw [← IsGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      have h1 := hab σ
      rw [hσ _ (IntermediateField.subset_adjoin ℚ _ (by simp))] at h1
      have h2 := (hth σ).mpr (hσ _ (IntermediateField.subset_adjoin ℚ _ (by simp)))
      have h3 : (galE e ζ a b σ).1.1 * (galE e ζ a b σ).1.2 = 1 := by
        have h4 : a * b = ((((galE e ζ a b σ).1.1 *
          (galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * (a * b) := h1
        have h5 := (right_eq_mul₀ (mul_ne_zero ha hb)).mp h4
        exact Units.ext (Int.cast_injective (α := L) (by simpa using h5))
      have h6 : galE e ζ a b σ = 1 ∨ galE e ζ a b σ = cc e := by
        generalize galE e ζ a b σ = g at h2 h3
        obtain ⟨⟨s, t⟩, u⟩ := g
        dsimp only at h2 h3
        subst h2
        rcases Int.units_eq_one_or s with rfl | rfl
        · left
          rw [one_mul] at h3
          rw [h3]
          rfl
        · right
          have : t = -1 := by
            rw [neg_mul, one_mul, neg_eq_iff_eq_neg] at h3
            exact h3
          rw [this]
          rfl
      rcases h6 with h6 | h6
      · rw [hbij.1 (h6.trans hone.symm)]
        rfl
      · rw [hbij.1 (h6.trans hσ₀.symm)]
        exact hx
    · intro hx
      have hle : K ≤ IntermediateField.fixedField (Subgroup.zpowers σ₀) := by
        rw [hK, IntermediateField.adjoin_le_iff]
        have hgen : ∀ y, σ₀ y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers σ₀) := by
          intro y hy
          rw [IntermediateField.mem_fixedField_iff, Subgroup.forall_mem_zpowers]
          exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := σ₀)).mpr hy
        rintro y (rfl | rfl)
        · refine hgen _ (Subtype.ext ?_)
          rw [hab σ₀, hσ₀]
          simp [cc, c0, aE, bE]
        · exact hgen _ ((hth σ₀).mp (by rw [hσ₀]; rfl))
      exact (IntermediateField.mem_fixedField_iff _ x).mp (hle hx) σ₀ (Subgroup.mem_zpowers σ₀)

end

end UpperTheory.Reformulated.B.JumpSetsAlt
