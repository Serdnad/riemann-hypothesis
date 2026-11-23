module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle183
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle175
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjectiveOfFg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle033
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle274
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
import Mathlib.Topology.Sheaves.Init
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphLabelOps

variable {G : Type} [Group G]

def SameDC (K : Subgroup G) (a b : G) : Prop := ∃ k₁ ∈ K, ∃ k₂ ∈ K, b = k₁ * a * k₂

theorem SameDC.refl (K : Subgroup G) (a : G) : SameDC K a a :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem SameDC.symm {K : Subgroup G} {a b : G} (h : SameDC K a b) : SameDC K b a := by
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h
  exact ⟨k₁⁻¹, inv_mem h₁, k₂⁻¹, inv_mem h₂, by group⟩

theorem SameDC.trans {K : Subgroup G} {a b c : G} (h : SameDC K a b) (h' : SameDC K b c) : SameDC K a c := by
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h
  obtain ⟨l₁, i₁, l₂, i₂, rfl⟩ := h'
  exact ⟨l₁ * k₁, mul_mem i₁ h₁, k₂ * l₂, mul_mem h₂ i₂, by group⟩

theorem exists_dc_choice (K : Subgroup G) (a : G) :
    ∃ r : G → G, r a = a ∧ (∀ z, SameDC K z (r z)) ∧ ∀ b c, SameDC K b c → r b = r c := by
  classical
  let s : Setoid G := ⟨SameDC K, ⟨SameDC.refl K, SameDC.symm, SameDC.trans⟩⟩
  refine ⟨fun z => if SameDC K a z then a else (Quotient.mk s z).out, ?_, fun z => ?_, fun b c hbc => ?_⟩
  · simp [SameDC.refl K a]
  · by_cases hz : SameDC K a z
    · simpa [hz] using hz.symm
    · simp only [hz, if_false]
      exact SameDC.symm (Quotient.exact (s := s) (Quotient.out_eq (Quotient.mk s z)))
  · by_cases hb : SameDC K a b
    · simp [hb, hb.trans hbc]
    · have hc : ¬ SameDC K a c := fun h => hb (h.trans hbc.symm)
      simp only [hb, hc, if_false]
      rw [Quotient.sound (s := s) hbc]

theorem Reps.uniq {K : Subgroup G} {g a b c x : G} {R : Finset G} (h : Reps K g R) (ha : a ∈ R) (hb : b ∈ R)
    (e₁ : c⁻¹ * (x * a) ∈ K) (e₂ : c⁻¹ * (x * b) ∈ K) : a = b := by
  refine (h.2 b (h.1 b hb)).unique ⟨ha, ?_⟩ ⟨hb, by rw [inv_mul_cancel]; exact one_mem _⟩
  have := mul_mem (inv_mem e₁) e₂
  convert this using 1
  group

theorem Reps.exists_left {K : Subgroup G} {g γ k : G} {R R' : Finset G} (h : Reps K g R) (h' : Reps K g R')
    (hγ : γ ∈ R) (hk : k ∈ K) : ∃ δ ∈ R', δ⁻¹ * (k * γ) ∈ K := by
  obtain ⟨k₁, h₁, k₂, h₂, e⟩ := h.1 γ hγ
  obtain ⟨δ, ⟨hδ, hd⟩, -⟩ := h'.2 (k * γ) ⟨k * k₁, mul_mem hk h₁, k₂, h₂, by rw [e]; group⟩
  exact ⟨δ, hδ, hd⟩


open Classical in
noncomputable def pairMult (K : Subgroup G) (R₁ R₂ : Finset G) (y : G) : ℕ :=
  ((R₁ ×ˢ R₂).filter fun p => (p.1 * p.2)⁻¹ * y ∈ K).card

theorem pairMult_le {K : Subgroup G} {g h k : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    (hk : k ∈ K) (y : G) : pairMult K R₁ R₂ y ≤ pairMult K R₁ R₂ (k * y) := by
  classical
  have ex1 : ∀ γ, γ ∈ R₁ → ∃ δ, δ ∈ R₁ ∧ δ⁻¹ * (k * γ) ∈ K := fun γ hγ =>
    (h₁.exists_left h₁ hγ hk).imp fun _ h => ⟨h.1, h.2⟩
  have ex2 : ∀ κ γ, κ ∈ K → γ ∈ R₂ → ∃ δ, δ ∈ R₂ ∧ δ⁻¹ * (κ * γ) ∈ K := fun κ γ hκ hγ =>
    (h₂.exists_left h₂ hγ hκ).imp fun _ h => ⟨h.1, h.2⟩
  choose! a ha using ex1
  choose! b hb using ex2
  unfold pairMult
  refine Finset.card_le_card_of_injOn (fun p => (a p.1, b ((a p.1)⁻¹ * (k * p.1)) p.2)) ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp'.1
    have hκ := (ha _ p1).2
    have hb' := hb _ _ hκ p2
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨(ha _ p1).1, hb'.1⟩, ?_⟩)
    have := mul_mem hb'.2 hp'.2
    convert this using 1
    simp only
    group
  · intro p hp q hq e
    have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    have hq' := Finset.mem_filter.1 (Finset.mem_coe.1 hq)
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp'.1
    obtain ⟨q1, q2⟩ := Finset.mem_product.1 hq'.1
    have e1 : a p.1 = a q.1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only at e2
    have f1 : p.1 = q.1 := h₁.uniq p1 q1 (ha _ p1).2 (e1 ▸ (ha _ q1).2)
    rw [e1, f1] at e2
    have hκ := (ha _ q1).2
    have f2 : p.2 = q.2 := h₂.uniq p2 q2 (hb _ _ hκ p2).2 (e2 ▸ (hb _ _ hκ q2).2)
    exact Prod.ext f1 f2

theorem pairMult_mul_left {K : Subgroup G} {g h k : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    (hk : k ∈ K) (y : G) : pairMult K R₁ R₂ (k * y) = pairMult K R₁ R₂ y := by
  refine le_antisymm ?_ (pairMult_le h₁ h₂ hk y)
  simpa using pairMult_le h₁ h₂ (inv_mem hk) (k * y)

theorem pairMult_mul_right {K : Subgroup G} {k : G} (R₁ R₂ : Finset G) (hk : k ∈ K) (y : G) :
    pairMult K R₁ R₂ (y * k) = pairMult K R₁ R₂ y := by
  classical
  unfold pairMult
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  rw [← mul_assoc, Subgroup.mul_mem_cancel_right _ hk]

theorem pairMult_dc {K : Subgroup G} {g h a b : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    (e : SameDC K a b) : pairMult K R₁ R₂ b = pairMult K R₁ R₂ a := by
  obtain ⟨k₁, i₁, k₂, i₂, rfl⟩ := e
  rw [pairMult_mul_right _ _ i₂, pairMult_mul_left h₁ h₂ i₁]

open Classical in
theorem sum_single_of_dc {K : Subgroup G} {T : Finset G} {S : G → Finset G} (hS : ∀ x ∈ T, Reps K x (S x))
    (hT : ∀ x ∈ T, ∀ y ∈ T, SameDC K x y → x = y) {M : Type} [AddCommMonoid M] (F : G → M)
    (hF : ∀ x, ∀ l ∈ K, F (x * l) = F x) {z x₀ : G} (hx₀ : x₀ ∈ T) (hz : SameDC K x₀ z) :
    F z = ∑ x ∈ T, ∑ y ∈ S x, if y⁻¹ * z ∈ K then F y else 0 := by
  obtain ⟨y₀, ⟨hy₀, e⟩, hu⟩ := (hS x₀ hx₀).2 z hz
  rw [Finset.sum_eq_single x₀ ?_ (fun h => absurd hx₀ h), Finset.sum_eq_single y₀ ?_ (fun h => absurd hy₀ h),
    if_pos e]
  · have := hF y₀ _ e
    rwa [mul_inv_cancel_left] at this
  · intro y hy hne
    exact if_neg fun h => hne (hu y ⟨hy, h⟩)
  · intro x hx hne
    refine Finset.sum_eq_zero fun y hy => if_neg fun h => hne ?_
    have hxy : SameDC K x y := (hS x hx).1 y hy
    have hyz : SameDC K y z := ⟨1, one_mem _, _, h, by group⟩
    exact hT x hx x₀ hx₀ ((hxy.trans hyz).trans hz.symm)

theorem sum_pairs_eq {K : Subgroup G} {g h : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    {T : Finset G} {S : G → Finset G} (hS : ∀ x ∈ T, Reps K x (S x))
    (hT : ∀ x ∈ T, ∀ y ∈ T, SameDC K x y → x = y)
    (hcov : ∀ p ∈ R₁ ×ˢ R₂, ∃ x ∈ T, SameDC K x (p.1 * p.2))
    {M : Type} [AddCommMonoid M] (F : G → M) (hF : ∀ x, ∀ l ∈ K, F (x * l) = F x) :
    ∑ γ ∈ R₁, ∑ γ' ∈ R₂, F (γ * γ') = ∑ x ∈ T, pairMult K R₁ R₂ x • ∑ y ∈ S x, F y := by
  classical
  rw [← Finset.sum_product' (f := fun γ γ' => F (γ * γ'))]
  have e1 : ∀ p ∈ R₁ ×ˢ R₂, F (p.1 * p.2) =
      ∑ x ∈ T, ∑ y ∈ S x, if y⁻¹ * (p.1 * p.2) ∈ K then F y else 0 := fun p hp => by
    obtain ⟨x, hx, hd⟩ := hcov p hp
    convert sum_single_of_dc hS hT F hF hx hd
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [← Finset.sum_filter, Finset.sum_const, ← pairMult_dc h₁ h₂ ((hS x hx).1 y hy : SameDC K x y)]
  unfold pairMult
  congr 2
  refine Finset.filter_congr fun p _ => ?_
  have e : (p.1 * p.2)⁻¹ * y = (y⁻¹ * (p.1 * p.2))⁻¹ := by group
  rw [e, inv_mem_iff]

theorem reps_mul_decomp : ∀ {G : Type} [Group G] (K : Subgroup G) (g h : G) (R₁ R₂ : Finset G), GlobalTheory.SphLabelOps.Reps K g R₁ → GlobalTheory.SphLabelOps.Reps K h R₂ → ∃ (T : Finset G) (m : G → ℕ), g * h ∈ T ∧ (∀ x ∈ T, 0 < m x ∧ ∃ γ ∈ R₁, ∃ γ' ∈ R₂, ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * (γ * γ') * k₂) ∧ (∀ x ∈ T, ∀ y ∈ T, (∃ k₁ ∈ K, ∃ k₂ ∈ K, y = k₁ * x * k₂) → x = y) ∧ ∀ (S : G → Finset G), (∀ x ∈ T, GlobalTheory.SphLabelOps.Reps K x (S x)) → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : G →* Module.End ℂ M) (u : M), (∀ k ∈ K, π k u = u) → ∑ γ ∈ R₁, ∑ γ' ∈ R₂, π (γ * γ') u = ∑ x ∈ T, m x • ∑ y ∈ S x, π y u := by
  intro G _ K g h R₁ R₂ h₁ h₂
  classical
  obtain ⟨r, r0, r1, r2⟩ := exists_dc_choice K (g * h)
  have rr : ∀ z, r (r z) = r z := fun z => (r2 _ _ (r1 z)).symm
  have fixT : ∀ x ∈ (R₁ ×ˢ R₂).image (fun p => r (p.1 * p.2)), r x = x := fun x hx => by
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
    exact rr _
  have hT : ∀ x ∈ (R₁ ×ˢ R₂).image (fun p => r (p.1 * p.2)),
      ∀ y ∈ (R₁ ×ˢ R₂).image (fun p => r (p.1 * p.2)), SameDC K x y → x = y := fun x hx y hy e => by
    rw [← fixT x hx, ← fixT y hy]
    exact r2 _ _ e
  refine ⟨(R₁ ×ˢ R₂).image fun p => r (p.1 * p.2), pairMult K R₁ R₂, ?_, fun x hx => ?_, hT,
    fun S hS M _ _ π u hu => ?_⟩
  · obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h₁.2 g (SameDC.refl K g)
    obtain ⟨γ', ⟨hγ', e'⟩, -⟩ := h₂.2 (γ⁻¹ * g * h) ⟨_, e, 1, one_mem _, by group⟩
    refine Finset.mem_image.2 ⟨(γ, γ'), Finset.mem_product.2 ⟨hγ, hγ'⟩, ?_⟩
    have hd : SameDC K (γ * γ') (g * h) := ⟨1, one_mem _, _, e', by group⟩
    exact (r2 _ _ hd).trans r0
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp
    refine ⟨?_, p.1, p1, p.2, p2, r1 _⟩
    rw [pairMult_dc h₁ h₂ (r1 _)]
    refine Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨hp, ?_⟩⟩
    rw [inv_mul_cancel]
    exact one_mem _
  · refine sum_pairs_eq h₁ h₂ hS hT (fun p hp => ⟨_, Finset.mem_image_of_mem _ hp, (r1 _).symm⟩)
      (fun z => π z u) fun x l hl => ?_
    rw [map_mul, Module.End.mul_apply, hu l hl]

end GlobalTheory.SphLabelOps
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitPrimeChart

theorem entries_of_stab {R K : Type} [CommRing R] [CommRing K] {n : ℕ} {Λ : (Fin n → R) → Prop} {O : R → Prop}
    {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R) (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1)
    (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {A B C : Matrix (Fin n) (Fin n) R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B *ᵥ z)
    (hA : ∀ y, Λ y → Λ (A *ᵥ y)) (hCB : C.map φ * B.map φ = 1) :
    ∀ i j, (C.map φ * A.map φ * B.map φ) i j ∈ OK := by
  intro i j
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  let z : Fin n → R := fun k => s ((Pi.single j (1 : K) : Fin n → K) k)
  have hz : ∀ k, O (z k) := fun k => hO' _ (by
    by_cases hk : k = j
    · subst hk; simp [one_mem]
    · simp [hk, zero_mem])
  have hz' : φ ∘ z = Pi.single j 1 := funext fun k => hs _
  obtain ⟨z', hz1, hz2⟩ := h2 _ (hA _ (h1 z hz))
  have e1 : A.map φ *ᵥ (B.map φ *ᵥ Pi.single j 1) = B.map φ *ᵥ (φ ∘ z') := by
    have := congrArg (φ ∘ ·) hz2
    simp only [sm] at this
    rw [mv, sm, mv, hz', mv] at this
    exact this
  have e2 : (C.map φ * A.map φ * B.map φ) i j = (φ ∘ z') i := by
    have : (C.map φ * A.map φ * B.map φ) *ᵥ Pi.single j 1 = φ ∘ z' := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]
    have := congrFun this i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  rw [e2]
  exact hO _ (hz1 i)

theorem conj_mul_eq_one {K : Type} [CommRing K] {n : ℕ} {X Y Z W : Matrix (Fin n) (Fin n) K} (h1 : Y * X = 1)
    (h2 : X * Y = 1) (h3 : Z * W = 1) : X * Z * Y * (X * W * Y) = 1 := by
  calc X * Z * Y * (X * W * Y) = X * (Z * ((Y * X) * (W * Y))) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.one_mul, ← Matrix.mul_assoc Z, h3, Matrix.one_mul, h2]

theorem conj_conj {K : Type} [CommRing K] {n : ℕ} {X Y Z : Matrix (Fin n) (Fin n) K} (h1 : Y * X = 1) :
    Y * (X * Z * Y) * X = Z := by
  calc Y * (X * Z * Y) * X = (Y * X) * Z * (Y * X) := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [h1, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.SplitPrimeChart

namespace GlobalTheory.SplitPrimeChart

open Formalism.L2.NTheta



theorem exists_chart : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E), (∀ M : GL (Fin V.rank) (P.adicCompletion D.host.E), ∃ g, Formalism.L2.Theta.SuppAt e V g ∧ ρ g = M) ∧ (∀ k ∈ KsphC V ∅, ρ k ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P)) ∧ ∀ (g : GA D V) (a : Fin V.rank → ℤ), ∀ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∀ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) = (k₁ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) * Formalism.UG.diagPow D.host.E P (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) a * (k₂ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) → DivAt V e (ϖ : D.host.E) (List.ofFn a) g := by
  intro D V P e he ϖ h1 h2
  have hee' : e * e = e := he.1.1
  have ht := GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (P := P) (f := e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨φ, s, hs, hε, hφ, hO, hO', hinc⟩ := GlobalTheory.SphLabelOps.exists_component hee' ht
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis V hee' ht
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, hee']
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * Y) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) → X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
      one_mul] at this
  let b : GL (Fin V.rank) (P.adicCompletion D.host.E) := ⟨B.map φ, C.map φ, mp _ _ c1, mp _ _ c2⟩
  let ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E) :=
    (MulAut.conj b⁻¹).toMonoidHom.comp ((Formalism.UG.bc φ).comp (finHom V))
  have hρ : ∀ g, ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
      C.map φ * (finMat D.sp.cm.sig V.gram g).map φ * B.map φ := fun g => by
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul]
    rfl
  refine ⟨ρ, fun M => ?_, fun k hk => ?_, fun g a k₁ hk₁ k₂ hk₂ hg => ?_⟩
  · have hsM : ∀ N : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E), (N.map s).map φ = N :=
      fun N => Matrix.ext fun i j => hs _
    have hm : finPart D e • ((B * (M : Matrix _ _ _).map s * C) * (B * ((M⁻¹ : GL _ _) : Matrix _ _ _).map s * C)) =
        finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      apply hφ
      have : ((B * (M : Matrix _ _ _).map s * C) * (B * ((M⁻¹ : GL _ _) : Matrix _ _ _).map s * C)).map φ =
          (1 : Matrix (Fin V.rank) (Fin V.rank) _).map φ := by
        simp only [Matrix.map_mul]
        rw [Matrix.map_one φ (map_zero φ) (map_one φ), hsM, hsM]
        exact conj_mul_eq_one (mp _ _ c2) (mp _ _ c1) (Units.mul_inv M)
      exact congrFun (congrFun this i) j
    obtain ⟨g, hgs, hg⟩ := GlobalTheory.SplitLift.split_lift V e he.1 _ _ hm
    refine ⟨g, hgs, Units.ext ?_⟩
    have hgm : (finMat D.sp.cm.sig V.gram g).map φ = (B * (M : Matrix _ _ _).map s * C).map φ :=
      Matrix.ext fun i j => by
        have := congrArg φ (congrFun (congrFun hg i) j)
        rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
          one_mul] at this
    rw [hρ, hgm, Matrix.map_mul, Matrix.map_mul, hsM]
    exact conj_conj (mp _ _ c2)
  · have hint : ∀ g ∈ KsphC V ∅, ∀ i j,
        ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) i j ∈
          Formalism.UG.Ov D.host.E P := by
      intro g hg i j
      rw [hρ]
      exact entries_of_stab (Λ := fun y => y ∈ LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1
        (fun y hy => b2 y hy) (fun y hy => (hg.2.1 y).1 hy) (mp _ _ c2) i j
    have hk' : k⁻¹ ∈ KsphC V ∅ :=
      (GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG k).2 hk))
    refine Formalism.UG.P.cartan_mem_of_entries _ _ (hint k hk) ?_
    rw [← map_inv]
    exact hint _ hk'
  · rw [GlobalTheory.DivDual.divAt_iff]
    refine ⟨List.length_ofFn, GlobalTheory.SphLabelOps.dv_of_cartan φ s hs hε hφ hO hO' (B := B) b1 b2
      (Formalism.UG.P.cartan_entries_of_mem _ _ hk₁) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁))
      (Formalism.UG.P.cartan_entries_of_mem _ _ hk₂) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₂)) ?_⟩
    have e1 : (Matrix.diagonal fun i : Fin V.rank =>
        φ (finPart D (incA D ((ϖ : D.host.E) ^ ((List.ofFn a).getD i.1 0))))) =
        Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) a := by
      unfold Formalism.UG.diagPow
      congr 1
      funext i
      rw [hinc, map_zpow₀]
      simp
    rw [e1, ← hg, hρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mp _ _ c1, Matrix.one_mul]

end GlobalTheory.SplitPrimeChart
end

section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField
open scoped Matrix

namespace GlobalTheory.RepEqAt

section General

open Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem exists_triv (hur : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)) {n : ℕ} (hn : 0 < n)
    (Λ : GenLat E N) (hU : Λ.Unimod) :
    ∃ γ : Matrix (Fin N) (Fin N) E, IsUnitaryM γ ∧ ∃ k : ℕ, Nat.Coprime k n ∧
      (∀ v ∈ Λ.La, k • (γ *ᵥ v) ∈ Formalism.L2.Pj.stdLat E N) ∧
      ∀ x ∈ Formalism.L2.Pj.stdLat E N, ∃ v ∈ Λ.La, γ *ᵥ v = k • x := by
  have hsub : ∀ a b : 𝓞 E ⧸ Ideal.span {((1 : ℕ) : 𝓞 E)}, a = b := fun a b => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨a - b, by simp⟩)
  have hiso : IsIsomMod Λ 1 0 := by
    refine ⟨fun y => ⟨0, funext fun j => hsub _ _⟩, fun v => ⟨fun _ => ⟨v, v.2, by simp⟩, fun _ => rfl⟩,
      fun v w x y _ _ => ?_⟩
    obtain ⟨a, ha⟩ := (hU w).1 w.2 v v.2
    refine ⟨a - ∑ j, x j * IsCMField.ringOfIntegersComplexConj E (y j), ?_⟩
    have e1 : ∑ j, (v : Fin N → E) j * IsCMField.complexConj E ((w : Fin N → E) j) = (a : E) := by
      refine Eq.trans ?_ ha.symm
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : ∑ j, (x j : E) * IsCMField.complexConj E (y j : E) =
        ((∑ j, x j * IsCMField.ringOfIntegersComplexConj E (y j) : 𝓞 E) : E) := by
      change _ = algebraMap (𝓞 E) E _

      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← IsCMField.coe_ringOfIntegersComplexConj]
    rw [e1, e2, Nat.cast_one, one_mul]
    exact (map_sub (algebraMap (𝓞 E) E) _ _).symm
  obtain ⟨γ, hγ, ⟨k, hk, h1, h2⟩, -⟩ :=
    GlobalTheory.RepTrivial.repExists E N hur 1 n one_pos hn Λ 0 hU hiso
  rw [GlobalTheory.GenusLatCompare.span_smul_le_iff] at h1 h2
  exact ⟨γ, hγ, k, hk, fun v hv => h1 _ ⟨v, hv, rfl⟩, fun x hx => h2 x hx⟩

end General

theorem repExS (D : D7) : GL3Theta.repExS D := by
  letI := D.host.cmStar
  intro n hn N L L₀
  have hur := Formalism.L2.Pj.unramBridge D.host.E (Formalism.L2.Pj.cmUnram_conj D)
  have hst : ∀ x : D.host.E, star x = IsCMField.complexConj D.host.E x := fun _ => rfl
  have hU : ∀ M : SDLat D.host.E N, (⟨M.1⟩ : Formalism.L2.Pj.GenLat D.host.E N).Unimod := fun M v => by
    refine (M.2.2.2 v).trans (forall₂_congr fun w _ => ?_)
    have e : ∀ x y : Fin N → D.host.E, IsCMField.complexConj D.host.E (stdH D.host.E N x y) =
        stdH D.host.E N y x := fun x y => by
      rw [← hst]
      simp [stdH, mul_comm]
    have c : ∀ x y : Fin N → D.host.E, stdH D.host.E N x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range →
        stdH D.host.E N y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
      rintro x y ⟨a, ha⟩
      refine ⟨IsCMField.ringOfIntegersComplexConj D.host.E a, ?_⟩
      rw [← e, ← ha]
      exact IsCMField.coe_ringOfIntegersComplexConj D.host.E a
    exact ⟨c w v, c v w⟩
  have hun : ∀ γ : Matrix (Fin N) (Fin N) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ →
      γ ∈ Matrix.unitaryGroup (Fin N) D.host.E := fun γ h => Matrix.mem_unitaryGroup_iff'.2 h
  obtain ⟨γ, hγ, k, hk, h1, h2⟩ := exists_triv hur hn _ (hU L)
  obtain ⟨δ, hδ, l, hl, h3, h4⟩ := exists_triv hur hn _ (hU L₀)
  have hδ1 : star δ * δ = 1 := Matrix.mem_unitaryGroup_iff'.1 (hun δ hδ)
  have hγ1 : star γ * γ = 1 := Matrix.mem_unitaryGroup_iff'.1 (hun γ hγ)
  have hinv : ∀ v, star δ *ᵥ (δ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hδ1, Matrix.one_mulVec]
  refine ⟨⟨star δ * γ, mul_mem (Unitary.star_mem (hun δ hδ)) (hun γ hγ)⟩, k * l,
    Nat.Coprime.mul_left hk hl, ?_, fun x hx => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu, e⟩ := h4 _ (h1 v hv)
    have : ((k * l : ℕ) : D.host.E) • ((star δ * γ) *ᵥ v) = u := by
      rw [← hinv u, e, Nat.cast_smul_eq_nsmul, ← Matrix.mulVec_mulVec, smul_smul, mul_comm l k,
        Matrix.mulVec_smul]
    exact this ▸ hu
  · obtain ⟨u, hu, e⟩ := h2 _ (h3 x hx)
    refine ⟨u, hu, ?_⟩
    change (star δ * γ) *ᵥ u = _
    rw [← Matrix.mulVec_mulVec, e, smul_smul, Matrix.mulVec_smul, hinv, Nat.cast_smul_eq_nsmul]

end GlobalTheory.RepEqAt
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.SqrtUnram

theorem sqrt_neg_prime_mem_Kur : ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), q.Prime → q % 4 = 3 → l ≠ q →
    ∀ x : PadicAlgCl l, x ^ 2 = -(q : PadicAlgCl l) → x ∈ Loc.MaximalUnramifiedExtension l := by
  intro l _ q hq h4 hne x hx
  exact GlobalTheory.MemN.SelfGood.sqrt_mem q hq h4 _
    (fun z hz => GlobalTheory.MemN.SelfGood.root_mem_Kur hq.pos
      (fun hd => hne ((Nat.prime_dvd_prime_iff_eq Fact.out hq).1 hd)) hz) x hx

end GlobalTheory.SqrtUnram
end
