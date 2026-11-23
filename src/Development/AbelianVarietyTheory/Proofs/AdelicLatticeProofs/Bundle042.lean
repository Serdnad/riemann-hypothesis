module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormPrincipleOfCyclicTower
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle009
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle041
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLocalNonnormOfNonsquareAdicCompletion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sUnits_union_sup_finSq_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → Disjoint S T → (∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ sUnits F S, ∀ v ∈ T, (IsSquare (algebraMap F (v.adicCompletion F) (u : F)) ↔ v ∉ A)) → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ := by
  intro F _ _ _ S T hS hST hA
  classical
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  obtain ⟨u, hu, huA⟩ := hA (T.filter fun v =>
    ¬ IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)))
  have huU : u ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits] at hu ⊢
    intro v hv
    exact hu v fun h => hv (Finset.mem_union_left _ h)
  have hsq : u * (a * x) ∈ finSq F T := by
    simp only [finSq, Subgroup.mem_iInf]
    intro v hv
    rw [mem_sqSub, Units.val_mul, map_mul]
    have h := huA v hv
    rw [Finset.mem_filter] at h
    by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F))
    · exact (h.2 fun hh => hh.2 hs).mul hs
    · refine isSquare_mul_of_nonsquare_units F v ?_ _ _ ?_ ?_ (fun hh => h.1 hh ⟨hv, hs⟩) hs
      · rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2, hval]
        exact (hS v (hTS v hv)).1
      · rw [hval]
        exact (mem_sUnits F S u).1 hu v (hTS v hv)
      · rw [hval]
        exact hy v hv
  have hx : x = (u * a)⁻¹ * (u * (a * x)) := by group
  rw [hx]
  exact Subgroup.mul_mem_sup (inv_mem (mul_mem huU haU)) hsq

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ y ∈ pts Γ ℂ, evC f y = 0 := by
  first | exact @GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable | exact GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable | (intros; apply GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_isQGroup_weilRestriction_alt : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ Γ : Set (Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) ℂ), IsQGroup Γ ∧ ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → (∀ y ∈ pts Γ R, ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) ∧ y = emb b g) ∧ (IsReduced R → ∀ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) → emb b g ∈ pts Γ R) := by
  first | exact @GlobalTheory.ClassFin.exists_isQGroup_weilRestriction | exact GlobalTheory.ClassFin.exists_isQGroup_weilRestriction | (intros; apply GlobalTheory.ClassFin.exists_isQGroup_weilRestriction <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_finset_span_image_eq {G V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : G → V) : ∃ T : Finset G, ∀ S : Set G, (T : Set G) ⊆ S →
      Submodule.span ℂ (f '' S) = Submodule.span ℂ (Set.range f) := by
  classical
  have h : (Submodule.span ℂ (Set.range f)).FG := Submodule.FG.of_finite
  obtain ⟨s, hs, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 h
  have hs' : (s : Set V) ⊆ f '' Set.univ := by simpa using hs
  obtain ⟨T, -, hT⟩ := Finset.subset_set_image_iff.1 hs'
  refine ⟨T, fun S hS => le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_⟩
  rw [hsp, ← hT, Finset.coe_image]
  exact Submodule.span_mono (Set.image_mono hS)

theorem ss_kronecker_of_span_top : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Type) [Group G] (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix κ κ ℂ), Submodule.span ℂ (Set.range ρ) = ⊤ → Submodule.span ℂ (Set.range ρ') = ⊤ → SS (Set.range fun g => ρ g ⊗ₖ ρ' g) := by
  intro ι _ _ κ _ _ G _ ρ ρ' h h'
  classical
  obtain ⟨T₁, h₁⟩ := exists_finset_span_image_eq (ρ : G → Matrix ι ι ℂ)
  obtain ⟨T₂, h₂⟩ := exists_finset_span_image_eq (ρ' : G → Matrix κ κ ℂ)
  obtain ⟨T₃, h₃⟩ := exists_finset_span_image_eq (fun g => ρ g ⊗ₖ ρ' g)
  set T : Finset G := T₁ ∪ T₂ ∪ T₃ with hT
  set S : Finset G := T ∪ T.image (fun g => g⁻¹) with hS
  have hinv : ∀ g ∈ S, g⁻¹ ∈ S := by
    intro g hg
    rw [hS, Finset.mem_union] at hg ⊢
    rcases hg with hg | hg
    · exact Or.inr (Finset.mem_image_of_mem _ hg)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hg
      exact Or.inl (by simpa using ha)
  let τ : S ≃ S :=
    { toFun := fun s => ⟨s.1⁻¹, hinv _ s.2⟩
      invFun := fun s => ⟨s.1⁻¹, hinv _ s.2⟩
      left_inv := fun s => Subtype.ext (inv_inv _)
      right_inv := fun s => Subtype.ext (inv_inv _) }
  have hτ : ∀ s : S, (τ s : G) = (s : G)⁻¹ := fun _ => rfl
  have e₁ := h₁ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  have e₂ := h₂ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  have e₃ := h₃ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  rw [Set.image_eq_range] at e₁ e₂ e₃
  have i₁ : ∀ s : S, ρ (τ s : G) * ρ (s : G) = 1 := fun s => by
    rw [hτ, ← map_mul, inv_mul_cancel, map_one]
  have i₂ : ∀ s : S, ρ' (τ s : G) * ρ' (s : G) = 1 := fun s => by
    rw [hτ, ← map_mul, inv_mul_cancel, map_one]
  obtain ⟨P, hP, HP⟩ := GlobalTheory.T.exists_conj_harm_of_span' ι S τ (fun s => ρ (s : G)) i₁ (e₁.trans h)
  obtain ⟨Q, hQ, HQ⟩ := GlobalTheory.T.exists_conj_harm_of_span' κ S τ (fun s => ρ' (s : G)) i₂ (e₂.trans h')
  have HK := harm_kronecker ι κ S _ _ HP HQ
  have hPQ : IsUnit (P ⊗ₖ Q).det := by
    rw [det_kronecker]
    exact (hP.pow _).mul (hQ.pow _)
  have key : ∀ s : S, (P * ρ (s : G) * P⁻¹) ⊗ₖ (Q * ρ' (s : G) * Q⁻¹) =
      (P ⊗ₖ Q) * (ρ (s : G) ⊗ₖ ρ' (s : G)) * (P ⊗ₖ Q)⁻¹ := fun s => by
    rw [inv_kronecker, mul_kronecker_mul, mul_kronecker_mul]
  have conj : ∀ {n : Type} [Fintype n] [DecidableEq n] (A X Y : Matrix n n ℂ), IsUnit A.det → X * Y = 1 →
      (A * X * A⁻¹) * (A * Y * A⁻¹) = 1 := by
    intro n _ _ A X Y hA hXY
    calc (A * X * A⁻¹) * (A * Y * A⁻¹) = A * (X * (A⁻¹ * A) * Y) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hA, Matrix.mul_one, hXY, Matrix.mul_one, mul_nonsing_inv _ hA]
  have hss := ss_of_harm (ι × κ) S τ _ (fun s => by
    show ((P * ρ (τ s : G) * P⁻¹) ⊗ₖ (Q * ρ' (τ s : G) * Q⁻¹)) *
      ((P * ρ (s : G) * P⁻¹) ⊗ₖ (Q * ρ' (s : G) * Q⁻¹)) = 1
    rw [← mul_kronecker_mul, conj _ _ _ hP (i₁ s), conj _ _ _ hQ (i₂ s), one_kronecker_one]) HK
  have hss' : SS (Set.range fun s : S => ρ (s : G) ⊗ₖ ρ' (s : G)) := by
    refine (ss_transfer (ι × κ) _ ∅).2 (P ⊗ₖ Q) hPQ ?_
    rw [← Set.range_comp]
    convert hss using 2
    funext s
    exact (key s).symm
  refine (ss_transfer (ι × κ) _ _).1 ?_ ?_ hss'
  · rintro _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · intro x hx
    have : x ∈ Submodule.span ℂ (Set.range fun g => ρ g ⊗ₖ ρ' g) := Submodule.subset_span hx
    rw [← e₃] at this
    exact this

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem evC_map_ringEquiv {ι : Type} (σ : ℂ ≃+* ℂ) (f : MvPolynomial (ι × ι) ℂ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (σ : ℂ →+* ℂ) f) g = σ (evC f (g.map σ.symm)) := by
  unfold evC
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp]; simp

theorem evC_map_rat {ι : Type} (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  unfold evC ev
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

theorem mem_span_vanI_of_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ) := by
  intro ι _ _ Γ hΓ f hf
  let W : Submodule ℂ (MvPolynomial (ι × ι) ℂ) :=
    { carrier := {f | ∀ g ∈ Γ, evC f g = 0}
      add_mem' := by
        intro a b ha hb g hg
        have h1 := ha g hg
        have h2 := hb g hg
        unfold evC at *
        rw [map_add (f := _), h1, h2, add_zero]
      zero_mem' := by
        intro g hg
        simp [evC]
      smul_mem' := by
        intro c a ha g hg
        have h1 := ha g hg
        unfold evC at *
        rw [MvPolynomial.smul_eval, h1, mul_zero] }
  have hrepr : ∀ (p : MvPolynomial (ι × ι) ℂ) k,
      (MvPolynomial.basisMonomials (ι × ι) ℂ).repr p k = AddMonoidAlgebra.coeff p k := fun p k => rfl
  have key := GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ) W (by
    intro σ w hw
    refine ⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, ?_, ?_⟩
    · intro g hg
      rw [evC_map_ringEquiv, hw _ (hΓ σ.symm g hg), map_zero]
    · intro k
      rw [hrepr, hrepr, MvPolynomial.coeff_map]
      rfl)
  refine Submodule.span_mono ?_ (key (show f ∈ W from hf))
  rintro w ⟨hw, hq⟩
  have hl : w ∈ Set.range (MvPolynomial.map (σ := ι × ι) (algebraMap ℚ ℂ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    simp only [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hc
    obtain ⟨k, -, rfl⟩ := hc
    obtain ⟨q, hq⟩ := hq k
    exact ⟨q, by rw [← hrepr, hq]; rfl⟩
  obtain ⟨w₀, rfl⟩ := hl
  refine ⟨w₀, ?_, rfl⟩
  intro g hg
  rw [← evC_map_rat]
  exact hw g hg

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RationalInvariants

def invSub {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (n : ℕ) :
    Submodule ℂ ((Fin n → ι) → ℂ) where
  carrier := {μ | ∀ g ∈ Γ, μ ᵥ* tpow n g = μ}
  add_mem' := by
    intro a b ha hb g hg
    rw [Matrix.add_vecMul, ha g hg, hb g hg]
  zero_mem' := by
    intro g _
    exact Matrix.zero_vecMul _
  smul_mem' := by
    intro c a ha g hg
    rw [Matrix.smul_vecMul, ha g hg]

theorem mem_span_rational :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ (n : ℕ) (l : (Fin n → ι) → ℂ), (∀ g ∈ Γ, l ᵥ* tpow n g = l) → l ∈ Submodule.span ℂ {μ : (Fin n → ι) → ℂ | (∀ g ∈ Γ, μ ᵥ* tpow n g = μ) ∧ ∀ a, ∃ q : ℚ, μ a = q} := by
  intro ι _ _ Γ hΓ n l hl
  have h := GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (Pi.basisFun ℂ (Fin n → ι)) (invSub Γ n) (by
    intro σ w hw
    refine ⟨fun a => σ (w a), ?_, fun k => by simp⟩
    intro g hg
    funext b
    have h1 := congrArg σ (congrFun (hw _ (hΓ σ.symm g hg)) b)
    rw [← h1]

    simp [Matrix.vecMul, dotProduct, tpow, map_sum, map_prod])
  have h2 := h (show l ∈ invSub Γ n from hl)
  simp only [Pi.basisFun_repr] at h2
  exact h2

end GlobalTheory.ClassFin.RationalInvariants
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem finite_bdd_denominator_vectors {κ : Type} [Fintype κ] (D : ℕ) (hD : 0 < D) (B : ℝ) :
    {w : κ → ℚ | (∀ k, ∃ z : ℤ, (D : ℚ) * w k = z) ∧ nsq (fun k => ((w k : ℚ) : ℂ)) ≤ B}.Finite := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge ((D : ℝ) * (B + 1))
  have hDq : (D : ℚ) ≠ 0 := by positivity
  have hfin : ((fun z : ℤ => (z : ℚ) / D) '' (Set.Icc (-(N : ℤ)) N)).Finite :=
    (Set.finite_Icc _ _).image _
  refine (Set.Finite.pi' (fun _ : κ => hfin)).subset ?_
  rintro w ⟨hw, hB⟩ k
  obtain ⟨z, hz⟩ := hw k
  refine ⟨z, ?_, ?_⟩
  · have h1 : ‖((w k : ℚ) : ℂ)‖ ^ 2 ≤ B := by
      refine le_trans ?_ hB
      exact Finset.single_le_sum (f := fun k => ‖((w k : ℚ) : ℂ)‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ k)
    have h2 : ‖((w k : ℚ) : ℂ)‖ = |(w k : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    rw [h2] at h1
    have h3 : |(w k : ℝ)| ≤ B + 1 := by nlinarith [abs_nonneg (w k : ℝ), sq_nonneg (|(w k : ℝ)| - 1)]
    have h4 : (z : ℝ) = D * (w k : ℝ) := by exact_mod_cast hz.symm
    have h5 : |(z : ℝ)| ≤ N := by
      rw [h4, abs_mul, Nat.abs_cast]
      exact le_trans (mul_le_mul_of_nonneg_left h3 (by positivity)) hN
    have h6 : |z| ≤ (N : ℤ) := by exact_mod_cast h5
    exact abs_le.mp h6
  · simp only
    rw [← hz]; field_simp

theorem finite_integral_classes_closed_orbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), IsClosed (orb d (fun k => ((t k : ℚ) : ℂ))) → ∀ D : ℕ, 0 < D → ∃ Z : Finset (TIdx ι d → ℚ), ∀ h : Matrix ι ι ℚ, h.det = 1 → (∀ k, ∃ z : ℤ, (D : ℚ) * act d t h k = z) → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ act d t (h * γ.map (Int.cast : ℤ → ℚ)) ∈ Z := by
  intro ι _ _ m d t hcl D hD
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hC := (GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℂ).2 m d
  have hQ := (GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℚ).2 m d
  set tC : TIdx ι d → ℂ := fun k => ((t k : ℚ) : ℂ) with htC
  have htR : (fun k => (((t k : ℚ) : ℝ) : ℂ)) = tC := by
    funext k; simp [htC]
  obtain ⟨g, hg, hmin⟩ := GlobalTheory.T.exists_real_translate_isMinNormTensorInOrbit ι m d (fun k => ((t k : ℚ) : ℝ))
    (by rw [htR]; exact GlobalTheory.T.exists_minNormTensor_of_isClosed_tensorSLOrbit ι m d tC hcl)
  rw [htR] at hmin
  have hmap : ∀ x y : Matrix ι ι ℝ, (x * y).map (fun r : ℝ => (r : ℂ)) =
      x.map (fun r : ℝ => (r : ℂ)) * y.map (fun r : ℝ => (r : ℂ)) := fun x y =>
    Matrix.map_mul (f := Complex.ofRealHom)
  have hgg : g * g.adjugate = 1 := by rw [mul_adjugate, hg, one_smul]
  set gC : Matrix ι ι ℂ := g.map (fun r : ℝ => (r : ℂ)) with hgC
  have hgCd : gC.det = 1 := by
    have := (RingHom.map_det Complex.ofRealHom g)
    rw [hg, map_one] at this
    exact this.symm
  have hgCadj : gC * gC.adjugate = 1 := by rw [mul_adjugate, hgCd, one_smul]
  set v := act d tC gC with hv
  have horb : orb d v = orb d tC := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨gC * y, by rw [det_mul, hgCd, hy, one_mul], by rw [(hC tC).2.1]⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨gC.adjugate * y, by rw [det_mul, det_adjugate, hgCd, hy, one_pow, one_mul], ?_⟩
      rw [hv, ← (hC tC).2.1, ← mul_assoc, hgCadj, one_mul]
  obtain ⟨C, hSieg⟩ := GlobalTheory.T.exists_siegel_decomposition_mul_int_matrix_of_det_eq_one ι
  obtain ⟨B, hB⟩ := GlobalTheory.T.nsq_act_le_of_isSiegel_of_entries_zero_or_ge ι m d v (GlobalTheory.T.tensorSLOrbit_map_proper_of_isClosed ι m d v (horb ▸ hcl))
    (GlobalTheory.T.minNormTensor_stabilizer_conjTranspose_invariant ι m d v hmin) C (1 / D) (by positivity)
  refine ⟨(finite_bdd_denominator_vectors (κ := TIdx ι d) D hD B).toFinset, ?_⟩
  intro h hh hint
  have hhR : (h.map (fun q : ℚ => (q : ℝ))).det = 1 := by
    have := (RingHom.map_det (Rat.castHom ℝ) h)
    rw [hh, map_one] at this
    exact this.symm
  obtain ⟨γ, hγ, k, a, n, hS, hkan⟩ := hSieg (g.adjugate * h.map (fun q : ℚ => (q : ℝ)))
    (by rw [det_mul, det_adjugate, hg, hhR, one_pow, one_mul])
  refine ⟨γ, hγ, ?_⟩
  set w := act d t (h * γ.map (Int.cast : ℤ → ℚ)) with hw
  have hwint : ∀ j, ∃ z : ℤ, (D : ℚ) * w j = z := by
    intro j
    have h1 := (hQ ((D : ℚ) • act d t h)).2.2.2.1 (Int.castRingHom ℚ).range
      (γ.map (Int.cast : ℤ → ℚ)) (fun k => by
        obtain ⟨z, hz⟩ := hint k
        exact ⟨z, hz.symm⟩) (fun i j => ⟨γ i j, rfl⟩) j
    rw [(hQ _).2.2.2.2.1, ← (hQ t).2.1] at h1
    obtain ⟨z, hz⟩ := h1
    exact ⟨z, hz.symm⟩
  have hact : act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) = fun j => ((w j : ℚ) : ℂ) := by
    rw [← hkan, hv, ← (hC tC).2.1, hgC, ← hmap, ← mul_assoc, ← mul_assoc, hgg, one_mul]
    have h2 := (hQ t).2.2.2.2.2 ℂ (Rat.castHom ℂ) (h * γ.map (Int.cast : ℤ → ℚ))
    have h3 : (h.map (fun q : ℚ => (q : ℝ)) * γ.map (Int.cast : ℤ → ℝ)).map (fun r : ℝ => (r : ℂ)) =
        (h * γ.map (Int.cast : ℤ → ℚ)).map (Rat.castHom ℂ) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [h3]
    exact h2
  rw [Set.Finite.mem_toFinset]
  refine ⟨hwint, ?_⟩
  rw [← hact]
  refine hB k a n hS ?_
  intro j
  rw [hact]
  obtain ⟨z, hz⟩ := hwint j
  by_cases hz0 : z = 0
  · left
    have : w j = 0 := by
      rw [hz0] at hz
      have hDq : (D : ℚ) ≠ 0 := by positivity
      simpa [hD.ne'] using hz
    simp [this]
  · right
    have h2 : ‖((w j : ℚ) : ℂ)‖ = |(w j : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    have h4 : (z : ℝ) = D * (w j : ℝ) := by exact_mod_cast hz.symm
    have h5 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
    show 1 / (D : ℝ) ≤ ‖((w j : ℚ) : ℂ)‖
    rw [h2, div_le_iff₀ (by positivity)]
    rw [h4, abs_mul, Nat.abs_cast] at h5
    linarith

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.hilbert90_sUnits_kummer' : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → AdmP p F S → (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ sUnits E SE → ∏ i ∈ Finset.range p, σ^[i] (u : E) = 1 → ∃ y : Eˣ, y ∈ sUnits E SE ∧ (u : E) = σ y / y := by
  first | exact @GlobalTheory.CNorm.hilbert90_sUnits_kummer | exact GlobalTheory.CNorm.hilbert90_sUnits_kummer | (intros; apply GlobalTheory.CNorm.hilbert90_sUnits_kummer <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.hasseNormPrinciple_of_cyclic_tower : ∀ (F M E : Type) [Field F] [NumberField F] [Field M] [NumberField M] [Field E] [NumberField E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [IsGalois F E], IsCyclic (E ≃ₐ[F] E) → NP M E → NP F M → NP F E := by
  first | exact @GlobalTheory.CNorm.np_of_cyclic_tower | exact GlobalTheory.CNorm.np_of_cyclic_tower | (intros; apply GlobalTheory.CNorm.np_of_cyclic_tower <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.zlattice_tsum_dilate_sub_integral_le_rapid : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) / ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  exact @GlobalTheory.latticeSum_dilate_sub_integral_le
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.exists_local_nonnorm_of_nonsquare_adicCompletion : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ : v.adicCompletion F), δ ≠ 0 → ¬ IsSquare δ → ∃ x : v.adicCompletion F, x ≠ 0 ∧ ¬ ∃ a b : v.adicCompletion F, x = a ^ 2 - δ * b ^ 2 := by
  first | exact @GlobalTheory.QNorm.exists_local_nonnorm | exact GlobalTheory.QNorm.exists_local_nonnorm | (intros; apply GlobalTheory.QNorm.exists_local_nonnorm <;> assumption)
end
