module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle297
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle316
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseIdeleTriv

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem adele_algebraMap_apply (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = algebraMap F (v.adicCompletion F) k := rfl

theorem adele_mul_apply (v : HeightOneSpectrum (𝓞 F)) (a b : FiniteAdeleRing (𝓞 F) F) :
    (a * b) v = a v * b v := rfl

theorem adele_sub_apply (v : HeightOneSpectrum (𝓞 F)) (a b : FiniteAdeleRing (𝓞 F) F) :
    (a - b) v = a v - b v := rfl

theorem adele_one_apply (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := rfl

theorem close_scaled (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hf : ∀ k : F, f (algebraMap F _ k) = algebraMap E _ (algebraMap F E k))
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (h0 : ∀ (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ), Valued.v (a v) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (f a P) ≤ WithZero.exp (-(n : ℤ)))
    (a : FiniteAdeleRing (𝓞 F) F) (k m : F) (hm : m ≠ 0) (n : ℕ)
    (h : Valued.v (a v - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) * v.valuation F m) :
    Valued.v (f a P - algebraMap E _ (algebraMap F E k)) ≤
      WithZero.exp (-(n : ℤ)) * P.valuation E (algebraMap F E m) := by
  have hm1 : v.valuation F m ≠ 0 := (Valuation.ne_zero_iff _).2 hm
  have hm2 : P.valuation E (algebraMap F E m) ≠ 0 := (Valuation.ne_zero_iff _).2 (by simpa using hm)
  have h1 := h0 ((a - algebraMap F _ k) * algebraMap F _ m⁻¹) n (by
    rw [adele_mul_apply, adele_sub_apply, adele_algebraMap_apply, adele_algebraMap_apply, map_mul, val_algebraMap,
      map_inv₀]
    exact (mul_inv_le_iff₀ (zero_lt_iff.2 hm1)).2 h)
  rw [map_mul, map_sub, hf, hf, adele_mul_apply, adele_sub_apply, adele_algebraMap_apply, adele_algebraMap_apply,
    map_mul, val_algebraMap, map_inv₀, map_inv₀] at h1
  exact (mul_inv_le_iff₀ (zero_lt_iff.2 hm2)).1 h1

theorem val_eq_one (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (h0 : ∀ (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ), Valued.v (a v) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (f a P) ≤ WithZero.exp (-(n : ℤ)))
    (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (h : Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v) = 1) :
    Valued.v (f a P) = 1 := by
  have e1 : Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v (((a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul, ← adele_mul_apply, Units.mul_inv, adele_one_apply, map_one]
  have e2 : Valued.v (f a P) * Valued.v (f (a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) P) = 1 := by
    rw [← map_mul, ← adele_mul_apply, ← map_mul, Units.mul_inv, map_one, adele_one_apply, map_one]
  rw [h, one_mul] at e1
  have l1 := h0 a 0 (by simp [h])
  have l2 := h0 (a⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) 0 (by simp [e1])
  simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero] at l1 l2
  refine le_antisymm l1 ?_
  rw [← e2]
  exact mul_le_of_le_one_right' l2

theorem mem_aboveF (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  simp [aboveF]

theorem algebraMap_tmul_one {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (k : R) : (algebraMap R A k) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B k) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_approx (f : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hf : ∀ k : F, f (algebraMap F _ k) = algebraMap E _ (algebraMap F E k))
    (h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (b : FiniteAdeleRing (𝓞 F) F) (n : ℕ),
      Valued.v (b (P.under (𝓞 F))) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (f b P) ≤ WithZero.exp (-(n : ℤ)))
    (χ : HChar E) (hχ : χ.TrivOn F) (N : ℕ) (hN : 0 < N) (α : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 E))) (k : HeightOneSpectrum (𝓞 E) → Eˣ),
      (∀ P ∈ S, Valued.v (f α P) = P.valuation E (k P : E) ∧
        Valued.v (f α P - algebraMap E _ (k P : E)) ≤ P.valuation E (N : E) * P.valuation E (k P : E)) ∧
      (∀ P, P ∉ S → Valued.v (f α P) = 1 ∧ (N : 𝓞 E) ∉ P.asIdeal) ∧
      ∏ P ∈ S, ((χ.locK P (k P) : ℂˣ) : ℂ) = 1 := by
  classical
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx F N hN α
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨S.biUnion (aboveF (L := E) F), fun P => upF F (k (P.under (𝓞 F))), ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨v, hv, hPv⟩ := Finset.mem_biUnion.1 hP
    obtain rfl := (mem_aboveF v P).1 hPv
    obtain ⟨-, b1, b2⟩ := hS _ hv
    beta_reduce
    set kk := k (P.under (𝓞 F)) with hkk
    have hk : ((upF F kk : Eˣ) : E) = algebraMap F E kk := rfl
    rw [hk]
    have c1 := close_scaled f hf P _ (h0 P) α kk (N * kk) (mul_ne_zero hNF kk.ne_zero) 0 (by simpa using b1)
    have c2 := close_scaled f hf P _ (h0 P) α kk kk kk.ne_zero 1 (by simpa using b2)
    refine ⟨?_, by simpa using c1⟩
    rw [← val_algebraMap]
    apply Valuation.map_eq_of_sub_lt
    rw [val_algebraMap]
    refine c2.trans_lt ?_
    have hm2 : P.valuation E (algebraMap F E kk) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (by simp)
    refine mul_lt_of_lt_one_left (zero_lt_iff.2 hm2) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro P hP
    have hv : P.under (𝓞 F) ∉ S := fun h =>
      hP (Finset.mem_biUnion.2 ⟨_, h, (mem_aboveF _ P).2 rfl⟩)
    obtain ⟨b1, b2⟩ := hS' _ hv
    refine ⟨val_eq_one f P _ (h0 P) α b1, fun h => b2 ?_⟩
    change algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
    simpa using h
  · rw [Finset.prod_biUnion]
    · refine Finset.prod_eq_one fun v _ => ?_
      have := hχ.1 v (k v)
      rw [HChar.resFin, MonoidHom.finsetProd_apply] at this
      rw [← Units.coe_prod, Units.val_eq_one, ← this]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [← (mem_aboveF v P).1 hP]; rfl
    · intro v _ w _ hvw
      refine Finset.disjoint_left.2 fun P hv hw => hvw ?_
      rw [← (mem_aboveF v P).1 hv, ← (mem_aboveF w P).1 hw]

end General

theorem finite_idele_base_trivial : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F → ∀ a : (AF D.host.F)ˣ, infPart D (idF D a : AE D) = 1 → c (idF D a) = 1 := by
  intro D c χ hc hχ a ha
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  let α : (Af D.host.F)ˣ := Units.map (sndA D.host.F).toRingHom.toMonoidHom a
  let f : Af D.host.F →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    ι.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (B := D.host.E))
  have hfa : ∀ b, f b = ι (b ⊗ₜ[D.host.F] (1 : D.host.E)) := fun _ => rfl
  have hf : ∀ k : D.host.F, f (algebraMap D.host.F _ k) = algebraMap D.host.E _ (algebraMap D.host.F D.host.E k) := by
    intro k
    rw [hfa, ← h1, algebraMap_tmul_one]
  have h0 : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (b : Af D.host.F) (n : ℕ),
      Valued.v (b (P.under (𝓞 D.host.F))) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (f b P) ≤ WithZero.exp (-(n : ℤ)) := by
    intro P b n h
    have := h3 b 0 P n (by rwa [map_zero, sub_zero])
    rwa [map_zero, map_zero, sub_zero] at this
  have hfin : ι (finPart D (idF D a : AE D)) = f α := rfl
  obtain ⟨S, k, hS, hS', hp⟩ := exists_approx f hf h0 χ hχ N hN α
  rw [← hfin] at hS hS'
  exact Circle.ext ((hprod (idF D a) ha S k hS hS').trans hp)

end GlobalTheory.BaseIdeleTriv
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeChar_eq_prod_localComponents_approximating : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∃ N : ℕ, 0 < N ∧ ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ), (∀ P ∈ S, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) ∧ Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤ P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k P : D.host.E)) → (∀ P, P ∉ S → Valued.v (ι (finPart D (x : AE D)) P) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal) → ((c x : Circle) : ℂ) = ∏ P ∈ S, ((χ.locK P (k P) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.CharLocProd.char_eq_prod_locK | exact GlobalTheory.CharLocProd.char_eq_prod_locK | (intros; apply GlobalTheory.CharLocProd.char_eq_prod_locK <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.QuadPhase

theorem exists_top_extension (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ) (hS : S.Countable) :
    ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  let M₀ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (S ∩ (M : Set ℂ))
  have hle : M₀ ≤ M := IntermediateField.adjoin_le_iff.2 Set.inter_subset_right
  have hc : Countable M₀ := by
    have h1 := IntermediateField.cardinalMk_adjoin_le ℚ (S ∩ (M : Set ℂ))
    have h2 : (S ∩ (M : Set ℂ)).Countable := hS.mono Set.inter_subset_left
    refine Cardinal.mk_le_aleph0_iff.1 (h1.trans (max_le (max_le ?_ ?_) le_rfl))
    · exact Cardinal.mk_le_aleph0
    · exact Cardinal.mk_le_aleph0_iff.2 h2
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := M₀)
    (algebraMap M₀ ℂ) ((ρ.comp (IntermediateField.inclusion hle)).toRingHom)
  refine ⟨((σ : ℂ →+* ℂ).toRatAlgHom).comp (IntermediateField.val ⊤), fun x hx hxM => ?_⟩
  have hx0 : x ∈ M₀ := IntermediateField.subset_adjoin ℚ _ ⟨hx, hxM⟩
  have h := hσ ⟨x, hx0⟩
  unfold cj TaylorLogMetric.liftM
  rw [dite_eq_left IntermediateField.mem_top, dite_eq_left hxM]
  exact h

theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem cmQuadraticForm_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x = gl3FieldFirst Λ (w0 D * x) x := by
  unfold q1 gl3FieldFirst w0
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.add_im,
    Complex.one_im, Complex.I_re, Complex.I_im]
  ring

theorem cmQuadraticForm_half_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x / 2 = gl3FieldFirst Λ (w0 D * x / 2) x := by
  rw [cmQuadraticForm_eq_alternatingForm]
  unfold gl3FieldFirst
  rw [div_mul_eq_mul_div, Complex.div_ofNat_im]
  ring

theorem cmQuadraticForm_half_add_translation (D : D7) (Λ : AddSubgroup ℂ) (x l : ℂ) (m : ℕ) :
    q1 D Λ (x + 2 * (m : ℂ) * l) / 2 = q1 D Λ x / 2 + gl3FieldFirst Λ (w0 D * ((m : ℂ) * x)) l +
      gl3FieldFirst Λ (w0 D * l) ((m : ℂ) * x) + gl3FieldFirst Λ (w0 D * l) (((2 * m * m : ℕ) : ℂ) * l) := by
  rw [cmQuadraticForm_half_eq_alternatingForm, cmQuadraticForm_half_eq_alternatingForm]
  unfold gl3FieldFirst
  rw [← add_div, ← add_div, ← add_div, ← Complex.add_im, ← Complex.add_im, ← Complex.add_im]
  congr 2
  simp only [map_add (f := _), map_mul, map_natCast, map_ofNat]
  push_cast
  ring

theorem phase_top (D : D7) (hS : galStar D) (hW : WeilPairingGaloisAlt D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hc : Crv D cc δ) (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ)
    (x x' : ℂ) (m₀ : ℕ) (hm : 0 < m₀) (hx : (m₀ : ℂ) * x ∈ lamOf D cc δ)
    (hA : Adp1 ⊤ ρ (lamOf D cc δ) (2 * m₀) x x') :
    cj ⊤ ρ (ee (q1 D (lamOf D cc δ) x / 2)) = ee (q1 D (lamConj ⊤ ρ (lamOf D cc δ)) x' / 2) := by
  obtain ⟨hex, huniq, -, hadd, hmul, hord, -⟩ :=
    hS cc δ hc ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  have hWP := hW cc δ hc ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  set Λ := lamOf D cc δ with hΛ
  set Λ' := lamConj ⊤ ρ Λ with hΛ'
  have hm0 : (m₀ : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmulw : ∀ t t', StarPt ⊤ ρ Λ t t' → StarPt ⊤ ρ Λ (w0 D * t) (w0 D * t') := fun t t' h => by
    have := hmul a t t' h
    rwa [ha] at this
  have hw : ∀ l ∈ Λ, w0 D * l ∈ Λ := fun l hl => by
    have h := hmulw l 0 (Or.inl ⟨hl, zero_mem _⟩)
    rcases h with h | h
    · exact h.1
    · exact absurd (by rw [mul_zero]; exact zero_mem _) h.2.1
  have hw' : ∀ l ∈ Λ', w0 D * l ∈ Λ' := fun l hl => by
    have h := hmulw 0 l (Or.inl ⟨zero_mem _, hl⟩)
    rcases h with h | h
    · exact h.2
    · exact absurd (by rw [mul_zero]; exact zero_mem _) h.1
  have hint : ∀ l ∈ Λ', ∀ l' ∈ Λ', ee (gl3FieldFirst Λ' l l') = 1 := fun l hl l' hl' => by
    have h := hWP 0 0 l l' 1 one_pos (by simp) (by simp)
      (Or.inl ⟨by simp, by simpa using hl⟩) (Or.inl ⟨by simp, by simpa using hl'⟩) IntermediateField.mem_top
    rw [← h]
    have h0 : gl3FieldFirst Λ 0 0 = 0 := by simp [gl3FieldFirst]
    rw [h0, ee_zero]
    unfold cj TaylorLogMetric.liftM
    rw [dite_eq_left IntermediateField.mem_top]
    exact map_one ρ
  have hnat : ∀ (A : AddSubgroup ℂ) (n : ℕ), ∀ l ∈ A, (n : ℂ) * l ∈ A := fun A n l hl => by
    rw [← nsmul_eq_mul]
    exact nsmul_mem hl n
  have htn : ((4 * m₀ * m₀ : ℕ) : ℂ) * (x / (4 * (m₀ : ℂ))) = (m₀ : ℂ) * x := by
    push_cast
    field_simp
  obtain ⟨t', ht'⟩ := hex (x / (4 * (m₀ : ℂ))) ⟨4 * m₀ * m₀, by positivity, htn ▸ hx⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  set y : ℂ := 4 * (m₀ : ℂ) * t' with hy
  have hA2 : Adp1 ⊤ ρ Λ (2 * m₀) x y := by
    have h := hadd _ _ _ _ ht' ht'
    unfold Adp1
    convert h using 1
    · push_cast
      field_simp
      ring
    · rw [hy]
      push_cast
      field_simp
      ring
  have hA3 : Adp1 ⊤ ρ Λ (2 * m₀) (w0 D * x / 2) (w0 D * y / 2) := by
    have h := hmulw _ _ ht'
    unfold Adp1
    convert h using 1
    · push_cast
      field_simp
      ring
    · rw [hy]
      push_cast
      field_simp
      ring
  have hl := (huniq _ _ _ hA).1 hA2
  have hμ : (m₀ : ℂ) * y ∈ Λ' := by
    have h := (hord (4 * m₀ * m₀) _ _ ht').1 (htn ▸ hx)
    convert h using 1
    rw [hy]
    push_cast
    ring
  set l : ℂ := x' / ((2 * m₀ : ℕ) : ℂ) - y / ((2 * m₀ : ℕ) : ℂ) with hldef
  have hx' : x' = y + 2 * (m₀ : ℂ) * l := by
    rw [hldef]
    push_cast
    field_simp
    ring
  have hmain := hWP (w0 D * x / 2) x (w0 D * y / 2) y (2 * m₀) (by positivity)
    (by
      convert hw _ hx using 1
      push_cast
      ring)
    (by
      convert hnat Λ 2 _ hx using 1
      push_cast
      ring)
    hA3 hA2 IntermediateField.mem_top
  rw [hx', cmQuadraticForm_half_add_translation, ee_add, ee_add, ee_add, hint _ (hw' _ hμ) _ hl, hint _ (hw' _ hl) _ hμ,
    hint _ (hw' _ hl) _ (hnat Λ' _ _ hl), cmQuadraticForm_half_eq_alternatingForm, cmQuadraticForm_half_eq_alternatingForm, hmain]
  simp

theorem galPh1_of (D : D7) (hS : galStar D) (hW : WeilPairingGaloisAlt D) : galPh1 D := by
  intro cc δ hc
  refine ⟨fun x => cmQuadraticForm_eq_alternatingForm D _ x, fun M ρ hK h2 h3 x x' m₀ hm hx hA he => ?_⟩
  set Λ := lamOf D cc δ with hΛ
  have hKc : Countable D.host.K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let S : Set ℂ := Set.range (fun a : D.host.K => D.host.φ₀ (a : D.host.E)) ∪
    {g2 Λ, g3 Λ, wpF Λ (x / ((2 * m₀ : ℕ) : ℂ)), wpD Λ (x / ((2 * m₀ : ℕ) : ℂ)), ee (q1 D Λ x / 2)}
  have hSc : S.Countable := (Set.countable_range _).union (Set.toFinite _).countable
  obtain ⟨σ, hσ⟩ := exists_top_extension M ρ S hSc
  have hK' : FixK D ⊤ σ := fun a =>
    ⟨IntermediateField.mem_top, by rw [hσ _ (Or.inl ⟨a, rfl⟩) (hK a).1, (hK a).2]⟩
  have hl : lamConj ⊤ σ Λ = lamConj M ρ Λ := by
    have e2 := hσ (g2 Λ) (Or.inr (by simp)) h2
    have e3 := hσ (g3 Λ) (Or.inr (by simp)) h3
    unfold cj at e2 e3
    unfold lamConj
    rw [e2, e3]
  have hA' : Adp1 ⊤ σ Λ (2 * m₀) x x' := by
    unfold Adp1 StarPt at hA ⊢
    rw [hl]
    rcases hA with h | ⟨h1, h2', h3', h4, h5, h6⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2', IntermediateField.mem_top, IntermediateField.mem_top, ?_, ?_⟩
      · rw [h5, hσ _ (Or.inr (by simp)) h3']
      · rw [h6, hσ _ (Or.inr (by simp)) h4]
  have h := phase_top D hS hW cc δ hc σ hK' x x' m₀ hm hx hA'
  rw [← hΛ, hl, hσ _ (Or.inr (by simp)) he] at h
  exact h

theorem galPh1_all : ∀ D : D7, galPh1 D := fun D =>
  galPh1_of D (GlobalTheory.T.galStar_complexMultiplication_points D) (GlobalTheory.T.weilPairing_galois_equivariant_cm_torsion D)

end GlobalTheory.QuadPhase
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.admissible_characters_exist : ∀ D : D7, GaussSumTripleConstant D := by
  first | exact @GlobalTheory.TripleIntertwiner.triple_constant | exact GlobalTheory.TripleIntertwiner.triple_constant | (intros; apply GlobalTheory.TripleIntertwiner.triple_constant <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.forall_use1 : ∀ D : D7, use1 D := by
  first | exact @GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate | exact GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate | (intros; apply GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates : ∀ D : D7, t0Ex D := by
  first | exact @GlobalTheory.TwoTorsionPt.exists_point | exact GlobalTheory.TwoTorsionPt.exists_point | (intros; apply GlobalTheory.TwoTorsionPt.exists_point <;> assumption)
end
