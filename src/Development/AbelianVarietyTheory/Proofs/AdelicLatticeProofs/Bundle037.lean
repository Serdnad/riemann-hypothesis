module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle032
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_multiplier_descend_of_closed {σ X : Type} [Fintype σ] [Nonempty X] (p : X → σ → ℂ)
    (hcl : ∀ y : σ → ℂ, (∀ f : MvPolynomial σ ℂ, (∀ x, MvPolynomial.aeval (p x) f = 0) →
      MvPolynomial.aeval y f = 0) → ∃ x, p x = y)
    (q : σ → MvPolynomial σ ℂ) (s : Finset (MvPolynomial σ ℂ))
    (hs : ∀ f ∈ s, ∀ x x', (∀ i, MvPolynomial.aeval (p x) (q i) = MvPolynomial.aeval (p x') (q i)) →
      MvPolynomial.aeval (p x) f = MvPolynomial.aeval (p x') f) :
    ∃ b : MvPolynomial σ ℂ, (∃ x, MvPolynomial.aeval (p x) (MvPolynomial.aeval q b) ≠ 0) ∧
      ∀ f ∈ s, ∃ b' : MvPolynomial σ ℂ, ∀ x,
        MvPolynomial.aeval (p x) (MvPolynomial.aeval q b) * MvPolynomial.aeval (p x) f =
          MvPolynomial.aeval (p x) (MvPolynomial.aeval q b') := by
  classical
  let φ : MvPolynomial σ ℂ →ₐ[ℂ] (X → ℂ) := Pi.algHom ℂ (fun _ => ℂ) fun x => MvPolynomial.aeval (p x)
  have hφ : ∀ f x, φ f x = MvPolynomial.aeval (p x) f := fun _ _ => rfl
  let A : Subalgebra ℂ (X → ℂ) := φ.range
  let π : MvPolynomial σ ℂ →ₐ[ℂ] A := φ.rangeRestrict
  have hπ : Function.Surjective π := φ.rangeRestrict_surjective
  have hπv : ∀ f x, ((π f : A) : X → ℂ) x = MvPolynomial.aeval (p x) f := fun _ _ => rfl
  let B : Subalgebra ℂ A := (π.comp (MvPolynomial.aeval q)).range
  haveI : Algebra.FiniteType ℂ A := Algebra.FiniteType.of_surjective π hπ
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A
  haveI : IsReduced A := isReduced_of_injective A.val Subtype.val_injective
  letI : Algebra ℚ B := ((algebraMap ℂ B).comp (algebraMap ℚ ℂ)).toAlgebra
  have hpt : ∀ χ : A →ₐ[ℂ] ℂ, ∃ x, ∀ f, χ (π f) = MvPolynomial.aeval (p x) f := by
    intro χ
    have h1 : χ.comp π = MvPolynomial.aeval (fun i => χ (π (MvPolynomial.X i))) := by
      ext i
      simp
    have h2 : ∀ f, χ (π f) = MvPolynomial.aeval (fun i => χ (π (MvPolynomial.X i))) f :=
      fun f => DFunLike.congr_fun h1 f
    obtain ⟨x, hx⟩ := hcl (fun i => χ (π (MvPolynomial.X i))) (by
      intro f hf
      have h0 : π f = 0 := Subtype.ext (funext fun x => hf x)
      rw [← h2, h0, map_zero])
    exact ⟨x, fun f => by rw [h2, hx]⟩
  have hnil : ∀ g ∈ s.image π, IsNilpotent (g ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] g) := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
    refine GlobalTheory.T.isNilpotent_tmul_sub_tmul_of_const_on_fibres' B A (π f) ?_
    intro χ χ' h
    obtain ⟨x, hx⟩ := hpt χ
    obtain ⟨x', hx'⟩ := hpt χ'
    rw [hx, hx']
    refine hs f hf x x' fun i => ?_
    rw [← hx, ← hx']
    exact h ⟨π (q i), MvPolynomial.X i, by simp⟩
  obtain ⟨b, hb, hbs⟩ := GlobalTheory.T.exists_common_denominator_nilpotent_coboundary B A Subtype.val_injective (s.image π) hnil
  obtain ⟨b, c, rfl⟩ := b
  refine ⟨c, ?_, fun f hf => ?_⟩
  · by_contra hc
    push_neg at hc
    exact hb (Subtype.ext (Subtype.ext (funext fun x => hc x)))
  · obtain ⟨⟨b', c', rfl⟩, hb'⟩ := hbs (π f) (Finset.mem_image_of_mem _ hf)
    exact ⟨c', fun x => congrFun (congrArg Subtype.val hb') x⟩

theorem exists_poly_blk_entries {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι ℚ) :
    ∃ q : ι × ι → MvPolynomial (ι × ι) ℂ, ∀ (x : Matrix ι ι ℂ) (ij : ι × ι),
      MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) (q ij) = blk e x ij.1 ij.2 := by
  let E : Matrix ι ι (MvPolynomial (ι × ι) ℂ) := (e.map (algebraMap ℚ ℂ)).map MvPolynomial.C
  let Y : Matrix ι ι (MvPolynomial (ι × ι) ℂ) := Matrix.of fun i j => MvPolynomial.X (i, j)
  refine ⟨fun ij => (E * Y * E + (1 - E) * Y * (1 - E)) ij.1 ij.2, fun x ij => ?_⟩
  let ψ : MvPolynomial (ι × ι) ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2)
  have hE : ψ.mapMatrix E = e.map (algebraMap ℚ ℂ) := by
    ext i j
    simp [E, ψ]
  have hY : ψ.mapMatrix Y = x := by
    ext i j
    simp [Y, ψ]
  have h : ψ.mapMatrix (E * Y * E + (1 - E) * Y * (1 - E)) = blk e x := by
    simp only [map_add (f := _), map_mul, map_sub, map_one, hE, hY, blk]
  rw [← h]
  rfl

theorem exists_multiplier_descend_blk :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), pts Γ ℂ ⊆ Γ → Γ.Nonempty → ∀ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ f ∈ s, ∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, (∃ x ∈ Γ, evC b (blk e x) ≠ 0) ∧ ∀ f ∈ s, ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC b (blk e x) * evC f x = evC b' (blk e x) := by
  intro ι _ _ Γ e hΓ hne s hs
  obtain ⟨q, hq⟩ := exists_poly_blk_entries e
  haveI : Nonempty Γ := hne.to_subtype
  have hev : ∀ (f : MvPolynomial (ι × ι) ℂ) (x : Matrix ι ι ℂ),
      evC f x = MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) f := fun f x => rfl
  have hcomp : ∀ (b : MvPolynomial (ι × ι) ℂ) (x : Matrix ι ι ℂ),
      MvPolynomial.aeval (fun kl : ι × ι => x kl.1 kl.2) (MvPolynomial.aeval q b) = evC b (blk e x) := by
    intro b x
    rw [hev, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp only [hq]
  obtain ⟨b, ⟨x₀, hx₀⟩, hb⟩ := exists_multiplier_descend_of_closed
    (fun (x : Γ) (kl : ι × ι) => x.1 kl.1 kl.2) (by
      intro y hy
      refine ⟨⟨Matrix.of fun i j => y (i, j), hΓ fun f hf => ?_⟩, rfl⟩
      have := hy (MvPolynomial.map (algebraMap ℚ ℂ) f) (fun x => by
        rw [MvPolynomial.aeval_map_algebraMap]
        exact hf x.1 x.2)
      rw [MvPolynomial.aeval_map_algebraMap] at this
      exact this) q s (by
      intro f hf x x' h
      refine hs f hf x.1 x.2 x'.1 x'.2 ?_
      ext i j
      have := h (i, j)
      rwa [hq, hq] at this)
  refine ⟨b, ⟨x₀.1, x₀.2, by rwa [hcomp] at hx₀⟩, fun f hf => ?_⟩
  obtain ⟨b', hb'⟩ := hb f hf
  refine ⟨b', fun x hx => ?_⟩
  have := hb' ⟨x, hx⟩
  rw [hcomp, hcomp] at this
  exact this

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryTransvectionSubmonoid_normal_det_one : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∀ γ, IsU σ G γ → γ.det * σ γ.det = 1 ∧ IsU σ G γ⁻¹) ∧ (∀ m ∈ TvGen σ G, IsU σ G m ∧ m.det = 1 ∧ m⁻¹ ∈ TvGen σ G ∧ ∀ γ, IsU σ G γ → ∃ m' ∈ TvGen σ G, γ * m = m' * γ ∧ ∃ m'' ∈ TvGen σ G, m * γ = γ * m'') := by
  first | exact @GlobalTheory.UTrans.tvGen_normal | exact GlobalTheory.UTrans.tvGen_normal | (intros; apply GlobalTheory.UTrans.tvGen_normal <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.two_mul_card_infinitePlace_le_quadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → 2 * Fintype.card (InfinitePlace F) ≤ Fintype.card (InfinitePlace E) + tReal F δ := by
  first | exact @GlobalTheory.QNorm.two_mul_card_infinitePlace_le | exact GlobalTheory.QNorm.two_mul_card_infinitePlace_le | (intros; apply GlobalTheory.QNorm.two_mul_card_infinitePlace_le <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sqIdx_hiUnits_anti {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {m n : ℕ} (h : m ≤ n) :
    hiUnits w n ≤ hiUnits w m := by
  rintro x ⟨hx, hx'⟩
  refine ⟨hx, hx'.trans ?_⟩
  rw [WithZero.exp_le_exp]
  omega

theorem sqIdx_relIndex_hiUnits_add {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (π : K)
    (R : Finset K) (hπ : w π = WithZero.exp (-1))
    (hR : ∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) (n k : ℕ) :
    (hiUnits w (n + k)).relIndex (hiUnits w n) ≠ 0 ∧
      (hiUnits w (n + k)).relIndex (hiUnits w n) ≤ R.card ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.T.relIndex_higherUnits_succ_le_card K w π R (n + k) hπ hR
    have := Subgroup.relIndex_mul_relIndex (hiUnits w (n + k + 1)) (hiUnits w (n + k))
      (hiUnits w n) (sqIdx_hiUnits_anti w (by omega)) (sqIdx_hiUnits_anti w (by omega))
    rw [← add_assoc, ← this]
    refine ⟨mul_ne_zero h1 ih.1, ?_⟩
    rw [pow_succ']
    exact Nat.mul_le_mul h2 ih.2

theorem sqIdx_sqSub_eq_comap {F L : Type} [Field F] [Field L] (φ : F →+* L) :
    sqSub φ = (sqs (⊤ : Subgroup Lˣ)).comap (Units.map (φ : F →* L)) := by
  ext x
  rw [mem_sqSub, Subgroup.mem_comap]
  constructor
  · rintro ⟨r, hr⟩
    have hx : φ (x : F) ≠ 0 := by simp
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hr)
    refine ⟨Units.mk0 r hr0, Subgroup.mem_top _, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨r, -, hr⟩
    refine ⟨(r : L), ?_⟩
    have := congrArg (fun u : Lˣ => (u : L)) hr
    simpa [sq] using this.symm

theorem index_sqSub_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  intro F _ _ v e he
  obtain ⟨⟨π, -, hπ⟩, hval, -, R, hcard, -, hR⟩ := GlobalTheory.T.exists_global_uniformizer_residue_representatives F v
  have h2 : Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, ← hval, map_ofNat (algebraMap F (v.adicCompletion F))]
  have hsq := GlobalTheory.T.higherUnits_le_squares_higherUnits F v e h2
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v with hw
  have hA := sqIdx_relIndex_hiUnits_add w _ R hπ hR (e + 1) e
  have hB := sqIdx_relIndex_hiUnits_add w _ R hπ hR 0 (e + 1)
  rw [show e + 1 + e = 2 * e + 1 by ring] at hA
  rw [zero_add] at hB
  have hC0 : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≠ 0 :=
    fun h => hA.1 (Subgroup.relIndex_eq_zero_of_le_left hsq h)
  have hC : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≤ R.card ^ e :=
    (Subgroup.relIndex_le_of_le_left hsq hA.1).trans hA.2
  have hD := GlobalTheory.T.relIndex_squares_le_two_mul_of_subgroup (v.adicCompletion F)ˣ (hiUnits w 0) (hiUnits w (e + 1)) (-1)
    (sqIdx_hiUnits_anti w (by omega)) hB.1 (fun a ha => by
      have h : (a : v.adicCompletion F) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
      rcases sq_eq_one_iff.mp h with h | h
      · left; exact Units.ext h
      · right; exact Units.ext (by simpa using h)) hC0
  have hE := GlobalTheory.T.index_squares_le_two_mul_units_squares (v.adicCompletion F) w _ hπ hD.1
  rw [sqIdx_sqSub_eq_comap, Subgroup.index_comap]
  rw [← Subgroup.relIndex_top_right] at hE
  refine ⟨fun h => hE.1 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hE.1).trans (hE.2.trans ?_)
  have hp : R.card ^ e ≤ Ideal.absNorm v.asIdeal ^ e := Nat.pow_le_pow_left hcard e
  have := hD.2
  omega

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem prime_mul_card_le_card_over : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → p * S.card ≤ SE.card + (p - 1) * tNon p F δ S := by
  intro p F E _ _ _ _ _ ζ δ θ σ hq S SE hSE
  classical
  have hp := hq.prime
  obtain ⟨-, hrk, hgal, -, -, -, hemb⟩ := kummer_galois p F E ζ δ θ σ hq
  have h1 : SE.card = ∑ v ∈ S, (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => (hSE w).1 hw)
  have h2 : tNon p F δ S
      = ∑ v ∈ S, if (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ)
        then 1 else 0 := by
    rw [← Finset.card_filter, tNon, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hs : ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ
  · obtain ⟨w, hw⟩ := (places_over F E).2.1 v
    have : 0 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩⟩
    rw [if_pos hs]
    omega
  · rw [if_neg hs]
    push Not at hs
    obtain ⟨r, hr⟩ := hs
    have hδ : δ ≠ 0 := fun h0 => hq.nonpow 0 (by rw [h0, zero_pow hp.ne_zero])
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero, eq_comm, map_eq_zero] at hr
      exact hδ hr
    obtain ⟨ψ, hψ⟩ := hemb (v.adicCompletion F) r hr
    obtain ⟨ψ', hψ'⟩ := hemb (v.adicCompletion F) (algebraMap F (v.adicCompletion F) ζ * r)
      (by rw [mul_pow, ← map_pow, hq.root.pow_eq_one, map_one, one_mul, hr])
    have hne : ψ ≠ ψ' := by
      intro h
      rw [← h, hψ, eq_comm, mul_eq_right₀ hr0,
        ← map_one (algebraMap F (v.adicCompletion F))] at hψ'
      exact hq.root.ne_one hp.one_lt ((algebraMap F (v.adicCompletion F)).injective hψ')
    obtain ⟨w, w', hww, hw, hw'⟩ := two_places_of_embeddings F E v ψ ψ' hne
    have h3 := ncard_places_over_eq_of_prime_degree p F E hp hrk v w w' hww hw hw'
    have h4 : (SE.filter (fun w => w.under (𝓞 F) = v)).card = p := by
      rw [← h3, ← Set.ncard_coe_finset]
      congr 1
      ext u
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨(hSE u).2 (h ▸ hv), h⟩⟩
    omega

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pIdx_eq_pTor_of_finite_group (p : ℕ) {G : Type} [CommGroup G] [Finite G]
    (U : Subgroup G) : pTor p U ≠ 0 ∧ pIdx p U = pTor p U := by
  have h1 : pTor p U = Nat.card (powMonoidHom p : U →* U).ker := by
    unfold pTor
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        invFun := fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 : pIdx p U = (powMonoidHom p : U →* U).range.index := by
    unfold pIdx pows Subgroup.relIndex
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext h⟩
    · rintro ⟨y, h⟩
      exact ⟨y.1, y.2, congrArg Subtype.val h⟩
  have h3 := (powMonoidHom p : U →* U).range.card_mul_index
  have h4 := (powMonoidHom p : U →* U).ker.card_mul_index
  rw [Subgroup.index_ker] at h4
  have h5 : Nat.card (powMonoidHom p : U →* U).range ≠ 0 := Nat.card_pos.ne'
  refine ⟨h1 ▸ Nat.card_pos.ne', ?_⟩
  rw [h1, h2]
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5)
  rw [h3, ← h4, mul_comm]

theorem pIdx_units_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by
  intro p O _ _ _ π hp hπ hc hfin
  haveI : Finite (O ⧸ Ideal.span {(p : O) * π}) := Nat.finite_of_card_ne_zero hfin
  have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  obtain ⟨hd1, hd2⟩ := GlobalTheory.T.subgroupPowImage_unitsCongruentOneMod_of_isAdicComplete p O π hp hπ hc
  have hle : Ideal.span {(p : O) * π} ≤ Ideal.span {π} :=
    Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro_left _ rfl)
  have hle' : Ideal.span {(p : O) * π} ≤ Ideal.span {(p : O)} :=
    Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro _ rfl)
  have hs := GlobalTheory.T.relIndex_oneUnits_mul_eq_card_quotient' O ((p : O) * π) p (mul_ne_zero hp0 hπ) (Dvd.intro _ rfl)
    (hle.trans (IsAdicComplete.le_jacobson_bot _))
  have hk : pIdx p (oneUnits ((p : O) * π)) = Nat.card (O ⧸ Ideal.span {(p : O)}) := by
    unfold pIdx
    rw [hd1, ← hs, sq, mul_assoc]
  haveI : Finite (O ⧸ Ideal.span {(p : O)}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle')
  have hk0 : Nat.card (O ⧸ Ideal.span {(p : O)}) ≠ 0 := Nat.card_pos.ne'
  let g : Oˣ →* (O ⧸ Ideal.span {(p : O) * π})ˣ :=
    Units.map (Ideal.Quotient.mk (Ideal.span {(p : O) * π}) : O →* O ⧸ Ideal.span {(p : O) * π})
  have hker : g.ker = oneUnits ((p : O) * π) := rfl
  obtain ⟨hr1, hr2⟩ := pIdx_eq_pTor_of_finite_group p g.range
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.powIndex_torsion_ker_range_mul p _ _ g (by rw [hker, hk]; exact hk0)
    (by rw [hker, hd2]; exact one_ne_zero) (by rw [hr2]; exact hr1) hr1
  refine ⟨h2, ?_⟩
  rw [hker, hd2, hk, hr2, mul_one, mul_right_comm] at h3
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr1) h3

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ (∀ y : E, σ^[p] y = y) ∧ (∀ y : E, σ y = y → ∃ a : F, y = algebraMap F E a) ∧ (∀ y : E, ∏ i ∈ Finset.range p, σ^[i] y = 1 → ∃ z : E, z ≠ 0 ∧ y = σ z / z) ∧ (∀ (u : F) (y : E), y ^ p = algebraMap F E u → ∃ (k : ℕ) (r : F), u = δ ^ k * r ^ p) ∧ ∀ x : Fˣ, x ∈ kNorm p (RingHom.id F) δ ↔ ∃ y : E, ∏ i ∈ Finset.range p, σ^[i] y = algebraMap F E (x : F) := by
  first | exact @GlobalTheory.CNorm.kummer_basic | exact GlobalTheory.CNorm.kummer_basic | (intros; apply GlobalTheory.CNorm.kummer_basic <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.mem_unitsLocalKummerNorms_of_baseChange_norm : ∀ (p : ℕ) (F E L : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field L] [Algebra F L] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ x : Fˣ, TNorm F E L (x : F) → x ∈ kNorm p (algebraMap F L) δ := by
  first | exact @GlobalTheory.CNorm.mem_kNorm_of_tNorm | exact GlobalTheory.CNorm.mem_kNorm_of_tNorm | (intros; apply GlobalTheory.CNorm.mem_kNorm_of_tNorm <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow : ∀ (p : ℕ) (F L : Type) [Field F] [Field L] [CharZero L] (φ : F →+* L) (δ : F) (r : L), 0 < p → δ ≠ 0 → r ^ p = φ δ → kNorm p φ δ = ⊤ := by
  first | exact @GlobalTheory.CNorm.kNorm_eq_top_of_pow | exact GlobalTheory.CNorm.kNorm_eq_top_of_pow | (intros; apply GlobalTheory.CNorm.kNorm_eq_top_of_pow <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.valuation_unramified_kummer_of_coprime_unit : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 F)).valuation F (p : F) = 1 → (w.under (𝓞 F)).valuation F δ = 1 → ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x := by
  first | exact @GlobalTheory.CNorm.kummer_valuation_unramified | exact GlobalTheory.CNorm.kummer_valuation_unramified | (intros; apply GlobalTheory.CNorm.kummer_valuation_unramified <;> assumption)
end
