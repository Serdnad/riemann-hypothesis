module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle007
public import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCarryDual
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle068
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalToGlobal.Divisibility.Bundle001
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx


open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
theorem _root_.GlobalTheory.GaugeEx.isOpenUnits_of_basis {R S ι : Type} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsOpenUnits R] [CommRing S] [Algebra R S] [TopologicalSpace S]
    [IsModuleTopology R S] [IsTopologicalRing S] [Fintype ι] (b : Module.Basis ι R S) :
    IsOpenUnits S := by
  classical
  have hR : IsOpenEmbedding (Units.val : Rˣ → R) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hLc : Continuous (fun x : S => Algebra.leftMulMatrix b x) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have hopenR : IsOpen {r : R | IsUnit r} := hR.isOpen_range
  have hinvR : ContinuousOn (Ring.inverse : R → R) {r | IsUnit r} := by
    rintro _ ⟨u, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [← hR.continuousAt_iff]
    have h : (Ring.inverse ∘ Units.val : Rˣ → R) = fun v => ↑v⁻¹ := by
      funext v
      simp [Ring.inverse_unit]
    rw [h]
    exact Units.continuous_coe_inv.continuousAt
  obtain ⟨g, hg⟩ : ∃ g : S → S, ∀ x, g x =
      b.equivFun.symm (Matrix.mulVec (Algebra.leftMulMatrix b x)⁻¹ (b.equivFun 1)) :=
    ⟨_, fun _ => rfl⟩
  have key : ∀ x, IsUnit (Algebra.leftMulMatrix b x).det → x * g x = 1 := by
    intro x hx
    apply b.equivFun.injective
    rw [Module.Basis.equivFun_apply, ← Algebra.leftMulMatrix_mulVec_repr,
      ← Module.Basis.equivFun_apply, hg, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hx, Matrix.one_mulVec, Module.Basis.equivFun_apply]
  have hunit : ∀ x : S, IsUnit x ↔ IsUnit (Algebra.leftMulMatrix b x).det := by
    intro x
    constructor
    · intro h
      exact (Matrix.isUnit_iff_isUnit_det _).mp (h.map (Algebra.leftMulMatrix b))
    · intro h
      exact ⟨⟨x, g x, key x h, by rw [mul_comm]; exact key x h⟩, rfl⟩
  have hopenS : IsOpen {x : S | IsUnit x} := by
    have h : {x : S | IsUnit x} =
        (fun x : S => (Algebra.leftMulMatrix b x).det) ⁻¹' {r : R | IsUnit r} :=
      Set.ext hunit
    rw [h]
    exact hopenR.preimage hLc.matrix_det
  have hc1 : ContinuousOn (fun x : S => Ring.inverse (Algebra.leftMulMatrix b x).det)
      {x : S | IsUnit x} :=
    hinvR.comp hLc.matrix_det.continuousOn (fun x hx => (hunit x).mp hx)
  have hc2 : ContinuousOn (fun x : S => (Algebra.leftMulMatrix b x)⁻¹) {x : S | IsUnit x} := by
    simp_rw [Matrix.inv_def]
    exact hc1.smul hLc.matrix_adjugate.continuousOn
  have hsymm : Continuous (b.equivFun.symm : (ι → R) → S) :=
    LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hc3 : ContinuousOn g {x : S | IsUnit x} := by
    have h : g = (fun M : Matrix ι ι R => b.equivFun.symm (Matrix.mulVec M (b.equivFun 1))) ∘
        (fun x : S => (Algebra.leftMulMatrix b x)⁻¹) := by
      funext x
      exact hg x
    rw [h]
    exact (hsymm.comp (continuous_id.matrix_mulVec continuous_const)).comp_continuousOn hc2
  have hgu : ∀ u : Sˣ, g u = ↑u⁻¹ := by
    intro u
    calc g u = ↑u⁻¹ * (↑u * g u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ↑u⁻¹ := by rw [key _ ((hunit _).mp u.isUnit), mul_one]
  exact ⟨⟨Units.isEmbedding_val_mk' hc3 hgu, hopenS⟩⟩


open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
theorem _root_.GlobalTheory.GaugeEx.nice_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], _root_.GlobalTheory.GaugeEx.Nice R → IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsOpenUnits (R ⊗[F] E) := by
  intro F E _ _ _ _ _ R _ _ _ _ _ _ _ _ _ hR
  obtain ⟨hArt, hRed, hOpen, -⟩ := hR
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨?_, ?_, ?_⟩
  · exact IsArtinianRing.of_finite R (R ⊗[F] E)
  · exact _root_.GlobalTheory.ReducedAlg.isReduced_tensor (k := F) R E
  · haveI := _root_.GlobalTheory.GaugeEx.modTopTens (F := F) (E := E) R
    haveI := _root_.GlobalTheory.GaugeEx.topRingTens (F := F) (E := E) R
    exact _root_.GlobalTheory.GaugeEx.isOpenUnits_of_basis
      (Algebra.TensorProduct.basis R (Module.finBasis F E))

end GlobalTheory.GaugeEx
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix

theorem _root_.GlobalTheory.T.exists_latS_eq_of_lattice_last_coord_dvd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → (∀ x, σ (σ x) = x) → ∃ e : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∀ t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∃ s : intV E w, (t - s • e).1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L := by
  first | exact @GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span | exact GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span | (intros; apply GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix

theorem _root_.GlobalTheory.T.unitary_maps_latS_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → ∀ (L' : Submodule (𝓞 E) (Fin n → E)) (Y : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), Y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ x : Fin n → TensorProduct F E (FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L' ↔ ((Y⁻¹ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) : Matrix (Fin n) (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L) → ∀ z ∈ dualSet (σ : E →+* E) J L', ((bc (prV (E := E) w) Y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z a)) ∈ latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)) := by
  first | exact @GlobalTheory.Mem.LevDual.unitary_carry_dual | exact GlobalTheory.Mem.LevDual.unitary_carry_dual | (intros; apply GlobalTheory.Mem.LevDual.unitary_carry_dual <;> assumption)
end

section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaDensityScale

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ENNReal}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c' = c := by
  obtain ⟨l, hl, ht⟩ := h
  obtain ⟨l', hl', ht'⟩ := h'
  have e : l = l' := GlobalTheory.OmegaLebUnique.omegaLeb_unique P Q l l' hl hl'
  subst e
  exact tendsto_nhds_unique ht' ht

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ENNReal}
    (h : OmegaDensity μ c) (a : NNReal) : OmegaDensity ((a : ENNReal) • μ) (a * c) := by
  obtain ⟨l, hl, ht⟩ := h
  refine ⟨l, hl, ?_⟩
  have h2 := ENNReal.Tendsto.const_mul (a := (a : ENNReal)) ht (Or.inr ENNReal.coe_ne_top)
  refine h2.congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

theorem omegaDensity_unique_and_smul : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)) (c : ENNReal),
    OmegaDensity μ c → (∀ c', OmegaDensity μ c' → c' = c) ∧
      ∀ a : NNReal, OmegaDensity ((a : ENNReal) • μ) (a * c) :=
  fun _ _ _ _ h => ⟨fun _ h' => omegaDensity_unique h h', fun a => omegaDensity_smul h a⟩

end GlobalTheory.OmegaDensityScale
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.NormPrime

variable {R : Ranks}

theorem sqrtMinusD_mem (H : Host R) : H.sqrtMinusD ∈ H.K :=
  IntermediateField.mem_adjoin_simple_self ℚ _

theorem isTotallyComplex_K (H : Host R) : IsTotallyComplex H.K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  set b : H.K := ⟨H.sqrtMinusD, sqrtMinusD_mem H⟩
  have hb : b ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [b] using H.sqrtMinusD_sq
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hw) hb
  rw [map_pow, map_neg, map_natCast] at h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw b)]

end GlobalTheory.Mem.NormPrime
end

section

open NumberField
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.AmbCrd

open Formalism.L2.DIV

section Frames

variable {K : Type} [Field K] [NumberField K]


open Classical in
def frm {n : ℕ} (H : Matrix (Fin n) (Fin n) K) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => if (H.map v.embedding).PosDef then frameOf (H.map v.embedding) else 1

theorem frm_det {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) : IsUnit (frm H v).det := by
  unfold frm
  split_ifs with h
  · exact (frameOfSpec _ _ h).1
  · simp

theorem frm_of_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : (H.map v.embedding).PosDef) :
    frm H v = frameOf (H.map v.embedding) := by
  unfold frm
  rw [if_pos h]

end Frames

section Coord

variable {K : Type} [Field K]

def rdx {a b : ℕ} (h : a = b) : (Fin b → K) ≃ₗ[K] (Fin a → K) := LinearEquiv.funCongrLeft K K (finCongr h)

theorem rdx_apply {a b : ℕ} (h : a = b) (x : Fin b → K) (i : Fin a) : rdx h x i = x (Fin.cast h i) := rfl

theorem rdx_refl {a : ℕ} (h : a = a) (x : Fin a → K) : rdx h x = x := by
  funext i
  rw [rdx_apply]
  rfl

end Coord

end GlobalTheory.AmbCrd

end
end

section

open Formalism.L2.DIV

namespace GlobalTheory.IdemExpand

theorem coeff_idemOf_eq {G : Type} [Group G] [Fintype G] (X : Finset (G → ℂ)) (t : G) :
    (idemOf X).coeff t = ∑ χ ∈ X, χ 1 / (Fintype.card G : ℂ) * χ t⁻¹ := by
  classical
  simp only [idemOf, chiIdem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ t]
  simp

theorem sum_coeff_mul {G : Type} [Group G] [Fintype G] (x y : MonoidAlgebra ℂ G) (ψ : G → ℂ) :
    ∑ g, (x * y).coeff g * ψ g = ∑ b, y.coeff b * ∑ a, x.coeff a * ψ (a * b) := by
  have h : ∀ g, (x * y).coeff g = ∑ b, x.coeff (g * b⁻¹) * y.coeff b := by
    intro g
    rw [MonoidAlgebra.coeff_mul_apply_right, Finsupp.sum_fintype]
    intro i; simp
  simp only [h, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight b⁻¹) _ _ fun g => ?_
  simp only [Equiv.coe_mulRight, inv_mul_cancel_right]
  ring

theorem eq_idemOf_filter : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] [inst_2 : DecidableEq G] (A : Finset (G → ℂ)) (e : MonoidAlgebra ℂ G), (∀ ψ ∈ A, ψ 1 ≠ 0) → (∀ g : G, ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0) → (∀ ψ ∈ A, ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x) → e * e = e → e = idemOf (A.filter fun ψ => ∑ g, e.coeff g * ψ g = ψ 1) := by
  intro G _ _ _ A e hone hcol hsc hee
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 : ∀ ψ ∈ A, (∑ g, e.coeff g * ψ g) = 0 ∨ (∑ g, e.coeff g * ψ g) = ψ 1 := by
    intro ψ hψ
    have h := sum_coeff_mul e e ψ
    rw [hee] at h
    have h' : ψ 1 * ∑ b, e.coeff b * ∑ a, e.coeff a * ψ (a * b)
        = (∑ g, e.coeff g * ψ g) * ∑ g, e.coeff g * ψ g := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, hsc ψ hψ b]
      ring
    rw [← h] at h'
    by_cases h0 : (∑ g, e.coeff g * ψ g) = 0
    · exact Or.inl h0
    · exact Or.inr (mul_right_cancel₀ h0 h').symm
  refine MonoidAlgebra.ext (Finsupp.ext fun t => ?_)
  have h1 : (Fintype.card G : ℂ) * e.coeff t = ∑ ψ ∈ A, (∑ g, e.coeff g * ψ g) * ψ t⁻¹ := by
    have a1 : ∑ g, e.coeff g * ∑ ψ ∈ A, ψ 1 * ψ (g * t⁻¹) = (Fintype.card G : ℂ) * e.coeff t := by
      simp only [hcol, mul_inv_eq_one, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ t]
      simp [mul_comm]
    rw [← a1, ← Finset.sum_congr rfl fun ψ hψ => hsc ψ hψ t⁻¹]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ψ _ => Finset.sum_congr rfl fun g _ => ?_
    ring
  apply mul_left_cancel₀ hn
  rw [h1, coeff_idemOf_eq, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ψ hψ => ?_
  split_ifs with h
  · rw [h]; field_simp
  · rcases h2 ψ hψ with h0 | h0
    · rw [h0, zero_mul]
    · exact absurd h0 h

end GlobalTheory.IdemExpand
end

section

open Formalism.L2.DIV

namespace GlobalTheory

theorem absIrrChar_mem_closure_primitiveRoot {G : Type} [Group G] [Fintype G] {K : Type} [Field K]
    [CharZero K] (z : K) (hz : IsPrimitiveRoot z (Fintype.card G)) (χ : G → K) (hχ : IsAbsIrrChar χ)
    (g : G) : χ g ∈ Subring.closure ({z} : Set K) := by
  obtain ⟨n, ρ, -, hch⟩ := hχ
  set N := Fintype.card G with hN
  haveI : NeZero N := ⟨Fintype.card_ne_zero⟩
  set f := ρ g with hf
  have hfN : f ^ N = 1 := by rw [hf, ← map_pow, pow_card_eq_one, map_one]
  have htr : LinearMap.trace (AlgebraicClosure K) _ f = (LinearMap.charpoly f).roots.sum := by
    rw [LinearMap.trace_eq_matrix_trace (AlgebraicClosure K) (Pi.basisFun (AlgebraicClosure K) (Fin n)),
      Matrix.trace_eq_sum_roots_charpoly, LinearMap.charpoly_toMatrix]
  have hz' : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) z) N :=
    hz.map_of_injective (algebraMap K (AlgebraicClosure K)).injective
  have hroot : ∀ μ ∈ (LinearMap.charpoly f).roots,
      ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k) := by
    intro μ hμ
    have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := hv.pow_apply N
    rw [hfN] at h1
    have hμN : μ ^ N = 1 := by
      have h2 : (μ ^ N - 1) • v = 0 := by
        rw [sub_smul, ← h1, one_smul]; simp
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv.2
    obtain ⟨k, -, hk⟩ := hz'.eq_pow_of_pow_eq_one hμN
    exact ⟨k, by rw [map_pow, hk]⟩
  have hsum : ∀ m : Multiset (AlgebraicClosure K),
      (∀ μ ∈ m, ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k)) →
      ∃ y ∈ Subring.closure ({z} : Set K), algebraMap K (AlgebraicClosure K) y = m.sum := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; exact ⟨0, zero_mem _, by simp⟩
    | cons a m ih =>
      intro h
      obtain ⟨y, hy, hy'⟩ := ih (fun μ hμ => h μ (Multiset.mem_cons_of_mem hμ))
      obtain ⟨k, hk⟩ := h a (Multiset.mem_cons_self a m)
      refine ⟨z ^ k + y, add_mem (pow_mem (Subring.subset_closure (Set.mem_singleton z)) k) hy, ?_⟩
      rw [Multiset.sum_cons, map_add (f := _), hy', hk]
  obtain ⟨y, hy, hy'⟩ := hsum _ hroot
  have hχg : algebraMap K (AlgebraicClosure K) (χ g) = algebraMap K (AlgebraicClosure K) y := by
    rw [← hch g, hy', ← htr]; rfl
  rw [(algebraMap K (AlgebraicClosure K)).injective hχg]
  exact hy

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem uloc_of_triv_disc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (_ : (T : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ levelVL σ J v S.Lb)
    (_ : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb),
    x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad S v hT x hx hy
  have hL : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := by
    unfold Formalism.UG.levelVL Formalism.UG.level at hx
    exact hx.2
  have hLi : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔
      ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
        latS (F := F) (v.adicCompletion F) (intV E v) S.Lb :=
    (stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)).inv_mem hL
  have hsub : latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    unfold Formalism.UG.latS
    apply Submodule.span_mono
    apply Set.image_mono
    intro z hz
    exact Submodule.subset_span (S.Lb_int z hz)
  have hfw : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    intro y hy'
    have h2 := Submodule.add_mem _ (hsub (hy y hy')) hy'
    rwa [sub_add_cancel] at h2
  have hbw : ∀ y, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) →
      y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    intro y hw
    have hd := hy _ hw
    have hi := hsub ((hLi _).1 hd)
    have key : y = (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y -
        ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
          ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
            ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) -
            (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) := by
      have hinv : ∀ u, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
          ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ u) = u := by
        intro u
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [Matrix.mulVec_sub, hinv, hinv, sub_sub_cancel]
    rw [key]
    exact Submodule.sub_mem _ hw hi
  rw [S.UlocAlt v hT, Subgroup.mem_inf]
  refine ⟨hx, ⟨?_, ?_⟩⟩
  · show ∀ y, y ∈ _ ↔ _
    exact fun y => ⟨hfw y, hbw y⟩
  · intro z
    have h0 := S.fT_L v hT
      (⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (z : Fin n → E ⊗[F] v.adicCompletion F), hfw z z.2⟩ - z)
      (by
        show (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (z : Fin n → E ⊗[F] v.adicCompletion F) -
          (z : Fin n → E ⊗[F] v.adicCompletion F) ∈ _
        exact hy z z.2)
    rw [map_sub, sub_eq_zero] at h0
    exact h0

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG

namespace GlobalTheory.Mem.Col2

def FunKilled {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (π : 𝓞 E) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (t t' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
    t'.1 = inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0

end GlobalTheory.Mem.Col2
end
