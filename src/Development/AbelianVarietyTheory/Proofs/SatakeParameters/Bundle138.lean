module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle121
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle131
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle122
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle128
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle087
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem filtration_eq_span_pow : ∀ (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  ∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n} := by
  intro l _ Co ϖ hb n
  have he := core_isEps l Co
  obtain ⟨hfil, -, -, -⟩ := filtration_eq_xi_pow l Co.ε he
  obtain ⟨-, -, -, -, hdom, -, hk⟩ := thetaP_facts l
  haveI := hdom
  have hass : Associated (algebraMap (Per.Ainf l) (Per.AinfP l) (xi Co.ε)) (beta ϖ) :=
    Ideal.span_singleton_eq_span_singleton.1 ((hk Co.ε he).symm.trans hb)
  have hD : Associated (aDp l (xi Co.ε) ^ n) (betaD ϖ ^ n) :=
    (hass.map (algebraMap (Per.AinfP l) (Per.BdRp l))).pow_pow
  ext y
  rw [hfil, Ideal.mem_span_singleton]
  exact hD.dvd_iff_dvd_left

end GlobalTheory.Pst.StLat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem betaD_dvd_of_res : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ y : Per.BdRp l, (∀ k : ℕ, ∃ s ∈ Sg ϖ, betaD ϖ ∣ y - ((l : ℕ) : Per.BdRp l) ^ k * s) → betaD ϖ ∣ y := by
  intro l _ ϖ hk hF y hy
  obtain ⟨-, hker, hA, hD, -⟩ := GlobalTheory.MemLoc.thetaP_facts l
  have hb0 : Per.θP l (beta ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker, hk]; exact Ideal.mem_span_singleton_self _
  have hb : Per.θD l (betaD ϖ) = 0 := by rw [betaD, hD, hb0]
  have hS : ∀ a ∈ Sa ϖ, Per.θP l a ∈ 𝓞_ℂ_[l] := by
    intro a ha
    change a ∈ Algebra.adjoin _ _ at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx, hb0]; exact zero_mem _
    | algebraMap r => rw [hA]; exact (Per.θ l r).2
    | add x z _ _ hx hz => rw [map_add (Per.θP l)]; exact add_mem hx hz
    | mul x z _ _ hx hz => rw [map_mul]; exact mul_mem hx hz
  have hs : ∀ s ∈ Sg ϖ, ‖Per.θD l s‖ ≤ 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hD]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (hS a ha)
  have h0 : Per.θD l y = 0 := by
    have hle : ∀ k : ℕ, ‖Per.θD l y‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ ^ k := by
      intro k
      obtain ⟨s, hsS, c, hc⟩ := hy k
      have h1 := congrArg (Per.θD l) hc
      rw [map_sub, map_mul, map_mul, hb, zero_mul, sub_eq_zero, map_pow, map_natCast] at h1
      rw [h1, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hs s hsS)
    exact norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (GlobalTheory.RingBasics.norm_p_lt (p := l))) hle)
  have hmem : y ∈ Per.FilP l 1 := ((GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.1 y).1 h0
  rw [hF 1, pow_one] at hmem
  exact Ideal.mem_span_singleton.1 hmem

end GlobalTheory.Pst.StLat
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceDiv

section Abstract

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (O : Subring R)

theorem single_mem (j i : n) : (Pi.single j (1 : R) : n → R) i ∈ O := by
  by_cases h : i = j
  · subst h; simpa using O.one_mem
  · simpa [Pi.single_eq_of_ne h] using O.zero_mem

theorem exists_factor (P Q : Matrix n n R)
    (H : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ P.mulVec y = Q.mulVec z) :
    ∃ M : Matrix n n O, P = Q * M.map O.subtype := by
  choose z hz1 hz2 using fun j => H (Pi.single j 1) (single_mem O j)
  refine ⟨Matrix.of fun i j => ⟨z j i, hz1 j i⟩, ?_⟩
  ext i j
  have := congrFun (hz2 j) i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this]
  rfl

theorem mem_range_of_mul_eq_one (M N : Matrix n n O) (h : M.map O.subtype * N.map O.subtype = 1) :
    ∃ k ∈ (Formalism.UG.bc (n := n) O.subtype).range, k.1 = M.map O.subtype := by
  have h1 : M * N = 1 := by
    apply Matrix.map_injective O.subtype_injective
    simp only [Matrix.map_mul]
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨_, ⟨⟨M, N, h1, mul_eq_one_comm.1 h1⟩, rfl⟩, rfl⟩

theorem double_coset (B m T T' : Matrix n n R) (hT : T' * T = 1)
    (h1 : ∀ z : n → R, (∀ i, z i ∈ O) → ∀ i, B.mulVec z i ∈ O)
    (h2 : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ y = B.mulVec z)
    (h3 : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ m.mulVec y = (B * T).mulVec z)
    (h4 : ∀ z : n → R, (∀ i, z i ∈ O) → ∃ y : n → R, (∀ i, y i ∈ O) ∧ m.mulVec y = (B * T).mulVec z) :
    ∃ k₁ ∈ (Formalism.UG.bc (n := n) O.subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := n) O.subtype).range,
      m = k₁.1 * T * k₂.1 := by
  obtain ⟨B0, hB0⟩ := exists_factor O B 1 fun y hy => ⟨_, h1 y hy, by rw [Matrix.one_mulVec]⟩
  rw [Matrix.one_mul] at hB0
  obtain ⟨C, hC⟩ := exists_factor O 1 B fun y hy => by rw [Matrix.one_mulVec]; exact h2 y hy
  obtain ⟨M, hM⟩ := exists_factor O m (B * T) h3
  obtain ⟨N, hN⟩ := exists_factor O (B * T) m fun z hz => (h4 z hz).imp fun y hy => ⟨hy.1, hy.2.symm⟩
  have hCB : C.map O.subtype * B = 1 := mul_eq_one_comm.1 hC.symm
  have hinv : T' * C.map O.subtype * (B * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ B, hCB, Matrix.one_mul, hT]
  have hMN : M.map O.subtype * N.map O.subtype = 1 := by
    have e : B * T * (M.map O.subtype * N.map O.subtype) = B * T := by
      rw [← Matrix.mul_assoc, ← hM, ← hN]
    calc _ = T' * C.map O.subtype * (B * T) * (M.map O.subtype * N.map O.subtype) := by
          rw [hinv, Matrix.one_mul]
      _ = 1 := by rw [Matrix.mul_assoc, e, hinv]
  obtain ⟨k₁, hk₁, e₁⟩ := mem_range_of_mul_eq_one O B0 C (by rw [← hB0, ← hC])
  obtain ⟨k₂, hk₂, e₂⟩ := mem_range_of_mul_eq_one O M N hMN
  exact ⟨k₁, hk₁, k₂, hk₂, by rw [e₁, e₂, ← hB0, hM]⟩

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sgT_mem_intA (v : HeightOneSpectrum (𝓞 F)) {y : Fv F v ⊗[F] E} (hy : y ∈ ordAt E v) :
    sgT E v y ∈ intA F E := by
  refine (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).2 fun w => ?_
  by_cases h : w = v
  · subst h; rwa [evF_sgT_self]
  · rw [evF_sgT_ne h]; exact zero_mem _

theorem sgT_mem_lamHat [StarRing E] (V : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    {y : Fin V.rank → Fv F v ⊗[F] E} (hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v) :
    (fun i => sgT E v (y i)) ∈ lamHat F V := by
  refine (mem_lamHat_iff V _).2 fun w => ?_
  by_cases h : w = v
  · subst h; simpa only [evF_sgT_self] using hy
  · simp only [evF_sgT_ne h]; exact zero_mem _

omit [NumberField E] in
theorem evF_mulVec {n : Type} [Fintype n] (v : HeightOneSpectrum (𝓞 F)) {f : Af F ⊗[F] E} (hf : evF E v f = 1)
    (A : Matrix n n (Af F ⊗[F] E)) (z : n → Af F ⊗[F] E) :
    (fun a => evF E v (f * A.mulVec z a)) = (A.map (evF E v)).mulVec fun i => evF E v (z i) := by
  funext a
  rw [map_mul, hf, one_mul, RingHom.map_mulVec]
  rfl

theorem double_coset_of_divG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram), IsIdemOf E v e → IsFrameAt V v h → ϖ ≠ 0 → DivG hc V e ϖ d g → ∃ k₁ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, (h⁻¹ * locMat hc V v g * h).1 = k₁.1 * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i)) * k₂.1 := by
  intro F E _ _ _ _ _ _ hc V v e h ϖ d g he hh hϖ ⟨B, h1, h2, h3, h4⟩
  have he1 := he.2.1
  have hfr : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (∀ i, y i ∈ ordAt E v) →
      h.1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := fun y hy => by
    refine (hh _).2 ?_
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]; exact hy
  have hback : ∀ y : Fin V.rank → Fv F v ⊗[F] E, h.1.mulVec ((h⁻¹).1.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hback' : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (h⁻¹).1.mulVec (h.1.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have key : ∀ y z : Fin V.rank → Af F ⊗[F] E,
      ((fun a => finP F E e * (finMat hc.sig V.gram g).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a) →
      (locMat hc V v g).1.mulVec (fun i => evF E v (y i)) =
        (B.map (evF E v) * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i))).mulVec fun i => evF E v (z i) := by
    intro y z hyz
    rw [locMat_val, ← evF_mulVec v he1, ← Matrix.mulVec_mulVec]
    have e2 : (Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i))).mulVec (fun i => evF E v (z i)) =
        fun i => evF E v (finP F E (inclR (AF F) (ϖ ^ d i)) * z i) := by
      funext i
      rw [Matrix.mulVec_diagonal, map_mul, evF_finP_incl]
    rw [e2, ← evF_mulVec v he1]
    funext a
    rw [congrFun hyz a]
  refine double_coset (ordAt E v) ((h⁻¹).1 * B.map (evF E v)) _ _
    (Matrix.diagonal fun i => inclR (Fv F v) (ϖ ^ d i)⁻¹) ?_ ?_ ?_ ?_ ?_
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← map_mul, inv_mul_cancel₀ (zpow_ne_zero _ hϖ), map_one]
  · intro z hz
    have := (mem_lamHat_iff V _).1 (h1 (fun i => sgT E v (z i)) fun i => sgT_mem_intA v (hz i)) v
    rw [evF_mulVec v he1] at this
    simp only [evF_sgT_self] at this
    rw [← Matrix.mulVec_mulVec]
    exact (hh _).1 this
  · intro y hy
    obtain ⟨z, hz, e2⟩ := h2 _ (sgT_mem_lamHat V v (hfr y hy))
    refine ⟨fun i => evF E v (z i), fun i => (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).1 (hz i) v, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← evF_mulVec v he1, ← hback' y]
    congr 1; funext a
    rw [← congrFun e2 a, map_mul, he1, one_mul, evF_sgT_self]
  · intro y hy
    obtain ⟨z, hz, e2⟩ := h3 _ (sgT_mem_lamHat V v (hfr y hy))
    refine ⟨fun i => evF E v (z i), fun i => (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).1 (hz i) v, ?_⟩
    have := key _ _ e2
    simp only [evF_sgT_self] at this
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (h⁻¹).1, ← this, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  · intro z hz
    obtain ⟨y, hy, e2⟩ := h4 (fun i => sgT E v (z i)) fun i => sgT_mem_intA v (hz i)
    refine ⟨(h⁻¹).1.mulVec fun i => evF E v (y i), (hh _).1 ((mem_lamHat_iff V _).1 hy v), ?_⟩
    have := key _ _ e2
    simp only [evF_sgT_self] at this
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (h⁻¹).1, ← this, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hback]

end GlobalTheory.PlaceDiv
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E), IsIdemOf E v e → (∀ g, Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1) ∧ (∀ g g', Supp hc V e g → Supp hc V e g' → locMat hc V v g = locMat hc V v g' → g = g') ∧ ∀ u ∈ HR (Fv F v) hc.sig V.gram, ∃ g, Supp hc V e g ∧ locMat hc V v g = u := by
  first | exact @GlobalTheory.SuppLocal.supp_local | exact GlobalTheory.SuppLocal.supp_local | (intros; apply GlobalTheory.SuppLocal.supp_local <;> assumption)
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

section General

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem SamePrime.lt_one_imp {ρ ρ' : E →+* ℂ_[l]} (h : SamePrime ρ ρ') (x : E) (hx : ‖ρ x‖ < 1) : ‖ρ' x‖ < 1 := by
  have hone : ∀ (σ : E →+* ℂ_[l]) (a : 𝓞 E), ¬ ‖σ (a : E)‖ < 1 → ‖σ (a : E)‖ = 1 := fun σ a ha =>
    le_antisymm (norm_int_le σ a) (not_lt.1 ha)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) :=
    ⟨primeOf ρ, primeOf_isPrime ρ, fun hb => by
      have := natCast_mem_primeOf ρ
      rw [hb, Ideal.mem_bot] at this
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)⟩
  obtain ⟨n, d, e | e⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  · have hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1 := d.2
    have hd' : ¬ ‖ρ' ((d : 𝓞 E) : E)‖ < 1 := fun c => hd ((h _).2 c)
    have e' : x * ((d : 𝓞 E) : E) = (n : E) := e
    have hn : ‖ρ (n : E)‖ < 1 := by
      rw [← e', map_mul, norm_mul, hone ρ _ hd, mul_one]
      exact hx
    have hn' := (h n).1 hn
    rwa [← e', map_mul, norm_mul, hone ρ' _ hd', mul_one] at hn'
  · exfalso
    have hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1 := d.2
    have e' : x * (n : E) = ((d : 𝓞 E) : E) := e
    apply hd
    rw [← e', map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (norm_int_le ρ n)) hx

theorem SamePrime.norm_eq {ρ ρ' : E →+* ℂ_[l]} (h : SamePrime ρ ρ') (x : E) : ‖ρ x‖ = ‖ρ' x‖ := by
  let u : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ_[l]).comp ρ.injective
  let w : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ_[l]).comp ρ'.injective
  have hu (x) : u x = ‖ρ x‖ := rfl
  have hw (x) : w x = ‖ρ' x‖ := rfl
  have he : u.IsEquiv w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun a =>
    ⟨SamePrime.lt_one_imp h a, SamePrime.lt_one_imp (fun b => (h b).symm) a⟩
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hn (σ : E →+* ℂ_[l]) : ‖σ (l : E)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have h1 : c = 1 := by
    have h2 := congrFun hce (l : E)
    simp only [hu, hw, hn] at h2
    have h3 : ((l : ℝ)⁻¹) ^ c = ((l : ℝ)⁻¹) ^ (1 : ℝ) := by rw [h2, Real.rpow_one]
    exact (Real.rpow_right_inj (by positivity) (by
      exact (inv_lt_one₀ (by positivity)).2 hl |>.ne)).1 h3
  have h4 := congrFun hce x
  simp only [hu, hw, h1, Real.rpow_one] at h4
  exact h4

end General

theorem norm_tauEmb_posPl_conj_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (IsResidueClassZero D p ∨ IsSg D p) → ∀ (z : Bool × HH D) (y : D.host.E), ‖tauEmb D lam (tauPl D (posPl D p z 1)) (D.host.conj y)‖ = ‖tauEmb D lam (tauPl D z) y‖ := by
  intro D p _ lam h z y
  have hcc : D.host.conj (D.host.conj y) = y := D.host.φ₀.injective (by
    rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply, Complex.conj_conj])
  have h1 := SamePrime.norm_eq (samePrime_step D p lam h z) (D.host.conj y)
  have h2 : rhoC D lam (tauPl D z) (D.host.conj y) = rhoH D lam (tauPl D z) y := by
    change rhoH D lam (tauPl D z) (D.host.conj (D.host.conj y)) = _
    rw [hcc]
  rw [h2] at h1
  rw [← coe_rhoH, ← coe_rhoH]
  exact h1

end GlobalTheory.KerStd
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.Proof.NarrowJetMoments

namespace GlobalTheory.DatumJets.HidaSetting

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem conj_notMem (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hT : Pr.T u ∈ S) (hg : ∀ i, Pr.g i ∈ S) :
    ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  have hTn : ∀ P ∈ rowSG Pr sel mu, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun P hP =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hP
  intro P hP hP'
  rcases (mem_Sall sel mu u P).1 hP with h | h <;> rcases (mem_Sall sel mu u _).1 hP' with h' | h'
  · refine conj_piT_notMem hPr u ⟨conjPrime₂ P, h'⟩ ?_
    change cO X.E (Pr.piT u) ∈ (conjPrime₂ P).asIdeal
    rw [mem_conjP, cO_cO]
    exact decoFin_mem_of_mem_divs h
  · exact hTn _ h' (natCast_mem_conjP.2 (T_mem hPr u ⟨P, h⟩))
  · exact hTn _ h (natCast_mem_conjP.1 (T_mem hPr u ⟨conjPrime₂ P, h'⟩))
  · exact conjP_notMem_rowSG hX hPr hsel hg h h'

theorem notMem_Sall (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) (hd : l ∣ Pr.cond)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Sall sel mu u) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  rcases (mem_Sall sel mu u P).1 hP with h | h
  · intro hm
    have h0 : Pr.piT u ∈ P.asIdeal := decoFin_mem_of_mem_divs h
    have h1 : (l : 𝓞 X.E) ∣ Pr.piT u - 1 :=
      (Nat.cast_dvd_cast (hd.mul_right _)).trans (hPr.piT_cong u)
    have h2 : Pr.piT u - 1 ∈ P.asIdeal := Ideal.mem_of_dvd _ h1 hm
    have h3 := P.asIdeal.sub_mem h0 h2
    rw [sub_sub_cancel] at h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · refine notMem_rowSG hPr hsel hl hS (fun i e => ?_) h
    subst e
    have h1 : Pr.g i ≡ 1 [MOD Pr.g i] := (hPr.g_cong i).of_dvd hd
    have h2 : Pr.g i ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
    exact (hPr.g_prime i).one_lt.ne' (Nat.dvd_one.1 h2)

theorem qOf_pos (P : HeightOneSpectrum (𝓞 X.E)) : 0 < Formalism.L2.Col.qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem vG_mem_rowSG {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) : P ∈ rowSG Pr sel mu := by
  classical
  exact Finset.mem_union.2 (Or.inl (mem_vGs_iff.2 ⟨i, h⟩))

theorem ne_bot_of_locP {E : Type} [Field E] [NumberField E] [StarRing E] {I : Submodule (𝓞 E) E} {P : HeightOneSpectrum (𝓞 E)}
    (h : localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) : I ≠ ⊥ := by
  rintro rfl
  have h1 : (1 : E) ∈ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) :=
    (mem_locP P _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, Submodule.mem_one.2 ⟨1, by simp⟩⟩
  rw [← h] at h1
  obtain ⟨s, hs, hs'⟩ := (mem_locP P _ _).1 h1
  rw [Submodule.mem_bot, smul_eq_zero] at hs'
  rcases hs' with h | h
  · exact hs (h ▸ zero_mem _)
  · exact one_ne_zero h

theorem setting_of_unit (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (i : Fin 2) (u : Pr.Word) (hT : Pr.T u ∈ S)
    (hg : ∀ i, Pr.g i ∈ S) (cst : LocCst X (rowSG Pr sel mu)) (hcst : cst.Ok) (A : Amb X) (a b : ℕ) (hLa : A.LaHyp a b ∅)
    (hE : A.ESmooth a b) (hU : A.AAUnit (Sall sel mu u)) :
    SplitSet A a b (Sall sel mu u) (X.conjO (Pr.piG i)) (Pr.g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ Pr.g i ∣ cBof sel mu cst u := by
  have hc2 : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P₀, hP₀⟩ : (Pr.vG i).Nonempty := Finset.card_pos.1 (hPr.vG_card i ▸ hX.f_pos)
  have hP₀r : P₀ ∈ rowSG Pr sel mu := vG_mem_rowSG hP₀
  have hne : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast this.symm)
  have hprod : 0 < ∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1 := Finset.prod_pos fun P _ => qOf_pos P.1
  obtain ⟨h1, h2, -, -, h5, h6⟩ := hLa
  refine ⟨⟨hX, ⟨h1, h2, conj_notMem hX hPr hsel u hT hg, hU, h5, h6⟩,
    ne_bot_of_locP (hU P₀ ((mem_Sall sel mu u P₀).2 (Or.inr hP₀r))), hE, hPr.g_prime i, ?_, ?_, fun P hP => ?_⟩,
    pow_pos hprod _, Nat.mul_pos (hPr.T_prime u).pos (pow_pos hprod _), ?_⟩
  · rw [hc2, mul_comm]
    exact hPr.piG_norm i
  · rw [hc2]
    exact (hPr.piG_cop i).symm
  · exact (mem_Sall sel mu u P).2 (Or.inr (vG_mem_rowSG (i := i) ((mem_divs hne P).2 hP)))
  · refine Dvd.dvd.mul_left (dvd_pow ?_ (Nat.one_le_iff_ne_zero.1 hcst.B_pos)) _
    have e : Formalism.L2.Col.qOf P₀ = Pr.g i := hPr.vG_norm i P₀ hP₀
    have hd := Finset.dvd_prod_of_mem (fun P : rowSG Pr sel mu => Formalism.L2.Col.qOf P.1)
      (Finset.mem_univ (⟨P₀, hP₀r⟩ : rowSG Pr sel mu))
    beta_reduce at hd
    rw [e] at hd
    exact hd

theorem typePrimeBadPrimesLevelsHypotheses_proof : GlobalTheory.DatumJets.TypePrimeBadPrimesLevelsHypotheses := by
  intro D EX sel δ B χ cD hH hsel i u mu cst hcst a b hLa hE
  obtain ⟨hcc, -, -, hX1, hPr⟩ := hH
  have hT : (recPrimes EX).T u ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)
  have hg : ∀ j, (recPrimes EX).g j ∈ badS D := fun j => Or.inl (by fin_cases j <;> simp)
  refine setting_of_unit hX1.ok hPr hsel i u hT hg cst hcst _ a b hLa hE fun P hP => ?_
  obtain ⟨l, n, -, hlP, hl, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  refine GlobalTheory.AAUnitAway.locP_AA D _ (recSeam D) _ δ B χ cD P l hl ?_ ?_ hlP ?_
  · intro hs
    refine notMem_Sall hPr hsel u hl (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.small_mem_badS D l hs) ?_ hP hlP
    exact ((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _
  · rintro rfl
    refine notMem_Sall hPr hsel u hl (Or.inl (by simp)) ?_ hP hlP
    exact (dvd_mul_left _ _).mul_right _
  · rw [hcc, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.DatumJets.HidaSetting
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.irreducible_wd_eigen_equal_norm : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := by
  first | exact @GlobalTheory.IrrWeilAbs.irrWD_eig_norm_eq | exact GlobalTheory.IrrWeilAbs.irrWD_eig_norm_eq | (intros; apply GlobalTheory.IrrWeilAbs.irrWD_eig_norm_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.segment_sum_tempered : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ Δ Δ' : Segment (w.adicCompletion E), (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → ¬ Δ.Precedes Δ' := by
  first | exact @GlobalTheory.UnitaryPrecedes.not_precedes_of_unitary | exact GlobalTheory.UnitaryPrecedes.not_precedes_of_unitary | (intros; apply GlobalTheory.UnitaryPrecedes.not_precedes_of_unitary <;> assumption)
end
