module

public import Formalism.PeriodIntegrals.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Bundle001
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

def TopStep : Prop := CayleyFin → EigAvoid → PI.UnitaryApproxFin.UnitaryApproxFin
def CayleyStep : Prop := ApproxE → BddR → UnitS → CayleyFin
def ApproxEStep : Prop := WeakApproxF → ApproxE

theorem unitaryApproxFin_of (h1 : TopStep) (h2 : CayleyStep) (h3 : ApproxEStep)
    (hW : WeakApproxF) (hB : BddR) (hU : UnitS) (hE : EigAvoid) :
    PI.UnitaryApproxFin.UnitaryApproxFin :=
  h1 (h2 (h3 hW) hB hU) hE

end PI.UnitaryApproxFinWork

end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : Type} [Fintype n] [DecidableEq n]

def MS (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
    (M : Matrix n n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i j, M i j ∈ Sv E v

def MC (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F)
    (M : Matrix n n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∃ A, MS E v A ∧ M = dv E v d • A

variable {v : HeightOneSpectrum (𝓞 F)}

theorem MS_mul {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)

theorem MS_add {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M + N) := fun i j => Subring.add_mem _ (hM i j) (hN i j)

theorem MS_sub {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M - N) := fun i j => Subring.sub_mem _ (hM i j) (hN i j)

theorem MS_one : MS E v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem MS_smul {a : E ⊗[F] v.adicCompletion F} (ha : a ∈ Sv E v)
    {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : MS E v (a • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ ha (hM i j)

def toS {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : Matrix n n (Sv E v) :=
  fun i j => ⟨M i j, hM i j⟩

theorem map_toS {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    (Sv E v).subtype.mapMatrix (toS hM) = M := by
  ext i j
  rfl

theorem MS_adjugate {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    MS E v M.adjugate := by
  intro i j
  rw [← map_toS hM, ← RingHom.map_adjugate]
  exact ((toS hM).adjugate i j).2

private lemma dv_mem_Sv' (d : 𝓞 F) : dv E v d ∈ Sv E v := by
  apply Subring.subset_closure
  left
  exact ⟨⟨algebraMap F E (d : F),
    ⟨⟨algebraMap F E (d : F), (RingOfIntegers.isIntegral_coe d).algebraMap⟩, rfl⟩⟩, rfl⟩

theorem det_one_add (π : 𝓞 F) {A : Matrix n n (E ⊗[F] v.adicCompletion F)} (hA : MS E v A) :
    ∃ s ∈ Sv E v, (1 + dv E v π • A).det = 1 + dv E v π * s := by
  let p : Sv E v := ⟨dv E v π, dv_mem_Sv' π⟩
  let B := toS hA
  let I : Ideal (Sv E v) := Ideal.span {p}
  have hp0 : Ideal.Quotient.mk I p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have h0 : (Ideal.Quotient.mk I).mapMatrix (p • B) = 0 := by
    ext i j
    simp [hp0]
  have hmap : (Ideal.Quotient.mk I).mapMatrix (1 + p • B) = 1 := by
    rw [map_add (f := _), map_one, h0, add_zero]
  have hdet : Ideal.Quotient.mk I ((1 + p • B).det - 1) = 0 := by
    rw [map_sub, RingHom.map_det, hmap, Matrix.det_one, map_one, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdet)
  refine ⟨(t : E ⊗[F] v.adicCompletion F), t.2, ?_⟩
  have h2 : (Sv E v).subtype.mapMatrix (1 + p • B) = 1 + dv E v π • A := by
    rw [map_add (f := _), map_one]
    congr 1
  have h4 : (1 + p • B).det = 1 + p * t := by
    rw [mul_comm, ht]
    ring
  rw [← h2, ← RingHom.map_det, h4]
  simp [p]

theorem MC_entries {d : 𝓞 F} {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (h : MC E v d M) (i j : n) :
    Cong E v d (M i j) := by
  obtain ⟨A, hA, rfl⟩ := h
  exact ⟨A i j, hA i j, by rw [Matrix.smul_apply, smul_eq_mul]⟩

theorem MC_of_entries {d : 𝓞 F} {M : Matrix n n (E ⊗[F] v.adicCompletion F)}
    (h : ∀ i j, Cong E v d (M i j)) : MC E v d M := by
  choose t ht heq using h
  refine ⟨Matrix.of fun i j => t i j, fun i j => ht i j, ?_⟩
  ext i j
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact heq i j

theorem MC_cancel {c e : 𝓞 F} (hc : c ≠ 0) {M A : Matrix n n (E ⊗[F] v.adicCompletion F)}
    (h : dv E v c • M = dv E v (c * e) • A) : M = dv E v e • A := by
  have hx : algebraMap F E (c : F) ≠ 0 := by simpa using hc
  have hu : IsUnit (dv E v c) :=
    (IsUnit.mk0 _ hx).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))
  have hmul : dv E v (c * e) = dv E v c * dv E v e := by simp [dv]
  rw [hmul, mul_smul] at h
  exact hu.smul_left_cancel.1 h

theorem sigma_mem_intOE (σ : E →ₐ[F] E) {x : E} (hx : x ∈ PI.UnitaryApproxDefs.intOE E) : σ x ∈ PI.UnitaryApproxDefs.intOE E := by
  simp only [PI.UnitaryApproxDefs.intOE, RingHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨σ y, (RingOfIntegers.isIntegral_coe y).map σ.toRingHom.toIntAlgHom⟩, rfl⟩

theorem sigR_mem_Sv (σ : E →ₐ[F] E) {s : E ⊗[F] v.adicCompletion F} (hs : s ∈ Sv E v) :
    PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) s ∈ Sv E v := by
  have h : Sv E v ≤ (Sv E v).comap (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · simp only [Subring.coe_comap, Set.mem_preimage]
      apply Subring.subset_closure
      left
      exact ⟨⟨σ x, sigma_mem_intOE σ hx⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩
    · simp only [Subring.coe_comap, Set.mem_preimage]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩
  exact h hs

theorem MS_cT (σ : E →ₐ[F] E) {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    MS E v (PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) M) := fun i j => sigR_mem_Sv σ (hM j i)

theorem sigR_dv (σ : E →ₐ[F] E) (d : 𝓞 F) : PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (dv E v d) = dv E v d := by
  simp [PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE, dv]

theorem cT_map (σ : E →ₐ[F] E) (M : Matrix n n E) :
    PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (M.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) =
      (PI.UnitaryApproxDefs.cT (σ : E →+* E) M).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT, PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]

end PI.UnitaryApproxFinWork

end
end

section

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace PI.UnitaryApproxFinWork

variable {F : Type} [Field F] [NumberField F]

theorem wa_isOpen_lt_one (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    IsOpen {y : v.adicCompletion F | Valued.v (y - x) < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [Valued.mem_nhds]
  refine ⟨1, fun z hz => ?_⟩
  have hz' : Valued.v (z - y) < 1 := by
    first
      | simpa using hz
  simp only [Set.mem_setOf_eq] at hy ⊢
  have hzx : z - x = (z - y) + (y - x) := by abel
  rw [hzx]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hz' hy)

theorem wa_valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem wa_exists_close (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ b : F, Valued.v (x - algebraMap F (v.adicCompletion F) b) < 1 := by
  have hd : DenseRange (algebraMap F (v.adicCompletion F)) := by
    first
      | exact denseRange_algebraMap F v
  obtain ⟨b, hb⟩ := hd.exists_mem_open (wa_isOpen_lt_one v x) ⟨x, by simp⟩
  refine ⟨b, ?_⟩
  rw [Valuation.map_sub_swap]
  exact hb

theorem wa_exists_int_approx (T : Finset (HeightOneSpectrum (𝓞 F)))
    (b : HeightOneSpectrum (𝓞 F) → F) :
    ∃ a : F, ∀ v ∈ T, v.valuation F (a - b v) ≤ 1 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) (T.image b)
  have hd0 : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hdF : algebraMap (𝓞 F) F (d : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hint : ∀ v ∈ T, ∃ n : 𝓞 F, algebraMap (𝓞 F) F n = algebraMap (𝓞 F) F (d : 𝓞 F) * b v := by
    intro v hv
    obtain ⟨n, hn⟩ := hd (b v) (Finset.mem_image_of_mem b hv)
    exact ⟨n, by rw [hn, Algebra.smul_def]⟩
  choose! n hn using hint
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), v.intValuation (d : 𝓞 F) ≠ 0 := by
    intro v
    first
      | exact v.intValuation_ne_zero _ hd0
  have hexp : ∀ v : HeightOneSpectrum (𝓞 F), ∃ e : ℕ,
      WithZero.exp (-(e : ℤ)) ≤ v.intValuation (d : 𝓞 F) := by
    intro v
    obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation (d : 𝓞 F) = WithZero.exp k := by
      first
        | exact ⟨_, (WithZero.exp_log (hne v)).symm⟩
    refine ⟨k.natAbs, ?_⟩
    rw [hk, WithZero.exp_le_exp]
    first
      | omega
  choose e he using hexp
  obtain ⟨m, hm⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) e
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => n v.1)
  refine ⟨algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F (d : 𝓞 F), fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ (e v)).mpr (hm v hv)
  have hkey : algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F (d : 𝓞 F) - b v =
      algebraMap (𝓞 F) F (m - n v) / algebraMap (𝓞 F) F (d : 𝓞 F) := by
    rw [eq_div_iff hdF, sub_mul, div_mul_cancel₀ _ hdF, map_sub, hn v hv]
    ring
  rw [hkey, map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
  have hlt : (0 : WithZero (Multiplicative ℤ)) < v.intValuation (d : 𝓞 F) := zero_lt_iff.mpr (hne v)
  first
    | exact (div_le_one₀ hlt).mpr (h1.trans (he v))

theorem weak_approximation_finite_unitary : WeakApproxF := by
  intro F _ _ T c D hD
  have hDF : ((D : 𝓞 F) : F) ≠ 0 := by
    first
      | exact_mod_cast hD
  choose b hb using fun v : HeightOneSpectrum (𝓞 F) =>
    wa_exists_close v (c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹)
  obtain ⟨a', ha'⟩ := wa_exists_int_approx T b
  refine ⟨(D : F) * a', fun v hv => ?_⟩
  have hdv0 : algebraMap F (v.adicCompletion F) (D : F) ≠ 0 := (map_ne_zero _).mpr hDF
  refine ⟨c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) a', ?_, ?_⟩
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    have e1 : c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) a' =
        (c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) (b v)) +
          algebraMap F (v.adicCompletion F) (b v - a') := by
      rw [map_sub]
      ring
    rw [e1]
    refine le_trans (Valuation.map_add _ _ _) (max_le (hb v).le ?_)
    rw [wa_valued_algebraMap, Valuation.map_sub_swap]
    exact ha' v hv
  · rw [map_mul, mul_sub, mul_comm (algebraMap F (v.adicCompletion F) (D : F)) (c v * _), mul_assoc,
      inv_mul_cancel₀ hdv0, mul_one]

end PI.UnitaryApproxFinWork

end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cT_smul_one {A : Type} [CommRing A] (ρ : A →+* A) (a : A) :
    PI.UnitaryApproxDefs.cT ρ (a • (1 : Matrix n n A)) = ρ a • 1 := by
  ext i j
  simp only [PI.UnitaryApproxDefs.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

def scU {A : Type} [CommRing A] (a b : A) (h : a * b = 1) : GL n A :=
  ⟨a • 1, b • 1, by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, h, one_smul],
    by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_comm, h, one_smul]⟩

theorem scU_val {A : Type} [CommRing A] (a b : A) (h : a * b = 1) :
    ((scU (n := n) a b h : GL n A) : Matrix n n A) = a • 1 := rfl

theorem scU_mem_UJ {A : Type} [CommRing A] (ρ : A →+* A) (J : Matrix n n A) (a b : A) (h : a * b = 1)
    (hρ : ρ a * a = 1) : scU (n := n) a b h ∈ PI.UnitaryApproxDefs.UJ ρ J := by
  show PI.UnitaryApproxDefs.cT ρ ((scU (n := n) a b h : GL n A) : Matrix n n A) * J *
    ((scU (n := n) a b h : GL n A) : Matrix n n A) = J
  rw [scU_val, cT_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    mul_comm, hρ, one_smul]

end General

section Tensor

variable {F E : Type} [Field F] [CommRing E] [Algebra F E]

theorem sigR_inclE (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) :
    PI.UnitaryApproxDefs.sigR σ R (PI.UnitaryApproxDefs.inclE (F := F) R e) = PI.UnitaryApproxDefs.inclE (F := F) R (σ e) := by
  first
  | rfl
  | simp [PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]

end Tensor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_intOE_of_isIntegral {x : E} (h : IsIntegral ℤ x) : x ∈ PI.UnitaryApproxDefs.intOE E := RingHom.mem_range.2 ⟨⟨x, h⟩, rfl⟩

theorem algebraMap_mem_intOE (a : 𝓞 F) : algebraMap F E (a : F) ∈ PI.UnitaryApproxDefs.intOE E := mem_intOE_of_isIntegral (IsIntegral.algebraMap (NumberField.RingOfIntegers.isIntegral_coe a))

theorem exists_nat_mul (x : E) : ∃ m : ℕ, 0 < m ∧ (m : E) * x ∈ PI.UnitaryApproxDefs.intOE E := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  rw [zsmul_eq_mul] at hyint
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, mem_intOE_of_isIntegral ?_⟩
  rw [Nat.cast_natAbs]
  rcases abs_choice y with h | h
  · rw [h]
    exact hyint
  · rw [h]
    push_cast
    rw [neg_mul]
    exact hyint.neg

theorem exists_int_mul (x : E) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ algebraMap F E (c : F) * x ∈ PI.UnitaryApproxDefs.intOE E := by
  obtain ⟨m, hm, hx⟩ := exists_nat_mul x
  refine ⟨(m : 𝓞 F), by exact_mod_cast hm.ne', ?_⟩
  simpa using hx

theorem inclE_mem_Sv (v : HeightOneSpectrum (𝓞 F)) {x : E} (hx : x ∈ PI.UnitaryApproxDefs.intOE E) :
    PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) x ∈ Sv E v := Subring.subset_closure (Set.mem_union_left _ ⟨⟨x, hx⟩, rfl⟩)

theorem one_tmul_mem_Sv (v : HeightOneSpectrum (𝓞 F)) {t : v.adicCompletion F}
    (ht : t ∈ v.adicCompletionIntegers F) : (1 : E) ⊗ₜ[F] t ∈ Sv E v := Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)

theorem dv_mem_Sv (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) : dv E v d ∈ Sv E v := inclE_mem_Sv v (algebraMap_mem_intOE d)

theorem dv_mul (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) : dv E v (a * b) = dv E v a * dv E v b := by
  unfold dv
  rw [show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul, map_mul]

end PI.UnitaryApproxFinWork

end
end
