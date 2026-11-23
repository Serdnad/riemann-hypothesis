module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle187
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Mathlib.Algebra.Algebra.Hom.Rat
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.Proof.AbsoluteIrreducibilitySpan


open Formalism.MainNotions.N in
theorem absIrr_of_span {Γ k : Type} [Group Γ] [Field k] {a : ℕ} (ha : 0 < a) (ρ : Γ →* GL (Fin a) k)
    (M : Γ → Matrix (Fin a) (Fin a) k) (c : Γ → k)
    (hM : ∀ g, M g = c g • (ρ g : Matrix (Fin a) (Fin a) k))
    (h : Submodule.span k (Set.range M) = ⊤) : AbsIrrSub ρ ⊤ := by
  classical
  set K := AlgebraicClosure k
  have htop : Submodule.span K ((fun v : Fin a → k => (algebraMap k K) ∘ v) ''
      ((⊤ : Submodule k (Fin a → k)) : Set (Fin a → k))) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin a)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, trivial, ?_⟩
    ext x
    by_cases hx : x = j
    · subst hx; simp
    · simp [hx]
  unfold AbsIrrSub
  rw [htop]
  have : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W' _ hW => ?_⟩
  have key : ∀ X : Matrix (Fin a) (Fin a) k, ∀ v ∈ W', (X.map (algebraMap k K)).mulVec v ∈ W' := by
    intro X
    have hX : X ∈ Submodule.span k (Set.range M) := h ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      have h1 : (M g).map (algebraMap k K) = algebraMap k K (c g) •
          ((mapRep (algebraMap k K) ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := by
        ext p q
        simp [hM, mapRep]
      rw [h1, Matrix.smul_mulVec]
      exact W'.smul_mem _ (hW g v hv)
    | zero => intro v hv; simp
    | add x y _ _ hx hy =>
      intro v hv
      rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec]
      exact W'.add_mem (hx v hv) (hy v hv)
    | smul r x _ hx =>
      intro v hv
      have h1 : (r • x).map (algebraMap k K) = algebraMap k K r • x.map (algebraMap k K) := by
        ext p q
        simp
      rw [h1, Matrix.smul_mulVec]
      exact W'.smul_mem _ (hx v hv)
  by_cases hb : W' = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨b, hb'⟩ := Function.ne_iff.mp hv0
  rw [eq_top_iff, ← (Pi.basisFun K (Fin a)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have h2 := W'.smul_mem (v b)⁻¹ (key (Matrix.single j b 1) v hv)
  have hb2 : v b ≠ 0 := hb'
  have h3 : (v b)⁻¹ • ((Matrix.single j b (1 : k)).map (algebraMap k K)).mulVec v = Pi.basisFun K (Fin a) j := by
    rw [Matrix.map_single, map_one, Matrix.single_mulVec]
    ext x
    by_cases hx : x = j
    · subst hx; simp [hb2]
    · simp [hx]
  rw [h3] at h2
  exact h2

end GlobalTheory.Proof.AbsoluteIrreducibilitySpan
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

noncomputable section

namespace GlobalTheory.EmbInj

open Formalism.BasicNotions.Loc

section Local

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_iff_norm (x : Om l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact ((minpoly ℤ_[l] x).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_iff (LL : FinExt l) (x : ↥LL.1) : x ∈ OL LL ↔ ‖(x : Om l)‖ ≤ 1 := by
  rw [← isIntegral_iff_norm, OL, mem_integralClosure_iff]
  exact (isIntegral_algHom_iff (LL.1.val.restrictScalars ℤ_[l]) LL.1.val.toRingHom.injective).symm

theorem norm_algHom (K L : FinExt l) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq (L.1.val.comp τ) (L.1.val.comp τ).toRingHom.injective x
  have h2 := minpoly.algHom_eq K.1.val K.1.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
  [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : _root_.Formalism.BasicNotions.LocBridge l E Ω Gw O)

theorem norm_le_one_iff (y : ↥B.LL.1) : ‖(y : Om l)‖ ≤ 1 ↔ ∃ n : O, y = B.toLL n := by
  rw [← mem_OL_iff]
  constructor
  · intro h
    refine ⟨B.eO.symm ⟨y, h⟩, ?_⟩
    simp [LocBridge.toLL]
  · rintro ⟨n, rfl⟩
    exact (B.eO n).2

theorem toLL_inj : Function.Injective B.toLL := fun _ _ h => B.eO.injective (Subtype.ext h)

theorem exists_frac (y : ↥B.LL.1) : ∃ n d : O, d ≠ 0 ∧ B.toLL d * y = B.toLL n := by
  by_cases h : ‖(y : Om l)‖ ≤ 1
  · obtain ⟨n, hn⟩ := (norm_le_one_iff B y).1 h
    refine ⟨n, 1, fun h1 => ?_, by simp [hn]⟩
    have := congrArg B.toLL h1
    simp at this
  · have hy : y ≠ 0 := by
      rintro rfl
      simp at h
    have h' : ‖((y⁻¹ : ↥B.LL.1) : Om l)‖ ≤ 1 := by
      rw [IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 h).le
    obtain ⟨d, hd⟩ := (norm_le_one_iff B _).1 h'
    refine ⟨1, d, fun h1 => ?_, by rw [← hd, map_one, inv_mul_cancel₀ hy]⟩
    rw [h1, map_zero] at hd
    exact hy (inv_eq_zero.1 hd)

theorem algHom_ext (τ τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥B.LL.1)
    (h : ∀ x : E, τ ⟨B.j (algebraMap E Ω x), B.j_E x⟩ = τ' ⟨B.j (algebraMap E Ω x), B.j_E x⟩) :
    τ = τ' := by
  ext y
  by_contra hne
  have hpos : 0 < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (B.j_dense y.2) _ (half_pos hpos)
  rw [dist_eq_norm] at hx
  set z : ↥B.Kw.1 := ⟨B.j (algebraMap E Ω x), B.j_E x⟩ with hz
  have e : ((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1) =
      ((τ (y - z) : ↥B.LL.1) : Om l) - (τ' (y - z) : ↥B.LL.1) := by
    rw [map_sub, map_sub, hz, h x]
    push_cast
    ring
  have h1 := norm_algHom _ _ τ (y - z)
  have h2 := norm_algHom _ _ τ' (y - z)
  have h3 := norm_sub_le ((τ (y - z) : ↥B.LL.1) : Om l) (τ' (y - z) : ↥B.LL.1)
  have h4 : ‖((y - z : ↥B.Kw.1) : Om l)‖ < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ / 2 := hx
  rw [← e, h1, h2] at h3
  linarith

end Local

end GlobalTheory.EmbInj
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.EmbThroughCompletion

section Norm

theorem norm_le_one_of_isIntegral {R C : Type} [CommRing R] [NormedField C] [IsUltrametricDist C]
    [Algebra R C] (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {x : C} (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  let f : R →+* (NormedField.valuation (K := C)).integer :=
    (algebraMap R C).codRestrict _ (fun r => by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
      exact hR r)
  have h1 : IsIntegral (NormedField.valuation (K := C)).integer x :=
    hx.map_of_comp_eq f (RingHom.id C) (by ext r; rfl)
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h1
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe] at h2
  exact h2

variable {E C : Type} [Field E] [NumberField E] [NormedField C] [IsUltrametricDist C]

theorem norm_int_le_one (a : E →+* C) (x : 𝓞 E) : ‖a (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (R := ℤ) (fun r => by simpa using IsUltrametricDist.norm_intCast_le_one C r)
    (map_isIntegral_int a x.isIntegral_coe)

theorem norm_lt_one_iff (v : HeightOneSpectrum (𝓞 E)) (a b : E →+* C)
    (ha : ∀ x : 𝓞 E, ‖a (x : E)‖ < 1 ↔ x ∈ v.asIdeal) (hb : ∀ x : 𝓞 E, ‖b (x : E)‖ < 1 ↔ x ∈ v.asIdeal)
    (x : E) : ‖a x‖ < 1 ↔ ‖b x‖ < 1 := by
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  have hd : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ‖c ((d : 𝓞 E) : E)‖ = 1 :=
    fun c hc => le_antisymm (norm_int_le_one c _) (not_lt.1 fun h' => d.2 ((hc _).1 h'))
  rcases h with h | h
  · have key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) →
        (‖c x‖ < 1 ↔ n ∈ v.asIdeal) := by
      intro c hc
      have h1 := congrArg (fun y => ‖c y‖) h
      simp only [map_mul, norm_mul] at h1
      rw [← hc n]
      change ‖c x‖ * ‖c ((d : 𝓞 E) : E)‖ = ‖c (n : E)‖ at h1
      rw [hd c hc, mul_one] at h1
      rw [h1]
    rw [key a ha, key b hb]
  · have key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ¬ ‖c x‖ < 1 := by
      intro c hc hlt
      have h1 := congrArg (fun y => ‖c y‖) h
      simp only [map_mul, norm_mul] at h1
      change ‖c x‖ * ‖c (n : E)‖ = ‖c ((d : 𝓞 E) : E)‖ at h1
      rw [hd c hc] at h1
      have h2 := norm_int_le_one c n
      have h3 := norm_nonneg (c x)
      have h4 := norm_nonneg (c (n : E))
      nlinarith
    exact iff_of_false (key a ha) (key b hb)

end Norm

section Padic

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_iff (K : Loc.FinExt l) (x : K.1) : x ∈ Loc.OL K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  refine (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).symm.trans
    ⟨fun h => norm_le_one_of_isIntegral (fun r => ?_) h, fun h => isIntegral_of_norm_le_one _ h⟩
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  exact r.2

theorem not_isUnit_iff (K : Loc.FinExt l) (x : Loc.OL K) :
    ¬ IsUnit x ↔ ‖((x : K.1) : PadicAlgCl l)‖ < 1 := by
  have hx := (mem_OL_iff K _).1 x.2
  constructor
  · intro h
    refine lt_of_le_of_ne hx fun h1 => h ?_
    have h0 : (x : K.1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : K.1)⁻¹, (mem_OL_iff K _).2 ?_⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    rw [IntermediateField.coe_inv, norm_inv, h1, inv_one]
  · intro h hu
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hu
    have hy' := (mem_OL_iff K _).1 y.2
    have h1 := congrArg (fun z : Loc.OL K => ‖((z : K.1) : PadicAlgCl l)‖) hy
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h1
    have h3 := norm_nonneg ((x : K.1) : PadicAlgCl l)
    have h4 := norm_nonneg ((y : K.1) : PadicAlgCl l)
    nlinarith

variable {E : Type} [Field E] [NumberField E]

theorem sum_eq_zero (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) {n : ℕ}
    (y : Fin n → E) (c : Fin n → ℚ_[l]) (hc : ∑ k, c k • a (y k) = 0) : ∑ k, c k • b (y k) = 0 := by
  have hd : DenseRange (Pi.map fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ f : E →+* PadicAlgCl l, IsClopen {c : Fin n → ℚ_[l] | ‖∑ k, c k • f (y k)‖ < 1} := by
    intro f
    have := (IsUltrametricDist.isClopen_ball (0 : PadicAlgCl l) 1).preimage
      (f := fun c : Fin n → ℚ_[l] => ∑ k, c k • f (y k)) (by fun_prop)
    convert this using 1
    ext c
    simp
  have key : ∀ c : Fin n → ℚ_[l], ‖∑ k, c k • a (y k)‖ < 1 → ‖∑ k, c k • b (y k)‖ < 1 := by
    intro c
    refine hd.induction_on c ?_ fun q => ?_
    · have := (hcl a).compl.isClosed.union (hcl b).isClosed
      convert this using 1
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      exact imp_iff_not_or
    · have e : ∀ f : E →+* PadicAlgCl l,
          ∑ k, (Pi.map (fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) q) k • f (y k) =
            f (∑ k, (q k : E) * y k) := by
        intro f
        simp [Algebra.smul_def]
      rw [e a, e b]
      exact (h _).1
  by_contra hne
  have hpos : 0 < ‖∑ k, c k • b (y k)‖ := norm_pos_iff.2 hne
  obtain ⟨r, hr⟩ := NormedField.exists_lt_norm ℚ_[l] ‖∑ k, c k • b (y k)‖⁻¹
  have h1 := key (r • c) (by
    simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, hc, smul_zero, norm_zero, zero_lt_one])
  simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, norm_smul] at h1
  rw [inv_lt_iff_one_lt_mul₀ hpos] at hr
  linarith

theorem exists_conj (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) :
    ∃ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, g (a x) = b x := by
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ E
  have hroot : Polynomial.aeval (b pb.gen) (minpoly ℚ_[l] (a pb.gen)) = 0 := by
    have h0 := minpoly.aeval ℚ_[l] (a pb.gen)
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range] at h0 ⊢
    simp only [← map_pow] at h0 ⊢
    exact sum_eq_zero a b h _ _ h0
  obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) hroot
  refine ⟨g, fun x => ?_⟩
  have : ((g : PadicAlgCl l →+* PadicAlgCl l).comp a).toRatAlgHom = b.toRatAlgHom :=
    pb.algHom_ext hg
  exact DFunLike.congr_fun this x

variable {Ω : Type} [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

end Padic

end GlobalTheory.EmbThroughCompletion
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BlochKatoIntegralScalars

section Local

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_of_norm_le_one (K : Loc.FinExt l) (x : K.1) (h : ‖(x : PadicAlgCl l)‖ ≤ 1) :
    x ∈ Loc.OL K :=
  (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1
    (isIntegral_of_norm_le_one _ h)

theorem compactSpace_GK (K : Loc.FinExt l) : CompactSpace ↥(Loc.GK K) := by
  haveI := K.2
  have h : IsClosed ((Loc.GK K : Subgroup (Loc.GQ l)) : Set (Loc.GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed K.1
  exact isCompact_iff_compactSpace.1 h.isCompact

theorem exists_pow_mul_mem_OL {X : Type} [TopologicalSpace X] [CompactSpace X] (K : Loc.FinExt l) {m : ℕ}
    (c : X → Fin m → K.1) (hc : Continuous c) :
    ∃ N : ℕ, ∀ g j, (l : K.1) ^ N * c g j ∈ Loc.OL K := by
  have hc' : Continuous fun g (j : Fin m) => ((c g j : K.1) : PadicAlgCl l) :=
    continuous_pi fun j => continuous_subtype_val.comp ((continuous_apply j).comp hc)
  obtain ⟨C, hC⟩ := (isCompact_range hc').isBounded.exists_norm_le
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C hl
  refine ⟨N, fun g j => mem_OL_of_norm_le_one K _ ?_⟩
  have h1 : ‖((c g j : K.1) : PadicAlgCl l)‖ ≤ C :=
    (norm_le_pi_norm (fun j : Fin m => ((c g j : K.1) : PadicAlgCl l)) j).trans (hC _ ⟨g, rfl⟩)
  have h2 : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have := PadicAlgCl.norm_extends l (l : ℚ_[l])
    rw [map_natCast] at this
    rw [this, Padic.norm_p]
  have h3 : (((l : K.1) ^ N * c g j : K.1) : PadicAlgCl l) =
      (l : PadicAlgCl l) ^ N * ((c g j : K.1) : PadicAlgCl l) := by
    push_cast
    rfl
  rw [h3, norm_mul, norm_pow, h2, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  exact h1.trans hN.le

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

end Local

theorem mem_of_mk_mem_span {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (ρ : Representation R G M) (S : Submodule R (G → M)) (hB : ∀ x : M, (fun g => ρ g x - x) ∈ S)
    (A : Set (ReciprocityTheory.Gal.H1 ρ))
    (hA : ∀ x ∈ A, ∃ w : ReciprocityTheory.Gal.Z1 ρ, (w : G → M) ∈ S ∧ x = Submodule.Quotient.mk w)
    (w : ReciprocityTheory.Gal.Z1 ρ) (hw : Submodule.Quotient.mk w ∈ Submodule.span R A) : (w : G → M) ∈ S := by
  have hB' : (ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype ≤ S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype := by
    intro w hw
    obtain ⟨x, hx⟩ := (mem_coboundaries1 ρ _).1 hw
    have : (ReciprocityTheory.Gal.Z1 ρ).subtype w = fun g => ρ g x - x := funext hx
    rw [Submodule.mem_comap, this]
    exact hB x
  have hle : Submodule.span R A ≤ (S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map (Submodule.mkQ _) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hA x hx
    exact ⟨w, hw, rfl⟩
  have h2 : w ∈ ((S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map
      (Submodule.mkQ ((ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype))).comap (Submodule.mkQ _) :=
    hle hw
  rw [Submodule.comap_map_mkQ, sup_eq_right.2 hB'] at h2
  exact h2

end GlobalTheory.BlochKatoIntegralScalars
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.local_positivity_eulerFactor_prime : ∀ (b ω : ℕ → ℂ) (s C : ℝ) (p : ℕ), 0 < s → p.Prime → b 1 = 1 → ‖ω p‖ = 1 → (∀ r : ℕ, b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → Real.exp (‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ * ‖∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)‖ ^ 2 * (∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s)) * (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ := by
  first | exact @GlobalTheory.LocIneq.local_positivity_eulerFactor | exact GlobalTheory.LocIneq.local_positivity_eulerFactor | (intros; apply GlobalTheory.LocIneq.local_positivity_eulerFactor <;> assumption)
end
