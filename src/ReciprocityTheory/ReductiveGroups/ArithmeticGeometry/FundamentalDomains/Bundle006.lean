module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

lemma mem_orthogonal_lattice_iff {r : ℕ} (X : Data E r) (ξ v : Fin r → E) :
    v ∈ X.Λp ξ ↔ v ∈ X.Λ ∧ herm X.Gm v ξ = 0 := by first | exact Iff.rfl | simp [Data.Λp, Data.hermL]

lemma integer_smul_eq_coe_smul {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := by
  first
    | rfl
    | (funext i; simp [Algebra.smul_def])

lemma trace_form_integer_smul {r : ℕ} (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E)
    (β : 𝓞 E) :
    EFf ξ0 G x (β • y) = Algebra.trace ℚ E (cc (β : E) * (-ξ0 * herm G x y)) := by
  unfold EFf herm
  rw [integer_smul_eq_coe_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma herm_eq_zero_of_trace_form_vanish {r : ℕ} (ξ0 : E) (hξ0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E)
    (x y : Fin r → E) (h : ∀ β : 𝓞 E, EFf ξ0 G x (β • y) = 0) : herm G x y = 0 := by
  have hb : ∀ β : 𝓞 E, Algebra.trace ℚ E (cc (β : E) * (-ξ0 * herm G x y)) = 0 := fun β =>
    (trace_form_integer_smul ξ0 G x y β).symm.trans (h β)
  have hinv : ∀ a : E, cc (cc a) = a := by
    have h2 := pow_orderOf_eq_one (NumberField.IsCMField.complexConj E)
    rw [NumberField.IsCMField.orderOf_complexConj, pow_two] at h2
    intro a
    have := congrArg (fun σ => σ a) h2
    simpa [cc] using this
  have hw : ∀ w : E, Algebra.trace ℚ E (w * (-ξ0 * herm G x y)) = 0 := by
    intro w
    rw [← hinv w, ← (NumberField.integralBasis E).sum_repr (cc w)]

    simp only [cc, map_sum, map_rat_smul, Finset.sum_mul, smul_mul_assoc, LinearMap.map_smul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [NumberField.integralBasis_apply]
    have := hb ((NumberField.RingOfIntegers.basis E) i)
    simp only [cc] at this
    rw [smul_eq_zero]
    exact Or.inr this
  have hz : -ξ0 * herm G x y = 0 := by
    have hnd := traceForm_nondegenerate ℚ E
    have hw' : ∀ w : E, Algebra.traceForm ℚ E (-ξ0 * herm G x y) w = 0 := fun w => by
      rw [Algebra.traceForm_apply, mul_comm]
      exact hw w
    first
      | exact hnd _ hw'
      | exact hnd.1 _ hw'
  rcases mul_eq_zero.1 hz with h1 | h1
  · exact absurd (neg_eq_zero.1 h1) hξ0
  · exact h1

theorem hermitian_dual_lattice_identity : PerfectPairingQuotient (E := E) := by
  intro r X ξ hξ
  obtain ⟨hξΛ, hξξ, hξ0⟩ := hξ
  have hsm : ∀ (β : 𝓞 E) v, v ∈ X.Λp ξ → β • v ∈ X.Λp ξ := by
    intro β v hv
    rw [mem_orthogonal_lattice_iff] at hv ⊢
    refine ⟨X.Λ.smul_mem β hv.1, ?_⟩
    rw [integer_smul_eq_coe_smul, herm_smul_left, hv.2, mul_zero]
  have hξp : ξ ∈ X.Λp ξ := (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hξΛ, hξξ⟩
  constructor
  · intro φ hφ
    have : Module.Finite (𝓞 E) ↥X.Λ := Module.Finite.iff_fg.mpr X.Λ_fg
    have : Module.Finite ℤ ↥X.Λ := Module.Finite.trans (𝓞 E) ↥X.Λ
    let f : ↥X.Λ →ₗ[ℤ] E := ((X.hermL ξ).comp X.Λ.subtype.toAddMonoidHom).toIntLinearMap
    have hf : ∀ m : ↥X.Λ, f m = herm X.Gm (m : Fin r → E) ξ := fun m => rfl
    let P := LinearMap.ker f
    have : Module.IsTorsionFree ℤ (↥X.Λ ⧸ P) := by
      rw [Module.isTorsionFree_iff_smul_eq_zero]
      intro n q hq
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective P q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker,
        map_zsmul] at hq
      rcases smul_eq_zero.mp hq with h | h
      · exact Or.inl h
      · exact Or.inr ((Submodule.Quotient.mk_eq_zero P).mpr (LinearMap.mem_ker.mpr h))
    obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ LinearMap.id P.mkQ_surjective
    have hsq : ∀ q, P.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
    have hρ : ∀ m : ↥X.Λ, m - s (P.mkQ m) ∈ P := by
      intro m
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      change P.mkQ m - P.mkQ (s (P.mkQ m)) = 0
      rw [hsq, sub_self]
    let ψ : ↥X.Λ →+ ℤ :=
      { toFun := fun m => φ ⟨((m - s (P.mkQ m) : ↥X.Λ) : Fin r → E),
          (mem_orthogonal_lattice_iff _ _ _).mpr ⟨(m - s (P.mkQ m)).2, LinearMap.mem_ker.mp (hρ m)⟩⟩
        map_zero' := by
          rw [← map_zero φ]; congr 1; ext1; simp
        map_add' := by
          intro a b
          rw [← map_add φ]; congr 1; ext1
          simp only [map_add (f := _)]
          push_cast
          abel }
    obtain ⟨x, hxΛ, hx⟩ := X.EF_perf ψ
    have hval : ∀ ν : X.Λp ξ, (φ ν : ℚ) = EFf X.ξ0 X.Gm x ν := by
      intro ν
      have hν := (mem_orthogonal_lattice_iff _ _ _).mp ν.2
      have hP : (⟨ν, hν.1⟩ : ↥X.Λ) ∈ P := by rw [LinearMap.mem_ker, hf]; exact hν.2
      have hmk : P.mkQ (⟨ν, hν.1⟩ : ↥X.Λ) = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hP
      have hψ : ψ ⟨ν, hν.1⟩ = φ ν := by
        show φ _ = φ ν
        congr 1; ext1
        simp [hmk]
      rw [← hψ]; exact hx ⟨ν, hν.1⟩
    have hxξ : herm X.Gm x ξ = 0 := by
      apply herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne
      intro β
      have hmem := hsm β ξ hξp
      have h0 := hφ ⟨β • ξ, hmem⟩ ⟨(β : E), integer_smul_eq_coe_smul β ξ⟩
      have h1 := hval ⟨β • ξ, hmem⟩
      rw [h0] at h1
      simpa using h1.symm
    exact ⟨⟨x, (mem_orthogonal_lattice_iff _ _ _).mpr ⟨hxΛ, hxξ⟩⟩, hval⟩
  · intro μ hμ
    apply exists_eq_smul_of_herm X.Gm X.Gm_det X.Gm_herm ξ μ hξ0
    intro y hy
    have horth : ∀ ν ∈ X.Λp ξ, herm X.Gm μ ν = 0 := by
      intro ν hν
      apply herm_eq_zero_of_trace_form_vanish X.ξ0 X.ξ0_ne
      intro β
      exact hμ ⟨β • ν, hsm β ν hν⟩
    obtain ⟨d, hd, hdy⟩ := exists_smul_mem (F := E) X.Λ (x := y)
      (by rw [X.Λ_span]; exact Submodule.mem_top)
    have hdyp : d • y ∈ X.Λp ξ := by
      rw [mem_orthogonal_lattice_iff]
      refine ⟨hdy, ?_⟩
      rw [integer_smul_eq_coe_smul, herm_smul_left, hy, mul_zero]
    have h2 := horth _ hdyp
    rw [integer_smul_eq_coe_smul, herm_smul_right] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by simpa using hd)
    · exact h

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_eq_two_mul_half_degree : (Module.finrank ℚ E : ℝ) = 2 * (fdeg E : ℝ) := by
  have hf : fdeg E = Module.finrank ℚ E / 2 := rfl
  rw [hf, NumberField.IsTotallyComplex.finrank (K := E), Nat.mul_div_cancel_left _ two_pos]
  push_cast
  ring

theorem one_le_field_half_degree : 1 ≤ (fdeg E : ℝ) := by
  have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h0' : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast h0
  have hr : (0 : ℝ) < fdeg E := by
    have := finrank_eq_two_mul_half_degree (E := E)
    linarith
  have hn : 0 < fdeg E := by exact_mod_cast hr
  exact_mod_cast Nat.succ_le_of_lt hn

theorem field_discr_constant_pos : 0 < dE E := by
  unfold dE
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero (K := E))

theorem rootDiscriminant_eq_rpow : rdE E = dE E ^ (1 / (2 * (fdeg E : ℝ))) := by
  unfold rdE
  rw [finrank_eq_two_mul_half_degree]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem orthogonal_component_apply (z : Frame X.Ψ r) (ξ x : Fin r → E) (τ : X.Ψ) :
    X.ucomp z ξ (X.embV x) τ = Data.emb τ.1 x -
      (X.Hf z τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := rfl

theorem orthogonal_component_ne_zero (z : Frame X.Ψ r) {ξ x : Fin r → E} (hξ : ξ ≠ 0) (hx : ∀ e : E, x ≠ e • ξ)
    (τ : X.Ψ) : X.ucomp z ξ (X.embV x) τ ≠ 0 := by
  intro h
  rw [orthogonal_component_apply] at h

  obtain ⟨c, hb⟩ : ∃ c : ℂ, ∀ b, τ.1 (x b) = c * τ.1 (ξ b) := ⟨_, fun b => by
    have hb := congrFun h b
    simp only [Data.emb, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hb
    exact sub_eq_zero.mp hb⟩
  obtain ⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hξ (funext hcon)
  have hτa : τ.1 (ξ a) ≠ 0 := (map_ne_zero τ.1).mpr ha

  apply hx (x a / ξ a)
  funext b
  apply τ.1.injective
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_div₀, hb a, hb b]
  field_simp

end Data

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace HermitianPairingAlgebra

lemma cc_cc (a : E) : cc (cc a) = a := by
  exact IsCMField.complexConj_apply_apply E a

lemma cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  exact map_mul (IsCMField.complexConj E) a b

lemma cc_add (a b : E) : cc (a + b) = cc a + cc b := by
  exact map_add (IsCMField.complexConj E) a b

lemma cc_sum {ι : Type*} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) := by
  exact map_sum (IsCMField.complexConj E) f s

lemma herm_add_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma herm_smul_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G (a • x) y = a * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma herm_sub_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x - x') y = herm G x y - herm G x' y := by
  simp only [herm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma herm_symm {r : ℕ} {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin r → E) : cc (herm G x y) = herm G y x := by
  simp only [herm, cc_sum, cc_mul, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma smul_mem' {r : ℕ} {M : Submodule (𝓞 E) (Fin r → E)} {a : E} (ha : IsIntegral ℤ a)
    {y : Fin r → E} (hy : y ∈ M) : a • y ∈ M := by
  convert M.smul_mem (⟨a, ha⟩ : 𝓞 E) hy using 1
  rw [← algebraMap_smul E]
  rfl

noncomputable def pairL {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) :
    (Fin r → E) →ₗ[𝓞 E] E where
  toFun y := herm G y ξ
  map_add' x y := herm_add_left G x y ξ
  map_smul' a y := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul E a y, herm_smul_left, Algebra.smul_def]

lemma pairL_apply {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ y : Fin r → E) :
    pairL G ξ y = herm G y ξ := rfl

end HermitianPairingAlgebra

open HermitianPairingAlgebra in
theorem hermitian_lattice_pairing_duality : PerpQuotientSelfDual (E := E) := by
  intro r X ξ _ x _ hx
  have hsym : ∀ u v, cc (herm X.Gm u v) = herm X.Gm v u := fun u v => herm_symm X.Gm_herm u v
  have hintcc : ∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (cc a) := fun a ha =>
    ha.map (IsCMField.complexConj E).toAlgHom.toRingHom.toIntAlgHom
  suffices hP : ∃ c : E, ∀ y ∈ X.L', IsIntegral ℤ (herm X.Gm y x - c * herm X.Gm y ξ) by
    obtain ⟨c, hc⟩ := hP
    refine ⟨-cc c, X.L'_dual _ fun y hy => ?_⟩
    have h := hintcc _ (hc y hy)
    have e : cc (herm X.Gm y x - c * herm X.Gm y ξ) = herm X.Gm (x + (-cc c) • ξ) y := by
      rw [herm_add_left, herm_smul_left, ← hsym y x, ← hsym y ξ]
      simp only [cc, map_sub, map_mul, map_neg]
      ring
    rwa [e] at h
  by_cases hI : X.L'.map (pairL X.Gm ξ) = ⊥
  · refine ⟨0, fun y hy => ?_⟩
    have hy0 : herm X.Gm y ξ = 0 := by
      have hm : pairL X.Gm ξ y ∈ X.L'.map (pairL X.Gm ξ) := Submodule.mem_map_of_mem hy
      rw [hI, Submodule.mem_bot, pairL_apply] at hm
      exact hm
    rw [zero_mul, sub_zero, ← hsym x y]
    exact hintcc _ (hx y hy hy0)
  · let J : FractionalIdeal (𝓞 E)⁰ E :=
      ⟨X.L'.map (pairL X.Gm ξ), FractionalIdeal.isFractional_of_fg (X.L'_fg.map _)⟩
    have hJc : (J : Submodule (𝓞 E) E) = X.L'.map (pairL X.Gm ξ) := rfl
    have hJ0 : J ≠ 0 := by
      intro h
      apply hI
      rw [← hJc, h, FractionalIdeal.coe_zero]
    have h1 : (1 : E) ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ0]
      exact FractionalIdeal.one_mem_one _
    have key := Submodule.mul_induction_on
      (C := fun w => ∃ c : E, ∀ y ∈ X.L', IsIntegral ℤ (w * herm X.Gm y x - c * herm X.Gm y ξ)) h1
      (fun t ht u hu => by
        rw [hJc] at ht
        obtain ⟨yt, hyt, rfl⟩ := Submodule.mem_map.mp ht
        have hu' := (FractionalIdeal.mem_inv_iff hJ0).mp hu
        have hint : ∀ y ∈ X.L', IsIntegral ℤ (u * herm X.Gm y ξ) := fun y hy => by
          have hs : herm X.Gm y ξ ∈ J := by
            rw [← FractionalIdeal.mem_coe, hJc, ← pairL_apply]
            exact Submodule.mem_map_of_mem hy
          obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp (hu' _ hs)
          rw [← ha]
          exact a.isIntegral_coe
        refine ⟨u * herm X.Gm yt x, fun y hy => ?_⟩
        have hb := hint yt hyt
        have ha := hint y hy
        have hmem : (u * herm X.Gm yt ξ) • y - (u * herm X.Gm y ξ) • yt ∈ X.L' :=
          X.L'.sub_mem (smul_mem' hb hy) (smul_mem' ha hyt)
        have hz : herm X.Gm ((u * herm X.Gm yt ξ) • y - (u * herm X.Gm y ξ) • yt) ξ = 0 := by
          rw [herm_sub_left, herm_smul_left, herm_smul_left]
          ring
        have h2 := hintcc _ (hx _ hmem hz)
        rw [hsym, herm_sub_left, herm_smul_left, herm_smul_left] at h2
        rw [pairL_apply]
        convert h2 using 1
        ring)
      (fun w1 w2 ⟨c1, h1⟩ ⟨c2, h2⟩ => ⟨c1 + c2, fun y hy => by
        have h3 := (h1 y hy).add (h2 y hy)
        have e : (w1 + w2) * herm X.Gm y x - (c1 + c2) * herm X.Gm y ξ =
            (w1 * herm X.Gm y x - c1 * herm X.Gm y ξ) + (w2 * herm X.Gm y x - c2 * herm X.Gm y ξ) := by
          ring
        show IsIntegral ℤ ((w1 + w2) * herm X.Gm y x - (c1 + c2) * herm X.Gm y ξ)
        rw [e]
        exact h3⟩)
    obtain ⟨c, hc⟩ := key
    exact ⟨c, fun y hy => by simpa using hc y hy⟩

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def epStar (M f w k0 : ℝ) : ℝ := min 1 (Real.pi / (M * (f * w + 2) * k0 * Real.log 2))

def CuspFormGapCondition : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
    ∃ c' : ℝ, 0 < c' ∧ P ∈ X.SSgt la c'

def CuspidalExponentialDecay : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (c : ℝ), 0 ≤ c → P ∈ X.SSgt la c →
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ C * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x)

def MahlerCompactnessCriterion : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ K : Set (Frame X.Ψ r), IsCompact K ∧ K ⊆ X.dom ∧
    ∀ x ∈ X.dom, ε ≤ X.la1 x → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ K

def MaxBoundStatement : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (M w : ℝ), P ∈ X.SS la →
    0 < M → (∑ τ, X.spread la τ) ≤ w → 0 < w →
    (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧
        ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) →
    ∀ z0 ∈ X.dom, (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    ∀ v ∈ X.L', v ≠ 0 → ∃ τ : X.Ψ, epStar M (fdeg E) w X.k0 ≤ X.maj z0 τ (Data.emb τ.1 v)

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion

open NumberField Complex MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma exists_fd (X : Data E r) (la : Wt X.Ψ r) :
    ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ := by
  let L : Submodule ℤ (X.Ψ → ℝ) := (X.periods la).toIntSubmodule
  haveI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (X.periods la))
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using RealEmbeddingCharacters.periods_span (X := X) (la := la)⟩
  haveI := ZLattice.module_free ℝ L
  haveI := ZLattice.module_finite ℝ L
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L := by
    show Submodule.span ℤ (Set.range ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) = L
    rw [Module.Basis.ofZLatticeBasis_span]
  refine ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, ?_, ?_, ?_⟩
  · have h := ZSpan.isAddFundamentalDomain b volume
    rw [hspan] at h
    exact h
  · exact pos_iff_ne_zero.2 (ZSpan.measure_fundamentalDomain_ne_zero b)
  · exact (ZSpan.fundamentalDomain_isBounded b).measure_lt_top

lemma integral_swap_of_bdd {m n : Type} [Fintype m] [Fintype n] {D : Set (m → ℝ)} {K : Set (n → ℝ)}
    (hD : volume D < ⊤) (hK : volume K < ⊤) {f : (m → ℝ) → (n → ℝ) → ℂ}
    (hf : Continuous (Function.uncurry f)) {M : ℝ} (hM : ∀ s t, ‖f s t‖ ≤ M) :
    ∫ s in D, ∫ t in K, f s t = ∫ t in K, ∫ s in D, f s t := by
  haveI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.2 hD.ne
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.ne
  apply MeasureTheory.integral_integral_swap
  exact Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hM p.1 p.2)

end

end ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
end
