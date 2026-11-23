module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.PowNeZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LinkedUnlOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle352
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr

namespace UpperTheory.V.J

private theorem coef_inj {l : ℕ} [Fact l.Prime] (c : Coef l) : Function.Injective (algebraMap c.O (Qbar l)) :=
  Subtype.val_injective

theorem endJ : End := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro Ω _ _ _ l _ c η Ψ σ g₁ B M L _ _ _ _ _ Φ k c₁ _ f ka R φ hφ hs J ξ w hJ hTI har hirr hann D hD D' hD' h1 h2
    have key : ∀ E ∈ PtDer ξ (↥c₁.O),
        (∀ (v : (Φ.ext f).V) (i : Fin 3), ∀ g ∈ (Φ.ext f).Iv v, E ((R.S.ρ.ψ v i) g : R.S.R) = 0) →
        ∀ a ∈ R.S.B, E a = 0 := by
      intro E hE hI a ha
      have hmul : ∀ x y : R.S.R, E (x * y) = ξ x * E y + ξ y * E x := fun x y => hE x y
      have hone : E 1 = 0 := by
        have h := hmul 1 1
        simp at h
        exact h
      have halg : ∀ (r : ↥c₁.O), E (algebraMap (↥c₁.O) R.S.R r) = 0 := by
        intro r
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hone, smul_zero]
      have hJa : ∀ a ∈ J, ξ ((φ a : R.S.B) : R.S.R) = 0 ∧ E ((φ a : R.S.B) : R.S.R) = 0 := by
        intro x hx
        obtain ⟨s, hs1, hs2⟩ := hann x hx
        have e : (s : R.S.R) * ((φ x : R.S.B) : R.S.R) = 0 := by
          exact congrArg (fun z : R.S.A => (z : R.S.R)) hs2
        have hξs : ξ (s : R.S.R) ≠ 0 := by
          intro h0
          apply hs1
          simp [ptA, h0]
        have hξ : ξ ((φ x : R.S.B) : R.S.R) = 0 := by
          have h := congrArg ξ e
          rw [map_mul, map_zero] at h
          exact (mul_eq_zero.mp h).resolve_left hξs
        refine ⟨hξ, ?_⟩
        have h := hmul (s : R.S.R) ((φ x : R.S.B) : R.S.R)
        rw [e, map_zero, hξ, zero_mul, add_zero] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hξs
      let incl : ↥R.S.B →ₐ[↥c₁.O] R.S.R := Subalgebra.val R.S.B
      let δ : R.B₀.B →ₗ[↥c₁.O] Qbar l :=
        (Algebra.ofId (↥c₁.O) (Qbar l)).toLinearMap ∘ₗ E ∘ₗ (AlgHom.toLinearMap (AlgHom.comp incl φ))
      have hδ : δ ∈ PtDer (ptOf R φ ξ) (Qbar l) := by
        intro x y
        simp [δ, incl, ptOf, hmul]
      have hle : J ≤ RingHom.ker (ptOf R φ ξ) := by
        intro x hx
        simp [ptOf, (hJa x hx).1]
      have hδJ : ∀ x ∈ J, δ x = 0 := by
        intro x hx
        simp [δ, incl, (hJa x hx).2]
      have hδψ : ∀ (v : R.V.frame.Vl) (i : Fin 3), ∀ g ∈ R.V.frame.Iv v, δ ((R.B₀.u.ψ v i) g : R.B₀.B) = 0 := by
        intro v i g hg
        have hm := congrArg (fun χ => ((χ g : (R.S.R)ˣ) : R.S.R)) (hφ.2 v i)
        simp only [pushCh, TwLink.twψ, TwLink.κA] at hm
        have hm' : ((φ ((R.B₀.u.ψ v i) g : R.B₀.B) : R.S.B) : R.S.R) =
            ((R.S.ρ.ψ (R.K.e v) i ((R.K.lam v) g) : R.S.Rˣ) : R.S.R) *
              algebraMap (↥c₁.O) R.S.R ((R.K.κ (R.V.frame.φ v g) : (↥c₁.O)ˣ) : ↥c₁.O) := hm
        have hin : (R.K.lam v) g ∈ (Φ.ext f).Iv (R.K.e v) := (R.K.lam_I v g).mpr hg
        simp only [δ, incl, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, AlgHom.coe_comp,
          Subalgebra.coe_val]
        rw [hm', hmul, halg, hI _ _ _ hin]
        simp
      have h0 := hJ (ptOf R φ ξ) w hle har hirr δ hδ hδJ hδψ
      obtain ⟨b, hb⟩ := hs ⟨a, ha⟩
      have h := LinearMap.congr_fun h0 b
      have h' : algebraMap (↥c₁.O) (Qbar l) (E a) = 0 := by
        simpa [δ, incl, hb] using h
      exact coef_inj c₁ (by rw [h', map_zero])
    exact tor l (↥c₁.O) (Φ.ext f) R.S ξ hTI D hD D' hD' (key D hD h1) (key D' hD' h2)

end UpperTheory.V.J
end

section

noncomputable section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open IsLocalRing Formalism.ConjugateSelfDual UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.Pr

namespace UpperTheory.V.J

private def xiExt {l : ℕ} [Fact l.Prime] {k k' : Type} [Field k] [Field k'] {Φ : Fr.Frame l k} {n : ℕ}
    {K : Type} [CommRing K] (f : k →+* k') (ρ : Fr.NRep Φ n K) : Fr.NRep (Φ.ext f) n K where
  r := ρ.r
  ψ := ρ.ψ
  pol := ρ.pol
  diag := ρ.diag
  ord := ρ.ord

private theorem xi_adic {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] {u : Γ → R} (h : AdicCont (maximalIdeal R) u) :
    AdicCont (maximalIdeal S) fun g => φ (u g) := by
  unfold AdicCont at h ⊢
  intro N
  have h1 : Ideal.map φ (maximalIdeal R) ≤ maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr (fun a ha => Ideal.mem_comap.mpr (map_nonunit φ a ha))
  have hle : maximalIdeal R ^ N ≤ Ideal.comap φ (maximalIdeal S ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono h1 N
  have hc := (h N).comp (Ideal.quotientMap (maximalIdeal S ^ N) φ hle)
  convert hc using 1
  ext g
  rfl

private theorem xi_key {O A O₁ : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [CommRing O₁] [IsLocalRing O₁] [IsNoetherianRing O₁] [IsAdicComplete (maximalIdeal O₁) O₁]
    [Algebra O A] [IsLocalHom (algebraMap O A)] (j : A →+* O₁) [IsLocalHom j]
    (f : ResidueField O →+* ResidueField O₁)
    (hf : ∀ a, f (residue O a) = residue O₁ (j (algebraMap O A a))) (x : A) (u : ResidueField O)
    (h : residue A x = ResidueField.map (algebraMap O A) u) : res O₁ O₁ (j x) = f u := by
  obtain ⟨a, rfl⟩ := residue_surjective u
  have h1 : x - algebraMap O A a ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_sub, h, ResidueField.map_residue, sub_self]
  have h2 : j x - j (algebraMap O A a) ∈ maximalIdeal O₁ := by
    rw [← map_sub]
    exact map_nonunit j _ h1
  have h3 : residue O₁ (j x) = residue O₁ (j (algebraMap O A a)) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact h2
  rw [hf, ← h3]
  simp only [res]
  simp
  rw [RingEquiv.symm_apply_eq]
  rfl

private theorem xi_lift {l : ℕ} [Fact l.Prime] {O A O₁ : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [IsLocalRing A] [CommRing O₁] [IsLocalRing O₁] [IsNoetherianRing O₁]
    [IsAdicComplete (maximalIdeal O₁) O₁] [Algebra O A] [IsLocalHom (algebraMap O A)] (j : A →+* O₁)
    [IsLocalHom j] (f : ResidueField O →+* ResidueField O₁)
    (hf : ∀ a, f (residue O a) = residue O₁ (j (algebraMap O A a)))
    {Φ : Fr.Frame l (ResidueField O)} {n : ℕ} (ρ : Fr.NRep Φ n A) (h : IsLiftA O ρ) :
    Fr.IsLift O₁ ((xiExt f ρ).map j) := by
  obtain ⟨hc, hb, hd⟩ := h
  refine ⟨⟨fun i k => ?_, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i k hik => ?_⟩
  · exact xi_adic j (hc.1 i k)
  · exact xi_adic j (hc.2 v i)
  · change res O₁ O₁ (j (ρ.r g i i)) = _
    rw [xi_key j f hf (ρ.r g i i) _ (hb.1 g i)]
    simp [Fr.Frame.ext, map_pow]
    rfl
  · change res O₁ O₁ (j ((ρ.ψ v i g : Aˣ) : A)) = _
    rw [xi_key j f hf _ _ (hb.2 v i g)]
    simp [Fr.Frame.ext, map_pow]
    rfl
  · change res O₁ O₁ (j (ρ.r g i k)) = 0
    rw [xi_key j f hf (ρ.r g i k) 0 (by rw [map_zero]; exact hd g i k hik), map_zero]

private theorem xi_loc {l : ℕ} [Fact l.Prime] (c c₁ : Coef l) (A : Subalgebra c.O (PadicAlgCl l))
    (hA : ∀ x ∈ A, x ∈ c₁.O) : ∃ j : A →+* c₁.O, (∀ x, (j x).1 = x.1) ∧ IsLocalHom j := by
  let j : A →+* c₁.O :=
    { toFun := fun x => ⟨x.1, hA x.1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨j, fun x => rfl, ?_⟩
  have hfin := c₁.fin
  have hint : (algebraMap ℤ_[l] c₁.O).IsIntegral :=
    algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.of_finite ℤ_[l] c₁.O)
  have hcomp : j.comp ((algebraMap c.O A).comp (algebraMap ℤ_[l] c.O)) = algebraMap ℤ_[l] c₁.O :=
    RingHom.ext fun x => Subtype.ext rfl
  have hj : j.IsIntegral := RingHom.IsIntegral.tower_top _ j (hcomp ▸ hint)
  refine hj.isLocalHom (fun x y h => ?_)
  have h' := congrArg (fun z : c₁.O => (z : PadicAlgCl l)) h
  exact Subtype.ext h'

theorem xiEx :
    UpperTheory.V.J.XiEx := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f R A _ _ _ hA ρ hρ
  obtain ⟨j, hj, _⟩ := xi_loc c c₁ A hA
  have hf : ∀ a, f (residue c.O a) = residue c₁.O (j (algebraMap c.O A a)) := fun a =>
    R.hf a _ (hj (algebraMap c.O A a)).symm
  obtain ⟨ξ, hξ, -⟩ := R.S.univ c₁.O _ (xi_lift j f hf ρ hρ)
  refine ⟨ξ, fun g a b => ?_, fun v i g => ?_⟩
  · exact (congrArg (fun t : Fr.NRep _ _ c₁.O => (t.r g a b).1) hξ).trans (hj _)
  · exact (congrArg (fun t : Fr.NRep _ _ c₁.O => ((t.ψ v i g : c₁.Oˣ) : c₁.O).1) hξ).trans (hj _)

end UpperTheory.V.J

end
end

section

noncomputable section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr

namespace UpperTheory.V.J

private theorem norm_lt_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : x ∈ maximalIdeal c.O) :
    ‖(x : Qbar l)‖ < 1 := by
  haveI := c.dvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  by_cases hx0 : x = 0
  · subst hx0
    simp
  have hcast : (((l : ℕ) : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := map_natCast c.O.val l
  have hlne : ((l : ℕ) : c.O) ≠ 0 := by
    intro h0
    have h1 : (((l : ℕ) : c.O) : Qbar l) = 0 := by rw [h0]; rfl
    rw [hcast] at h1
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h1)
  obtain ⟨e, u, hle⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hlne hϖ
  obtain ⟨a, v, hxa⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hlt := GlobalTheory.CoefCoord.norm_natCast_lt_one (l := l)
  have he : e ≠ 0 := by
    rintro rfl
    have hu := GlobalTheory.CoefCoord.norm_unit c u
    rw [pow_zero, mul_one] at hle
    rw [← hle, hcast] at hu
    linarith
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hxa
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hxa] at hx
    exact hx v.isUnit
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero ha
  have key : x ^ e = ((l : ℕ) : c.O) * (↑u⁻¹ * ↑v ^ e * ϖ ^ (a' * e)) := by
    rw [hxa, hle]
    linear_combination (-(↑v ^ e * ϖ ^ e * ϖ ^ (a' * e))) * u.mul_inv
  have h2 : ‖(x : Qbar l)‖ ^ e
      = ‖(((l : ℕ) : c.O) : Qbar l)‖ * ‖((↑u⁻¹ * ↑v ^ e * ϖ ^ (a' * e) : c.O) : Qbar l)‖ := by
    rw [← norm_pow, ← norm_mul, ← SubmonoidClass.coe_pow, ← MulMemClass.coe_mul, key]
  have h3 := GlobalTheory.CoefCoord.norm_le_one c (↑u⁻¹ * ↑v ^ e * ϖ ^ (a' * e))
  have h4 : ‖(x : Qbar l)‖ ^ e < 1 := by
    rw [h2, hcast]
    calc _ ≤ ‖((l : ℕ) : Qbar l)‖ * 1 := by gcongr
      _ < 1 := by simpa using hlt
  by_contra hge
  push_neg at hge
  exact absurd h4 (not_lt.mpr (one_le_pow₀ hge))

private theorem map_mem_max {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    (ξ : R →ₐ[O] O) (x : R) (hx : x ∈ maximalIdeal R) : ξ x ∈ maximalIdeal O := by
  by_contra h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
  obtain ⟨u, hu⟩ := h
  have hy : ξ (x * algebraMap O R (↑u⁻¹ : O) - 1) = 0 := by
    rw [map_sub, map_mul, AlgHom.commutes, ← hu, map_one]
    simp
  have hm : x * algebraMap O R (↑u⁻¹ : O) - 1 ∈ maximalIdeal R := by
    by_contra h2
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h2
    have h3 := h2.map ξ
    rw [hy] at h3
    exact not_isUnit_zero h3
  have h1 : (1 : R) ∈ maximalIdeal R := by
    have h4 := (maximalIdeal R).sub_mem ((maximalIdeal R).mul_mem_right (algebraMap O R ↑u⁻¹) hx) hm
    simpa using h4
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem not_irr_of_line {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 3) k) (j : Fin 3)
    (h : ∀ s i, i ≠ j → (r s).val i j = 0) : ¬ IsIrr r := by
  intro hI
  obtain ⟨-, -, hmin⟩ := hI
  have hinv : Formalism.MainNotions.N.IsInv r (Submodule.span k {Pi.single j (1 : k)}) := by
    intro g v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine Submodule.mem_span_singleton.mpr ⟨a * (r g).val j j, ?_⟩
    ext i
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply, hij, h g i hij]
  rcases hmin _ le_top hinv with h0 | htop
  · have hs : (Pi.single j (1 : k) : Fin 3 → k) = 0 := by
      rw [← Submodule.mem_bot k, ← h0]
      exact Submodule.mem_span_singleton_self _
    have := congrFun hs j
    simp at this
  · have hj : j + 1 ≠ j := by fin_cases j <;> decide
    have hmem : (Pi.single (j + 1) (1 : k) : Fin 3 → k) ∈ Submodule.span k {Pi.single j (1 : k)} := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have := congrFun ha (j + 1)
    simp [Pi.single_apply, hj] at this

private theorem ti_of {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Fr.Frame l k} {K : Type} [CommRing K]
    (ρ : Fr.NRep F 3 K) (p : Ideal K) (H : ∀ j : Fin 3, ¬ ∀ g i, i ≠ j → ρ.r g i j ∈ p) : ρ.TI p := by
  refine ⟨⟨fun hle => H 0 ?_, fun hle => H 2 ?_⟩, fun _ hle => H 1 ?_⟩
  · intro g i hi
    exact hle (Ideal.subset_span ⟨g, i, 0, by revert hi; fin_cases i <;> decide, rfl⟩)
  · intro g i hi
    exact hle (Ideal.subset_span ⟨g, i, 2, by revert hi; fin_cases i <;> decide, rfl⟩)
  · intro g i hi
    refine hle (Ideal.subset_span ⟨g, i, 1, ?_, rfl⟩)
    revert hi
    fin_cases i <;> simp [Fr.w] <;> decide

end UpperTheory.V.J

theorem UpperTheory.V.J.xiTI :
    UpperTheory.V.J.XiTI := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f R ξ r hr hi
  have hcol : ∀ j : Fin 3, ¬ ∀ g i, i ≠ j → ξ (R.S.ρ.r g i j) = 0 := by
    intro j h
    refine not_irr_of_line r j (fun s i hij => ?_) hi
    rw [hr s]
    exact congrArg Subtype.val (h (k.p0 s) i hij)
  refine ⟨ti_of _ _ fun j h => hcol j fun g i hij => h g i hij, ⟨fun a => GlobalTheory.CoefCoord.norm_le_one c₁ _,
    fun b hb => norm_lt_of_mem c₁ _ (map_mem_max ξ b.1 hb)⟩, ti_of _ _ fun j h => hcol j fun g i hij => ?_⟩
  have h0 : ptA R ξ (R.S.u.r g i j) = 0 := h g i hij
  exact Subtype.ext h0

end
end
