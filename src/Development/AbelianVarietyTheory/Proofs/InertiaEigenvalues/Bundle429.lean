module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle196
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle207
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle412
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilBrauer

theorem eq_of_induced : BrauerDegreeZero → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ε ε' : WD h → ℂˣ), (∀ x y, ε (x.lpSum y) = ε x * ε y) → (∀ x y, ε' (x.lpSum y) = ε' x * ε' y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → ε x = ε y ∧ ε' x = ε' y) → (∀ ξ hξ, ε (WD.lpOfChar h ξ hξ) = ε' (WD.lpOfChar h ξ hξ)) → (∀ (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∀ (χ₁ χ₂ : H →* ℂˣ) (n : ℕ) (b₁ b₂ : WDRep h (Fin n → ℂ)) (v₁ v₂ : Fin n → ℂ), n = H.index → (∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) → (∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂) → Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤ → Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤ → ε (WD.mk b₁) * ε' (WD.mk b₂) = ε (WD.mk b₂) * ε' (WD.mk b₁)) → ∀ x, ε x = ε' x := by
  intro hB E Ω _ _ _ _ _ A w h ε ε' hε hε' hcp hchar hind
  classical
  set f : WD h → ℂˣ := fun x => ε x / ε' x with hf
  have fmul : ∀ x y, f (x.lpSum y) = f x * f y := by
    intro x y
    simp only [hf, hε, hε']
    exact mul_div_mul_comm _ _ _ _
  have fcp : ∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y := by
    intro x y hxy
    obtain ⟨h1, h2⟩ := hcp x y hxy
    simp only [hf, h1, h2]
  have key : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → f (WD.mk (a.twist μ hμ)) = 1 := by
    intro n a μ hμ hfin
    let u : Weil h →* (Module.End ℂ (Fin n → ℂ))ˣ := a.ρ.toHomUnits
    let G : Subgroup (Module.End ℂ (Fin n → ℂ))ˣ := u.range
    have hGfin : Finite G := by
      have hr : (Set.range u).Finite := by
        refine Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn
        refine hfin.subset ?_
        rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, rfl⟩
      have : ((G : Set (Module.End ℂ (Fin n → ℂ))ˣ)) = Set.range u := MonoidHom.coe_range u
      exact Set.finite_coe_iff.mpr (this ▸ hr)
    letI : Fintype G := Fintype.ofFinite G
    let π : Weil h →* G := u.rangeRestrict
    have hπs : Function.Surjective π := MonoidHom.rangeRestrict_surjective u
    let ρG : Representation ℂ G (Fin n → ℂ) := (Units.coeHom _).comp G.subtype
    have hρG : ∀ σ, ρG (π σ) = a.ρ σ := fun σ => rfl
    have hπ1 : ∀ σ, π σ = 1 ↔ a.ρ σ = 1 := by
      intro σ
      constructor
      · intro h1
        rw [← hρG, h1, map_one]
      · intro h1
        apply Subtype.ext
        apply Units.ext
        exact h1
    have hopen : IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} := by
      have : {σ : Ine (F := E) A | π (ineIncl h σ) = 1} = {σ | a.ρ (ineIncl h σ) = 1} :=
        Set.ext fun σ => hπ1 _
      rw [this]
      exact a.smooth
    obtain ⟨r, H, χ, c, hbr⟩ := hB G (Fin n → ℂ) ρG
    have hi1 := fun i => GlobalTheory.T.induced_representation_character G (H i) (χ i)
    have hi2 := fun i => GlobalTheory.T.induced_representation_character G (H i) 1
    choose Rχ vχ hRχ using hi1
    choose R1 v1 hR1 using hi2
    have hp1 := fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (Rχ i) μ hμ
    have hp2 := fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (R1 i) μ hμ
    choose bχ hbχ using hp1
    choose b1 hb1 using hp2
    have span_of : ∀ (i : Fin r) (R : Representation ℂ G (Fin (H i).index → ℂ))
        (b : WDRep h (Fin (H i).index → ℂ)) (v : Fin (H i).index → ℂ),
        (∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ)) → Submodule.span ℂ (Set.range fun g => R g v) = ⊤ →
        Submodule.span ℂ (Set.range fun σ => b.ρ σ v) = ⊤ := by
      intro i R b v hb hs
      rw [eq_top_iff, ← hs, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨σ, rfl⟩ := hπs g
      show R (π σ) v ∈ _
      have e : R (π σ) v = (((μ σ)⁻¹ : ℂˣ) : ℂ) • b.ρ σ v := by
        rw [hb, LinearMap.smul_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
    have hpair : ∀ i, f (WD.mk (bχ i)) = f (WD.mk (b1 i)) := by
      intro i
      let H' := (H i).comap π
      have hidx : (H i).index = H'.index := (Subgroup.index_comap_of_surjective _ hπs).symm
      haveI : H'.FiniteIndex := ⟨by rw [← hidx]; exact Subgroup.index_ne_zero_of_finite⟩
      have hop : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H'} := by
        have hle : (π.comp (ineIncl h)).ker ≤ H'.comap (ineIncl h) := by
          intro σ hσ
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ
          show π (ineIncl h σ) ∈ H i
          rw [hσ]
          exact one_mem _
        exact Subgroup.isOpen_mono hle hopen
      let χ₁ : H' →* ℂˣ := μ.comp H'.subtype * (χ i).comp (π.subgroupComap (H i))
      let χ₂ : H' →* ℂˣ := μ.comp H'.subtype * (1 : H i →* ℂˣ).comp (π.subgroupComap (H i))
      have e1 : ∀ σ : H', (bχ i).ρ σ (vχ i) = (χ₁ σ : ℂ) • vχ i := by
        intro σ
        rw [hbχ, LinearMap.smul_apply, (hRχ i).1 ⟨π σ, σ.2⟩, smul_smul]
        rfl
      have e2 : ∀ σ : H', (b1 i).ρ σ (v1 i) = (χ₂ σ : ℂ) • v1 i := by
        intro σ
        rw [hb1, LinearMap.smul_apply, (hR1 i).1 ⟨π σ, σ.2⟩, smul_smul]
        rfl
      have hh := hind H' inferInstance hop χ₁ χ₂ _ (bχ i) (b1 i) (vχ i) (v1 i) hidx e1 e2
        (span_of i _ _ _ (hbχ i) (hRχ i).2.1) (span_of i _ _ _ (hb1 i) (hR1 i).2.1)
      simp only [hf]
      exact div_eq_div_iff_mul_eq_mul.mpr hh
    have hμ1 : f (WD.mk (WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ)) = 1 := by
      have := hchar μ hμ
      simp only [hf]
      exact div_eq_one.mpr this
    let F : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → Σ m, WDRep h (Fin m → ℂ) :=
      Sum.elim (Sum.elim (fun _ => ⟨n, a.twist μ hμ⟩)
          (fun _ => ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ⟩))
        (Sum.elim (fun i => ⟨_, bχ i⟩) (fun i => ⟨_, b1 i⟩))
    let cc : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → ℤ :=
      Sum.elim (Sum.elim (fun _ => 1) (fun _ => -(n : ℤ))) (Sum.elim (fun i => -c i) (fun i => c i))
    have htr : ∀ σ, ∑ j, (cc j : ℂ) * LinearMap.trace ℂ (Fin (F j).1 → ℂ) ((F j).2.ρ σ) = 0 := by
      intro σ
      have hb := hbr (π σ)
      rw [Module.finrank_fin_fun] at hb
      have t0 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inl (default : Unit)))).1 → ℂ)
          ((F (Sum.inl (Sum.inl (default : Unit)))).2.ρ σ) =
          (μ σ : ℂ) * LinearMap.trace ℂ (Fin n → ℂ) (ρG (π σ)) := by
        show LinearMap.trace ℂ (Fin n → ℂ) ((a.twist μ hμ).ρ σ) = _
        rw [WDRep.twist_ρ, map_smul, smul_eq_mul, hρG]
      have t1 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inr (default : Unit)))).1 → ℂ)
          ((F (Sum.inl (Sum.inr (default : Unit)))).2.ρ σ) = (μ σ : ℂ) := by
        show LinearMap.trace ℂ (Fin 1 → ℂ)
          ((WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ).ρ σ) = _
        rw [WDRep.ofChars_ρ]
        have e : (GlobalTheory.WeilDeligne.diagEnd fun _ : Fin 1 => (μ σ : ℂ)) = (μ σ : ℂ) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
          ext v i
          simp
        rw [e, map_smul, LinearMap.trace_one, smul_eq_mul, Module.finrank_fin_fun, Nat.cast_one,
          mul_one]
      have tχ : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inl i))).1 → ℂ)
          ((F (Sum.inr (Sum.inl i))).2.ρ σ) =
          (μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ) := by
        intro i
        show LinearMap.trace ℂ _ ((bχ i).ρ σ) = _
        rw [hbχ, map_smul, smul_eq_mul, (hRχ i).2.2]
      have t1' : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inr i))).1 → ℂ)
          ((F (Sum.inr (Sum.inr i))).2.ρ σ) =
          (μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ) := by
        intro i
        show LinearMap.trace ℂ _ ((b1 i).ρ σ) = _
        rw [hb1, map_smul, smul_eq_mul, (hR1 i).2.2]
        simp
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, t0, t1, tχ, t1']
      simp only [cc, Sum.elim_inl, Sum.elim_inr, Int.cast_one, Int.cast_neg, Int.cast_natCast,
        one_mul]
      have hs : ∑ i, -(c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ)) +
          ∑ i, (c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ)) =
          -(μ σ : ℂ) * ∑ i, (c i : ℂ) * (indFun (H i) (fun x => (χ i x : ℂ)) (π σ) -
            indFun (H i) (fun _ => 1) (π σ)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hs]
      linear_combination (μ σ : ℂ) * hb
    have hv := GlobalTheory.T.multiplicative_virtual_character E Ω A w h f fmul fcp _ (fun j => (F j).1) (fun j => (F j).2) cc htr
    have hμ1' : f (WD.mk (F (Sum.inl (Sum.inr (default : Unit)))).2) = 1 := hμ1
    have hp' : ∀ i, f (WD.mk (F (Sum.inr (Sum.inl i))).2) = f (WD.mk (F (Sum.inr (Sum.inr i))).2) :=
      hpair
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, hμ1', hp'] at hv
    simp only [cc, Sum.elim_inl, Sum.elim_inr, zpow_one, _root_.zpow_neg, _root_.one_zpow, inv_one,
      mul_one, ← Finset.prod_mul_distrib, _root_.inv_mul_cancel, Finset.prod_const_one] at hv
    exact hv
  intro x
  have hx := GlobalTheory.T.weil_deligne_induction_principle E Ω A w h (fun x => f x = 1)
    (fun x y hx hy => by rw [fmul, hx, hy, one_mul])
    (fun x y hxy hx => by rw [← fcp x y hxy, hx]) key x
  simp only [hf] at hx
  exact div_eq_one.mp hx

end GlobalTheory.WeilBrauer
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem unit_pow_dvd_sub_one_of_finite {R : Type} [CommRing R] (g : R)
    [Finite (R ⧸ Ideal.span {g})] :
    ∃ m : ℕ, 0 < m ∧ ∀ ε : Rˣ, g ∣ (ε : R) ^ m - 1 := by
  haveI : Finite (R ⧸ Ideal.span {g})ˣ := Finite.of_injective (fun u => (u : R ⧸ Ideal.span {g})) (fun _ _ h => Units.ext h)
  refine ⟨Nat.card (R ⧸ Ideal.span {g})ˣ, Nat.card_pos, fun ε => ?_⟩
  have h := pow_card_eq_one' (G := (R ⧸ Ideal.span {g})ˣ) (x := Units.map (Ideal.Quotient.mk _).toMonoidHom ε)
  have h2 : Ideal.Quotient.mk (Ideal.span {g}) ((ε : R) ^ Nat.card (R ⧸ Ideal.span {g})ˣ - 1) = 0 := by
    have := congrArg Units.val h
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one] at this
    rw [map_sub, map_pow, this, map_one, sub_self]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2
  exact h2

end GlobalTheory

namespace GlobalTheory


open IsDedekindDomain.HeightOneSpectrum in
theorem eq_one_of_approx_by_congruent_units : ChevalleyUnits → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E), Valued.v x = 1 → (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - x) ≤ Valued.v t) → x = 1 := by
  intro hCh E _ _ w x hx hap
  have hE : ∀ k : E, Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    fun k => valuedAdicCompletion_eq_valuation' w k
  set q : ℕ := Ideal.absNorm w.asIdeal with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hqmem : (q : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
  set γ := w.intValuation (q : 𝓞 E) with hγdef
  have hγ : γ < 1 := (w.intValuation_lt_one_iff_mem _).2 hqmem
  have key : ∀ n : ℕ, Valued.v (x - 1) ≤ γ ^ (n + 1) := by
    intro n
    set g : 𝓞 E := (q : 𝓞 E) ^ (n + 1) with hgdef
    have hg0 : g ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hq0)
    haveI : Finite (𝓞 E ⧸ Ideal.span {g}) := by
      refine (Ideal.absNorm_ne_zero_iff _).1 ?_
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hg0
    obtain ⟨m, hm, hmg⟩ := unit_pow_dvd_sub_one_of_finite g
    obtain ⟨a, ha0, hacop, hch⟩ := hCh E m q hm (Nat.pos_of_ne_zero hq0)

    have hanot : (a : 𝓞 E) ∉ w.asIdeal := by
      intro ha
      obtain ⟨s, t, hst⟩ := (Nat.isCoprime_iff_coprime.2 hacop).map (Int.castRingHom (𝓞 E))
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← hst]
      simp only [eq_intCast, Int.cast_natCast]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hqmem)
    have hva : w.intValuation (a : 𝓞 E) = 1 := intValuation_eq_one_iff.2 hanot
    have haE : (a : E) = algebraMap (𝓞 E) E (a : 𝓞 E) := (map_natCast _ _).symm
    have ha0E : (a : E) ≠ 0 := Nat.cast_ne_zero.2 ha0.ne'
    have hvaE : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (a : E) ≤ 1 := fun v => by
      rw [haE, valuation_of_algebraMap]; exact v.intValuation_le_one _
    have hwaE : w.valuation E (a : E) = 1 := by rw [haE, valuation_of_algebraMap]; exact hva
    set t : w.adicCompletion E := algebraMap E _ (algebraMap (𝓞 E) E g) with htdef
    have hvt : Valued.v t = γ ^ (n + 1) := by
      rw [htdef, hE, valuation_of_algebraMap, hgdef, map_pow]
    have ht0 : t ≠ 0 := by
      intro h; have := hvt; rw [h, map_zero] at this
      exact (pow_ne_zero _ (by have hq0' : (q : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq0; rw [hγdef]; exact w.intValuation_ne_zero _ hq0')) this.symm
    obtain ⟨k, hkv, hkw⟩ := hap a ha0 t ht0
    rw [hvt] at hkw
    have hγn : γ ^ (n + 1) < 1 := pow_lt_one₀ zero_le' hγ (Nat.succ_ne_zero n)

    have hwk : w.valuation E (k : E) = 1 := by
      rw [← hE, ← hx]
      exact Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt hkw (hx ▸ hγn))
    have hk1 : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ((k : E) - 1) ≤ 1 := by
      intro v
      by_cases hv : v = w
      · subst hv
        exact Valuation.map_sub_le _ hwk.le (by rw [map_one])
      · have h1 := (hkv v hv).1
        have : (k : E) - 1 = ((k : E) - 1) / (a : E) * (a : E) := by field_simp
        rw [this, map_mul]
        exact mul_le_one' h1 (hvaE v)
    have hkle : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (k : E) ≤ 1 := by
      intro v
      have : (k : E) = ((k : E) - 1) + 1 := by ring
      rw [this]; exact Valuation.map_add_le _ (hk1 v) (by rw [map_one])
    have hkile : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ((k : E)⁻¹) ≤ 1 := by
      intro v
      by_cases hv : v = w
      · subst hv; rw [map_inv₀, hwk, inv_one]
      · exact (hkv v hv).2
    obtain ⟨κ, hκ⟩ := mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hkle
    obtain ⟨κ', hκ'⟩ := mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hkile
    have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
    have hkk : κ * κ' = 1 := hinj (by rw [map_mul, hκ, hκ', map_one, mul_inv_cancel₀ k.ne_zero])
    let u : (𝓞 E)ˣ := ⟨κ, κ', hkk, by rw [mul_comm]; exact hkk⟩
    have hdivE : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 := by
      intro v
      by_cases hv : v = w
      · subst hv; rw [map_div₀, hwaE, div_one]; exact hk1 _
      · exact (hkv v hv).1
    obtain ⟨y, hy⟩ := mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hdivE
    have hdvd : (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 := by
      refine ⟨y, hinj ?_⟩
      show algebraMap (𝓞 E) E (κ - 1) = algebraMap (𝓞 E) E ((a : 𝓞 E) * y)
      rw [map_sub, map_one, hκ, map_mul, hy, ← haE]
      field_simp
    obtain ⟨ε, hε⟩ := hch u hdvd
    have hgk : g ∣ κ - 1 := by
      have := hmg ε
      rw [← Units.val_pow_eq_pow_val, ← hε] at this
      exact this
    have hwk1 : w.valuation E ((k : E) - 1) ≤ γ ^ (n + 1) := by
      obtain ⟨c, hc⟩ := hgk
      rw [← hκ, ← map_one (algebraMap (𝓞 E) E), ← map_sub, valuation_of_algebraMap, hc, map_mul]
      have : w.intValuation g = γ ^ (n + 1) := by rw [hgdef, map_pow]
      rw [this]
      exact mul_le_of_le_one_right' (w.intValuation_le_one c)
    have hsplit : x - 1 = -(algebraMap E (w.adicCompletion E) (k : E) - x)
        + algebraMap E (w.adicCompletion E) ((k : E) - 1) := by
      rw [map_sub, map_one]; ring
    rw [hsplit]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Valuation.map_neg]; exact hkw
    · rw [hE]; exact hwk1
  by_contra hne
  have hne' : Valued.v (x - 1) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hγ (Units.mk0 _ hne')
  have h1 := key n
  have h2 : γ ^ (n + 1) ≤ γ ^ n := by rw [pow_succ]; exact mul_le_of_le_one_right' hγ.le
  exact absurd (lt_of_le_of_lt (h1.trans h2) hn) (lt_irrefl _)

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.CycRing

theorem letφ_pow_const {O : Type} [CommRing O] {n : ℕ} (f : PowerSeries O →ₐ[O] PowerSeries O)
    (k : ℕ) (c : PowerSeries O) :
    (letφ (n := n) f ^ k) (fun _ => c) = fun _ => (f ^ k) c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih]
    funext i
    simp [letφ]

theorem XX_ne_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    (hl : (l : O) ≠ 0) (s : ℕ) : GlobalTheory.Cyc.XX l O s ≠ 0 := by
  intro h
  have h1 := congrArg (PowerSeries.coeff 1) h
  rw [GlobalTheory.Cyc.XX, map_sub, PowerSeries.coeff_one_pow] at h1
  simp [PowerSeries.coeff_one] at h1
  exact hl h1.1



theorem rings_cyclotomic : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∃ χ : W.Gam →* ℤ_[l]ˣ, (∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) ∧ W.φ₀ = GlobalTheory.Cyc.phi l ↥(OL LL) ∧ (∀ g, W.γ₀ g = GlobalTheory.Cyc.act l ↥(OL LL) (χ g : ℤ_[l])) ∧ (∀ i, W.X i = GlobalTheory.Cyc.XX l ↥(OL LL) s) ∧ (∀ i, W.Q i = GlobalTheory.Cyc.QQ l ↥(OL LL) s) ∧ ‖(χ W.gam : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) ∧ ∀ u : ℤ_[l]ˣ, ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) → ∃ g, χ g = u := by
  intro D HW l _ K s LL h W
  obtain ⟨χ₀, hχ₀, -, honto⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l (D.loc l)
  obtain ⟨hdvr, hcomp, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hWs : W.s = s := (HW l).W_s K s LL h
  clear_value W
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hcoe : ∀ z : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z)
      = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) := by
    intro z
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
    rfl
  have hinjO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
    intro a b hab
    have := congrArg (algebraMap ↥(OL LL) ↥LL.1) hab
    rw [hcoe, hcoe] at this
    exact Subtype.ext ((algebraMap ℚ_[l] ↥LL.1).injective this)
  have hres : ∀ g : ↥(GK K), algebraMap ℤ_[l] ↥(OL LL) (χ₀ (g : GQ l) : ℤ_[l])
      = (W.χΓ (W.resΓ g) : ↥(OL LL)) := by
    intro g
    apply hinjO
    rw [hcoe, W.χΓ_res, hχ₀, (D.loc l).PD_χ]
  choose sec hsec using W.resΓ_onto
  have hsec' : ∀ g : W.Gam, algebraMap ℤ_[l] ↥(OL LL) (χ₀ (sec g : GQ l) : ℤ_[l])
      = (W.χΓ g : ↥(OL LL)) := fun g => by rw [hres, hsec]
  let χ : W.Gam →* ℤ_[l]ˣ := MonoidHom.mk' (fun g => χ₀ (sec g : GQ l)) (fun a b => by
    apply Units.ext
    apply hinj
    rw [Units.val_mul, map_mul, hsec', hsec', hsec', map_mul, Units.val_mul])
  have hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL)) := hsec'
  have hφX : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 := by
    rw [W.φ₀_X, W.q₀_def, hp]
  have hact : ∀ g, W.φ₀ = GlobalTheory.Cyc.phi l ↥(OL LL) ∧ W.γ₀ g = GlobalTheory.Cyc.act l ↥(OL LL) (χ g : ℤ_[l]) :=
    fun g => GlobalTheory.Cyc.act_unique l ↥(OL LL) hl0 hlu (W.γ₀ g) W.φ₀ (χ g : ℤ_[l]) hφX (W.γ₀_comm g)
      (W.γ₀_X g).1 (by rw [(W.γ₀_X g).2, hχ])
  have hφ := (hact 1).1
  have hX : W.X = fun _ => GlobalTheory.Cyc.XX l ↥(OL LL) s := by
    rw [← GlobalTheory.Cyc.Series.phi_pow_X, ← hφ, ← letφ_pow_const, LocWach.X, hWs]
    rfl
  refine ⟨χ, hχ, hφ, fun g => (hact g).2, fun i => by rw [hX], fun i => ?_, ?_, ?_⟩
  · have h1 := congrFun W.φA_X i
    rw [hX, Pi.mul_apply] at h1
    have h2 : W.φA (fun _ => GlobalTheory.Cyc.XX l ↥(OL LL) s) i = W.φ₀ (GlobalTheory.Cyc.XX l ↥(OL LL) s) := by
      simp [LocWach.φA, letφ]
    rw [h2, hφ, GlobalTheory.Cyc.Series.phi_XX] at h1
    exact (mul_left_cancel₀ (XX_ne_zero l _ hl0 s) h1).symm
  · have h1 := W.gam_gen
    rw [hWs, ← hχ, hcoe] at h1
    have h2 := ((GlobalTheory.HWL.NormVal.locPrime_v_normalised l (D.loc l) LL).1 _ (s : ℚ)).1 (by exact_mod_cast h1)
    have h3 : ((algebraMap ℚ_[l] ↥LL.1 ((χ W.gam : ℤ_[l]) : ℚ_[l]) - 1 : ↥LL.1) : Om l)
        = algebraMap ℚ_[l] (Om l) (((χ W.gam : ℤ_[l]) - 1 : ℤ_[l]) : ℚ_[l]) := by
      rw [PadicInt.coe_sub, PadicInt.coe_one, map_sub, map_one]
      rfl
    rw [h3, norm_algebraMap'] at h2
    rw [PadicInt.norm_def, h2, ← Real.rpow_intCast]
    push_cast
    rfl
  · intro u hu
    have hd : (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 :=
      Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ s).1 hu)
    obtain ⟨g, hg, hgu⟩ := honto K s h.2.2.1 u hd
    refine ⟨W.resΓ ⟨g, hg⟩, Units.ext (hinj ?_)⟩
    rw [hχ, ← hres, hgu]

end GlobalTheory.NL.CycRing
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

theorem _root_.GlobalTheory.T.depthZeroAdmissible_all_pending_data : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → PairedCharacterCondition.admDZ P := by
  first | exact @GlobalTheory.AdmDepthZero.main | exact GlobalTheory.AdmDepthZero.main | (intros; apply GlobalTheory.AdmDepthZero.main <;> assumption)
end
