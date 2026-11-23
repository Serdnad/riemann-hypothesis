module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
private theorem val_smul_lt (g : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have e : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := fun z => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g z = g • z from rfl, inv_smul_smul]
  rw [valuation_lt_one_iff', valuation_lt_one_iff', e, ← map_inv₀, e, map_eq_zero]

omit [NumberField F] in
private theorem val_smul_le (g : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g y = g • y from rfl, inv_smul_smul]

omit [NumberField F] in
private theorem conj_dec {g τ : G F Ω} {A : ValuationSubring Ω} (h : τ ∈ (g • A).decompositionSubgroup F) :
    g⁻¹ * τ * g ∈ A.decompositionSubgroup F := by
  have h1 : τ • g • A = g • A := h
  show (g⁻¹ * τ * g) • A = A
  rw [mul_smul, mul_smul, h1, inv_smul_smul]

omit [NumberField F] in
private theorem conj_apply (g τ : G F Ω) (x : Ω) : g ((g⁻¹ * τ * g) x) = τ (g x) := by
  change g • ((g⁻¹ * τ * g) • x) = τ • (g • x)
  rw [mul_smul, mul_smul, smul_inv_smul]

omit [NumberField F] in
private theorem conj_frob {g τ : G F Ω} {A : ValuationSubring Ω} {q : ℕ} (h : IsFrob (g • A) q τ) :
    IsFrob A q (g⁻¹ * τ * g) := by
  refine ⟨conj_dec h.1, fun x hx => ?_⟩
  have h1 := h.2 (g x) ((val_smul_le g A x).2 hx)
  rwa [← conj_apply, ← map_pow, ← map_sub, val_smul_lt] at h1

private theorem conj_ine {g τ : G F Ω} {A : ValuationSubring Ω} (h : τ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * τ * g ∈ Ine (F := F) A := by
  refine ⟨conj_dec h.1, fun x hx => ?_⟩
  have h1 := h.2 (g x) ((val_smul_le g A x).2 hx)
  rwa [← conj_apply, ← map_sub, val_smul_lt] at h1

private theorem ine_fix {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) {M : ℕ}
    (hM : ((M : ℕ) : 𝓞 F) ∉ w.asIdeal) {s : G F Ω} (hs : s ∈ Ine (F := F) A) (ζ : Ω) (hζ : ζ ^ M = 1) : s ζ = ζ := by
  set v := A.valuation with hvdef
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hM (by simp)
  have hvM : ¬ v (M : Ω) < 1 := by
    intro hlt
    apply hM
    rw [← hA]
    simpa using hlt
  have hζ1 : v ζ = 1 := by
    rcases lt_trichotomy (v ζ) 1 with h | h | h
    · have h2 := pow_lt_one' h hM0
      rw [← map_pow, hζ, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
    · exact h
    · have h2 := one_lt_pow' h hM0
      rw [← map_pow, hζ, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hsd : v (s ζ - ζ) < 1 := hs.2 ζ hζ1.le
  have hηM : (s ζ) ^ M = 1 := by rw [← map_pow, hζ, map_one]
  set η := s ζ with hη
  set u := η * ζ⁻¹ with hu
  have huM : u ^ M = 1 := by rw [hu, mul_pow, inv_pow, hηM, hζ, inv_one, mul_one]
  have hu1 : v (u - 1) < 1 := by
    have e : u - 1 = (η - ζ) * ζ⁻¹ := by rw [hu, sub_mul, mul_inv_cancel₀ hζ0]
    rw [e, map_mul, map_inv₀, hζ1, inv_one, mul_one]
    exact hsd
  have hule : v u ≤ 1 := by
    have e : u = (u - 1) + 1 := by ring
    rw [e]
    exact (v.map_add _ _).trans (max_le hu1.le (by rw [map_one]))
  by_contra hne
  have hu_ne : u ≠ 1 := by
    intro h1
    apply hne
    have e : η = u * ζ := by rw [hu, mul_assoc, inv_mul_cancel₀ hζ0, mul_one]
    rw [e, h1, one_mul]
  have hsum : ∑ i ∈ Finset.range M, u ^ i = 0 := by
    have h := geom_sum_mul u M
    rw [huM, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hu_ne)
  have hlt : v (∑ i ∈ Finset.range M, (u ^ i - 1)) < 1 := by
    apply Valuation.map_sum_lt v one_ne_zero
    intro i _
    rw [← geom_sum_mul u i, map_mul]
    have hs1 : v (∑ j ∈ Finset.range i, u ^ j) ≤ 1 :=
      Valuation.map_sum_le v (fun j _ => by rw [map_pow]; exact pow_le_one' hule j)
    calc v (∑ j ∈ Finset.range i, u ^ j) * v (u - 1) ≤ 1 * v (u - 1) := by gcongr
      _ = v (u - 1) := one_mul _
      _ < 1 := hu1
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, zero_sub, Valuation.map_neg] at hlt
  apply hvM
  simpa using hlt

end

theorem UpperTheory.V.Br.frobEx :
    UpperTheory.V.Br.FrobEx := by
  intro F Ω _ _ _ _ _ l _ ι n r w
  refine ⟨?_, ?_⟩
  · intro B B' hB hB'
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have h1 := (hB A hA).2 σ hσ
    have h2 := (hB' A hA).2 σ hσ
    have h3 := congrArg Polynomial.roots (h1.symm.trans h2)
    simpa [Polynomial.roots_multiset_prod_X_sub_C] using h3
  · intro M hlev hl hM
    obtain ⟨A0, hA0, χ, hχ, P, hP⟩ := hlev w hl
    have hI0 : ∀ t ∈ Ine (F := F) A0, r t = 1 := by
      intro t ht
      have hd := hP t ht
      have hc : ∀ i, χ i t = 1 := fun i => hχ i t (fun ζ hζ => ine_fix hA0 hM ht ζ hζ)
      simp only [hc, Units.val_one, Matrix.diagonal_one] at hd
      have hq : P * r t * P⁻¹ = 1 := Units.ext hd
      calc r t = P⁻¹ * (P * r t * P⁻¹) * P := by group
        _ = 1 := by rw [hq]; group
    obtain ⟨σ0, hσ0⟩ := exists_isFrob hA0
    refine ⟨(Polynomial.map ι.toRingHom
      ((r σ0⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).roots, ?_⟩
    intro A hA
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver hA0 hA
    subst hg
    refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · have ht := hI0 _ (conj_ine hs)
      calc r s = r g * r (g⁻¹ * s * g) * r g⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = 1 := by rw [ht]; simp
    · have hc := inv_mul_mem_Ine_of_isFrob hσ0 (conj_frob hσ)
      have he : r (g⁻¹ * σ * g) = r σ0 := by
        have h4 := hI0 _ hc
        rw [map_mul, map_inv] at h4
        exact (inv_mul_eq_one.1 h4).symm
      have hu : r σ⁻¹ = r g * r σ0⁻¹ * (r g)⁻¹ := by
        rw [map_inv r σ0, ← he]
        simp only [map_mul, map_inv]
        group
      rw [hu, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
      exact Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits _)
        ((Matrix.charpoly_monic _).map _)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
open GlobalTheory.CuspRep (Af finId pFin)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)

section

variable {F : Type} [Field F] [NumberField F]

private theorem cc_finId_local (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finId F (Units.map (pFin F).toMonoidHom (localIdele F w x)) = localIdele F w x := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
    simp
  · change (1 : Af F) - 1 + _ = _
    rw [sub_self, zero_add]
    rfl

private theorem cc_pFin_inf (v : InfinitePlace F) (x : (v.Completion)ˣ) :
    Units.map (pFin F).toMonoidHom (infIdele F v x) = 1 := Units.ext rfl

private theorem cc_split (k : Fˣ) :
    infDiag k * finId F (Units.map (algebraMap F (Af F)).toMonoidHom k) = diagUnits F k := by
  classical
  have h : ((infDiag k : Ideles F) : AdeleRing (𝓞 F) F) = (algebraMap F (InfiniteAdeleRing F) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace F, w.Completion) →* AdeleRing (𝓞 F) F :=
      MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    change ∏ w : InfinitePlace F, ι (Pi.mulSingle w (algebraMap F w.Completion k)) =
      ι (fun w => algebraMap F w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  refine Prod.ext ?_ ?_
  · change algebraMap F (InfiniteAdeleRing F) k * (1 - 0 + 0) = algebraMap F (InfiniteAdeleRing F) k
    simp
  · change (1 : Af F) * (1 - 1 + algebraMap F (Af F) k) = algebraMap F (Af F) k
    simp

private theorem cc_inf_fixed (hF : Module.finrank ℚ F = 1) (χ : HChar F) (a : (F →+* ℂ) → ℤ) (h : IsAlgPos χ a)
    (σ : ℂ ≃+* ℂ) (k : Fˣ) : σ ((χ.inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
  have hs : Function.Surjective (algebraMap ℚ F) := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hF).2
  obtain ⟨q, hq⟩ := hs (k : F)
  have h1 := h (k ^ 2) fun φ => by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_two_pos_of_ne_zero ((map_ne_zero φ).2 k.ne_zero)
  have h2 : ((χ.inf k : ℂˣ) : ℂ) ^ 2 = (∏ φ : F →+* ℂ, (q : ℂ) ^ a φ) ^ 2 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun φ _ => ?_
    rw [Units.val_pow_eq_pow_val, map_pow, ← hq, eq_ratCast, map_ratCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, mul_comm]
  have h3 : σ (∏ φ : F →+* ℂ, (q : ℂ) ^ a φ) = ∏ φ : F →+* ℂ, (q : ℂ) ^ a φ := by
    simp only [map_prod, map_zpow₀, map_ratCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with e | e
  · rw [e, h3]
  · rw [e, map_neg, h3]

end

theorem UpperTheory.V.Br.charConj :
    UpperTheory.V.Br.CharConj := by
  intro F _ _ hF χ a ha σ
  have hσ : ∀ k : Fˣ, σ ((χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) : ℂˣ) : ℂ) =
      ((χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) : ℂˣ) : ℂ) := fun k => by
    have h1 := χ.2.2 k
    rw [← cc_split k, map_mul] at h1
    have h2 : χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) = (χ.inf k)⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    rw [h2, Units.val_inv_eq_inv_val, map_inv₀, cc_inf_fixed hF χ a ha σ k]
  let ψ : (Af F)ˣ →* ℂˣ := χ.1.comp (finId F)
  have hψ : Continuous ψ := χ.2.1.comp (GlobalTheory.CuspRep.continuous_finId F)
  let ψ' : (Af F)ˣ →* ℂˣ := (Units.map (σ : ℂ →+* ℂ).toMonoidHom).comp ψ
  have hψ' : Continuous ψ' := by
    refine continuous_of_continuousAt_one ψ' ?_
    have h1 : {u | ψ u = 1} ∈ nhds (1 : (Af F)ˣ) :=
      (GlobalTheory.CuspRep.isOpen_ker_finIdele F ψ hψ).mem_nhds (map_one ψ)
    refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [h1] with u hu
    change 1 = Units.map _ (ψ u)
    rw [hu, map_one]
  let p := Units.map (pFin F).toMonoidHom
  have hp : Continuous p := Continuous.units_map _ continuous_snd
  let χ' : HChar F := ⟨χ.1 * (ψ.comp p)⁻¹ * ψ'.comp p, (χ.2.1.mul (hψ.comp hp).inv).mul (hψ'.comp hp), fun k => by
    have e : ψ' (Units.map (algebraMap F (Af F)).toMonoidHom k) = ψ (Units.map (algebraMap F (Af F)).toMonoidHom k) :=
      Units.ext (hσ k)
    change χ.1 _ * (ψ (Units.map (algebraMap F (Af F)).toMonoidHom k))⁻¹ *
      ψ' (Units.map (algebraMap F (Af F)).toMonoidHom k) = 1
    rw [χ.2.2 k, e, one_mul, inv_mul_cancel]⟩
  have hloc : ∀ w x, χ'.loc w x = Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.loc w x) := fun w x => by
    have e := cc_finId_local w x
    change χ.1 (localIdele F w x) * (χ.1 (finId F (Units.map (pFin F).toMonoidHom (localIdele F w x))))⁻¹ *
      Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.1 (finId F (Units.map (pFin F).toMonoidHom (localIdele F w x)))) = _
    rw [e, mul_inv_cancel, one_mul]
    rfl
  refine ⟨χ', fun v => ?_, fun w hw => ⟨fun x hx => ?_, ?_⟩⟩
  · change χ.1 (infIdele F v (-1)) * (ψ (Units.map (pFin F).toMonoidHom (infIdele F v (-1))))⁻¹ *
      ψ' (Units.map (pFin F).toMonoidHom (infIdele F v (-1))) = χ.1 (infIdele F v (-1))
    rw [cc_pFin_inf, map_one, map_one, inv_one, mul_one, mul_one]
  · rw [hloc, hw x hx, map_one]
  · exact congrArg Units.val (hloc w (atFin w (unif w)))
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open scoped Matrix

section General

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ G V} {ρ : Representation ℂ G W} {K : Subgroup G} {h : G → ℂ} {x : V} {y : W}

private theorem pair_heckeVec (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed σ K)
    (hy : y ∈ fixed ρ K) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (θ : G ≃* G) (hθ : ∀ k, k ∈ K ↔ θ k ∈ K)
    (hi : ∀ g v w, β (σ (θ g) v) (ρ g w) = β v w)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t⁻¹ = t ∧ g = a * t * b) :
    β (heckeVec σ K h x) y = β x (heckeVec ρ K h y) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have hg := GlobalTheory.LGrp.mem_fixed.1 hy
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (σ (a * t * b) x) y = β (σ t x) y := fun a ha b hb t => by
    obtain ⟨a, rfl⟩ := θ.surjective a
    rw [map_mul σ, map_mul σ, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hg a ((hθ a).2 ha)).symm).trans (hi a _ _)
  have bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y) := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]
    exact (congrArg (fun u => β u _) (hf _ ((hθ a).1 ha)).symm).trans (hi a _ _)
  have inv : ∀ t, β (σ (θ t⁻¹) x) y = β x (ρ t y) := fun t => by
    rw [← hi t⁻¹ x (ρ t y)]; simp
  have e1 := (β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh σ x)
  have e2 := (β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • σ c.out x) y = β x (h c.out • ρ c.out y)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, bi _ ha _ hb, bi' _ ha _ hb, ← inv, htt]

private theorem exists_fixed_pair [TopologicalSpace G] [IsTopologicalGroup G] (hρ : IsSmooth ρ)
    (hK : IsCompact (K : Set G)) (l : W →ₗ[ℂ] ℂ) (hl : ∀ k ∈ K, ∀ v, l (ρ k v) = l v) (y : W) :
    ∃ y' ∈ fixed ρ K, l y' = l y := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex := by
    have ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K) := (hρ y).preimage continuous_subtype_val
    haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨GlobalTheory.OrbitAvg.avg ρ K y,
    GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩
  haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)
  have hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
  have h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y := fun q => hl _ q.out.2 y

  simp only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]

end General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.ConjPlace in
private theorem sat_eq_of_pair {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (hρ : IsSmooth ρ) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n g) x) (ρ g y) = β x y)
    {x : V} {B C : Multiset ℂˣ} (hx : IsSatVecGL w σ x B) (hC : HasSatGL w ρ C) : B = C := by
  classical
  have hKc : IsCompact (KGL w (n := n) : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  obtain ⟨y₀, hy₀⟩ : ∃ y, β x y ≠ 0 := by
    by_contra hn
    exact hx.1 (hβ x fun y => by_contra fun h => hn ⟨y, h⟩)
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨y, hyK, hy⟩ := exists_fixed_pair hρ hKc (β x) (fun k hk v => by
    have := hi k x v
    rwa [GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ ((hK k).1 hk)] at this) y₀
  have hne : β x y ≠ 0 := hy ▸ hy₀
  have hy' := hC.2 y hyK fun h0 => hne (by rw [h0, map_zero])
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  refine eq_of_satEig_eq (qV_ne_zero w) hx.2.2.1 hy'.2.2.1 fun j hj => ?_
  have key := pair_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 hyK β
    (GlobalTheory.LFun.ConjPlace.invT c n) hK hi
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, invT_dGL c ϖ j, e⟩)
  rw [hx.2.2.2 _ hp j hj, hy'.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul] at key
  exact mul_right_cancel₀ hne key

open Neutral.B1 ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published

private theorem conj_locGL {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) ((cPl w).adicCompletion E)) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g) =
      locGL E a w (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cPl v)) (locGL E a (cPl w) g)) := fun v => rfl
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E a w (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin a) (v.adicCompletion E) => u.val i j) (key2 v)

private theorem conjLoc_surjective {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (GlobalTheory.ThetaPull.cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (GlobalTheory.ThetaPull.cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

theorem UpperTheory.V.Br.satOfPol :
    UpperTheory.V.Br.SatOfPol := by
  intro E _ _ _ n P ψ hd w hu B B' hB hB'
  have hu' : (ψ⁻¹).UnrAt w := fun x hx => by
    have h3 : ψ.loc w x = 1 := hu x hx
    exact (congrArg Inv.inv h3).trans inv_one
  have hC := GlobalTheory.SphGal.hasSatGL_twist E n P ψ⁻¹ w B hu' hB
  rw [CG.hasSat_mk] at hB'
  let c : (cPl w).adicCompletion E ≃+* w.adicCompletion E :=
    RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surjective w⟩
  have hq : Formalism.UG.qV E w = Formalism.UG.qV E (cPl w) := by
    change Ideal.absNorm w.asIdeal = Ideal.absNorm (conjSrc (IsCMField.complexConj E).toRingEquiv w).asIdeal
    rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
    rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
    exact (Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)) w.asIdeal (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)
      (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv).symm
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB'
  have hx' := GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c (conjLoc_spec _ w).2.2 hq hx
  obtain ⟨β, -, hr, hf, -⟩ := hd
  refine sat_eq_of_pair ((P.twist ψ⁻¹).isSmooth_locRep w) β.flip hr (fun g u v => ?_) hx' hC
  obtain ⟨g, rfl⟩ : ∃ g', Matrix.GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g' = g :=
    ⟨Matrix.GeneralLinearGroup.map c.symm.toRingHom g, Units.ext (Matrix.ext fun i j => c.apply_symm_apply _)⟩
  have e1 : GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      GlobalTheory.LFun.ConjPlace.invT c n g := Units.ext (Matrix.ext fun i j => by
    rw [GlobalTheory.LFun.ConjPlace.invT_val, GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]; rfl)
  rw [e1]
  change β ((P.twist ψ⁻¹).locRep w _ v) (P.locRep (cPl w) ((GlobalTheory.LFun.ConjPlace.invT c n).symm (GlobalTheory.LFun.ConjPlace.invT c n g)) u) = β v u
  rw [MulEquiv.symm_apply_apply, CuspSub.locRep_eq, CuspSub.locRep_eq, ← conj_locGL, ← hf (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E n (cPl w) g)) v u]
  have e2 : Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E n (cPl w) g)) = locGL E n (cPl w) g :=
    Units.ext (Matrix.ext fun i j => GlobalTheory.ThetaPull.cFin_cFin _)
  exact congrArg (fun k => β _ (P.op (.fin k) u)) e2.symm
end
