module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem dual_nontriv (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Nontrivial V] :
    Nontrivial (Module.Dual K V) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hv ((Module.forall_dual_apply_eq_zero_iff K v).mp fun φ => by
    rw [Subsingleton.elim φ 0]
    rfl)

theorem UpperTheory.V.Fr.st_loc :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] [Nontrivial M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → (∀ g ∈ Dec (F := ℚ) A, cycMod ℚ Ω l 1 g = 1) → ∀ ρ : Representation (ZMod (l ^ 1)) (Dec (F := ℚ) A) M, (∀ g m, ρ g m = m) → Nat.card (H0 ρ) < Nat.card (H1 ρ) := by
  intro hFin hTate hEuler Ω _ _ _ l hl M _ _ _ _ _ _ A v hv hlv hcyc ρ htriv
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact hl.out⟩
  have hcont : ReciprocityTheory.Gal.ContAction ρ := by
    show Continuous fun p : Dec (F := ℚ) A × M => ρ p.1 p.2
    simp only [htriv]
    exact continuous_snd
  have hF := hFin ℚ Ω l 1 M A ρ v one_pos hv hcont
  have hE := (hEuler ℚ Ω l 1 M A ρ v one_pos hv hcont).2 hlv
  obtain ⟨⟨e⟩, -, -, -, hbij⟩ := hTate ℚ Ω l 1 M A ρ v one_pos hv hcont
  haveI : Finite (H2 ρ) := hF.2.2.1
  haveI : Finite (H0 ρ) := hF.1
  have hinv : ∀ φ : TDual (ZMod (l ^ 1)) M,
      φ ∈ H0 ((twDual ((cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype) ρ).comp (MonoidHom.id _)) := by
    intro φ g
    apply LinearMap.ext
    intro m
    simp [twDual, hcyc g.1 g.2]
    show φ (ρ g⁻¹ m) = φ m
    rw [htriv]
  haveI : Nontrivial (TDual (ZMod (l ^ 1)) M) := dual_nontriv (ZMod (l ^ 1)) M
  obtain ⟨φ0, hφ0⟩ := exists_ne (0 : TDual (ZMod (l ^ 1)) M)
  set X := H0 ((twDual ((cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype) ρ).comp (MonoidHom.id _))
  have hx0 : (⟨φ0, hinv φ0⟩ : X) ≠ 0 := fun h => hφ0 (congrArg Subtype.val h)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod (l ^ 1)) X, f ⟨φ0, hinv φ0⟩ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff (ZMod (l ^ 1)) _).mp h)
  let ψ : X →ₗ[ZMod (l ^ 1)] H2 ((charRep ((cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype)).comp
      (MonoidHom.id _)) := e.symm.toLinearMap ∘ₗ f
  have hψ : ψ ≠ 0 := by
    intro h
    have h1 : ψ ⟨φ0, hinv φ0⟩ = 0 := by rw [h]; rfl
    exact hf (e.symm.map_eq_zero_iff.mp h1)
  obtain ⟨y, hy⟩ := hbij.2 ψ
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hψ (by rw [← hy, map_zero])
  haveI : Nontrivial (H2 ρ) := ⟨⟨y, 0, hy0⟩⟩
  rw [hE]
  exact lt_mul_of_one_lt_right (Nat.card_pos) Finite.one_lt_card
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem card_bot' {R N : Type} [Ring R] [AddCommGroup N] [Module R N] :
    Nat.card (⊥ : Submodule R N) = 1 := by
  exact Nat.card_unique

theorem UpperTheory.V.Fr.st_count :
    GlobalFiniteness → GreenbergWiles → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContainsAbove S l → ContAction ρ → ∀ μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* (ZMod (l ^ 1))ˣ, μ.comp (toGS Ω _) = cycMod ℚ Ω l 1 → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ σ : G ℚ Ω, IsCC σ → (∀ m, ρ (toGS Ω _ σ) m = m → m = 0) → H0 (twDual μ ρ) = ⊥ → ∀ v₀ : S, (∀ v, v ≠ v₀ → H0 (ρ.comp (locFam S Av v)) = ⊥) → Nat.card (H0 (ρ.comp (locFam S Av v₀))) < Nat.card (H1 (ρ.comp (locFam S Av v₀))) → ∃ z ∈ Z1 ρ, z ∉ B1 ρ ∧ ∀ v, v ≠ v₀ → ∃ m, ∀ g ∈ Dec (F := ℚ) (Av v), z (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := by
  intro hGF hGW Ω _ _ _ l _ hl2 M _ _ _ _ _ S ρ hS hρ μ hμ Av hAv σ hσ hfix hdual v₀ hloc hlt
  classical
  have hH0 : H0 ρ = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    change m ∈ ρ.invariants at hm
    exact (Submodule.mem_bot _).2 (hfix m ((Representation.mem_invariants ρ m).1 hm _))
  obtain ⟨L, hL⟩ : ∃ L : LocCond ρ (locFam S Av), ∀ v, L v = if v = v₀ then ⊤ else ⊥ :=
    ⟨fun v => if v = v₀ then ⊤ else ⊥, fun _ => rfl⟩
  have hcc : ∀ w : InfinitePlace ℚ, w.IsReal → IsCCAt w ((fun _ => σ) w) := by
    intro w _
    obtain ⟨j, hj⟩ := hσ
    exact ⟨j, hj, Subsingleton.elim _ _⟩
  have hgw := hGW ℚ Ω l 1 M S ρ one_pos hl2 hS hρ μ hμ Av hAv (fun _ => σ) hcc L
  obtain ⟨_, hfin1, _, _⟩ := hGF ℚ Ω l 1 M S ρ one_pos hS hρ
  have e1 : Nat.card (H0 (twDual μ ρ)) = 1 := by
    rw [hdual]
    exact card_bot'
  have e2 : ∏ v, Nat.card (H0 (ρ.comp (locFam S Av v))) = Nat.card (H0 (ρ.comp (locFam S Av v₀))) := by
    refine Finset.prod_eq_single v₀ (fun v _ hv => ?_) (fun h => absurd (Finset.mem_univ _) h)
    rw [hloc v hv]
    exact card_bot'
  have e3 : archH0Card S ρ (fun _ => σ) = 1 := by
    unfold archH0Card
    rw [InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ), pow_zero, mul_one]
    apply Finset.prod_eq_one
    intro w _
    exact Nat.card_eq_one_iff_unique.2
      ⟨⟨fun a b => Subtype.ext ((hfix _ a.2).trans (hfix _ b.2).symm)⟩, ⟨⟨0, map_zero _⟩⟩⟩
  have e4 : Nat.card (H0 ρ) = 1 := by
    rw [hH0]
    exact card_bot'
  have e5 : ∏ v, Nat.card (L v) = Nat.card (H1 (ρ.comp (locFam S Av v₀))) := by
    rw [Finset.prod_eq_single v₀ (fun v _ hv => by rw [hL, if_neg hv]; exact card_bot')
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [hL, if_pos rfl]
    exact Nat.card_congr Submodule.topEquiv.toEquiv
  rw [e1, e2, e3, e4, e5] at hgw
  have hapos : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have hcpos : 0 < Nat.card (H0 (ρ.comp (locFam S Av v₀))) := Nat.card_pos
  have key : ∀ a b c d : ℕ, a * 1 * c * 1 = b * 1 * d → c < d → 0 < a → 0 < c → 1 < a := by
    intro a b c d h hcd ha hc
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp at h
      omega
    · by_contra hle
      have ha1 : a = 1 := by omega
      subst ha1
      nlinarith
  have h2 := key _ _ _ _ hgw hlt hapos hcpos
  haveI := Finite.one_lt_card_iff_nontrivial.1 h2
  obtain ⟨x, hx⟩ := exists_ne (0 : Sel ρ (locFam S Av) (continuous_locFam S Av) L)
  obtain ⟨z', hz'⟩ := Submodule.Quotient.mk_surjective _ x.1
  refine ⟨z'.1, z'.2, ?_, ?_⟩
  · intro hz
    apply hx
    apply Subtype.ext
    rw [Submodule.coe_zero, ← hz']
    exact (Submodule.Quotient.mk_eq_zero _).2 hz
  · intro v hv
    have hm := (mem_Sel ρ (locFam S Av) (continuous_locFam S Av) L x.1).1 x.2 v
    rw [hL, if_neg hv, Submodule.mem_bot, ← hz'] at hm
    simp only [resH1, Submodule.mapQ_apply] at hm
    obtain ⟨m, hm'⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hm)
    exact ⟨m, fun g hg => hm' ⟨g, hg⟩⟩
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.sc_quad :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (η : G ℚ Ω →* ℤˣ) (D : ℕ) (δ : Ω), 0 < D → δ ^ 2 = -(D : Ω) → (∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K Ω), Module.finrank ℚ K = 2 ∧ IsTotallyComplex K ∧ galOf ℚ K Ω = η.ker := by
  intro Ω _ _ _ η D δ hD hδ hη
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 : ((D : ℕ) : Ω) = 0 := by
      have := hδ.symm
      simpa using this
    exact hD.ne' (by exact_mod_cast h0)
  set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (D : ℚ) with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_add_C _ two_ne_zero
  have hdeg : p.natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hroot : Polynomial.aeval δ p = 0 := by
    simp [hp, hδ]
  have hirr : Irreducible p := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_
    intro x hx
    simp only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  have hmin : p = minpoly ℚ δ := minpoly.eq_of_irreducible_of_monic hirr hroot hmon
  have hint : IsIntegral ℚ δ := ⟨p, hmon, by rw [← Polynomial.aeval_def]; exact hroot⟩
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({δ} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField (IntermediateField.adjoin ℚ ({δ} : Set Ω)) := by constructor
  refine ⟨IntermediateField.adjoin ℚ ({δ} : Set Ω), inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [IntermediateField.adjoin.finrank hint, ← hmin, hdeg]
  · refine ⟨fun v => ?_⟩
    rw [NumberField.InfinitePlace.isComplex_iff]
    intro hr
    rw [NumberField.ComplexEmbedding.isReal_iff] at hr
    set φ := v.embedding
    let d : IntermediateField.adjoin ℚ ({δ} : Set Ω) := ⟨δ, IntermediateField.mem_adjoin_simple_self ℚ δ⟩
    have hd : d ^ 2 = -(D : IntermediateField.adjoin ℚ ({δ} : Set Ω)) := Subtype.ext (by simpa [d] using hδ)
    have hz : (φ d) ^ 2 = -(D : ℂ) := by
      have := congrArg φ hd
      simpa using this
    have hc : (starRingEnd ℂ) (φ d) = φ d := by
      have := RingHom.congr_fun hr d
      simpa using this
    have him : (φ d).im = 0 := Complex.conj_eq_iff_im.mp hc
    have hre := congrArg Complex.re hz
    simp [pow_two, him] at hre
    nlinarith [mul_self_nonneg (φ d).re]
  · ext σ
    rw [mem_galOf, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : σ δ = δ := h ⟨δ, IntermediateField.mem_adjoin_simple_self ℚ δ⟩
      rw [hη σ] at h1
      rcases Int.units_eq_one_or (η σ) with h2 | h2
      · exact h2
      · exfalso
        rw [h2] at h1
        simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h1
        have : (2 : Ω) * δ = 0 := by linear_combination -h1
        rcases mul_eq_zero.mp this with h3 | h3
        · exact two_ne_zero h3
        · exact hδ0 h3
    · intro h x
      have hσδ : σ δ = δ := by rw [hη σ, h]; simp
      have hext : ((σ : Ω →ₐ[ℚ] Ω).comp (IntermediateField.val _) :
          IntermediateField.adjoin ℚ ({δ} : Set Ω) →ₐ[ℚ] Ω) = IntermediateField.val _ :=
        IntermediateField.algHom_ext_of_eq_adjoin ℚ rfl (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hσδ)
      exact AlgHom.congr_fun hext x
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

theorem UpperTheory.V.Fr.st_conj :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k : Type) [Field k] (κ : G ℚ Ω →* kˣ) (y : G ℚ Ω → k), (∀ s t, y (s * t) = y s + κ s * y t) → ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v → (∃ b, ∀ s ∈ Dec (F := ℚ) A, y s = κ s * b - b) → ∃ b, ∀ s ∈ Dec (F := ℚ) A', y s = κ s * b - b := by
  intro Ω _ _ _ k _ κ y hy v A A' hA hA' ⟨b, hb⟩
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) hA hA'
  refine ⟨(κ σ : k) * b - y σ, fun s hs => ?_⟩
  have hs' : s • A' = A' := mem_Dec.mp hs
  have ht : σ⁻¹ * s * σ ∈ Dec (F := ℚ) A := by
    rw [mem_Dec, mul_smul, mul_smul, hσ, hs', ← hσ, ← mul_smul, inv_mul_cancel, one_smul]
  have hbt := hb _ ht
  have hκ : κ (σ⁻¹ * s * σ) = κ s := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have hκ' : ((κ (σ⁻¹ * s * σ) : kˣ) : k) = κ s := congrArg Units.val hκ
  have h1 := hy s σ
  have h2 := hy σ (σ⁻¹ * s * σ)
  have h3 : σ * (σ⁻¹ * s * σ) = s * σ := by group
  rw [h3] at h2
  linear_combination -h1 + h2 + (κ σ : k) * hbt + (κ σ : k) * b * hκ'
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_eta :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (η : G ℚ Ω →* ℤˣ) (D : ℕ) (δ : Ω), 0 < D → δ ^ 2 = -(D : Ω) → (∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) → ∀ σ : G ℚ Ω, IsCC σ → η σ = -1 := by
  intro Ω _ _ _ η D δ hD hδ hs σ hσ
  obtain ⟨j, hj⟩ := hσ
  rcases Int.units_eq_one_or (η σ) with h | h
  · exfalso
    have h1 : σ δ = δ := by rw [hs σ, h]; simp
    have h2 : j δ = starRingEnd ℂ (j δ) := by
      have := hj δ
      rw [← this]
      exact congrArg j h1.symm
    have h3 : (j δ) ^ 2 = -(D : ℂ) := by
      rw [← map_pow, hδ]; simp
    have him : (j δ).im = 0 := Complex.conj_eq_iff_im.mp h2.symm
    have h4 := congrArg Complex.re h3
    simp [sq, him] at h4
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    nlinarith [mul_self_nonneg (j δ).re]
  · exact h
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem valuation_not_lt_one_of_coprime {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {l N : ℕ} (h : Nat.Coprime l N)
    (hl : B.valuation (l : Ω) < 1) : ¬ B.valuation (N : Ω) < 1 := by
  intro hN
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * (l : Ω) + (b : Ω) * (N : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have key : ∀ (c : ℤ) (x : Ω), B.valuation x < 1 → B.valuation ((c : Ω) * x) < 1 := by
    intro c x hx
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((B.valuation_le_one_iff _).2 (intCast_mem B c))) hx
  have := B.valuation.map_add_lt (key a _ hl) (key b _ hN)
  rw [e, map_one] at this
  exact lt_irrefl _ this

private theorem eq_idempotent_mul_add_of_mul_sub_eq {Ω : Type} [Field Ω] {a b : ℕ} (h : Nat.Coprime a b) {x y : Ω} (hy : y ≠ 0)
    (ha : x ^ a = y ^ a) (hb : x ^ b = y ^ b) : x = y := by
  have h1 : (x / y) ^ a = 1 := by rw [div_pow, ha, div_self (pow_ne_zero _ hy)]
  have h2 : (x / y) ^ b = 1 := by rw [div_pow, hb, div_self (pow_ne_zero _ hy)]
  have h3 : (x / y) ^ (Nat.gcd a b) = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [h.gcd_eq_one, pow_one] at h3
  exact (div_eq_one_iff_eq hy).1 h3

theorem UpperTheory.V.Fr.sc_strip :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (C : Type) [Group C] (χ : G ℚ Ω →* C) (r N : ℕ), N ≠ 0 → ¬ l ∣ N → Af.KillsMu (l ^ r * N) χ → ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 → Ine (F := ℚ) B ≤ χ.ker → Af.KillsMu N χ := by
  intro Ω _ _ _ l hl C _ χ r N hN hlN hχ B hB hI s hs
  haveI : NeZero N := ⟨hN⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ hl.out.ne_zero)⟩
    infer_instance
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlN
  obtain ⟨σ, hσ, hc⟩ := GlobalTheory.T.cyclotomicChar_inertia_surjective Ω l B hB (cycZ ℚ Ω l s)
  have hker := (UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 B (valuation_not_lt_one_of_coprime B hcop hB) hσ
  have hone := (UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 B (valuation_not_lt_one_of_coprime B hcop hB) (Ine (F := ℚ) B).one_mem
  have hσN : ∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ := by
    intro ζ hζ
    have h1 := UpperTheory.V.Chr.cls_spec (k := ℚ) N σ ζ hζ
    have h2 := UpperTheory.V.Chr.cls_spec (k := ℚ) N 1 ζ hζ
    rw [MonoidHom.mem_ker] at hker hone
    rw [hker] at h1
    rw [hone] at h2
    rw [h1, ← h2]
    rfl
  have hσl : ∀ ζ : Ω, ζ ^ l ^ r = 1 → s ζ = σ ζ := by
    intro ζ hζ
    have h1 : s ζ = ζ ^ ((cycZ ℚ Ω l s).val.toZModPow r).val :=
      cyclotomicCharacter.spec l s.toRingEquiv ζ hζ
    have h2 : σ ζ = ζ ^ ((cycZ ℚ Ω l σ).val.toZModPow r).val :=
      cyclotomicCharacter.spec l σ.toRingEquiv ζ hζ
    rw [h1, h2, hc]
  have h1 : χ (σ⁻¹ * s) = 1 := by
    refine hχ _ fun ζ hζ => ?_
    have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (mul_ne_zero (pow_ne_zero _ hl.out.ne_zero) hN)] at hζ
      exact zero_ne_one hζ
    have e : s ζ = σ ζ := by
      refine eq_idempotent_mul_add_of_mul_sub_eq (Nat.Coprime.pow_left r hcop) ((map_ne_zero σ).2 h0) ?_ ?_
      · have hz : (ζ ^ l ^ r) ^ N = 1 := by rw [← pow_mul, hζ]
        rw [← map_pow, ← map_pow, hs _ hz, hσN _ hz]
      · have hz : (ζ ^ N) ^ l ^ r = 1 := by rw [← pow_mul, mul_comm, hζ]
        rw [← map_pow, ← map_pow, hσl _ hz]
    rw [AlgEquiv.mul_apply, e, ← AlgEquiv.mul_apply, inv_mul_cancel]
    rfl
  have h2 : χ σ = 1 := hI hσ
  rw [map_mul, map_inv, h2, inv_one, one_mul] at h1
  exact h1
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem exists_place_rat {w : ℕ} (hw : w.Prime) :
    ∃ v₀ : HeightOneSpectrum (𝓞 ℚ), ∀ v : HeightOneSpectrum (𝓞 ℚ), ((w : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ v = v₀ := by
  have hne : ((w : ℕ) : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hw.ne_zero
  have hprime : Prime ((w : ℕ) : 𝓞 ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
    exact Nat.prime_iff_prime_int.mp hw
  have hP : (Ideal.span {((w : ℕ) : 𝓞 ℚ)}).IsPrime := (Ideal.span_singleton_prime hne).mpr hprime
  have hbot : Ideal.span {((w : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hne
  have hmax := hP.isMaximal hbot
  let v₀ : HeightOneSpectrum (𝓞 ℚ) := ⟨Ideal.span {((w : ℕ) : 𝓞 ℚ)}, hP, hbot⟩
  refine ⟨v₀, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rw [HeightOneSpectrum.ext_iff]
    symm
    exact hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  · rw [hv]
    exact Ideal.subset_span (Set.mem_singleton _)

private theorem finite_above {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(n : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hn
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem UpperTheory.V.Fr.st_set :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l w N : ℕ), l.Prime → w.Prime → N ≠ 0 → ∀ (C : Type) [Group C] (κ : G ℚ Ω →* C), (∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → Ine (F := ℚ) A ≤ κ.ker) → ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v₀ : HeightOneSpectrum (𝓞 ℚ)), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((w : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ v = v₀) ∧ ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω), IsPlaceOver A v → (v ∈ S ↔ ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨ v = v₀ ∨ ¬ Ine (F := ℚ) A ≤ κ.ker) := by
  intro Ω _ _ _ l w N hl hw hN C _ κ hκ
  classical
  obtain ⟨v₀, hv₀⟩ := exists_place_rat hw
  have hT := finite_above (n := l * w * N) (mul_ne_zero (mul_ne_zero hl.ne_zero hw.ne_zero) hN)
  have key : ∀ (A A' : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v →
      IsPlaceOver A' v → Ine (F := ℚ) A ≤ κ.ker → Ine (F := ℚ) A' ≤ κ.ker := by
    intro A A' v hA hA' hle τ hτ
    obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isPlaceOver hA hA'
    have h1 := hle (GlobalTheory.Cut.ShaBound.conj_mem_Ine' hτ)
    have h2 := κ.normal_ker.conj_mem _ h1 σ
    simpa [mul_assoc] using h2
  have hN' : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v →
      ¬ Ine (F := ℚ) A ≤ κ.ker → ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro A v hA hne
    have h1 : A.valuation (N : Ω) < 1 := by
      by_contra h
      exact hne (hκ A h)
    rw [← hA (N : 𝓞 ℚ)]
    have e : algebraMap ℚ Ω (((N : 𝓞 ℚ) : ℚ)) = (N : Ω) := by simp
    rw [e]
    exact h1
  refine ⟨hT.toFinset.filter (fun v => ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨ v = v₀ ∨
    ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ ¬ Ine (F := ℚ) A ≤ κ.ker), v₀, hv₀, ?_⟩
  intro v A hA
  rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, h | h | ⟨A', hA', hne⟩⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (fun hle => hne (key A A' v hA hA' hle)))
  · intro h
    refine ⟨?_, ?_⟩
    · have hmem : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨ ((w : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨
          ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ((hv₀ v).mpr h))
        · exact Or.inr (Or.inr (hN' A v hA h))
      push_cast
      rcases hmem with h | h | h
      · exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ h)
      · exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h)
      · exact v.asIdeal.mul_mem_left _ h
    · rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨A, hA, h⟩)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.st_mu :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M a : ℕ), M ≠ 0 → ∀ (C : Type) [Group C] (χ : G ℚ Ω →* C), Af.KillsMu (M ^ a) χ → IsOpen (χ.ker : Set (G ℚ Ω)) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ χ.ker := by
  intro Ω _ _ _ M a hM C _ χ hk
  haveI : NeZero (M ^ a) := ⟨pow_ne_zero _ hM⟩
  obtain ⟨hopen, -, -, -, hine⟩ := UpperTheory.V.Chr.clsFacts ℚ Ω (M ^ a)
  have hle : (UpperTheory.V.Chr.cls ℚ Ω (M ^ a)).ker ≤ χ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    apply hk s
    intro ζ hζ
    rw [UpperTheory.V.Chr.cls_spec (M ^ a) s ζ hζ, hs, Units.val_one, ZMod.val_one_eq_one_mod,
      ← pow_eq_pow_mod 1 hζ, pow_one]
  refine ⟨Subgroup.isOpen_mono hle hopen, ?_⟩
  intro A hA
  refine le_trans (hine A ?_) hle
  rw [Nat.cast_pow, map_pow, not_lt]
  exact one_le_pow₀ (not_lt.mp hA)
end
