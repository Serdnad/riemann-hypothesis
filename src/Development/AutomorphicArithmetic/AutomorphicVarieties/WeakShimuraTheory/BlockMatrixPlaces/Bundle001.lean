module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.plusCard :
    LocalFiniteness → LocalEulerChar → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (B : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (ρ : Representation (ZMod (l ^ r)) (Dec (F := ℚ) B) M), 0 < r → IsPlaceOver B v → ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ContAction ρ →
          ∀ P : Submodule (ZMod (l ^ r)) M, (∀ h, ∀ x ∈ P, ρ h x ∈ P) → (∃ s, Function.Bijective fun x => ρ s x - x) →
          ∃ L : Submodule (ZMod (l ^ r)) (H1 ρ), Nat.card P ≤ Nat.card L ∧ ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ L → ∃ y, ∀ h, z.1 h - (ρ h y - y) ∈ P := by
  intro hFin hEul Ω _ _ _ l _ r M _ _ _ _ _ B v ρ hr hB hl hc P hP hs
  let ρP : Representation (ZMod (l ^ r)) (Dec (F := ℚ) B) P :=
    { toFun := fun h => (ρ h).restrict (fun x hx => hP h x hx)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro a b
        ext x
        simp }
  have hρP : ∀ h (x : P), ((ρP h x : P) : M) = ρ h x := fun _ _ => rfl
  have hcP : ContAction ρP := by
    have h1 : Continuous fun p : Dec (F := ℚ) B × P => ρ p.1 (p.2 : M) :=
      hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact continuous_induced_rng.2 h1
  obtain ⟨hH0, hH1, hH2, -⟩ := hFin ℚ Ω l r P B ρP v hr hB hcP
  have hE := (hEul ℚ Ω l r P B ρP v hr hB hcP).1 hl
  have hdeg : 0 < locDeg v := by
    unfold locDeg
    exact Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hle : Nat.card P ≤ Nat.card (H1 ρP) := by
    rw [hE]
    have a0 : 0 < Nat.card (H0 ρP) := Nat.card_pos
    have a2 : 0 < Nat.card (H2 ρP) := Nat.card_pos
    calc Nat.card P ≤ Nat.card P ^ locDeg v := Nat.le_self_pow hdeg.ne' _
      _ ≤ Nat.card (H0 ρP) * Nat.card (H2 ρP) * Nat.card P ^ locDeg v :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos a0 a2)
  have hu : Continuous (P.subtype : P → M) := continuous_subtype_val
  have heq : ∀ (g : Dec (F := ℚ) B) (m : P), P.subtype (ρP g m) = ρ g (P.subtype m) := fun _ _ => rfl
  let φ := mapH1 ρP ρ P.subtype hu heq
  obtain ⟨s, hsb⟩ := hs
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
    rw [Submodule.Quotient.mk_eq_zero]
    have hw' : (φ (Submodule.Quotient.mk w)) = 0 := hw
    simp only [φ, mapH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.coe_subtype] at hw'
    rw [mem_coboundaries1] at hw'
    obtain ⟨m, hm⟩ := hw'
    have hm' : ∀ g, ((w.1 g : P) : M) = ρ g m - m := fun g => hm g
    have hmP : m ∈ P := by
      obtain ⟨q, hq⟩ : ∃ q : P, ρP s q - q = w.1 s := by
        have hinjP : Function.Injective fun q : P => ρP s q - q := by
          intro a b hab
          apply Subtype.ext
          apply hsb.1
          have := congrArg Subtype.val hab
          simpa [hρP] using this
        exact (Finite.injective_iff_surjective.1 hinjP) (w.1 s)
      have h1 : ρ s (q : M) - q = ρ s m - m := by
        have := congrArg Subtype.val hq
        simp only [AddSubgroupClass.coe_sub, hρP] at this
        rw [this, hm' s]
      have := hsb.1 h1
      rw [← this]
      exact q.2
    rw [Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    refine ⟨⟨m, hmP⟩, fun g => ?_⟩
    apply Subtype.ext
    rw [hm' g]
    rfl
  refine ⟨LinearMap.range φ, ?_, ?_⟩
  · calc Nat.card P ≤ Nat.card (H1 ρP) := hle
      _ = Nat.card (LinearMap.range φ) := Nat.card_congr (LinearEquiv.ofInjective φ hinj).toEquiv
  · intro z hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hz
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
    simp only [φ, mapH1, Submodule.mapQ_apply] at hw
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hw
    obtain ⟨y, hy⟩ := hw
    refine ⟨-y, fun h => ?_⟩
    have h1 := hy h
    have h2 : ((cocycles1MapOfEquivariant ρP ρ P.subtype hu heq w : Z1 ρ) : _ → M) h = (w.1 h : M) := rfl
    simp only [Submodule.coe_sub, Pi.sub_apply, h2] at h1
    have h3 : z.1 h - (ρ h (-y) - -y) = (w.1 h : M) := by
      rw [map_neg]
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel
    rw [h3]
    exact (w.1 h).2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem card_one_of {R N : Type} [Ring R] [AddCommGroup N] [Module R N] (P : Submodule R N)
    (h : ∀ x ∈ P, x = 0) : Nat.card P = 1 := by
  haveI : Subsingleton P := ⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩

theorem UpperTheory.V.Ws.Bl.gwIneq :
    GlobalFiniteness → GreenbergWiles → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), 0 < r → l ≠ 2 → ContainsAbove S l → ContAction ρ →
          ∀ c : G ℚ Ω, IsCC c → (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ (v0 : S) (s : G ℚ Ω), s ∈ Dec (F := ℚ) (Av v0) → cycZ ℚ Ω l s = 1 → (Function.Bijective fun x => ρ (toGS Ω _ s) x - x) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → Nat.card (H0 (ρ.comp (locFam S Av v))) ≤ Nat.card (L v)) →
          Nat.card (L v0) ≤ Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := by
  intro hGF hGW Ω _ _ _ l _ r M _ _ _ _ _ S ρ hr hl2 hS hρ c hc hcneg Av hAv v0 s hsD hsz hsbij L hL
  have hcop : Nat.Coprime 2 (l ^ r) :=
    Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two (Fact.out)).mpr (Ne.symm hl2))
  have hinv : ∀ m : M, m = -m → m = 0 := by
    intro m hm
    set u := ZMod.unitOfCoprime 2 hcop
    have hu : (u : ZMod (l ^ r)) = 2 := by simp [u]
    have h2 : (2 : ZMod (l ^ r)) • m = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hm]
      exact add_neg_cancel m
    calc m = ((u⁻¹ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • ((u : ZMod (l ^ r)) • m) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hu, h2, smul_zero]
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := r) hS
  have hcc : ∀ w : InfinitePlace ℚ, w.IsReal → IsCCAt w c := by
    intro w _
    obtain ⟨j, hj⟩ := hc
    exact ⟨j, hj, Subsingleton.elim _ _⟩
  have key := hGW ℚ Ω l r M S ρ hr hl2 hS hρ μ hμ Av hAv (fun _ => c) hcc L
  have hμs : μ (toGS Ω _ s) = 1 := by
    have h := congrArg (fun f => f s) hμ
    simp only [MonoidHom.comp_apply] at h
    rw [h]
    simp [cycMod, hsz]
  have htw : Nat.card (H0 (twDual μ ρ)) = 1 := by
    refine card_one_of _ (fun φ hφ => ?_)
    have hfix := (mem_riemannRochSpace_iff_regularAt_everywhere _ φ).mp hφ (toGS Ω _ s)
    change (φ : Module.Dual (ZMod (l ^ r)) M) = 0
    apply LinearMap.ext
    intro m
    obtain ⟨x, rfl⟩ := hsbij.2 m
    have hx : φ (ρ (toGS Ω _ s) x) = φ x := by
      have h := congrArg (fun ψ : TDual (ZMod (l ^ r)) M => ψ (ρ (toGS Ω _ s) x)) hfix
      simp only [twDual_apply, hμs, Units.val_one, one_mul] at h
      rw [← h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hsub : (φ : Module.Dual (ZMod (l ^ r)) M) (ρ (toGS Ω _ s) x - x) =
        (φ : Module.Dual (ZMod (l ^ r)) M) (ρ (toGS Ω _ s) x) - (φ : Module.Dual (ZMod (l ^ r)) M) x :=
      LinearMap.map_sub _ _ _
    show φ (ρ (toGS Ω _ s) x - x) = 0
    exact hsub.trans (by erw [hx]; exact sub_self _)
  have harch : archH0Card S ρ (fun _ => c) = 1 := by
    have h0 : InfinitePlace.nrComplexPlaces ℚ = 0 := by simp
    unfold archH0Card
    rw [h0, pow_zero, mul_one]
    refine Finset.prod_eq_one (fun w _ => ?_)
    haveI : Subsingleton {m : M // ρ (toGS Ω _ c) m = m} :=
      ⟨fun a b => Subtype.ext (by
        have ha := hinv a.1 (by rw [← hcneg a.1, a.2])
        have hb := hinv b.1 (by rw [← hcneg b.1, b.2])
        rw [ha, hb])⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨0, map_zero _⟩⟩⟩
  have hv0 : Nat.card (H0 (ρ.comp (locFam S Av v0))) = 1 := by
    refine card_one_of _ (fun m hm => ?_)
    have hfix := (mem_riemannRochSpace_iff_regularAt_everywhere _ m).mp hm ⟨s, hsD⟩
    have hfix' : ρ (toGS Ω _ s) m = m := hfix
    apply hsbij.1
    show ρ (toGS Ω _ s) m - m = ρ (toGS Ω _ s) 0 - 0
    rw [hfix', sub_self, map_zero, sub_self]
  classical
  rw [htw, harch, mul_one, mul_one] at key
  obtain ⟨-, hH1, -, -⟩ := hGF ℚ Ω l r M S ρ hr hS hρ
  have hSelpos : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have hH0pos : ∀ v, 0 < Nat.card (H0 (ρ.comp (locFam S Av v))) := fun v => Nat.card_pos
  have hP := Finset.mul_prod_erase Finset.univ (fun v => Nat.card (H0 (ρ.comp (locFam S Av v)))) (Finset.mem_univ v0)
  have hQ := Finset.mul_prod_erase Finset.univ (fun v => Nat.card (L v)) (Finset.mem_univ v0)
  simp only at hP hQ
  rw [hv0, one_mul] at hP
  set P' := ∏ v ∈ Finset.univ.erase v0, Nat.card (H0 (ρ.comp (locFam S Av v)))
  set Q' := ∏ v ∈ Finset.univ.erase v0, Nat.card (L v)
  have hP'pos : 0 < P' := Finset.prod_pos (fun v _ => hH0pos v)
  have hPQ : P' ≤ Q' := Finset.prod_le_prod₀ (fun v _ => Nat.zero_le _)
    (fun v hv => hL v (Finset.ne_of_mem_erase hv))
  rw [← hP, ← hQ] at key
  set a := Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L)
  set b := Nat.card (Sel (twDual μ ρ) (locFam S Av) _ (perpCond μ ρ (locFam S Av) _ L))
  set h0 := Nat.card (H0 ρ)
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · rw [hb, zero_mul, zero_mul] at key
      exact absurd key (Nat.mul_pos hSelpos hP'pos).ne'
    · exact hb
  have hh0 : 0 < h0 := Nat.card_pos
  have h1 : Nat.card (L v0) * Q' ≤ a * P' := by
    rw [key]
    calc Nat.card (L v0) * Q' ≤ (b * h0) * (Nat.card (L v0) * Q') :=
          Nat.le_mul_of_pos_left _ (Nat.mul_pos hbpos hh0)
      _ = _ := rfl
  have h2 : Nat.card (L v0) * P' ≤ a * P' :=
    le_trans (Nat.mul_le_mul_left _ hPQ) h1
  exact Nat.le_of_mul_le_mul_right h2 hP'pos
end
