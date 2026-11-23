module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.SplitCharY
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsSqEqNegOfDiscr
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.StatementLoc
import Formalism.GaloisCohomology.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem absorb (A N t e : ℝ) (k : ℕ) (hA : 0 ≤ A) (hk : A ≤ 16 ^ k) (hN : 16 ≤ N) (he : 0 ≤ e) (het : e ≤ t)
    (ht : 1 ≤ t) : A * N * N ^ 18 * e ^ 7 ≤ (N * t) ^ (k + 19) := by
  have h0 : 0 ≤ N := by linarith
  have h1 : A ≤ N ^ k := hk.trans (pow_le_pow_left₀ (by norm_num) hN k)
  have h2 : e ^ 7 ≤ t ^ (k + 19) := (pow_le_pow_left₀ he het 7).trans (pow_le_pow_right₀ ht (by omega))
  calc A * N * N ^ 18 * e ^ 7 ≤ N ^ k * N * N ^ 18 * t ^ (k + 19) := by gcongr
    _ = (N * t) ^ (k + 19) := by ring
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

open Polynomial in
private theorem splitting_field_iso_quadratic (p : ℕ) (hp : 0 < p) (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (δ : K) (hδ : δ ^ 2 = -(p : K)) (L : Type) [Field L] [NumberField L]
    [hL : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : Nonempty (L ≃ₐ[ℚ] K) := by
  classical
  set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf
  have hsK : (f.map (algebraMap ℚ K)).Splits := by
    have hfac : f.map (algebraMap ℚ K) = (X + C δ) * (X + C (-δ)) := by
      have hpK : (p : K) = -(δ ^ 2) := by rw [hδ]; ring
      rw [hf, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        map_natCast, hpK]
      simp only [map_neg, map_pow]
      ring
    rw [hfac]
    exact (Splits.X_add_C _).mul (Splits.X_add_C _)
  let φ := IsSplittingField.lift L f hsK
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hLK : Module.finrank ℚ L ≤ 2 :=
    hK ▸ LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hinj
  have hL1 : Module.finrank ℚ L ≠ 1 := by
    intro h1
    have hbt := Subalgebra.bot_eq_top_of_finrank_eq_one (F := ℚ) (E := L) h1
    have hsL := IsSplittingField.splits L f
    have hdeg : (f.map (algebraMap ℚ L)).degree ≠ 0 := by
      rw [Polynomial.degree_map, hf, Polynomial.degree_X_pow_add_C (by norm_num)]
      norm_num
    obtain ⟨r, hr⟩ := hsL.exists_eval_eq_zero hdeg
    have hrm : r ∈ (⊥ : Subalgebra ℚ L) := hbt ▸ Algebra.mem_top
    obtain ⟨q, rfl⟩ := Algebra.mem_bot.mp hrm
    have hq : algebraMap ℚ L (q ^ 2 + p) = 0 := by
      simpa [hf, Polynomial.eval_map] using hr
    have hq0 : q ^ 2 + (p : ℚ) = 0 := (algebraMap ℚ L).injective (by rw [hq, map_zero])
    have hpq : (0 : ℚ) < q ^ 2 + p := by
      have : (0 : ℚ) < p := by exact_mod_cast hp
      positivity
    linarith
  have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have h2 : Module.finrank ℚ L = 2 := by omega
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (h2.trans hK.symm)).1 hinj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem UpperTheory.V.HV.kstar :
    ∀ p : ℕ, p.Prime → p % 4 = 3 → discr (Kstar p) = -(p : ℤ) ∧ IsTotallyComplex (Kstar p) ∧ Module.finrank ℚ (Kstar p) = 2 ∧ ∃ s : Kstar p, s ^ 2 = -(p : Kstar p) := by
  intro p hp h3
  obtain ⟨K, _, _, hK2, hd⟩ := KStar.Consta.exists_quadField hp h3
  obtain ⟨⟨δ, hδ⟩, -⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hK2 hp.ne_zero hd
  haveI : Polynomial.IsSplittingField ℚ (Kstar p) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
    have h := Polynomial.IsSplittingField.splittingField (K := ℚ) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ))
    have h' : Polynomial.IsSplittingField ℚ (Polynomial.SplittingField (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)))
        (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
      convert h
    exact h'
  obtain ⟨e⟩ := splitting_field_iso_quadratic p hp.pos K hK2 δ hδ (Kstar p)
  have hfr : Module.finrank ℚ (Kstar p) = 2 := e.toLinearEquiv.finrank_eq.trans hK2
  have hdisc : discr (Kstar p) = -(p : ℤ) := by
    rw [NumberField.discr_eq_discr_of_algEquiv (Kstar p) e, hd]
  obtain ⟨hs, htc⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hfr hp.ne_zero hdisc
  exact ⟨hdisc, htc, hfr, hs⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem card_le_level (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N]
    (T : Finset (DirichletCharacter O N)) : T.card ≤ N := by
  classical
  have hli := linearIndependent_monoidHom (ZMod N) O
  let g : T → (ZMod N →* O) := fun χ => (χ.1 : MulChar (ZMod N) O).toMonoidHom
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply MulChar.ext'
    intro y
    have := DFunLike.congr_fun h y
    simpa [g] using this
  have hT := (hli.comp g hg).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card, Fintype.card_coe] at hT
  exact hT

theorem UpperTheory.V.HV.xCard :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N], (∀ T : Finset (DirichletCharacter O N), T.card ≤ N) ∧
      ∀ (M : ℕ), 0 < M → ∀ T : Finset (DirichletCharacter O N), (∀ ψ ∈ T, ψ.conductor ∣ M) → T.card ≤ M := by
  intro O _ _ N _
  refine ⟨card_le_level O N, ?_⟩
  intro M hM T hT
  classical
  set g := Nat.gcd M N with hgdef
  have hgN : g ∣ N := Nat.gcd_dvd_right M N
  have hgM : g ≤ M := Nat.le_of_dvd hM (Nat.gcd_dvd_left M N)
  haveI : NeZero g := ⟨(Nat.gcd_pos_of_pos_left N hM).ne'⟩
  have hex : ∀ ψ ∈ T, ∃ ψ₀ : DirichletCharacter O g, ψ = DirichletCharacter.changeLevel hgN ψ₀ := by
    intro ψ hψ
    obtain ⟨hc, χ₀, hχ₀⟩ := ψ.factorsThrough_conductor
    have hcg : ψ.conductor ∣ g := Nat.dvd_gcd (hT ψ hψ) hc
    refine ⟨DirichletCharacter.changeLevel hcg χ₀, ?_⟩
    rw [← DirichletCharacter.changeLevel_trans]
    exact hχ₀
  let f : DirichletCharacter O N → DirichletCharacter O g := fun ψ =>
    if h : ∃ ψ₀ : DirichletCharacter O g, ψ = DirichletCharacter.changeLevel hgN ψ₀ then h.choose else 1
  have hf : ∀ ψ ∈ T, ψ = DirichletCharacter.changeLevel hgN (f ψ) := by
    intro ψ hψ
    have h := hex ψ hψ
    simp only [f, dif_pos h]
    exact h.choose_spec
  have hinj : Set.InjOn f T := by
    intro a ha b hb hab
    rw [hf a ha, hf b hb, hab]
  calc T.card = (T.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ g := card_le_level O g _
    _ ≤ M := hgM
end
