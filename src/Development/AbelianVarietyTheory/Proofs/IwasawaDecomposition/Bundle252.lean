module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.LatticeGeometry.InstAddCommSemigroupWt
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle246
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import ReciprocityTheory.DualLattices.Bundle010
public import ReciprocityTheory.DualLattices.Bundle004
import ReciprocityTheory.DualLattices.Bundle005

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem intTrace_modEq (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K))
    (hvI : IsCoprime v.asIdeal I) (hpI : Ideal.span {(p : 𝓞 K)} = v.asIdeal * I)
    (hnorm : Ideal.absNorm v.asIdeal = p) (x : 𝓞 K) (b : ℤ) (hxv : x - (b : 𝓞 K) ∈ v.asIdeal) (hxI : x ∈ I) :
    ∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + p * m := by
  classical
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPm : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  letI := Ideal.Quotient.field P
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) P = v.asIdeal * I := by
    rw [hPdef, Ideal.map_span, Set.image_singleton, map_natCast]; exact hpI
  have hPv : P ≤ v.asIdeal.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact Ideal.mul_le_left (I := v.asIdeal) (J := I)
  have hPI : P ≤ I.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact Ideal.mul_le_right (I := v.asIdeal) (J := I)
  letI : Algebra (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap hPv
  letI : Algebra (ℤ ⧸ P) (𝓞 K ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap hPI
  haveI : IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ I) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ I) := Module.Finite.of_restrictScalars_finite ℤ _ _
  let e : (𝓞 K ⧸ Ideal.map (algebraMap ℤ (𝓞 K)) P) ≃ₐ[ℤ ⧸ P] ((𝓞 K ⧸ v.asIdeal) × (𝓞 K ⧸ I)) :=
    { __ := (Ideal.quotEquivOfEq hmap).trans (Ideal.quotientMulEquivQuotientProd v.asIdeal I hvI),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have he : e (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk v.asIdeal x, Ideal.Quotient.mk I x) := rfl
  have hx2 : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxI
  have hx1 : Ideal.Quotient.mk v.asIdeal x = algebraMap (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk P b) := by
    rw [Ideal.Quotient.eq.mpr hxv]
    show _ = Ideal.Quotient.mk v.asIdeal (algebraMap ℤ (𝓞 K) b)
    rw [algebraMap_int_eq, eq_intCast]
  have hcardP : Nat.card (ℤ ⧸ P) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hcardv : Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
    rw [← hnorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfr : Module.finrank (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ℤ ⧸ P) (V := 𝓞 K ⧸ v.asIdeal)
    rw [hcardP, hcardv] at h
    exact (Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm))
  have key : Ideal.Quotient.mk P (Algebra.intTrace ℤ (𝓞 K) x) = Ideal.Quotient.mk P b := by
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv e, he,
      Algebra.trace_prod_apply, hx2, map_zero, add_zero, hx1, Algebra.trace_algebraMap, hfr, one_smul]
  rw [Ideal.Quotient.eq, hPdef, Ideal.mem_span_singleton] at key
  obtain ⟨m, hm⟩ := key
  exact ⟨m, by linear_combination hm⟩

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem integral_of_mul (w : HeightOneSpectrum (𝓞 K)) (n z s y : 𝓞 K) (hn : n ≠ 0) (hs : s ∉ w.asIdeal)
    (h : z * s = n * y) :
    algebraMap K (Af K) ((z : K) / (n : K)) w ∈ w.adicCompletionIntegers K := by
  have hs0 : (s : K) ≠ 0 := by
    intro h0; apply hs; rw [show s = 0 from by exact_mod_cast h0]; exact zero_mem _
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn
  have hq : (z : K) / (n : K) = (y : K) / (s : K) := by
    rw [div_eq_div_iff hn0 hs0]
    have := congrArg (fun t : 𝓞 K => (t : K)) h
    simp only [map_mul] at this
    push_cast at this
    linear_combination this
  rw [hq, HeightOneSpectrum.mem_adicCompletionIntegers]
  have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w ((y : K) / (s : K))
  erw [e]
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, div_one]
  exact HeightOneSpectrum.intValuation_le_one w y

theorem exists_cofactor (p : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) :
    ∃ I : Ideal (𝓞 K), IsCoprime v.asIdeal I ∧ Ideal.span {(p : 𝓞 K)} = v.asIdeal * I := by
  have hpv : (p : 𝓞 K) ∈ v.asIdeal := by
    have := Ideal.absNorm_mem v.asIdeal
    rwa [hnorm] at this
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hpv)
  refine ⟨I, ?_, hI⟩
  have hpr := (Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime
  rw [Ideal.isCoprime_iff_gcd, hpr.irreducible.gcd_eq_one_iff]
  rintro ⟨J, rfl⟩
  apply hsq
  have : Ideal.span {(p : 𝓞 K)} ≤ v.asIdeal ^ 2 := by
    rw [hI, pow_two, ← mul_assoc]; exact Ideal.mul_le_left (I := v.asIdeal * v.asIdeal) (J := J)
  exact this (Ideal.mem_span_singleton_self _)

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem fin_part (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) (α : Af K)
    (hα1 : evalV K v α = 1) (hα0 : ∀ w, w ≠ v → evalV K w α = 0) (a : 𝓞 K) (b : ℤ)
    (hab : a - (b : 𝓞 K) ∈ v.asIdeal) :
    ∃ x : 𝓞 K, (∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + p * m) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (α * algebraMap K (Af K) ((a : K) / (p : K)) -
        algebraMap K (Af K) ((x : K) / (p : K))) w ∈ w.adicCompletionIntegers K := by
  obtain ⟨I, hvI, hpI⟩ := exists_cofactor p v hnorm hsq
  obtain ⟨u, hu, t, ht, hut⟩ := Ideal.isCoprime_iff_exists.mp hvI
  have htv : t ∉ v.asIdeal := fun h =>
    v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hut ▸ add_mem hu h))
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmemp : ∀ z ∈ v.asIdeal * I, ∃ y, z = (p : 𝓞 K) * y := fun z hz => by
    rw [← hpI, Ideal.mem_span_singleton'] at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, by rw [← hy, mul_comm]⟩
  have hxv : (b : 𝓞 K) * t - b ∈ v.asIdeal := by
    have e : (b : 𝓞 K) * t - b = -((b : 𝓞 K) * u) := by linear_combination (b : 𝓞 K) * hut
    rw [e]; exact neg_mem (Ideal.mul_mem_left _ _ hu)
  refine ⟨b * t, intTrace_modEq p hp v I hvI hpI hnorm _ b hxv (Ideal.mul_mem_left _ _ ht), fun w => ?_⟩
  have hcomp : (α * algebraMap K (Af K) ((a : K) / (p : K)) - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K))) w =
      α w * algebraMap K (Af K) ((a : K) / (p : K)) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) w := rfl
  rw [hcomp]
  by_cases hw : w = v
  · subst hw
    have h1 : α w = 1 := hα1
    have hsub : algebraMap K (Af K) ((a : K) / (p : K)) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) w =
        algebraMap K (Af K) (((a - (b : 𝓞 K) * t : 𝓞 K) : K) / ((p : 𝓞 K) : K)) w := by
      rw [show (((a - (b : 𝓞 K) * t : 𝓞 K) : K) / ((p : 𝓞 K) : K)) =
        (a : K) / (p : K) - ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) by push_cast; ring, map_sub]
      rfl
    rw [h1, one_mul, hsub]
    have hmem : (a - (b : 𝓞 K) * t) * t ∈ w.asIdeal * I := by
      refine Ideal.mul_mem_mul ?_ ht
      have e : a - (b : 𝓞 K) * t = (a - b) - ((b : 𝓞 K) * t - b) := by ring
      rw [e]; exact sub_mem hab hxv
    obtain ⟨y, hy⟩ := hmemp _ hmem
    exact integral_of_mul w _ _ t y hp0 htv hy
  · have h0 : α w = 0 := hα0 w hw
    rw [h0, zero_mul, zero_sub]
    refine neg_mem ?_
    obtain ⟨s, hsv, hsw⟩ : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := by
      by_contra hc
      push_neg at hc
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)
    obtain ⟨y, hy⟩ := hmemp _ (Ideal.mul_mem_mul hsv (Ideal.mul_mem_left _ (b : 𝓞 K) ht))
    have := integral_of_mul w (p : 𝓞 K) ((b : 𝓞 K) * t) s y hp0 hsw (by rw [mul_comm]; exact hy)
    simpa using this

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

theorem stdChar_placeIdem_div : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  intro D ψ hψ p hp v hnorm hsq ε hε a b hab
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  obtain ⟨x, ⟨m, hm⟩, hint⟩ := fin_part p hp v hnorm hsq α hα1 hα0 a b hab
  have hsplit : pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F)) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F))) +
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F))) := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * _ = 0 + 0
      rw [zero_mul, add_zero]
    · show α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) =
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)) +
        (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
          algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)))
      rw [add_sub_cancel]
  have htr : ∀ r : 𝓞 D.host.F, Algebra.trace ℚ D.host.F (r : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) r : ℤ) : ℚ) :=
    fun r => (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) r).symm
  have h1 : ψ (pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)))) = 1 := by
    refine GlobalTheory.IntDense.mem_of_isClosed D.host.F (C := {y | ψ (pairA D.host.F 0 y) = 1})
      (isClosed_eq (hψ.1.1.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const)
      (fun r => ?_) _ hint
    show ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (r : D.host.F))) = 1
    rw [GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ]
  have hq : Algebra.trace ℚ D.host.F ((x : D.host.F) / (p : D.host.F)) = ((b : ℚ) + p * m) / p := by
    have e : (x : D.host.F) / (p : D.host.F) = ((p : ℚ)⁻¹) • (x : D.host.F) := by
      rw [Algebra.smul_def, map_inv₀, map_natCast, div_eq_inv_mul]
    rw [e, map_smul, htr, hm, smul_eq_mul]
    push_cast
    ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hq, show 2 * ↑Real.pi * Complex.I * ((((b : ℚ) + p * m) / p : ℚ) : ℂ) =
      2 * Real.pi * Complex.I * b / (p : ℂ) + m * (2 * Real.pi * Complex.I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end GlobalTheory.StdCharDegOne
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RecordWeightVec

theorem aPl_eq_aPlusQ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) τ n : ℚ) = DV.aPlusQ D ((i : ℕ) + 1) τ n := by
  have hi := i.2
  have h1 : DV.sigPar D τ n = Formalism.L2.NTheta.lamAt (D.hc τ) n := by
    unfold DV.sigPar Formalism.L2.NTheta.lamAt
    rfl
  have h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i := by
    unfold DV.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [GlobalTheory.CoefMapRecord.aPl_cast D i τ n hn, DV.aPlusQ_eq, h1, h2]
  push_cast
  ring

theorem aMi_eq_aMinusQ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (q n c : ℕ) (hq : i + 1 + q = D.R.m)
    (hn : n + c + 1 = q) : (aMi D i (D.R.k + i) q τ n : ℚ) = DV.aMinusQ D ((i : ℕ) + 1) τ c := by
  have hi := i.2
  have h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i := by
    unfold DV.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [GlobalTheory.CoefMapRecord.aMi_cast D i τ q n c hq hn, DV.aMinusQ, dite_eq_left (by omega), h2]
  ring

theorem wtOf_kapTop : ∀ D : D7, DV.KapDef D → ∀ i : Fin D.R.m,
    (kapTop D i).n = D.R.nV ∧ Formalism.L2.Geo.wtOf (kapTop D i) = DV.kapW D ((i : ℕ) + 1) := by
  intro D hK i
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hs : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ =>
    D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by
    simp only [Ranks.sigW]; omega
  have hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m := by
    simp only [Ranks.sigW]; omega
  refine ⟨rfl, Formalism.L2.Geo.wtOf_eq_kapW _ (fun τ a => ?_) (fun τ c => ?_) rfl⟩
  · have h := (hK _ (inR i).1 (inR i).2 τ).1 a
    have h' := aPl_eq_aPlusQ D i τ a (hp ▸ a.2)
    have he := (kapIs_kapTop D i τ).1 a
    rw [he, hs τ]
    rw [← h, ← hp] at h'
    exact_mod_cast h'
  · have h := (hK _ (inR i).1 (inR i).2 τ).2 (Fin.rev c)
    have hc := c.2
    have h' := aMi_eq_aMinusQ D i τ _ c (Fin.rev c) hq (by rw [Fin.val_rev]; omega)
    have he := (kapIs_kapTop D i τ).2.1 c
    rw [he, hs τ]
    rw [← hp, ← neg_neg (DV.aMinusQ _ _ _ _), ← h] at h'
    exact_mod_cast h'

end GlobalTheory.RecordWeightVec
end

section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HighestPolynomial

open MvPolynomial ReciprocityTheory.PGsh

theorem differentiable_rowSubst {k : ℕ} {κ : Type} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (P : MvPolynomial (Fin k × κ) ℂ) (ψ : MvPolynomial (Fin k × κ) ℂ →ₗ[ℂ] F) :
    Differentiable ℂ fun g : Fin k → Fin k → ℂ => ψ (rowSubst (Matrix.of g) P) := by
  induction P using MvPolynomial.induction_on generalizing ψ with
  | C c => simp only [rowSubst_C]; exact differentiable_const _
  | add p q hp hq => simp only [map_add (f := _)]; exact (hp ψ).add (hq ψ)
  | mul_X p s hp =>
    have h : (fun g : Fin k → Fin k → ℂ => ψ (rowSubst (Matrix.of g) (p * X s))) =
        fun g : Fin k → Fin k → ℂ => ∑ l, g l s.1 •
          (ψ ∘ₗ LinearMap.mulRight ℂ (X (l, s.2))) (rowSubst (Matrix.of g) p) := by
      funext g

      rw [map_mul, rowSubst_X, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [LinearMap.comp_apply, LinearMap.mulRight_apply, ← map_smul, MvPolynomial.smul_eq_C_mul, Matrix.of_apply]
      congr 1
      ring
    rw [h]
    refine Differentiable.fun_sum fun l _ => Differentiable.smul ?_ (hp _)
    fun_prop

theorem totalDegree_rowSubst_le {k : ℕ} {κ : Type} (g : Matrix (Fin k) (Fin k) ℂ)
    (P : MvPolynomial (Fin k × κ) ℂ) : (rowSubst g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P

theorem fischer_conj {k : ℕ} {κ : Type} (P Q : MvPolynomial (Fin k × κ) ℂ) :
    starRingEnd ℂ (fischer P Q) = fischer Q P := by
  classical

  rw [fischer_eq_sum P Q (P.support ∪ Q.support) Finset.subset_union_left,
  fischer_eq_sum Q P (P.support ∪ Q.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [fw, map_mul, Complex.conj_conj, map_natCast]
  ring

theorem fischer_self_re_nonneg {k : ℕ} {κ : Type} (P : MvPolynomial (Fin k × κ) ℂ) : 0 ≤ (fischer P P).re := by
  rw [fischer_eq_sum P P P.support subset_rfl, Complex.re_sum]
  refine Finset.sum_nonneg fun A _ => ?_
  rw [Complex.mul_conj, fw, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

@[reducible] def fischerCore {k : ℕ} {κ : Type} (S : Submodule ℂ (MvPolynomial (Fin k × κ) ℂ)) :
    InnerProductSpace.Core ℂ S where
  inner x y := fischer y.1 x.1
  conj_inner_symm x y := fischer_conj _ _
  re_inner_nonneg x := fischer_self_re_nonneg _
  add_left x y z := fischer_add_right _ _ _
  smul_left x y r := fischer_smul_right _ _ _
  definite x hx := by
    by_contra h
    exact fischer_self_ne_zero x.1 (fun h' => h (Subtype.ext h')) hx

theorem mem_UJset_allPos {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : gᴴ * g = 1 := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  have h : gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) := hg
  rwa [hJ, Matrix.mul_one] at h

theorem exists_intertwiner_of_embedding (k : ℕ) (κ : Type) (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (j : E →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ) (hj : Function.Injective j)
    (hin : ∀ x y : E, inner ℂ x y = fischer (j y) (j x))
    (hst : ∀ g x, ∃ y, j y = rowSubst g (j x)) (D : E)
    (hτ : IsURepOn (UJset (allPos k)) τ) (hK : IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤) (hD : j D ≠ 0)
    (hu : ∀ g, IsUpperUnitri g → rowSubst g (j D) = j D)
    (hd : ∀ d : Fin k → ℂ, rowSubst (Matrix.diagonal d) (j D) = (∏ a, d a ^ ν a) • j D) :
    ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ,
      (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = rowSubst g (L u)) ∧ ∃ v, L v = j D := by
  obtain ⟨r, hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hrj : ∀ x, r (j x) = x := fun x => LinearMap.congr_fun hr x
  let π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E) := fun g =>
    LinearMap.toContinuousLinearMap (r ∘ₗ (rowSubst g).toLinearMap ∘ₗ j)
  have hπ : ∀ g x, π g x = r (rowSubst g (j x)) := fun g x => rfl
  have hjπ : ∀ g x, j (π g x) = rowSubst g (j x) := by
    intro g x
    obtain ⟨y, hy⟩ := hst g x
    rw [hπ, ← hy, hrj]
  have hdiff : ∀ w : E, Differentiable ℂ fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w := fun w =>
    differentiable_rowSubst (j w) r
  have hrep : IsURepOn (UJset (allPos k)) π := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · ext x
      apply hj
      rw [hjπ, rowSubst_one]
      rfl
    · intro a _ b _
      ext x
      apply hj
      change _ = j (π a (π b x))
      rw [hjπ, hjπ, hjπ, rowSubst_mul]
    · intro g hg v
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ v, hin, hin, hjπ, fischer_rowSubst,
        rowSubst_mul, mem_UJset_allPos hg, rowSubst_one]
    · intro v
      exact (hdiff v).continuous.continuousOn
  obtain ⟨L, hL, v, hv⟩ := GlobalTheory.T.exists_intertwiner_with_highestWeight_vector_in_range k (fun a => (ν a : ℝ)) H τ E π D hτ hK hrep (fun w => hdiff w _)
    (fun h => hD (by rw [h, map_zero]))
    (by
      intro a b hab s
      apply hj
      rw [hjπ]
      refine hu _ ⟨fun i => ?_, fun i l hl => ?_⟩
      · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
        rintro ⟨h1, h2⟩
        exact hab.ne (h1.trans h2.symm)
      · rw [Matrix.add_apply, Matrix.one_apply_ne hl.ne', Matrix.single_apply_of_ne, add_zero]
        rintro ⟨h1, h2⟩
        subst h1 h2
        exact lt_asymm hab hl)
    (by
      intro θ _
      apply hj
      rw [hjπ, hd, map_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← Complex.exp_nat_mul, mul_assoc])
  exact ⟨j ∘ₗ L, fun g hg u => by rw [LinearMap.comp_apply, hL g hg, hjπ]; rfl, v, by rw [LinearMap.comp_apply, hv]⟩

theorem exists_intertwiner : ∀ (k : ℕ) (κ : Type) [Fintype κ] (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (Δ : MvPolynomial (Fin k × κ) ℂ), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤ → Δ ≠ 0 → (∀ g, ReciprocityTheory.PGsh.IsUpperUnitri g → ReciprocityTheory.PGsh.rowSubst g Δ = Δ) → (∀ d : Fin k → ℂ, ReciprocityTheory.PGsh.rowSubst (Matrix.diagonal d) Δ = (∏ a, d a ^ ν a) • Δ) → ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = ReciprocityTheory.PGsh.rowSubst g (L u)) ∧ ∃ v, L v = Δ := by
  intro k κ _ ν H _ _ _ τ Δ hτ hK hΔ hu hd
  let S : Submodule ℂ (MvPolynomial (Fin k × κ) ℂ) := restrictTotalDegree (Fin k × κ) ℂ Δ.totalDegree
  have hfin : FiniteDimensional ℂ S := inferInstanceAs (Module.Finite ℂ (restrictTotalDegree (Fin k × κ) ℂ Δ.totalDegree))
  letI : InnerProductSpace.Core ℂ S := fischerCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  exact exists_intertwiner_of_embedding k κ ν H τ S S.subtype S.injective_subtype (fun _ _ => rfl)
    (fun g x => ⟨⟨rowSubst g x.1, (mem_restrictTotalDegree _ _ _).mpr
      ((totalDegree_rowSubst_le g x.1).trans ((mem_restrictTotalDegree _ _ _).mp x.2))⟩, rfl⟩)
    ⟨Δ, (mem_restrictTotalDegree _ _ _).mpr le_rfl⟩ hτ hK hΔ hu hd

end GlobalTheory.HighestPolynomial

end
end
