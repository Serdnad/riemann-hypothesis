module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle881
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle887
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle888
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle859
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle869
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle860
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle867
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle496
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumOneAddNormRpowNegLeEuclidean
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle886
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle876

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

open GlobalTheory.StdAtPrime

namespace GlobalTheory.MoveDenom



theorem denomAt_of_move : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ l : ℕ, l.Prime → ∀ s : GA D V, ∃ c : ℕ, ∀ z : GA D V, OneAt V l z → ∀ (γ h : GA D V) (γ' : GL (Fin V.rank) D.host.E) (k : Bridge.Gf V) (bad : ℕ), GlobalTheory.Member.IsRat V γ γ' → l ∣ bad → SplitOffBad V bad h → Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank → Bridge.hLat V k⁻¹ = Formalism.L2.Pj.stdLat D.host.E V.rank → fin V (s * z) = fin V γ * fin V h * k → DenomAt l c γ' := by
  intro D V hstd l hl s
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  set M := Matrix.GeneralLinearGroup.map (n := Fin V.rank) ι.toRingHom with hM
  obtain ⟨c1, hc1⟩ := GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over l hl V.rank (M (fin V s).1).1
  obtain ⟨c2, hc2⟩ := GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over l hl V.rank (M (fin V s).1)⁻¹.1
  refine ⟨max c1 c2, ?_⟩
  intro z hz γ h γ' k bad hrat hlb hsob hk hk' heq
  set C : FiniteAdeleRing (𝓞 D.host.E) D.host.E := ((l ^ max c1 c2 : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) with hC
  have bs : Bnd l (C • (M (fin V s).1).1) := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hc1 _ (le_max_left _ _) Q hQ i j
  have bs' : Bnd l (C • (M (fin V s).1)⁻¹.1) := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hc2 _ (le_max_right _ _) Q hQ i j
  have ez := GlobalTheory.T.finiteMatrix_apply_eq_one_at_places_over_of_oneAt D ι h1 h2 h3 V l z hz
  have bz : Bnd l (M (fin V z).1).1 := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [ez Q hQ i j]; exact one_entry_v_le_one _ Q i j
  have bz' : Bnd l (M (fin V z).1)⁻¹.1 := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [inv_eq_one_off _ _ Q (ez Q hQ) i j]; exact one_entry_v_le_one _ Q i j
  have bk' : Bnd l (M k.1)⁻¹.1 := bnd_inv_of_hLat_std D ι h1 h2 V hstd l k hk
  have bk : Bnd l (M k.1).1 := by
    have := bnd_inv_of_hLat_std D ι h1 h2 V hstd l k⁻¹ hk'
    rwa [Subgroup.coe_inv, map_inv, inv_inv] at this
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.T.placeIdempotent_components_conj_valuation D ι h1 h2 h4
  obtain ⟨-, e', P', he', hb', hs'⟩ := hsob
  have hp' : ∀ PP ∈ P', (l : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hpP
    obtain ⟨c, rfl⟩ := hlb
    exact hb' PP hPP (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpP)
  obtain ⟨S, hSf, hSp, hS0⟩ := GlobalTheory.T.idempotent_add_conj_support_finite_prime_to_p D ι hid hcj l e' P' he' hp'
  obtain ⟨bh, bh'⟩ := GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite l hl _ (M (fin V h).1) S hSf hSp fun Q hQ i j =>
    GlobalTheory.T.supported_adelic_point_eq_one_where_idempotent_vanishes D ι V e' h hs' Q (hS0 Q hQ) i j
  have eγ : fin V γ = fin V s * fin V z * k⁻¹ * (fin V h)⁻¹ := by
    have e1 : fin V (s * z) = fin V s * fin V z := map_mul _ _ _
    rw [e1] at heq
    rw [heq]; group
  have eMγ : M (fin V γ).1 = M (fin V s).1 * M (fin V z).1 * (M k.1)⁻¹ * (M (fin V h).1)⁻¹ := by
    rw [eγ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      map_mul, map_mul, map_mul, map_inv, map_inv]
  apply GlobalTheory.T.boundedDenom_rationalMatrix_of_finitePart D ι h1 V l (max c1 c2) γ γ' hrat
  · rw [eMγ, Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul]
    exact bnd_mul l _ _ _ (bnd_mul l _ _ _ (bnd_mul l _ _ _ bs bz) bk') bh'
  · rw [eMγ, _root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, inv_inv,
      Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_smul, ← Matrix.mul_smul, ← Matrix.mul_smul]
    exact bnd_mul l _ _ _ bh (bnd_mul l _ _ _ bk (bnd_mul l _ _ _ bz' bs'))

end GlobalTheory.MoveDenom
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellVanish

theorem eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (w : HeightOneSpectrum (𝓞 E)), w ∉ S →
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), IsUnifV E w (ϖ w : w.adicCompletion E) →
    ∀ (W : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, W (g * finGL E (m + 1) κ) = W g) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)), ¬ Antitone (l w) →
    ∀ p : GA E (m + 1), Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1 →
    W (p * GlobalTheory.CellDec.tl (m + 1) ϖ l) = 0 := by
  intro E _ _ _ m S J w hwS hψ ϖ hϖ W hWN hWK l hl p hp
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l with ht
  set D : GL (Fin (m + 1)) (w.adicCompletion E) := GlobalTheory.CellDec.compV E (m + 1) w t with hD
  have hDv : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ w ^ l w a : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    rw [hD, ht, GlobalTheory.CellDec.tl, GlobalTheory.CellDec.compV_finGL]
    refine Matrix.ext fun i j => ?_
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin (m + 1)) _ : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  set t' := t * (finGL E (m + 1) (locGL E (m + 1) w D))⁻¹ with ht'
  have ht'w : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t' = 1 := by
    change GlobalTheory.CellDec.compV E (m + 1) w t' = 1
    rw [ht', map_mul, map_inv, GlobalTheory.CellDec.compV_finGL_locGL_same, ← hD, mul_inv_cancel]
  have htt : t' * finGL E (m + 1) (locGL E (m + 1) w D) = t := by rw [ht', inv_mul_cancel_right]
  have hlev : ∀ k ∈ GlobalTheory.LFun.KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J := by
    intro k hk
    refine ⟨fun v => ?_, fun v hv i j => ?_⟩
    · by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL]; exact hk
      · rw [pLoc_locGL_of_ne hvw]; exact one_mem _
    · have hvw : v ≠ w := fun h => hwS (h ▸ hv)
      have h1 := congrArg (fun x : GL (Fin (m + 1)) (v.adicCompletion E) => (x : Matrix (Fin (m + 1)) (Fin (m + 1)) (v.adicCompletion E)) i j)
        (pLoc_locGL_of_ne hvw k)
      have h0 : ((locGL E (m + 1) w k).val - 1) i j v = 0 := by
        change pLoc E v (((locGL E (m + 1) w k).val - 1) i j) = 0
        rw [Matrix.sub_apply, map_sub]
        change (Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E (m + 1) w k)).val i j - _ = 0
        rw [h1]
        simp [Matrix.one_apply]
      rw [h0, map_zero]
      exact zero_le'
  let f : GL (Fin (m + 1)) (w.adicCompletion E) → ℂ := fun g => W (p * t' * finGL E (m + 1) (locGL E (m + 1) w g))
  have hfD : f D = W (p * t) := by
    simp only [f]
    rw [mul_assoc, htt]
  have hpt : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (p * t') = 1 := by
    rw [map_mul, hp, ht'w, mul_one]
  have hfN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ g,
      f (u * g) = GlobalTheory.JSW.psiLocChar w (GlobalTheory.Whittaker.superDiag u) * f g := by
    intro u hu g
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc (p * t'), GlobalTheory.JSW.commute_finGL_locGL w hpt, mul_assoc,
      hWN _ (GlobalTheory.JSW.CutTransfer.finGL_locGL_mem_NA' w hu), GlobalTheory.JSW.CutTransfer.psiN_finGL_locGL]
    rfl
  have hfK : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w (n := (m + 1)), f (g * k) = f g := by
    intro g k hk
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc]
    exact hWK _ (hlev k hk) _
  have h := GlobalTheory.WhitTorus.eq_zero_of_not_antitone_int E w (m + 1) (GlobalTheory.JSW.psiLocChar w) hψ f hfN hfK (ϖ w) hϖ (l w) hl D hDv
  rwa [hfD] at h

end GlobalTheory.CellVanish
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSParams

variable {E : Type} [Field E] [NumberField E]

theorem valued_natCast (v : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    Valued.v (N : v.adicCompletion E) = v.intValuation (N : 𝓞 E) := by
  have h := v.valuedAdicCompletion_eq_valuation (K := E) (N : 𝓞 E)
  rw [v.valuation_of_algebraMap] at h
  simpa using h

theorem exists_nat (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ (∀ v ∈ S, (N : 𝓞 E) ∈ v.asIdeal ^ k) ∧ ∀ v ∉ S, (N : 𝓞 E) ∉ v.asIdeal := by
  classical
  set q : HeightOneSpectrum (𝓞 E) → Ideal ℤ := fun w => Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal with hq
  have hq0 : ∀ w, q w ≠ ⊥ := fun w h => by
    have hm : ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∈ q w := by
      rw [hq, Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at hm
    exact w.ne_bot hm
  set 𝔞 : Ideal ℤ := ∏ w ∈ S, q w with h𝔞
  set n : ℤ := Submodule.IsPrincipal.generator 𝔞 with hn
  have hspan : Ideal.span {n} = 𝔞 := Ideal.span_singleton_generator 𝔞
  have h𝔞0 : 𝔞 ≠ ⊥ := by
    rw [h𝔞, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun w _ => hq0 w
  have hn0 : n ≠ 0 := fun h => h𝔞0 (by rw [← hspan, h, Ideal.span_singleton_eq_bot])
  set N₀ : ℕ := n.natAbs with hN₀
  have hN₀q : ∀ w ∈ S, (N₀ : ℤ) ∈ q w := fun w hw => by
    have h1 : (N₀ : ℤ) ∈ 𝔞 := by
      rw [← hspan, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    exact Ideal.prod_le_inf.trans (Finset.inf_le hw) h1
  refine ⟨N₀ ^ k, pow_pos (Int.natAbs_pos.2 hn0) k, fun v hv => ?_, fun v hv h => ?_⟩
  · have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := by
      have := hN₀q v hv
      rwa [hq, Ideal.mem_comap, map_natCast] at this
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow h1 k
  · rw [Nat.cast_pow] at h
    have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := v.isPrime.mem_of_pow_mem k h
    have h2 : (N₀ : ℤ) ∈ q v := by rwa [hq, Ideal.mem_comap, map_natCast]
    have h3 : n ∈ q v := by
      obtain ⟨c, hc⟩ := (Int.natAbs_dvd.2 (dvd_refl n) : (N₀ : ℤ) ∣ n)
      rw [hc]
      exact Ideal.mul_mem_right _ _ h2
    haveI hp : (q v).IsPrime := Ideal.comap_isPrime _ _
    have h4 : 𝔞 ≤ q v := by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact h3
    obtain ⟨w, hw, hle⟩ := (Ideal.IsPrime.prod_le hp).1 h4
    have hmax : (q w).IsMaximal := (Ideal.comap_isPrime _ w.asIdeal).isMaximal (hq0 w)
    have heq : q w = q v := hmax.eq_of_le hp.ne_top hle
    exact hv (hS w hw v heq.symm)

variable [_root_.NumberField.IsTotallyComplex E]

theorem mem_natLat_iff {N : ℕ} (hN : 0 < N) (z : Af E) :
    z ∈ GlobalTheory.RSJ.natLat E N ↔ ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (z v) ≤ Valued.v (N : v.adicCompletion E) := by
  constructor
  · rintro ⟨y, hy, rfl⟩ v
    change Valued.v ((N : v.adicCompletion E) * y v) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v))
  · intro h
    set c : Af E := algebraMap E (Af E) ((N : E)⁻¹) with hc
    have hcN : c * (N : Af E) = 1 := by
      rw [hc, ← map_natCast (algebraMap E (Af E)), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
    refine ⟨z * c, fun v => ?_, ?_⟩
    · have e : c v * (N : v.adicCompletion E) = 1 := congrArg (fun x : Af E => x v) hcN
      have e' : Valued.v (c v) * Valued.v (N : v.adicCompletion E) = 1 := by rw [← map_mul, e, map_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (z v * c v) ≤ 1
      rw [map_mul, ← e', mul_comm (Valued.v (c v))]
      exact mul_le_mul_of_nonneg_right (h v) zero_le'
    · calc z = z * (c * (N : Af E)) := by rw [hcN, mul_one]
        _ = (N : Af E) * (z * c) := by ring

end GlobalTheory.RSParams


open GlobalTheory.RSParams in
theorem GlobalTheory.RSParams.exists_level_nat_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  intro E _ _ _ m S hS V hV hw
  classical
  obtain ⟨J, hJS, -, hJV⟩ := GlobalTheory.RSLocalPart.exists_levelAt_subset S V hV hw
  set k : ℕ := ∑ v ∈ S, (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat with hk
  obtain ⟨N, hN, hNS, hNc⟩ := exists_nat S hS k
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (N : v.adicCompletion E) ≤ 1 := fun v => by
    rw [valued_natCast]; exact v.intValuation_le_one _
  have hvS : ∀ v ∈ S, Valued.v (N : v.adicCompletion E) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := fun v hv => by
    rw [valued_natCast]
    refine ((v.intValuation_le_pow_iff_mem _ k).2 (hNS v hv)).trans (WithZero.exp_le_exp.2 ?_)
    have h1 : FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E) ≤
        ((FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat ≤ k :=
      Finset.single_le_sum (f := fun v => (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat)
        (fun _ _ => Nat.zero_le _) hv
    omega
  have hvn : ∀ v ∉ S, Valued.v (N : v.adicCompletion E) = 1 := fun v hv => by
    rw [valued_natCast]
    exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hNc v hv ((v.intValuation_lt_one_iff_mem _).1 h))
  have he : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := fun w => by
    simp
  obtain ⟨ρ, hts, hcs, hcd, hr, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    ((GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds he)
  have hr' : ∀ u, ρ u ∈ Set.Icc (0 : ℝ) 1 := fun u => hr ⟨u, rfl⟩
  refine ⟨N, J, fun u => (ρ u : ℂ), hN, Complex.ofRealCLM.contDiff.comp hcd, hcs.comp_left Complex.ofReal_zero,
    (tsupport_comp_subset Complex.ofReal_zero ρ).trans hts, fun u => ⟨by simpa using (hr' u).1, by simp⟩,
    by simp [h1], hJS, hJV, fun z hz v => ?_, fun z hz v hv => ?_, fun z z' hzz hz hz' => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((mem_natLat_iff hN z).1 hz v).trans (hv1 v)
  · exact ((mem_natLat_iff hN z).1 hz v).trans (hvS v hv)
  · rw [mem_natLat_iff hN, mem_natLat_iff hN]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ S
    · rw [hzz v hv]
    · rw [hvn v hv]
      exact ⟨fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz' v hv),
        fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v hv)⟩
end
end

section

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global
  GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

namespace GlobalTheory.RSTheta

theorem summable_tsum_norm_le_of_le_shortest (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (N : ℕ) (hN : Module.finrank ℝ (Fin a → Cinf E) ≤ N) :
    ∃ (M : ℕ) (C : ℝ), ∀ (h : GA E a) (A : ℝ) (c : (Fin a → E) → ℂ), 0 ≤ A →
      (∀ ξ : Fin a → E, (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)) ∉ latt a J →
        c ξ = 0) →
      (∀ ξ ξ' : Fin a → E, ξ' ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)) ∈ latt a J →
        ‖c ξ‖ * (1 + ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)‖) ^ M ≤
          A * ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)‖ ^ N) →
      Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∧
        ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ ≤ C * A := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · haveI : IsEmpty {ξ : Fin 0 → E // ξ ≠ 0} := ⟨fun ξ => ξ.2 (Subsingleton.elim _ _)⟩
    exact ⟨0, 0, fun _ _ _ _ _ _ => ⟨summable_empty, by simp⟩⟩
  set D := Module.finrank ℝ (Fin a → Cinf E) with hD
  have hD1 : 1 ≤ D := by rw [hD, finrank_pi_Cinf]; exact Nat.mul_pos ha Module.finrank_pos
  have hND : (D : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨K, hK, hlat⟩ := GlobalTheory.LatticeCount.tsum_one_add_norm_rpow_neg_le_regimes (V := Fin a → Cinf E)
    hD1 (M := ((N + D + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  rw [← hD] at hlat
  refine ⟨N + D + 1, 2 ^ N * K, fun g A c hA hsupp hdec => ?_⟩
  let T : (Fin a → E) →+ (Fin a → Ad E) :=
    { toFun := fun ξ => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val
      map_zero' := by simp only [Pi.zero_apply, map_zero]; exact zero_vecMul _
      map_add' := fun x y => by simp only [Pi.add_apply, map_add (f := _)]; exact add_vecMul _ _ _ }
  let TI : (Fin a → E) →+ (Fin a → Cinf E) := ((pInf E).toAddMonoidHom.compLeft (Fin a)).comp T
  let TF : (Fin a → E) →+ (Fin a → Af E) := ((pFin E).toAddMonoidHom.compLeft (Fin a)).comp T
  let P : AddSubgroup (Fin a → E) := (AddSubgroup.pi Set.univ fun _ => idealFiniteAdeles J).comap TF
  have hP : ∀ ξ, ξ ∈ P ↔ TF ξ ∈ latt a J := fun ξ => ⟨fun h i => h i trivial, fun h i _ => h i⟩
  obtain ⟨δ, hδ, hδle⟩ := exists_le_norm g (isCompact_latt J)
  replace hδle : ∀ ξ ∈ P, ξ ≠ 0 → δ ≤ ‖TI ξ‖ := fun ξ h h0 => hδle ξ h0 ((hP ξ).1 h)
  have hsP : ∀ ξ, c ξ ≠ 0 → ξ ∈ P := fun ξ h => (hP ξ).2 (by_contra fun h' => h (hsupp ξ h'))
  set S : Set ℝ := (fun ξ => ‖TI ξ‖) '' {ξ | ξ ∈ P ∧ ξ ≠ 0} with hS
  rcases S.eq_empty_or_nonempty with hS0 | hS0
  · have : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ = 0 := fun ξ => by
      by_contra h
      exact Set.eq_empty_iff_forall_notMem.1 hS0 _ ⟨ξ.1, ⟨hsP _ (norm_ne_zero_iff.1 h), ξ.2⟩, rfl⟩
    simp only [this, tsum_zero]
    exact ⟨summable_zero, by positivity⟩
  have hr : 0 < sInf S := hδ.trans_le (le_csInf hS0 (by rintro _ ⟨ξ, hξ, rfl⟩; exact hδle ξ hξ.1 hξ.2))
  have hrle : ∀ ξ ∈ P, ξ ≠ 0 → sInf S ≤ ‖TI ξ‖ := fun ξ h h0 =>
    csInf_le ⟨0, by rintro _ ⟨ξ, -, rfl⟩; exact norm_nonneg _⟩ ⟨ξ, ⟨h, h0⟩, rfl⟩
  obtain ⟨_, ⟨ξ₀, hξ₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hS0 (show sInf S < 2 * sInf S by linarith)
  generalize sInf S = r at hr hrle hlt
  obtain ⟨hsum, hlo, hhi⟩ := hlat (P.map TI) r hr (by
    rintro _ ⟨ξ, hξ, rfl⟩ h0
    exact hrle ξ hξ fun e => h0 (by rw [e, map_zero]))
  set B : ℝ := A * (2 * r) ^ N with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ ξ, ‖c ξ‖ ≤ B * (1 + ‖TI ξ‖) ^ (-(((N + D + 1 : ℕ)) : ℝ)) := fun ξ => by
    have h1 := hdec ξ ξ₀ hξ₀.2 ((hP _).1 hξ₀.1)
    have hpos : 0 < (1 + ‖TI ξ‖) ^ (N + D + 1) := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hA)
    exact pow_le_pow_left₀ (norm_nonneg _) hlt.le _
  let j : {ξ // ξ ∈ P ∧ ξ ≠ 0} → {ξ : Fin a → E // ξ ≠ 0} := fun ξ => ⟨ξ.1, ξ.2.2⟩
  have hj : Function.Injective j := fun x y h => Subtype.ext (congrArg (fun z : {ξ : Fin a → E // ξ ≠ 0} => z.1) h)
  have hjs : ∀ ξ ∉ Set.range j, ‖c ξ‖ = 0 := fun ξ h => by
    by_contra h'
    exact h ⟨⟨ξ.1, hsP _ (norm_ne_zero_iff.1 h'), ξ.2⟩, rfl⟩
  let ι : {ξ // ξ ∈ P ∧ ξ ≠ 0} → ((P.map TI : Set (Fin a → Cinf E)) \ {0} : Set (Fin a → Cinf E)) := fun ξ =>
    ⟨TI ξ.1, ⟨ξ.1, ξ.2.1, rfl⟩, norm_pos_iff.1 (hr.trans_le (hrle _ ξ.2.1 ξ.2.2))⟩
  have hι : Function.Injective ι := fun x y h => Subtype.ext (by
    by_contra hne
    have h1 := hrle _ (P.sub_mem x.2.1 y.2.1) (sub_ne_zero.2 hne)
    rw [map_sub, show TI x.1 = TI y.1 from congrArg Subtype.val h, sub_self, norm_zero] at h1
    exact h1.not_gt hr)
  have hs1 := (hsum.mul_left B).comp_injective hι
  have hs2 : Summable ((fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∘ j) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hterm ξ.1) hs1
  refine ⟨(hj.summable_iff hjs).1 hs2, ?_⟩
  rw [← hj.tsum_eq (f := fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) fun ξ h => by_contra fun h' => h (hjs ξ h')]
  refine (Summable.tsum_le_tsum_of_inj ι hι (fun _ _ => by positivity) (fun ξ => hterm ξ.1) hs2
    (hsum.mul_left B)).trans ?_
  rw [tsum_mul_left]
  have key : ∀ e : ℝ, r ^ ((N : ℝ) + e) ≤ 1 → B * (K * r ^ e) ≤ 2 ^ N * K * A := by
    intro e he
    calc B * (K * r ^ e) = 2 ^ N * K * A * r ^ ((N : ℝ) + e) := by
          rw [hB, Real.rpow_add hr, Real.rpow_natCast, mul_pow]; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) he
  rcases le_total r 1 with h1 | h1
  · exact (mul_le_mul_of_nonneg_left (hlo h1) hB0).trans (key _ (Real.rpow_le_one hr.le h1 (by linarith)))
  · exact (mul_le_mul_of_nonneg_left (hhi h1) hB0).trans
      (key _ (Real.rpow_le_one_of_one_le_of_nonpos h1 (by push_cast; linarith)))

end GlobalTheory.RSTheta
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_langlands_transport : GlobalArtinReciprocity → ChevalleyUnits → BrauerDegreeZero → LocalLanglandsExists → LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w'.adicCompletion E') → WD h'), IsRecLit h rc → IsRecLit h' rc' → FieldCompatible rc rc' := by
  first | exact @GlobalTheory.LocLanglands.FieldCompat.fieldCompatible | exact GlobalTheory.LocLanglands.FieldCompat.fieldCompatible | (intros; apply GlobalTheory.LocLanglands.FieldCompat.fieldCompatible <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastStep_intertwiner_one_tuple_all_tuples : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.chain_ωX → R.chain_vX → ∀ (t₀ : T) (y : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY (D.R.m - 1))), IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t₀) (R.ptX t₀) y → R.PItX y := by
  first | exact @GlobalTheory.IntertwinerTransfer.pItX_of_one | exact GlobalTheory.IntertwinerTransfer.pItX_of_one | (intros; apply GlobalTheory.IntertwinerTransfer.pItX_of_one <;> assumption)
end
