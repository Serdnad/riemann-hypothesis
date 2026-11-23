module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle480
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDiagTangentUnitFrameHolomorphicArcLe
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle145
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle382
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
import Mathlib.Algebra.AffineMonoid.Basic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle147
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.admissible_cocycles_card_le_sum_dims : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (s : ℕ) (z : Fin s → G → Fin M.T.m → k), (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) → LinearIndependent k (fun a => (cob M.T).mkQ (z a)) → s ≤ Dt.dsum := by
  first | exact @GlobalTheory.Models.AdmBound.main | exact GlobalTheory.Models.AdmBound.main | (intros; apply GlobalTheory.Models.AdmBound.main <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitCount

theorem locDeg_mul_ncard (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite ∧
      ∀ w ∈ placesOver E l, locDeg E w * (placesOver E l).ncard = Module.finrank ℚ E := by
  have : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime
  have hinj : Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _) :=
    fun _ _ h => HeightOneSpectrum.ext h
  have him : HeightOneSpectrum.asIdeal '' placesOver E l = (Ideal.span {(l : ℤ)}).primesOver (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, GlobalTheory.HubLoc.liesOver_of_mem hl hv⟩
    · rintro ⟨hP, hlo⟩
      have hm : ((l : ℕ) : 𝓞 E) ∈ P := by
        have : (l : ℤ) ∈ P.under ℤ := by
          rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
        simpa [Ideal.under, Ideal.mem_comap] using this
      refine ⟨⟨P, hP, ?_⟩, hm, rfl⟩
      rintro rfl
      exact hl.ne_zero (by simpa using hm)
  refine ⟨Set.Finite.of_finite_image (him ▸ Algebra.QuasiFinite.finite_primesOver _) hinj.injOn, fun w hw => ?_⟩
  have := GlobalTheory.HubLoc.liesOver_of_mem hl hw
  have := w.isPrime
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(l : ℤ)}) (𝓞 E) Gal(E/ℚ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal Gal(E/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal Gal(E/ℚ), ← him,
    Set.ncard_image_of_injective _ hinj, IsGalois.card_aut_eq_finrank] at h
  rw [← h, mul_comm]
  rfl

section Host
variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  obtain ⟨φ⟩ : Nonempty (H.E →+* ℂ) := inferInstance
  apply φ.injective
  rw [GlobalTheory.SplitRowProbe.conj_sqrt, GlobalTheory.SplitRowProbe.conj_sqrt, starRingEnd_self_apply]

def cInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem cInt_coe (x : 𝓞 H.E) : (cInt H x : H.E) = H.conj (x : H.E) := rfl

theorem cInt_cInt (x : 𝓞 H.E) : cInt H (cInt H x) = x :=
  RingOfIntegers.ext (by rw [cInt_coe, cInt_coe, conj_conj])

def cPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.comap (cInt H).toRingHom (cInt H).surjective w

theorem mem_cPl (w : HeightOneSpectrum (𝓞 H.E)) (x : 𝓞 H.E) :
    x ∈ (cPl H w).asIdeal ↔ cInt H x ∈ w.asIdeal := Iff.rfl

theorem cPl_cPl (w : HeightOneSpectrum (𝓞 H.E)) : cPl H (cPl H w) = w :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cPl, mem_cPl, cInt_cInt])

theorem isConjPl_cPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (cPl H w) := by
  intro x y h
  have : y = cInt H x := RingOfIntegers.ext h
  rw [this, mem_cPl, cInt_cInt]

theorem mem_placesOver_of_conj {l : ℕ} {w w' : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E l)
    (h : IsConjPl H w w') : w' ∈ placesOver H.E l :=
  (h (l : 𝓞 H.E) (l : 𝓞 H.E) (by simp)).1 hw

end Host

theorem columns_count : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ s : Bool, (∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' → Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s)) ∧ (columns (N := D.nd) D.nbr i s).Finite ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), locDeg D.host.E w * (columns (N := D.nd) D.nbr i s).ncard = D.R.f := by
  intro D i hl s
  have hx : ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
    intro w hw w' h
    have hw' := mem_placesOver_of_conj D.host hw h
    have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
    have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
    rcases GlobalTheory.T.splitPrime_place_cmType_conjugate D i hl w w' hw hw' h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
    · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
    · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩
  have hgal := D.host.hostE_isGalois
  obtain ⟨hfin, hdeg⟩ := locDeg_mul_ncard D.host.E hl.1
  set C := columns (N := D.nd) D.nbr i s with hC
  have hsub : C ⊆ placesOver D.host.E (D.nd.l i) := fun w ⟨hw, _⟩ => hw
  have hCf : C.Finite := hfin.subset hsub
  refine ⟨hx, hCf, fun w hw => ?_⟩
  have hinj : Function.Injective (cPl D.host) := Function.LeftInverse.injective (cPl_cPl D.host)
  have hun : placesOver D.host.E (D.nd.l i) = C ∪ cPl D.host '' C := by
    ext v
    constructor
    · intro hv
      rcases hx v hv _ (isConjPl_cPl D.host v) with h | h
      · exact Or.inl h.1
      · exact Or.inr ⟨_, h.1, cPl_cPl D.host v⟩
    · rintro (hv | ⟨u, hu, rfl⟩)
      · exact hsub hv
      · exact mem_placesOver_of_conj D.host (hsub hu) (isConjPl_cPl D.host u)
  have hdis : Disjoint C (cPl D.host '' C) := by
    rw [Set.disjoint_left]
    rintro _ hv ⟨u, hu, rfl⟩
    rcases hx u (hsub hu) _ (isConjPl_cPl D.host u) with h | h
    · exact h.2 hv
    · exact h.2 hu
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h := hdeg w hw
  rw [hun, Set.ncard_union_eq hdis hCf (hCf.image _), Set.ncard_image_of_injective _ hinj, hfr] at h
  have h2 : 2 * (locDeg D.host.E w * C.ncard) = 2 * D.R.f := by rw [← h]; ring
  omega

end GlobalTheory.SplitCount

end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.norm_diag_tangent_unitFrame_holomorphicArc_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ∀ j, ‖Formalism.L2.PjFree.toC (t (some j) : CAt σ)‖ ≤ B := by
  first | exact @GlobalTheory.ArcLieBound.norm_diag_le | exact GlobalTheory.ArcLieBound.norm_diag_le | (intros; apply GlobalTheory.ArcLieBound.norm_diag_le <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PhiXiUnit

variable {l : ℕ} [Fact l.Prime]

theorem phiA_alg (x : Per.Ainf l) :
    phiA l (algebraMap (Per.Ainf l) (Per.Acris l) x) =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l x) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg x

theorem φA_tm (x : Per.Fl l) : Per.φA l (Per.tm x) = Per.tm x ^ l := by
  rw [← map_pow]
  exact GlobalTheory.RingIface.phiA_teich l x

theorem φA_tm_root (e : Per.Fl l) :
    Per.φA l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e)) = Per.tm e := by
  rw [φA_tm, ← map_pow, ← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem φA_xi (e : Per.Fl l) :
    Per.φA l (xi e) = ∑ i ∈ Finset.range l, Per.tm e ^ i := by

  rw [xi, map_sum]
  simp only [map_pow, φA_tm_root]

theorem φA_mu (e : Per.Fl l) : Per.φA l (mu e) = mu e * Per.φA l (xi e) := by
  rw [φA_xi, mu, map_sub, map_one, φA_tm, mul_comm, geom_sum_mul]

theorem φA_xi_sub (e : Per.Fl l) :
    ∃ s : Per.Ainf l, Per.φA l (xi e) - (l : Per.Ainf l) = mu e * s := by
  refine ⟨∑ i ∈ Finset.range l, ∑ j ∈ Finset.range i, Per.tm e ^ j, ?_⟩
  have h : (l : Per.Ainf l) = ∑ i ∈ Finset.range l, (1 : Per.Ainf l) := by simp
  rw [φA_xi, mu, Finset.mul_sum, h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, geom_sum_mul]

theorem cancel_mu (C : Core l) (x y : Per.Acris l)
    (h : algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) * x =
      algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) * y) : x = y := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  have hU : IsUnit (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε))) :=
    GlobalTheory.MemLoc.TFil.isUnit_mu he
  apply GlobalTheory.MemLoc.AwayT.acris_injective C
  apply hU.mul_left_cancel
  rw [← map_mul, ← map_mul, h]

theorem exists_unit (C : Core l) : ∃ u : Per.Acris l, IsUnit u ∧
    (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (xi C.ε)) := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  obtain ⟨t, ρ, ht, hρ, htρ⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he.1
  have h1 : t = C.t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t he.1 C.t_log).1 t ht
  have hφt := GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C
  rw [← h1, htρ, map_mul, phiA_alg, φA_mu, map_mul, mul_assoc, mul_left_comm (l : Per.Acris l)] at hφt
  have h2 := cancel_mu C _ _ hφt
  have hφρ : IsUnit (phiA l ρ) := hρ.map _
  refine ⟨ρ * ↑hφρ.unit⁻¹, hρ.mul (Units.isUnit _), ?_⟩
  rw [← mul_assoc, ← h2, mul_assoc, IsUnit.mul_val_inv, mul_one]

theorem iterate_sub_one (C : Core l) (u : Per.Acris l)
    (hu : (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (xi C.ε))) :
    ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑(phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  set a := algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) with ha_def
  have ha : phiA l a = a * ((l : Per.Acris l) * u) := by
    rw [ha_def, phiA_alg, φA_mu, map_mul, hu]
  have hdvd : ∀ m : ℕ, (l : Per.Acris l) ^ m ∣ (phiA l ^ m) a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [RingHom.coe_pow, Function.iterate_succ_apply, ha, ← RingHom.coe_pow, map_mul, map_mul,
        map_natCast, pow_succ]
      obtain ⟨c, hc⟩ := ih
      rw [hc]
      exact ⟨c * (phiA l ^ m) u, by ring⟩
  obtain ⟨s, hs⟩ := φA_xi_sub C.ε
  have hls : (l : Per.Acris l) * u - l = a * algebraMap (Per.Ainf l) (Per.Acris l) s := by
    rw [hu, ← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)) l, ← map_sub, hs, map_mul]
  have key : ∀ m : ℕ, (l : Per.Acris l) * ((phiA l ^ m) u - 1) =
      (phiA l ^ m) a * (phiA l ^ m) (algebraMap (Per.Ainf l) (Per.Acris l) s) := by
    intro m
    rw [← map_mul, ← hls, map_sub, map_mul, map_natCast, mul_sub, mul_one]
  have tf := (GlobalTheory.MemLoc.acris_basic l).2.1
  intro r
  refine ⟨r + 1, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [← RingHom.coe_pow]
  obtain ⟨c, hc⟩ := hdvd (k + 1)
  have h3 : (phiA l ^ (k + 1)) u - 1 =
      (l : Per.Acris l) ^ k * (c * (phiA l ^ (k + 1)) (algebraMap (Per.Ainf l) (Per.Acris l) s)) := by
    rw [← sub_eq_zero]
    apply tf
    rw [mul_sub, key, hc, pow_succ]
    ring
  have h4 : (phiA l ^ (k + 1)) u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, h3]
    exact dvd_mul_right _ _
  exact Ideal.pow_le_pow_right (by omega) h4

end GlobalTheory.MemLoc.PhiXiUnit

theorem GlobalTheory.MemLoc.phi_xi_unit_tendsto : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l),
    ∃ u : Per.Acris l, IsUnit u ∧
      (l : Per.Acris l) * u = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l (GlobalTheory.MemLoc.xi C.ε)) ∧
      ∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M,
        (⇑(GlobalTheory.MemLoc.phiA l))^[m] u - 1 ∈ Ideal.span {(l : Per.Acris l)} ^ r := by
  intro l _ C
  obtain ⟨u, hu, hlu⟩ := GlobalTheory.MemLoc.PhiXiUnit.exists_unit C
  exact ⟨u, hu, hlu, GlobalTheory.MemLoc.PhiXiUnit.iterate_sub_one C u hlu⟩
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.EigenDegree

theorem abstract {B D : Type} [CommRing B] [CommRing D] [IsDomain D] (ι : B →+* D)
    (hι : Function.Injective ι) (φ : B →+* B) (F : ℤ → D → Prop) (h1 : F 0 1)
    (hmul : ∀ a b x y, F a x → F b y → F (a + b) (x * y)) (p t : B) (hp : IsUnit p) (ht : IsUnit t)
    (hφt : φ t = p * t) (ht2 : ¬ F 2 (ι t)) (hsucc : ∀ y, F 1 y → ∃ z, F 0 z ∧ y = ι t * z)
    (hfund : ∀ b, φ b = b → F 0 (ι b) → b ≠ 0 → ∃ c, c * b = 1 ∧ F 0 (ι c))
    (n : ℕ) (hn : 0 < n) (x : B) (hx : (⇑φ)^[n] x = p * x) (hx0 : x ≠ 0) (hx1 : F 1 (ι x))
    (hj0 : ∀ j, j < n → F 0 (ι ((⇑φ)^[j] x))) :
    IsUnit x ∧ ¬ F 2 (ι x) ∧ ∀ j, 0 < j → j < n → ¬ F 1 (ι ((⇑φ)^[j] x)) := by
  haveI : IsDomain B := hι.isDomain ι
  have hprod : ∀ (d : ℕ → ℤ) (f : ℕ → D) (s : Finset ℕ), (∀ i ∈ s, F (d i) (f i)) →
      F (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
    intro d f s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using h1
    | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact hmul _ _ _ _ (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  have hne : ∀ j, j < n → (⇑φ)^[j] x ≠ 0 := by
    intro j hj h
    have e : (⇑φ)^[n] x = 0 := by
      rw [← Nat.sub_add_cancel hj.le, Function.iterate_add_apply, h, iterate_map_zero]
    rw [hx] at e
    exact mul_ne_zero hp.ne_zero hx0 e
  obtain ⟨N, hN⟩ : ∃ N, N = ∏ j ∈ Finset.range n, (⇑φ)^[j] x := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact Finset.prod_ne_zero_iff.2 fun j hj => hne j (Finset.mem_range.1 hj)
  have hφN : φ N = p * N := by
    apply mul_right_cancel₀ hx0
    have e1 := Finset.prod_range_succ (fun j => (⇑φ)^[j] x) n
    have e2 := Finset.prod_range_succ' (fun j => (⇑φ)^[j] x) n
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e2
    rw [← map_prod, ← hN, e1, ← hN, hx] at e2
    rw [← e2]
    ring
  have hN1 : F 1 (ι N) := by
    have := hprod (fun i => if i = 0 then 1 else 0) (fun i => ι ((⇑φ)^[i] x)) (Finset.range n) (by
      intro i hi
      split_ifs with h
      · subst h; exact hx1
      · exact hj0 i (Finset.mem_range.1 hi))
    rw [← map_prod, ← hN] at this
    simpa [hn] using this
  obtain ⟨s, hs⟩ := ht.exists_right_inv
  obtain ⟨z, hz, hz'⟩ := hsucc _ hN1
  have hb : t * (s * N) = N := by rw [← mul_assoc, hs, one_mul]
  have hφb : φ (s * N) = s * N := by
    apply (hp.mul ht).mul_left_cancel
    rw [← hφt, ← map_mul, hb, hφN, hφt, mul_assoc, hb]
  have hbz : ι (s * N) = z := by
    rw [map_mul, hz', ← mul_assoc, ← map_mul, mul_comm s, hs, map_one, one_mul]
  obtain ⟨c, hc, hc0⟩ := hfund _ hφb (hbz ▸ hz) (fun h => hN0 (by rw [← hb, h, mul_zero]))
  have htc : t = c * N := by
    calc t = t * (c * (s * N)) := by rw [hc, mul_one]
      _ = c * (t * (s * N)) := by ring
      _ = c * N := by rw [hb]
  have hNu : IsUnit N := isUnit_of_mul_isUnit_right (htc ▸ ht)
  have hN2 : ¬ F 2 (ι N) := by
    intro h
    apply ht2
    have := hmul _ _ _ _ hc0 h
    rwa [zero_add, ← map_mul, ← htc] at this
  have key : ∀ j, j < n → ¬ F ((if j = 0 then 1 else 0) + 1) (ι ((⇑φ)^[j] x)) := by
    intro j hj h
    apply hN2
    have := hprod (fun i => (if i = 0 then 1 else 0) + (if i = j then 1 else 0))
      (fun i => ι ((⇑φ)^[i] x)) (Finset.range n) (by
      intro i hi
      by_cases hij : i = j
      · subst hij
        simpa using h
      · by_cases h0 : i = 0
        · subst h0
          simpa [hij] using hx1
        · simpa [hij, h0] using hj0 i (Finset.mem_range.1 hi))
    rw [← map_prod, ← hN, Finset.sum_add_distrib] at this
    simpa [hn, hj, one_add_one_eq_two] using this
  refine ⟨?_, ?_, fun j h0 hj => ?_⟩
  · refine isUnit_of_dvd_unit ?_ hNu
    rw [hN]
    exact Finset.dvd_prod_of_mem (fun j => (⇑φ)^[j] x) (Finset.mem_range.2 hn)
  · simpa [one_add_one_eq_two] using key 0 hn
  · simpa [h0.ne'] using key j hj

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem main : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (n : ℕ), 0 < n → ∀ x : Per.Bcris l,
    (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x → x ≠ 0 → C.ι x ∈ Per.FilD l 1 →
    (∀ j : ℕ, j < n → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0) →
    IsUnit x ∧ C.ι x ∉ Per.FilD l 2 ∧
      ∀ j : ℕ, 0 < j → j < n → C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  intro l _ C n hn x hx hx0 hx1 hj0
  obtain ⟨-, h1, hmul, -, -, -, hP⟩ := filD_laws l
  obtain ⟨htu, -, ht2, hlu⟩ := core_t_unit_fil l C
  have he := core_isEps l C
  have hlog := (LogFun.log_fun l C.ε C.t he.1 C.t_log).2.2.2 C.j C.j_cris
  haveI : IsDomain (Per.BdR l) := (BdRField.bdR_isField l).2.2.1.isDomain
  refine abstract C.ι (ULaws.u_laws l C).2.2.2.1 (Per.φB l) (fun a y => y ∈ Per.FilD l a) h1 hmul
    (l : Per.Bcris l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t) hlu htu ?_ ?_ ?_ ?_ n hn x hx hx0 hx1 hj0
  · rw [fund_phiB_alg, TPhi.t_phi l C, map_mul, map_natCast]
  · intro h
    rw [C.ι_j] at h
    exact ht2 ((hP 2 _).1 h)
  · intro y hy
    obtain ⟨z, hz, e⟩ := (TiedUnif.filD_succ he hlog 0 y).1 (by rwa [zero_add])
    exact ⟨z, hz, by rw [C.ι_j]; exact e⟩
  · intro b hb hb0 hne
    obtain ⟨c, rfl⟩ := fundamental_exact l C b hb hb0
    have hc : c ≠ 0 := by
      rintro rfl
      exact hne (by rw [map_zero, map_zero])
    refine ⟨C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c⁻¹), ?_, ?_⟩
    · rw [← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
    · show C.ι _ ∈ _
      rw [C.ι_u]
      exact TiedUnif.alg_mem_FilD_zero _

end GlobalTheory.MemLoc.EigenDegree
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.continuous_globalWhittakerCoefficientGLAdeles : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → Continuous (GlobalTheory.JSW.whit F) := by
  first | (exact @GlobalTheory.JSW.WhitCont.continuous_whit) | (exact GlobalTheory.JSW.WhitCont.continuous_whit) | (intros; apply GlobalTheory.JSW.WhitCont.continuous_whit  <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachN_cokernel_killed_by_power : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∃ c : ℕ, ∀ z ∈ W.N T₂, (∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : AA K LL) ^ c • z) ∧ ∃ y ∈ W.N T₁, W.map π y = (letπ : AA K LL) ^ c • z := by
  first | exact @GlobalTheory.NL.CokerFin.coker_killed | exact GlobalTheory.NL.CokerFin.coker_killed | (intros; apply GlobalTheory.NL.CokerFin.coker_killed <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.exists_weakTopology_wachImage_isClosed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T))) := by
  first | exact @GlobalTheory.WeakClosedX.jD_XN_closed | exact GlobalTheory.WeakClosedX.jD_XN_closed | (intros; apply GlobalTheory.WeakClosedX.jD_XN_closed <;> assumption)
end
