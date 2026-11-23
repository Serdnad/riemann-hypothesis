module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle039
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
open IsDedekindDomain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalSup

section Prime

variable {K : Type} [Field K] [NumberField K]

abbrev primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s).symm la

theorem count_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [DecidableEq (Associates (Ideal R))] [∀ p : Associates (Ideal R), Decidable (Irreducible p)]
    [DecidableEq (Associates (Ideal S))] [∀ p : Associates (Ideal S), Decidable (Irreducible p)]
    (e : R ≃+* S) (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal).count (Associates.mk (I.comap e.symm)).factors =
      (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  have hI' : I.comap e.symm ≠ ⊥ := by
    rw [← Ideal.map_comap_of_equiv]
    exact fun h => hI ((Ideal.map_eq_bot_iff_of_injective e.injective).1 h)
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI') (HeightOneSpectrum.associates_irreducible _),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) (HeightOneSpectrum.associates_irreducible _),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  have : (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = p.asIdeal.map (e : R →+* S) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  rw [this, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  exact Ideal.comap_le_comap_iff_of_surjective e.symm e.symm.surjective _ _

theorem intValuation_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    (primeBack s la).intValuation a = la.intValuation (RingOfIntegers.mapRingEquiv s a) := by
  classical
  by_cases ha : a = 0
  · subst ha; simp
  have ha' : RingOfIntegers.mapRingEquiv s a ≠ 0 := by simpa using ha
  rw [HeightOneSpectrum.intValuation_if_neg _ ha, HeightOneSpectrum.intValuation_if_neg _ ha']
  have hc : (Ideal.span {RingOfIntegers.mapRingEquiv s a}).comap (RingOfIntegers.mapRingEquiv s).symm.symm =
      Ideal.span {a} := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_span, Set.image_singleton]
    simp
  have := count_equiv (RingOfIntegers.mapRingEquiv s).symm la
    (I := Ideal.span {RingOfIntegers.mapRingEquiv s a}) (by simpa using ha')
  rw [hc] at this
  rw [this]

theorem valuation_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    (primeBack s la).valuation K x = la.valuation K (s x) := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs : ∀ z : 𝓞 K, s (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv s z) :=
    fun _ => rfl
  rw [map_div₀, map_div₀, map_div₀, hs, hs, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_primeBack, intValuation_primeBack]

theorem vLa_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    vLa (primeBack s la) x = vLa la (s x) := by
  simp only [vLa, valuation_primeBack]

end Prime
end GlobalTheory.GalSup

namespace GlobalTheory.GalSup

section Pts

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

def changeEmbedding {L : Type} [CommRing L] (ι₀ ι₁ : c'.F →+* L) (κ : c.F →+* L)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) (h₁ : ∀ a, ι₁ (incF c c' hle a) = κ a)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' L) : letI := ι₁.toAlgebra; FrPt Xo c' L :=
  letI : Algebra c.F L := κ.toAlgebra
  let y₀ : FrPt Xo c L := (letI : Algebra c'.F L := ι₀.toAlgebra; y.res hle h₀)
  letI : Algebra c'.F L := ι₁.toAlgebra
  y₀.ext hle h₁

theorem evR_rulBC {L : Type} [CommRing L] (ι₀ : c'.F →+* L) (κ : c.F →+* L)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' L) :
    (letI := ι₀.toAlgebra; evR Xo c' (rulBC hle f) y) =
      (letI : Algebra c.F L := κ.toAlgebra; letI := ι₀.toAlgebra; evR Xo c f (y.res hle h₀)) := by
  letI : Algebra c.F L := κ.toAlgebra
  letI := ι₀.toAlgebra
  exact ((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2 L h₀ y

theorem integral_reread {T : CDVR} (ι₀ ι₁ : c'.F →+* T.Fr) (κ : c.F →+* T.Fr)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) (h₁ : ∀ a, ι₁ (incF c c' hle a) = κ a)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' T.Fr) (hy : Integral T ι₀ y) :
    Integral T ι₁ (changeEmbedding hle ι₀ ι₁ κ h₀ h₁ y) := by
  have key : ∀ (τ : E →+* ℂ) (b : 𝓞 E), ι₁ (embK c' τ b) = ι₀ (embK c' τ b) := fun τ b => by
    rw [← embK_incF hle τ b, h₀, h₁]
  have eig : ∀ (G : SAB H (Sp T.V)) τ (w : epsOver T.V T.V ⟶ G.G),
      IsEigV c' ι₁ G τ w ↔ IsEigV c' ι₀ G τ w := fun G τ w => by
    unfold IsEigV
    simp only [key]
  obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, rest⟩ := hy
  exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (eig G τ _).2 (h2 τ i),
    fun τ w ht he => h3 τ w ht ((eig G τ w).1 he), h4⟩, rest⟩

end Pts
end GlobalTheory.GalSup

namespace GlobalTheory.GalSup

open ReciprocityTheory.ChartRestriction.G

theorem evI_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) {m : ℕ}
    (b : Fin m → c.F) (g : Fin m → Rul Xo c) :
    evI y (∑ i, b i • g i) = ∑ i, io (b i) * evI y (g i) := by
  have h := map_sum (AddMonoidHom.mk' (evI y) (evI_add y)) (fun i => b i • g i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at h
  rw [h]
  simp only [evI_smul]

theorem intAt_galois : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : c'.F ≃+* c'.F), (∀ x : c.F, s (incF c c' hle x) = incF c c' hle x) → ∀ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ sec Xo c a n) → IntAt Xo c' (∑ i, as i • rulBC hle (fs i)) → IntAt Xo c' (∑ i, s (as i) • rulBC hle (fs i)) := by
  intro E _ _ _ H Dw l Xo c c' hle a n s hs m as fs hfs hint la v hv
  obtain ⟨⟨q, T, ι, e, ho, y, hy, eta, heta, hq⟩, rfl⟩ := hv
  subst hq
  show 0 ≤ nval T.V e (evI y _)
  let κ : c.F →+* T.Fr := ι.comp (incF c c' hle)
  let ι₁ : c'.F →+* T.Fr := ι.comp (s : c'.F →+* c'.F)
  have h₀ : ∀ x, ι (incF c c' hle x) = κ x := fun _ => rfl
  have h₁ : ∀ x, ι₁ (incF c c' hle x) = κ x := fun x => by
    show ι (s (incF c c' hle x)) = ι (incF c c' hle x)
    rw [hs x]
  let y₁ : IntFr Xo c' T ι₁ := ⟨changeEmbedding hle ι ι₁ κ h₀ h₁ y.1,
    (letI := ι₁.toAlgebra; GlobalTheory.FlagTan.fromTest_of_isLocalRing _), integral_reread hle ι ι₁ κ h₀ h₁ y.1 y.2.2⟩
  have ho₁ : OverLa (primeBack s la) T.V ι₁ e := ⟨ho.1, fun x => by
    rw [vLa_primeBack]; exact ho.2 (s x)⟩
  have key : 0 ≤ nval T.V e (evI y₁ (∑ i, as i • rulBC hle (fs i))) :=
    hint (primeBack s la) _ ⟨PtV.mk (primeBack s la) ho₁ y₁ hy () trivial, rfl⟩
  have e1 : evI y (∑ i, s (as i) • rulBC hle (fs i)) = evI y₁ (∑ i, as i • rulBC hle (fs i)) := by
    rw [evI_sum, evI_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold evI
    rw [evR_rulBC hle ι κ h₀ (hfs i), evR_rulBC hle ι₁ κ h₁ (hfs i)]
    rfl
  rw [e1]
  exact key

end GlobalTheory.GalSup
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
open IsDedekindDomain

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.IntCoefExt

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem nval_nonneg_iff {e : ℕ} (he : 0 < e) (x : K') : 0 ≤ nval V e x ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    simp [nval_zero, vV]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ he', zero_mul]
  exact_mod_cast Iff.rfl

theorem exists_nat_pos {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {ι : K →+* K'} {e : ℕ}
    (ho : OverLa la V ι e) : ∃ N : ℕ, N ≠ 0 ∧ 0 < vV V (N : K') := by
  have hN : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm la.asIdeal, hN, ?_⟩
  have h1 := ho.2 (Ideal.absNorm la.asIdeal : K)
  rw [map_natCast] at h1
  rw [h1]
  refine mul_pos (by exact_mod_cast ho.1) ?_
  have h2 : la.valuation K (Ideal.absNorm la.asIdeal : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) _).2 (Ideal.absNorm_mem la.asIdeal)
    simpa using this
  have h0 : la.valuation K (Ideal.absNorm la.asIdeal : K) ≠ 0 := by
    simpa using hN
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
  simp only [vLa]
  omega

theorem exists_overLa {K : Type} [Field K] [NumberField K] (ι : K →+* K') {N : ℕ} (hN : N ≠ 0)
    (h : 0 < vV V (N : K')) : ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la V ι e := by
  let u := (valV V (K' := K')).comap ι
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.CommonValuation.exists_centre u
  have hN' : (N : K') ≠ 0 := by
    rw [← map_natCast ι]
    exact (map_ne_zero ι).2 (Nat.cast_ne_zero.2 hN)
  have hNQ : (N : 𝓞 K) ∈ Q := by
    rw [hQm, map_natCast]
    show valV V (ι N) < 1
    rw [map_natCast, ← WithZero.exp_log (valV_ne_zero (V := V) hN'), ← WithZero.exp_zero, WithZero.exp_lt_exp]
    simp only [vV] at h
    omega
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hN (Nat.cast_eq_zero.1 ((Submodule.mem_bot _).1 hNQ))
  let la : HeightOneSpectrum (𝓞 K) := ⟨Q, hQ, h0⟩
  obtain ⟨e, he, hv⟩ := GlobalTheory.CommonValuation.exists_eq_pow la u
    (GlobalTheory.CommonValuation.le_one_of_ringOfIntegers u) (fun r => (hQm r).symm)
  refine ⟨la, e, he, fun a => ?_⟩
  have := hv a
  rw [Valuation.comap_apply] at this
  simp only [vV, vLa, this, WithZero.log_pow, nsmul_eq_mul]
  ring

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem integral_res_iff (T : CDVR) (io' : c'.F →+* T.Fr) (io : c.F →+* T.Fr)
    (h : ∀ a, io' (incF c c' hle a) = io a) (y : letI := io'.toAlgebra; FrPt Xo c' T.Fr) :
    Integral T io' y ↔ Integral T io (letI := io.toAlgebra; letI := io'.toAlgebra; y.res hle h) := by
  have e : ∀ (G : SAB H (Sp T.V)) τ v, IsEigV c' io' G τ v ↔ IsEigV c io G τ v := fun G τ v => by
    unfold IsEigV
    simp only [← embK_incF hle τ, h]
  constructor
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).1 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).2 he), h4⟩, h5⟩
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).2 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).1 he), h4⟩, h5⟩

theorem intAt_iff (f : Rul Xo c) : IntAt Xo c f ↔ ∀ (T : CDVR) (io : c.F →+* T.Fr) (N : ℕ), N ≠ 0 →
    0 < vV T.V (N : T.Fr) → T.FinRes → ∀ y : IntFr Xo c T io, 0 ≤ vV T.V (evI y f) := by
  constructor
  · intro h T io N hN hp hT y
    obtain ⟨la, e, ho⟩ := exists_overLa io hN hp
    exact (nval_nonneg_iff ho.1 _).1 (h la _ ⟨PtV.mk la ho y hT () trivial, rfl⟩)
  · rintro h la _ ⟨⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩, rfl⟩
    obtain ⟨N, hN, hp⟩ := exists_nat_pos ho
    exact (nval_nonneg_iff ho.1 _).2 (h T io N hN hp hy y)

theorem intAt_rulBC_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, (IntAt Xo c' (rulBC hle f) ↔ IntAt Xo c f) := by
  intro E _ _ _ H Dw l Xo c c' hle a n f hf
  have hval := ((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2
  rw [intAt_iff, intAt_iff]
  constructor
  · intro h T io N hN hp hT y
    letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
    haveI := c.fin
    haveI := c'.fin
    haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun x => by simp
    haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ _ _
    obtain ⟨L, _, _, g, hL, -, hg⟩ := GlobalTheory.exists_finite_separable_compositum c.F T.Fr c'.F io
    obtain ⟨T', iT, e, ψ, -, he, hv, hψ, -, hfin⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
    obtain ⟨⟨y₁, -, -, φ, hφ, hm⟩, -⟩ := GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw l Xo c T T' io y iT e he hv
    let io' : c'.F →+* T'.Fr := ψ.toRingHom.comp g
    have hio : ∀ x, io' (incF c c' hle x) = (iT.comp io) x := fun x => by
      have := DFunLike.congr_fun hg x
      exact (congrArg ψ this).trans (hψ _)
    have hp' : 0 < vV T'.V (N : T'.Fr) := by
      rw [← map_natCast iT, hv]
      exact mul_pos (by exact_mod_cast he) hp
    have e1 : evI y₁ f = iT (evI y f) := by
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      exact (pos_evR (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φ y.1 y.2.1 y₁.1 hm).trans
        (DFunLike.congr_fun hφ _)
    letI := (iT.comp io).toAlgebra
    letI := io'.toAlgebra
    let y' : IntFr Xo c' T' io' := ⟨y₁.1.ext hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      (integral_res_iff hle T' io' (iT.comp io) hio _).2 y₁.2.2⟩
    have e2 : evI y' (rulBC hle f) = evI y₁ f := hval T'.Fr hio y'.1
    have key := h T' io' N hN hp' (hfin hT) y'
    rw [e2, e1, hv] at key
    exact nonneg_of_mul_nonneg_right key (by exact_mod_cast he)
  · intro h T io' N hN hp hT y'
    let io : c.F →+* T.Fr := io'.comp (incF c c' hle)
    have hio : ∀ x, io' (incF c c' hle x) = io x := fun _ => rfl
    letI := io.toAlgebra
    letI := io'.toAlgebra
    let y : IntFr Xo c T io := ⟨y'.1.res hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      (integral_res_iff hle T io' io hio _).1 y'.2.2⟩
    have e2 : evI y' (rulBC hle f) = evI y f := hval T.Fr hio y'.1
    rw [e2]
    exact h T io N hN hp hT y

end GlobalTheory.IntCoefExt
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilProduct

open GlobalTheory.FinWeilO

variable {D : D7}

theorem isHeckeChar_pow {η : (AE D)ˣ →* Circle} (h : IsHeckeChar D η) (n : ℕ) : IsHeckeChar D (η ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEta_pow {η : (AE D)ˣ →* Circle} (h : ResEta D η 1) (n : ℕ) : ResEta D (η ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem mem_GfC_of_supp {a : AE D} (ha : infPart D a = 0) {V : HSp D} {g : GA D V}
    (hg : ∀ i j, a * (mt V g - 1) i j = (mt V g - 1) i j) : g ∈ GfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt V g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, ha, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]

theorem mem_GfC_of_suppAt {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : g ∈ GfC V := by
  obtain ⟨-, -, v, ε, h1, h2⟩ := he
  exact mem_GfC_of_supp (h2 ▸ infPart_placeIdem h1) hg

theorem exists_weilDatum_etaTilde : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∃ om, IsWeilDatumO ψ S T (η ^ S.rank) (η ^ T.rank) om ∧ (∀ v ε, NonSplitAt D v ε → FixesVacAt ψ S T ΛS ΛT om v ε) ∧ VacCharPlus ψ θ S T om := by
  intro D ψ hψ S T θ hθ ΛS ΛT hS hT η hη
  obtain ⟨of, hf⟩ := exists_isFinWeil D ψ hψ S T ΛS ΛT hS hT _ _ (isHeckeChar_pow hη.1 S.rank)
    (isHeckeChar_pow hη.1 T.rank) (resEta_pow hη.2.2.1 _) (resEta_pow hη.2.2.1 _)
  obtain ⟨oi, hi⟩ := GlobalTheory.RealWeil.exists_isInfWeil D ψ hψ θ hθ S T
  have hcomm := fun p q f h1 => fin_inf_comm hψ hS hT hf hi p q (f := f) h1
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T)
    ({ toFun := fun p => (of p * oi p).restrict fun f h1 => hf.pres p _ (hi.pres p f h1)
       map_one' := LinearMap.ext fun f => Subtype.ext (by
         show of 1 (oi 1 f) = f
         rw [map_one, map_one]; rfl)
       map_mul' := fun p q => LinearMap.ext fun f => Subtype.ext (by
         show of (p * q) (oi (p * q) f) = of p (oi p (of q (oi q f)))
         rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcomm q p _ (hi.pres q _ f.2)]) } :
      GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T))
  have ho : ∀ p f, IsThetaFunO ψ S T f → om p f = of p (oi p f) := fun p f h1 => hom p ⟨f, h1⟩
  have hp : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f) := fun p f h1 => by
    rw [ho p f h1]
    exact hf.pres p _ (hi.pres p f h1)
  have hfin : ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = of (g, h) f := fun g hg h hh f h1 => by
    rw [ho _ f h1, hi.triv g hg h hh f h1]
  have hinf : ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = oi (g, h) f :=
    fun g hg h hh f h1 => by rw [ho _ f h1, hf.triv g hg h hh _ (hi.pres _ f h1)]
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  refine ⟨om, ⟨hψ, isHeckeChar_pow hη.1 _, isHeckeChar_pow hη.1 _, resEta_pow hη.2.2.1 _, resEta_pow hη.2.2.1 _, hp,
    fun g h u f h1 => ?_, fun γ hγ γ' hγ' f h1 => ?_, fun f h1 u => ?_, fun μ 𝓕 hμ h𝓕 p f h1 => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩, fun v ε hv g h hg hh hst f h1 hfix => ?_,
    fun sS sT cS cT g hg h hh kS kT f h1 hv => ?_⟩
  · obtain ⟨a, ha, b, hb, k, hk, l, hl, e, -⟩ := exists_parts (g, h)
    obtain ⟨rfl, rfl⟩ : g = a * k ∧ h = b * l := Prod.ext_iff.1 e
    rw [actO_mul, e, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfin k hk l hl _ (hth u f h1),
      hf.Heisenberg₂ k hk l hl u f h1, hfin k hk l hl f h1, hinf a ha b hb _ (hth _ _ (hf.pres _ f h1)),
      hi.Heisenberg₂ a ha b hb _ _ (hf.pres _ f h1), hinf a ha b hb _ (hf.pres _ f h1)]
  · rw [show ((γ, γ') : GA D S × GA D T) = (γ, 1) * (1, γ') by simp, map_mul, Module.End.mul_apply,
      ho _ _ (hp _ f h1), GlobalTheory.T.thetaDistribution_automorphy_source_group D ψ hψ S T θ hθ ΛS ΛT hS hT η hη of oi hf hi γ hγ _ (hp _ f h1), ho _ f h1]
    exact GlobalTheory.T.thetaDistribution_invariant_rationalTarget D ψ hψ S T θ hθ ΛS ΛT hS hT η hη of oi hf hi γ' hγ' f h1
  · simp only [ho _ f h1]
    exact continuous_product hψ hS hT hf hi h1 u
  · rw [ho p f h1, hf.unit μ 𝓕 hμ h𝓕 p _ (hi.pres p f h1), hi.unit μ 𝓕 hμ h𝓕 p f h1]
  · obtain ⟨r, hr, h2⟩ := hf.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f h1 => ?_⟩
    rw [hfin g (mem_GfC_of_suppAt he hg) h (mem_GfC_of_suppAt he hh) f h1]
    exact h2 ℓ hℓ f h1
  · rw [hfin g (mem_GfC_of_supp (infPart_placeIdem hv.1) hg) h (mem_GfC_of_supp (infPart_placeIdem hv.1) hh) f h1]
    exact hf.inert v ε hv g h hg hh hst f h1 hfix
  · rw [hinf g hg h hh f h1]
    exact hi.vac sS sT cS cT g hg h hh kS kT f h1 hv

end GlobalTheory.WeilProduct

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translate_section_values_bounded_integral_tangent : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ α : N.X, ∃ b : ℝ, ∀ mu : N.X, ‖(trVal ν s gm α mu).fst‖ ≤ b ∧ ‖(trVal ν s gm α mu).snd‖ ≤ b := by
  exact @GlobalTheory.MBLow.trVal_bounded
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsionSymplecticLabels_of_levelStructure : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (g k : ℕ), 1 ≤ k → ∀ (ζ : Cˣ) (pt : (Fin (2 * g) → ZMod k) → (TFK (R := V) C ⟶ A.A)), IsPrimitiveRoot ζ k → (∀ a b, pt (a + b) = pt a * pt b) → Function.Injective pt → (∀ z : TFK (R := V) C ⟶ A.A, z ^ k = 1 → ∃ a, pt a = z) → (∀ i j, WeilIs A.A A.L k (pt (Pi.single i 1)) (pt (Pi.single j 1)) (unitOn (ζ ^ stdSymp g i j))) → ∃ (p : (Fin (2 * g) → ZMod k) → QkPt D.toPre C k) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q ∧ ∀ a, ν.QPt (p a) (q a) ∧ QkToAkU U.toUnifPre C k (p a) (pt a) := by
  first | exact @GlobalTheory.MBLow.qLevel_of_torsion_labels | exact GlobalTheory.MBLow.qLevel_of_torsion_labels | (intros; apply GlobalTheory.MBLow.qLevel_of_torsion_labels <;> assumption)
end
