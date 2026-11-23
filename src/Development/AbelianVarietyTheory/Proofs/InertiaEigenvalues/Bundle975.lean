module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle072
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle972
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle922
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle039
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle053
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle703
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle173
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle973
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology

theorem _root_.GlobalTheory.T.rankinSelberg_partialL_tendsto_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∃ z : ℂ, z ≠ 0 ∧ Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 z) := by
  first | (exact @GlobalTheory.RSNonvan.tendsto_partialL_ne_zero) | (exact GlobalTheory.RSNonvan.tendsto_partialL_ne_zero) | (intros; apply GlobalTheory.RSNonvan.tendsto_partialL_ne_zero  <;> assumption)
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

namespace GlobalTheory.CoverBound

theorem inV_iff (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0
    simp [InV, vV]
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log (valV_ne_zero (V := T.V) h0) one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV
    omega
  · intro h3
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log (valV_ne_zero h0) one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h3
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_map_iff {T T' : CDVR} (i : T.Fr →+* T'.Fr) {r : ℕ} (hr : 0 < r)
    (hi : ∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) (x : T.Fr) : InV T' (i x) ↔ InV T x := by
  rw [inV_iff, inV_iff, hi]
  exact mul_nonneg_iff_of_pos_left (by exact_mod_cast hr)

theorem inV_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR}
    {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {x : K} (hx : la.valuation K x ≤ 1) : InV T (io x) := by
  rw [inV_iff, ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : x = 0
  · simp [vLa, h0]
  have h2 := (WithZero.log_le_log ((la.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 hx
  rw [WithZero.log_one] at h2
  unfold vLa
  omega

theorem inV_of_pow_eq (T : CDVR) {x : T.Fr} {e : ℕ} (he : 0 < e) (hx : x ^ (e + 1) = x) : InV T x := by
  by_cases h0 : x = 0
  · subst h0
    exact zero_mem (algebraMap T.V T.Fr).range
  have h := GlobalTheory.PlaceExtField.vV_pow (V := T.V) h0 (e + 1)
  rw [hx] at h
  rw [inV_iff]
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  push_cast at h
  have : (e : ℤ) * vV T.V x = 0 := by linarith
  exact ((mul_eq_zero.1 this).resolve_left he'.ne').ge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem good_lift {X X₂ : Scheme.{0}} (t : SAB H X) (t₂ : SAB H X₂) (r : X₂ ⟶ X) (m : SABMap t₂ t r) (T T' : CDVR)
    (i : T.Fr →+* T'.Fr) (e : ℕ) (hi : ∀ a : T.Fr, vV T'.V (i a) = (e : ℤ) * vV T.V a) (x : Sp T.Fr ⟶ X)
    (x₂ : Sp T'.Fr ⟶ X₂) (hx : x₂ ≫ r = spMap i ≫ x)
    (h : ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' t x)
      (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), IsProper G.G.hom) :
    ∃ (G : SAB H (Sp T'.V)) (t' : SAB H (Sp T'.Fr)) (_ : SABMap t' t₂ x₂)
      (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), IsProper G.G.hom := by
  obtain ⟨G, t', m1, m2, hp⟩ := h
  obtain ⟨φ, hφ⟩ := GlobalTheory.PlaceInt.Ext.exists_restrict T T' i e hi
  obtain ⟨G', ⟨mG⟩⟩ : ∃ G' : SAB H (Sp T'.V), Nonempty (SABMap G' G (spMap φ)) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap φ) G⟩⟩
  obtain ⟨s, ⟨n⟩⟩ : ∃ s : SAB H (Sp T'.Fr), Nonempty (SABMap s t' (spMap i)) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap i) t'⟩⟩
  have hio : spMap i ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← GlobalTheory.FramedBaseChange.spec_comp, ← GlobalTheory.FramedBaseChange.spec_comp]
    exact congrArg spMap (RingHom.ext fun a => (hφ a).symm)
  obtain ⟨a1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 n
  obtain ⟨a2, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 n
  rw [← hx] at a1
  rw [hio] at a2
  obtain ⟨b1, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m a1
  obtain ⟨b2, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mG a2
  exact ⟨G', s, b1, b2, MorphismProperty.of_isPullback mG.cart.1 hp⟩

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem shortValAt_of_map (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (La : GenLat E n) (β : c.F)
    (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {K k : Type} [Field K] [Field k] [Algebra c.F K] [Algebra c.F k]
    (ψ : K →ₐ[c.F] k) (y : FrPt Xo c K) (z : FrPt Xo c k) (h : FrMap ψ y z) (v : K)
    (hv : ShortValAt Xo c nab w La β N P z (ψ v)) : ShortValAt Xo c nab w La β N P y v := by
  obtain ⟨S, _, _, φ, y', a, b, F, hf, hm, h1, h2, h3, h4, h5⟩ := hv
  refine ⟨S, inferInstance, inferInstance, φ.comp ψ, y', a, b, F, ?_, GlobalTheory.FramedBaseChange.trans ψ φ h hm,
    h1, h2, h3, h4, h5⟩
  haveI : Nontrivial S := hf.injective.nontrivial
  letI := (φ.comp ψ).toRingHom.toAlgebra
  exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance

theorem evR_pow_succ (f : Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (e : ℕ) :
    evR Xo c (f ^ (e + 1)) y = evR Xo c f y ^ (e + 1) := by
  induction e with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ e ih => rw [pow_succ f, pow_succ (evR Xo c f y), ← ih]; exact evalAt_mul _ _ _ _ _



theorem bddAll_of_theta_sum_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n d N m : ℕ) (dδ : DeltaDat Xo c n) (La : GenLat E n) (cs : Fin m → Rul dδ.Xo₂ dδ.c₂) (e : ℕ) (w : Fin m → (Fin n → LevQ Dw dδ.l₂) → c.F) (P : Fin m → MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), Dom a n → dδ.IsLev → IsNab dδ.Xo₂ dδ.c₂ dδ.nab₂ → La.Unimod → La.TrivAt dδ.l₂.M → La.LevOK N dδ.l₂.M → 0 < e → (∀ t, cs t ∈ sec dδ.Xo₂ dδ.c₂ 0 0 ∧ cs t ^ (e + 1) = cs t) → (∀ t q, la.valuation c.F (w t q) ≤ 1) → (∀ t, P t ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) ∧ (P t).IsHomogeneous d ∧ ∀ k, la.valuation c.F ((P t).coeff k) ≤ 1) → f ∈ cusp Xo c U a n → (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : Fin m → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) → BddAll Xo c la (((La.mIdx N (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw dδ.l₂) : ℕ) : c.F) * ((2 * NumberField.discr E * N : ℤ) : c.F) ^ d) f := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hl _ a n d N m dδ La cs e w P f hdom hlev hnab hun htr hN he hcs hw hP hf
    hval
  refine GlobalTheory.T.cuspFormBound_goodPoints_extends_allPoints E H Dw l Xo c r U hU la p hp hpl hl a n f _ hdom hf ?_
  intro T io e₀ ho y hfin hgood
  have laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨T₁, i₁, e₁, y₁, io₁, z₁, ⟨he₁, hv₁, φ₁, hφ₁, hm₁⟩, -, hio₁, hover⟩ :=
    GlobalTheory.CoverPoint.exists_ext_lift_to_cover E H Dw l Xo c n dδ hlev T io y hfin
  letI a0 : Algebra c.F T.Fr := io.toAlgebra
  letI a1 : Algebra c.F T₁.Fr := (i₁.comp io).toAlgebra
  letI b1 : Algebra dδ.c₂.F T₁.Fr := io₁.toAlgebra
  obtain ⟨k, _, _, _, _, -⟩ : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra T₁.Fr k)
      (_ : Algebra.IsAlgebraic T₁.Fr k), True :=
    ⟨AlgebraicClosure T₁.Fr, inferInstance, inferInstance, inferInstance, inferInstance, trivial⟩
  letI ak : Algebra c.F k := ((algebraMap T₁.Fr k).comp (i₁.comp io)).toAlgebra
  letI bk : Algebra dδ.c₂.F k := ((algebraMap T₁.Fr k).comp io₁).toAlgebra
  let ψ₁ : T₁.Fr →ₐ[c.F] k := { algebraMap T₁.Fr k with commutes' := fun _ => rfl }
  let ψ₂ : T₁.Fr →ₐ[dδ.c₂.F] k := { algebraMap T₁.Fr k with commutes' := fun _ => rfl }
  obtain ⟨yk, hyk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw l Xo c _ _ ψ₁ y₁.1
  obtain ⟨zk, hzk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ _ _ ψ₂ z₁.1
  have hc1 : ∀ x : c.F, algebraMap dδ.c₂.F T₁.Fr (dδ.eF x) = algebraMap c.F T₁.Fr x := hio₁
  have hck : ∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x := fun x =>
    congrArg (algebraMap T₁.Fr k) (hio₁ x)
  have hoverk : FrOver dδ zk yk :=
    (GlobalTheory.frames_lift_to_cover laws E H Dw l Xo c n dδ).2.1 T₁.Fr hc1 k hck ψ₁ ψ₂ rfl y₁.1 z₁.1 yk zk hover hyk hzk
  obtain ⟨v, hv, hev⟩ := hval k hck yk zk hoverk
  let K := IntermediateField.adjoin T₁.Fr (Set.range v)
  haveI : FiniteDimensional T₁.Fr K := IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨T₂, i₂, e₂, ρ, -, he₂, hv₂, hρ, -, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T₁ K
  obtain ⟨z₂, -, -, φ₂, hφ₂, hm₂⟩ :=
    (GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ T₁ T₂ io₁ z₁ i₂ e₂ he₂ hv₂).1
  letI b2 : Algebra dδ.c₂.F T₂.Fr := (i₂.comp io₁).toAlgebra
  obtain ⟨j, hj, hjv⟩ : ∃ j : T₂.Fr →+* k, (∀ x, j (i₂ x) = algebraMap T₁.Fr k x) ∧ ∀ t, ∃ u, j u = v t := by
    refine ⟨(algebraMap K k).comp ρ.symm.toRingHom, fun x => ?_, fun t =>
      ⟨ρ ⟨v t, IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩⟩, ?_⟩⟩
    · rw [← hρ]
      exact congrArg (algebraMap K k) (ρ.symm_apply_apply _)
    · exact congrArg (algebraMap K k) (ρ.symm_apply_apply _)
  choose u hu using hjv
  let χ : T₂.Fr →ₐ[dδ.c₂.F] k := { j with commutes' := fun x => hj (io₁ x) }
  have hχ : χ.comp φ₂ = ψ₂ := AlgHom.ext fun x => by
    show j (φ₂.toRingHom x) = algebraMap T₁.Fr k x
    rw [hφ₂, hj]
  have hm₃ : FrMap χ z₂.1 zk := GlobalTheory.FramedBaseChange.cancel φ₂ χ hm₂ (hχ ▸ hzk)
  have hv₀ : ∀ x : T.Fr, vV T₂.V ((i₂.comp i₁) x) = ((e₂ * e₁ : ℕ) : ℤ) * vV T.V x := fun x => by
    rw [RingHom.comp_apply, hv₂, hv₁]
    push_cast
    ring
  have he₀ : 0 < e₂ * e₁ := Nat.mul_pos he₂ he₁
  have hgood₂ : Good z₂ := by
    refine good_lift Xo.univ.t dδ.Xo₂.univ.t dδ.r dδ.m T T₂ (i₂.comp i₁) _ hv₀ y.1.x z₂.1.x ?_ hgood
    rw [hm₂.1, Category.assoc, hover.1, hm₁.1, hφ₁, hφ₂, ← Category.assoc, ← GlobalTheory.FramedBaseChange.spec_comp]
  have hint : ∀ x : c.F, la.valuation c.F x ≤ 1 → InV T₂ ((i₂.comp io₁) (dδ.eF x)) := fun x hx => by
    rw [RingHom.comp_apply, hio₁]
    exact (inV_map_iff (i₂.comp i₁) he₀ hv₀ _).2 (inV_of_overLa ho hx)
  have hth := fun t => GlobalTheory.T.shortThetaValue_bounded_goodReduction E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ dδ.nab₂ hnab T₂ (i₂.comp io₁) z₂ n d N La
    (fun q => dδ.eF (w t q)) (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) (u t) hgood₂ hun htr hN
    (fun q => hint _ (hw t q)) (ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map _ (hP t).1) ((hP t).2.1.map _)
    (fun q => by rw [coeff_map]; exact hint _ ((hP t).2.2 q))
    (shortValAt_of_map _ _ _ _ _ _ χ z₂.1 zk hm₃ (u t) (by
      have h := hv t
      rw [← hu t] at h
      exact h))
  have e1 : evR Xo c f yk = (ψ₁.comp φ₁) (evR Xo c f y.1) :=
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw l Xo c).2.2.1 f
      (cusp_le_sec Xo c U a n hf).1 _ y.1 y.2.1 yk (GlobalTheory.FramedBaseChange.trans φ₁ ψ₁ hm₁ hyk)
  have e2 : ∀ t, evR dδ.Xo₂ dδ.c₂ (cs t) zk = j (evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1) := fun t =>
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest
      (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂).2.2.1 (cs t) (hcs t).1.1 χ z₂.1
      z₂.2.1 zk hm₃
  have e3 : (i₂.comp i₁) (evI y f) = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1 * u t := by
    apply j.injective
    have e4 : j ((i₂.comp i₁) (evI y f)) = (ψ₁.comp φ₁) (evR Xo c f y.1) := by
      show j (i₂ (i₁ (evR Xo c f y.1))) = algebraMap T₁.Fr k (φ₁.toRingHom (evR Xo c f y.1))
      rw [hφ₁, hj]

    rw [e4, ← e1, hev, map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [map_mul, e2, hu]
  rw [← inV_map_iff (i₂.comp i₁) he₀ hv₀, map_mul, e3, Finset.mul_sum]
  refine sum_mem (S := (algebraMap T₂.V T₂.Fr).range) fun t _ => ?_
  have h1 : InV T₂ (evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1) :=
    inV_of_pow_eq T₂ he (by rw [← evR_pow_succ, (hcs t).2])
  have h2 := mul_mem h1 (hth t)
  rw [map_mul, map_natCast, map_pow, map_intCast, map_mul, map_natCast, map_pow, map_intCast, mul_left_comm]
  exact h2

end GlobalTheory.CoverBound
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.heckeChoice_flatVector_factoredForm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∃ (z : GA D (Vc D i)) (B : ℂ) (ε : ℤ) (r : ℕ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsCentAt i (R.Q t) z ∧ (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ B = B) ∧ (∀ PP ∈ R.Q t, (ψP PP).IsPrimitive) ∧ ∀ t' : T0, R.Q t' = R.Q t → ∀ f', IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, f' = (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε * ((R.xi t' s : Circle) : ℂ)) • R.ωP i t' (z, 1) (R.vP i t') := by
  first | exact @GlobalTheory.FlatConj.flatVec_factored_form | exact GlobalTheory.FlatConj.flatVec_factored_form | (intros; apply GlobalTheory.FlatConj.flatVec_factored_form <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain GlobalTheory.LocGL GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem good_loc_ofChar (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    UpperTheory.Zero.LLC.Good (⟨1, ParLaws.toCl ((CG.ofChar χ).loc w)⟩ : IrrGL (k := w.adicCompletion E)) := by
  have h : (⟨1, ParLaws.toCl ((CG.ofChar χ).loc w)⟩ : IrrGL (k := w.adicCompletion E)) =
      IrrGL.ofChar (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := ParLawsT.cls_loc_eq_of_isLocComp (CG.isLoc_ofChar χ w)
  rw [h]
  exact ⟨_, hasSupport_self (IrrGL.isCusp_ofChar _ _), fun y hy => Or.inl (by rw [Multiset.mem_singleton.1 hy]; rfl)⟩

theorem cls_loc_twist (π : CG E a) (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    (⟨a, ParLaws.toCl ((π.twist χ).loc w)⟩ : IrrGL (k := w.adicCompletion E)) =
      IrrGL.tw ⟨a, ParLaws.toCl (π.loc w)⟩ (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w
  refine (ParLawsT.cls_loc_eq_of_isLocComp (hσ.twist χ)).trans ?_
  rw [show (⟨a, ParLaws.toCl (CG.loc (Quotient.mk _ π) w)⟩ : IrrGL (k := w.adicCompletion E)) = _ from
    ParLawsT.cls_loc_eq_of_isLocComp hσ]
  exact (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm

end Loc

section Host
variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {a : ℕ}

theorem goodAll_one (χ : HostCGu H 1) : GoodAll χ := fun w => by
  haveI := host_isCMField H
  have h := good_loc_ofChar χ.1.toChar w
  rwa [CG.ofChar_toChar] at h

theorem goodAll_tw_iff (π : HostCGu H a) (χ : HostCGu H 1) :
    haveI := host_isCMField H; GoodAll (H := H) (π.tw χ) ↔ GoodAll π := by
  haveI := host_isCMField H
  refine forall_congr' fun w => ?_
  have h := cls_loc_twist π.1 χ.1.toChar w
  have h2 := GlobalTheory.RecT.good_tw_iff (⟨a, ParLaws.toCl (π.1.loc w)⟩ : IrrGL (k := w.adicCompletion H.E)) (χ.1.toChar.loc w)
    (ParLaws.isSmoothChar_loc _ w)
  rw [← h] at h2
  exact h2

end Host

section Char
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem locParT_unr (hT : UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (ParLawsT.locParT hT (CG.ofChar χ) h).unr ∧
      (ParLawsT.locParT hT (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨a, ha, H⟩ := ParLawsT.isRecT_locRecT hT h
  have e2 : ParLawsT.locParT hT (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [ParLawsT.locParT_ofChar_eq, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  exact ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), by simp⟩

end Char




def trueKT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLawsT.locGT hT D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLawsT.locGT hT D.nd.plOm η' w).unr ∧
      (ParLawsT.locGT hT D.nd.plOm η' w).frobEig = (ParLawsT.locGT hT D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ,
      (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {a} →
      (ParLawsT.locGT hT D.nd.plOm η w').frobEig = {b} → a * b = 1) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLawsT.lawsT hT GlobalTheory.automorphicFormsFiniteGL D.host D.nd.Om D.nd.plOm
  have U : ∀ {a} (π : HostCGu D.host a) w, D.naut.unr ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) ↔
      (ParLawsT.locGT hT D.nd.plOm π w).unr :=
    fun π w => by rw [T.unr, Equiv.apply_symm_apply]
  have Fr : ∀ {a} (π : HostCGu D.host a) w, (ParLawsT.locGT hT D.nd.plOm π w).unr →
      D.naut.frobEig ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) = (ParLawsT.locGT hT D.nd.plOm π w).frobEig :=
    fun π w h => by rw [T.frobEig _ _ ((U π w).2 h), Equiv.apply_symm_apply]
  have Dm : ∀ {a} (π : HostCGu D.host a) w, D.naut.lpDim ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) = a :=
    fun π w => by rw [← T.dim, Equiv.apply_symm_apply]; exact L.1 π w
  { CG := fun a => {π : HostCGu D.host a // 0 < a ∧ GoodAll π}
    csd := fun π => π.1.IsCsd
    ralg := fun π => π.1.IsRegAlg
    locG := fun π w => (T.e w).symm (ParLawsT.locGT hT D.nd.plOm π.1 w)
    locG_dim := fun π w => Dm π.1 w
    locG_unr_ae := fun π => (L.2.1 π.1).mono fun w h => (U π.1 w).2 h
    tw := fun π χ => ⟨π.1.tw χ.1, π.2.1, (goodAll_tw_iff π.1 χ.1).2 π.2.2⟩
    locG_tw := fun π χ w => (T.e w).injective (by
      rw [T.char _ _ _ (Dm χ.1 w), Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact L.2.2.1 π.1 χ.1 w (π.2.2 w))
    infG := fun π τ => π.1.infChar τ
    infG_card := fun π => L.2.2.2.1 π.1
    ralg_def := fun π => L.2.2.2.2.1 π.1
    infG_tw := fun π χ => L.2.2.2.2.2.1 π.1 χ.1
    csd_tw := fun π χ => L.2.2.2.2.2.2.1 π.1 χ.1
    csd_unr := fun π w w' hπ hc hu => by
      have h := L.2.2.2.2.2.2.2.1 π.1 w w' hπ hc ((U π.1 w).1 hu)
      exact ⟨(U π.1 w').2 h.1, by rw [Fr π.1 w' h.1, Fr π.1 w ((U π.1 w).1 hu)]; exact h.2⟩
    etaT := ⟨η, one_pos, goodAll_one η⟩
    etaTinv := ⟨η', one_pos, goodAll_one η'⟩
    etaT_unr := fun w => (U η w).2 (h1 w)
    etaT_inert := fun w h => by rw [Fr η w (h1 w)]; exact h2 w h
    etaTinv_def := fun w => ⟨(U η' w).2 (h3 w).1, by rw [Fr η' w (h3 w).1, Fr η w (h1 w)]; exact (h3 w).2⟩
    etaT_split := fun w w' hs hc a b ha hb => by
      rw [Fr η w (h1 w)] at ha; rw [Fr η w' (h1 w')] at hb; exact h4 w w' hs hc a b ha hb }




def trueCGT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' h1 h2 h3 h4) :
    CGTrueT hT (setCG D hE (trueKT hT D T η η' h1 h2 h3 h4)) (wdCG hE _ T) where
  e := fun _ => Function.Embedding.subtype _
  good := fun _ π => π.2.2
  surj := fun _ h π hπ => ⟨⟨π, h, hπ⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2.1⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl



theorem etaLawsT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) :
    haveI := host_isCMField D.host
    ∃ η η' : HostCGu D.host 1, η.1 = CG.ofChar χ ∧ η'.1 = CG.ofChar χ⁻¹ ∧
      (∀ w, (ParLawsT.locGT hT D.nd.plOm η w).unr) ∧
      (∀ w, ¬ IsSplitPl D.host w → (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {-1}) ∧
      (∀ w, (ParLawsT.locGT hT D.nd.plOm η' w).unr ∧
        (ParLawsT.locGT hT D.nd.plOm η' w).frobEig = (ParLawsT.locGT hT D.nd.plOm η w).frobEig.map (·⁻¹)) ∧
      (∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ,
        (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {a} →
        (ParLawsT.locGT hT D.nd.plOm η w').frobEig = {b} → a * b = 1) := by
  haveI := host_isCMField D.host
  have hi : (χ⁻¹).IsUnitary := fun x => by
    have := hχ.unitary x
    change ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, this, inv_one]
  have hu : ∀ w, (χ⁻¹).UnrAt w := fun w x hx => by
    have loc_inv : (χ⁻¹).loc w x = (χ.loc w x)⁻¹ := rfl
    rw [loc_inv, hχ.unr w x hx, inv_one]
  have P := fun w => locParT_unr hT χ (D.nd.plOm.2 w) (hχ.unr w)
  have Q := fun w => locParT_unr hT χ⁻¹ (D.nd.plOm.2 w) (hu w)
  refine ⟨⟨CG.ofChar χ, CG.isUnitary_ofChar hχ.unitary⟩, ⟨CG.ofChar χ⁻¹, CG.isUnitary_ofChar hi⟩, rfl, rfl,
    fun w => (P w).1, fun w hw => (P w).2.trans ?_, fun w => ⟨(Q w).1, (Q w).2.trans ?_⟩,
    fun w w' hw hc a b ha hb => ?_⟩
  · rw [CGTrueModel.val_inert hχ hw]; simp
  · refine Eq.trans ?_ (congrArg (Multiset.map (·⁻¹)) (P w).2).symm
    simp
  · have ha' := (P w).2.symm.trans ha
    have hb' := (P w').2.symm.trans hb
    rw [Multiset.singleton_inj] at ha' hb'
    rw [← ha', ← hb', ← Units.val_mul, ← mul_inv, CGTrueModel.val_split hχ hw hc, inv_one, Units.val_one]

end GlobalTheory.HeightCounting

end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem _root_.GlobalTheory.T.section_integral_equalChar_abelianLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, (letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) → evI y f ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.EqCharGood.inV_of_extIn_eqChar | exact GlobalTheory.EqCharGood.inV_of_extIn_eqChar | (intros; apply GlobalTheory.EqCharGood.inV_of_extIn_eqChar <;> assumption)
end
