module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle070
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle083
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle100
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle011
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle112
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem crisP_ker_dvd (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (x : Per.Acris l) (hx : j x = 0) : ∃ y : Per.Acris l, j y = 0 ∧ x = (l : Per.Acris l) * y := by
  obtain ⟨-, -, hd, hdv⟩ := acris_basic l
  obtain ⟨s, z, hs⟩ := hd x 1
  have h1 : (l : Per.Acris0 l) ∣ s := by
    refine GlobalTheory.T.acris_divisible_of_kernel_powers l s fun n => ?_
    obtain ⟨u, z', hu, e⟩ := GlobalTheory.T.acris_filtration_approx_by_envelope_kernel_power l j hj n x (by rw [hx]; exact zero_mem _)
    obtain ⟨w, hw⟩ := (hdv (s - u) 1).1 ⟨z' - z, by rw [map_sub]; linear_combination e - hs⟩
    exact ⟨u, w, by linear_combination hw, hu⟩
  obtain ⟨w, hw⟩ := h1
  have e : x = (l : Per.Acris l) * (algebraMap (Per.Acris0 l) (Per.Acris l) w + z) := by
    rw [hs, hw, map_mul, map_natCast]
    ring
  refine ⟨_, ?_, e⟩
  have hu : IsUnit (l : Per.BdRp l) := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))
    rwa [map_natCast] at this
  rw [e, map_mul, map_natCast] at hx
  exact hu.mul_right_eq_zero.1 hx

theorem crisP_injective : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Function.Injective j := by
  intro l _ j hj
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have h : ∀ n : ℕ, ∃ y : Per.Acris l, j y = 0 ∧ x = (l : Per.Acris l) ^ n * y := by
    intro n
    induction n with
    | zero => exact ⟨x, hx, by rw [pow_zero, one_mul]⟩
    | succ n ih =>
      obtain ⟨y, hy, e⟩ := ih
      obtain ⟨y', hy', e'⟩ := crisP_ker_dvd l j hj y hy
      exact ⟨y', hy', by rw [e, e', pow_succ, mul_assoc]⟩
  have hc := (acris_basic l).1
  refine hc.toIsHausdorff.haus x fun n => ?_
  obtain ⟨y, -, e⟩ := h n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨y, e⟩

end GlobalTheory.MemLoc
end

section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair GlobalTheory.IntTerm Formalism.BasicNotions IsDedekindDomain
open Formalism.MainNotions.S (FlagG XS ddS FrameOK)
open Formalism.MainNotions.S.Lat (LFlag hS Tu gS XLam IsFixedConv FixedHyp)
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm.Conv

section Ideals

variable {E : Type} [Field E] [NumberField E]

theorem exists_local_gen {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) :
    ∃ c : E, c ≠ 0 ∧ c ∈ I ∧ ∀ x ∈ I, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = o * c := by
  have int {a b : E} (ha : a ∈ I) (hb : b ∈ I⁻¹) : ∃ o : 𝓞 E, (o : E) = a * b := by
    have := FractionalIdeal.mul_mem_mul ha hb
    rw [mul_inv_cancel₀ hI] at this
    exact (FractionalIdeal.mem_one_iff _).1 this
  obtain ⟨a, ha, b, hb, s, hs, e⟩ : ∃ a ∈ I, ∃ b ∈ I⁻¹, ∃ s : 𝓞 E, s ∉ P ∧ (s : E) = a * b := by
    by_contra h
    have h1 : (1 : E) ∈ I * I⁻¹ := by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
    obtain ⟨s, hs, e⟩ := FractionalIdeal.mul_induction_on (C := fun x => ∃ s ∈ P, (s : E) = x) h1
      (fun a ha b hb => by
        obtain ⟨o, e⟩ := int ha hb
        exact ⟨o, by_contra fun k => h ⟨a, ha, b, hb, o, k, e⟩, e⟩)
      (fun _ _ ⟨s, hs, e⟩ ⟨t, ht, f⟩ => ⟨s + t, add_mem hs ht, by rw [← e, ← f]; simp⟩)
    obtain rfl : s = 1 := RingOfIntegers.ext e
    exact hP ((Ideal.eq_top_iff_one _).2 hs)
  refine ⟨a, fun h => hs ?_, ha, fun x hx => ⟨s, hs, ?_⟩⟩
  · obtain rfl : s = 0 := RingOfIntegers.ext (by rw [e, h, zero_mul]; rfl)
    exact zero_mem _
  · obtain ⟨o, f⟩ := int hx hb
    exact ⟨o, by rw [e, f]; ring⟩

theorem exists_gen_dInv (j : ℕ) (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    ∃ c : E, c ≠ 0 ∧ c ∈ dInv E j ∧ (¬ P ∣ differentIdeal ℤ (𝓞 E) → c = 1) ∧
      ∀ x ∈ dInv E j, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = o * c := by
  by_cases h : P ∣ differentIdeal ℤ (𝓞 E)
  · obtain ⟨c, h1, h2, h3⟩ := exists_local_gen (I := dInv E j)
      (fun e => by simpa [e] using Iota.one_mem_dInv (E := E) j) hP.ne_top
    exact ⟨c, h1, h2, fun k => absurd h k, h3⟩
  · obtain ⟨s, hs, hn⟩ := SetLike.not_le_iff_exists.1 (mt Ideal.dvd_iff_le.2 h)
    refine ⟨1, one_ne_zero, Iota.one_mem_dInv j, fun _ => rfl, fun x hx =>
      ⟨s ^ j, fun k => hn (hP.mem_of_pow_mem j k), ?_⟩⟩
    have h0 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
    have := FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ (P := E) (Ideal.pow_mem_pow hs j)) hx
    rw [FractionalIdeal.coeIdeal_pow, dInv, ← mul_pow, mul_inv_cancel₀ h0, one_pow] at this
    obtain ⟨o, e⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨o, by rw [mul_one]; exact e.symm⟩

theorem not_dvd_different {p : ℕ} (hp : p.Prime) (h : (placesOver E p).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hm : (p : 𝓞 E) ∈ P) : ¬ P ∣ differentIdeal ℤ (𝓞 E) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp'.irreducible
  have e : HeightOneSpectrum.asIdeal '' placesOver E p = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext Q
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := v.isPrime
      exact ⟨v.isPrime, (Ideal.liesOver_span_iff v.isPrime.ne_top hp').2 (by simpa [placesOver] using hv)⟩
    · rintro ⟨h1, h2⟩
      have k : (p : 𝓞 E) ∈ Q := by simpa using (Ideal.liesOver_span_iff h1.ne_top hp').1 h2
      exact ⟨⟨Q, h1, fun e => hp.ne_zero (by simpa [e] using k)⟩, k, rfl⟩
  have hd := GlobalTheory.SplitEmbSep.not_dvd_discr_of_split hp E (by
    rw [← e, Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw, h])
  exact not_dvd_differentIdeal_iff.2 ((not_dvd_discr_iff_forall_mem E (𝓞 E) hp').1 hd P hP (by simpa using hm))

end Ideals

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
  {Λ : Submodule (𝓞 E) (Fin S.rank → E)} {F : LFlag S r T}

variable (h : IntFrame (starRingEnd E) S.gram T Λ (coMat S (Formalism.MainNotions.S.Lat.frame F)))
include h

end Space

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ddS_eq : ddS D = (differentIdeal ℤ (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) := by
  rw [ddS, differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.F) (𝓞 D.host.E),
    GlobalTheory.CMDiscrSq.differentIdeal_eq_top D.sp.cm, Ideal.top_mul]

theorem level_not_dvd (P : HeightOneSpectrum (𝓞 D.host.E)) (h : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.E) := by
  have := P.isPrime
  rw [gS, Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact not_dvd_different (D.host.g_prime 0) (D.nd.g_split 0) _ h
  · exact not_dvd_different (D.host.g_prime 1) (D.nd.g_split 1) _ h

variable {D}

end Record

end GlobalTheory.IntTerm.Conv
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.StdProp

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_sigR [TopologicalSpace R] [IsTopologicalRing R] : Continuous (sigR R σ) := by
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  exact this

theorem continuous_qR [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 := continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem measurableSet_fibre [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [SecondCountableTopology R] (c : R) :
    MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E | qR R σ J (X 0) = c} :=
  (isClosed_eq (continuous_qR R σ J) continuous_const).measurableSet

omit [FiniteDimensional F E] in
theorem smul_eq_lrAct {n : ℕ} (g : HA R σ J) :
    (fun X : Fin n → Fin M → R ⊗[F] E => g • X) = lrAct (HA.mat R σ J g).val 1 := by
  funext X a
  show (HA.mat R σ J g).val.mulVec (X a) = _
  simp [lrAct, Matrix.one_apply]

end Local

theorem stdX_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → IsStdX s σ J β ν → ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 ∧ IsInvTup (AF F) σ J ν ∧ OnOrbit (AF F) σ J x ν ∧ IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM d b s M J x β ν hJ hβ hx ⟨mi, mv, hi, hv, hP⟩
  obtain ⟨nI, nV⟩ := nice_ainf_fv F
  obtain ⟨qloc, gloc⟩ := q_and_unitary_local_components F E σ M J
  have hβu : IsUnit β := Ne.isUnit hβ
  have bI := GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ (Ainf F) nI M J _ _ _ mi s.haar_nuI (hβu.map _) hi
  have bV := fun v => GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ (Fv F v) (nV v) M J _ _ _ (mv v) (s.haar_nuV v)
    (hβu.map _) (hv v)
  have pI := GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Ainf F) nI M J x β _ _ mi hJ hβ hx s.haar_lamI s.haar_nuI hi
  have pV := fun v => GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Fv F v) (nV v) M J x β _ _ (mv v) hJ hβ hx
    (s.haar_lamV v) (s.haar_nuV v) (hv v)
  obtain ⟨hfin, hne, huniq, hsupp⟩ := GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 M ν mi mv hP
  have h1 : ν {X | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} = 0 := by
    have := hsupp {X | qR (Ainf F) σ J (X 0) = algebraMap F _ β}
      (fun v => {X | qR (Fv F v) σ J (X 0) = algebraMap F _ β})
      (measurableSet_fibre _ σ J _) (fun v => measurableSet_fibre _ σ J _) bI.1 (fun v => (bV v).1)
    refine measure_mono_null (fun X hX => ?_) this
    exact fun h => hX ((qloc (X 0) β).2 h)
  refine ⟨h1, ?_, ?_, hfin, hne pI.2.2 fun v => (pV v).2.2⟩
  · intro g
    obtain ⟨⟨gi, hgi⟩, hgv⟩ := gloc g
    have hT := GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction F E d b 1 M ν mi mv (HA.mat (AF F) σ J g) 1 hP
    have e1 : mi.map (lrAct ((HA.mat (AF F) σ J g).val.map prInf)
        ((1 : GL (Fin 1) (AF F ⊗[F] E)).val.map prInf)) = mi := by
      rw [← hgi, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), ← smul_eq_lrAct]
      exact pI.1 gi
    have e2 : (fun v => (mv v).map (lrAct ((HA.mat (AF F) σ J g).val.map (prV v))
        ((1 : GL (Fin 1) (AF F ⊗[F] E)).val.map (prV v)))) = mv := by
      funext v
      obtain ⟨gv, hgv⟩ := hgv v
      rw [← hgv, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), ← smul_eq_lrAct]
      exact (pV v).1 gv
    rw [e1, e2, Units.val_one, ← smul_eq_lrAct] at hT
    exact huniq _ hT
  · refine measure_mono_null (fun X hX => ?_) h1
    exact fun h => hX (GlobalTheory.T.witt_theorem_adelic_one_vector F E σ hCM M J x β hJ hβ hx X h)

end GlobalTheory.GaugeEx.StdProp
end

section

open CategoryTheory Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.LabelUniqueAll

open Finset

theorem esymm_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k, 1 ≤ k → k ≤ d → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    ∀ k, k ≤ d → MvPolynomial.aeval a (MvPolynomial.esymm (Fin d) ℂ k) =
      MvPolynomial.aeval b (MvPolynomial.esymm (Fin d) ℂ k) := by
  first
  | exact @_root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq
  | exact _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq
  | (apply _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EsymmOfPowerSums.esymm_eq_of_psum_eq ..)

theorem map_eq_of_psum_eq {d : ℕ} (a b : Fin d → ℂ)
    (h : ∀ k, 1 ≤ k → k ≤ d → ∑ i, a i ^ k = ∑ i, b i ^ k) :
    Finset.univ.val.map a = Finset.univ.val.map b := by
  have he := esymm_eq_of_psum_eq a b h
  have hp : ((Finset.univ.val.map a).map fun t => X - C t).prod =
      ((Finset.univ.val.map b).map fun t => X - C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin d) (R := ℂ), ← MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin d) (R := ℂ),
      he j (by simpa [Nat.lt_succ_iff] using hj)]
  have := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this
  exact this

theorem two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]; omega

variable {g : ℕ} [Fact g.Prime]

theorem natDegree_minpoly_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {k : ℕ} (hk1 : 1 ≤ k)
    (hkd : k ≤ d) : (minpoly (ZMod g) (L.gen d ^ k)).natDegree = d := by
  set γ := L.gen d
  set m := g ^ d - 1 with hmdef
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgd : 2 ≤ g ^ d := le_trans hg2 (Nat.le_self_pow hd.ne' g)
  have hord : orderOf γ = m := L.gen_order d hd
  have hγm : γ ^ m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hγ0 : γ ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega)] at hγm; exact zero_ne_one hγm
  have hfix : (γ ^ k) ^ (g ^ d) = γ ^ k := by
    rw [← pow_mul, mul_comm, pow_mul, show g ^ d = m + 1 by omega, pow_succ, hγm, one_mul]
  have hdvd : (minpoly (ZMod g) (γ ^ k)).natDegree ∣ d :=
    (GlobalTheory.GLm.SubfieldCount.natDegree_dvd_iff _ d).2 hfix
  have hfe : (γ ^ k) ^ (g ^ (minpoly (ZMod g) (γ ^ k)).natDegree) = γ ^ k :=
    (GlobalTheory.GLm.SubfieldCount.natDegree_dvd_iff _ _).1 dvd_rfl
  have he0 : 0 < (minpoly (ZMod g) (γ ^ k)).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _)
  generalize (minpoly (ZMod g) (γ ^ k)).natDegree = e at hdvd hfe he0 ⊢
  by_contra hne
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hc; omega
    · simp at hc; omega
    · omega
  have hge : 2 ≤ g ^ e := le_trans hg2 (Nat.le_self_pow he0.ne' g)
  have hone : γ ^ (k * (g ^ e - 1)) = 1 := by
    have : γ ^ k * γ ^ (k * (g ^ e - 1)) = γ ^ k * 1 := by
      rw [mul_one, ← pow_add]
      conv_rhs => rw [← hfe, ← pow_mul]
      congr 1
      have : g ^ e = (g ^ e - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring
    exact mul_left_cancel₀ (pow_ne_zero _ hγ0) this
  have hmd : m ∣ k * (g ^ e - 1) := hord ▸ orderOf_dvd_of_pow_eq_one hone
  have hpos : 0 < k * (g ^ e - 1) := Nat.mul_pos (by omega) (by omega)
  have hle := Nat.le_of_dvd hpos hmd
  have hec : e * 2 ≤ e * c := Nat.mul_le_mul_left e hc2
  have h2 : d ≤ 2 * (d - e) := by omega
  have h3 : 2 * (d - e) ≤ 2 ^ (d - e) := two_mul_le_two_pow _
  have h4 : 2 ^ (d - e) ≤ g ^ (d - e) := Nat.pow_le_pow_left hg2 _
  have h5 : d * g ^ e ≤ g ^ d := by
    calc d * g ^ e ≤ g ^ (d - e) * g ^ e := Nat.mul_le_mul_right _ (by omega)
      _ = g ^ d := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have h6 : k * (g ^ e - 1) ≤ d * (g ^ e - 1) := Nat.mul_le_mul_right _ hkd
  have h7 : d * (g ^ e - 1) = d * g ^ e - d := Nat.mul_sub_one _ _
  omega

theorem label_eq (L : LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : Gn g d → ℂ)
    (h : IsCuspOf L P χ) (h' : IsCuspOf L P' χ) : P = P' := by
  obtain ⟨hPl, hc, hval⟩ := h
  obtain ⟨hPl', -, hval'⟩ := h'
  have hd : 0 < d := hc.1
  obtain ⟨x, hx⟩ := LabelUnique.exists_mem hd hPl
  obtain ⟨x', hx'⟩ := LabelUnique.exists_mem hd hPl'
  have hx1 := LabelUnique.pow_sub_one_eq_one hPl hx
  have hx1' := LabelUnique.pow_sub_one_eq_one hPl' hx'
  have hteich : ∀ w : Formalism.CyclotomicNorms.Fbar g, w ^ (g ^ d - 1) = 1 → L.teich w ^ (g ^ d - 1) = 1 := fun w hw => by
    rw [← map_pow, hw, map_one]
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgd : 2 ≤ g ^ d := le_trans hg2 (Nat.le_self_pow hd.ne' g)
  have hγ0 : L.gen d ≠ 0 := by
    have hγm : L.gen d ^ (g ^ d - 1) = 1 := by rw [← L.gen_order d hd]; exact pow_orderOf_eq_one _
    intro h0; rw [h0, zero_pow (by omega)] at hγm; exact zero_ne_one hγm
  have hsums : ∀ k, 1 ≤ k → k ≤ d → ∑ i : Fin d, L.teich (x ^ (g ^ (i : ℕ))) ^ k =
      ∑ i : Fin d, L.teich (x' ^ (g ^ (i : ℕ))) ^ k := by
    intro k hk1 hkd
    have hdeg := natDegree_minpoly_gen_pow L hd hk1 hkd
    obtain ⟨y, hy, hz⟩ := GlobalTheory.GLm.exists_irreducible_charpoly_mem_rootsBar g d (L.gen d ^ k)
      (pow_ne_zero _ hγ0) hdeg
    have e1 := hval x hx y hy _ hz
    have e2 := hval' x' hx' y hy _ hz
    rw [e1] at e2
    have e3 := mul_left_cancel₀ (pow_ne_zero (d - 1) (by norm_num : (-1 : ℂ) ≠ 0)) e2
    have conv : ∀ w : Formalism.CyclotomicNorms.Fbar g, w ^ (g ^ d - 1) = 1 → ∀ i : ℕ,
        thetaOf L d w ((L.gen d ^ k) ^ (g ^ i)) = L.teich (w ^ (g ^ i)) ^ k := by
      intro w hw i
      rw [← pow_mul, LabelUnique.thetaOf_gen_pow L d hd w (hteich w hw), map_pow, ← pow_mul,
        Nat.mul_comm]
    simp only [conv x hx1, conv x' hx1'] at e3
    rw [Fin.sum_univ_eq_sum_range (fun i => L.teich (x ^ g ^ i) ^ k),
      Fin.sum_univ_eq_sum_range (fun i => L.teich (x' ^ g ^ i) ^ k)]
    exact e3
  have hm := map_eq_of_psum_eq _ _ hsums
  have hmem : L.teich x ∈ Finset.univ.val.map (fun i : Fin d => L.teich (x ^ (g ^ (i : ℕ)))) :=
    Multiset.mem_map.2 ⟨⟨0, hd⟩, Finset.mem_univ_val _, by simp⟩
  rw [hm] at hmem
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  have hxe : x = x' ^ (g ^ (i : ℕ)) :=
    L.teich_inj _ _ (LabelUnique.ne_zero_of_mem hPl hx)
      (pow_ne_zero _ (LabelUnique.ne_zero_of_mem hPl' hx')) hi.symm
  have h1 : aeval x P' = 0 := by
    rw [hxe]; exact LabelUnique.aeval_pow_eq_zero (LabelUnique.aeval_eq_zero_of_mem hPl'.1.ne_zero hx') i
  have h2 := minpoly.eq_of_irreducible_of_monic hPl'.2.1 h1 hPl'.1
  rw [h2, LabelUnique.minpoly_eq_of_mem hPl hx]

end GlobalTheory.GLq.LabelUniqueAll

namespace GlobalTheory.GLq

theorem isCuspOf_label_unique_allPrimes : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime]
    (L : GlobalTheory.GLq.LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : GlobalTheory.GLq.Gn g d → ℂ),
    GlobalTheory.GLq.IsCuspOf L P χ → GlobalTheory.GLq.IsCuspOf L P' χ → P = P' :=
  fun _ _ _ L d P P' χ h h' => LabelUniqueAll.label_eq L d P P' χ h h'

end GlobalTheory.GLq
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (τ : L →+* ℂ), (∃! lam, a.HWAt τ lam) ∧ ∀ lam, a.HWAt τ lam → Antitone lam := by
  first | exact @GlobalTheory.AlgWtHW.hw_exists_unique_antitone | exact GlobalTheory.AlgWtHW.hw_exists_unique_antitone | (intros; apply GlobalTheory.AlgWtHW.hw_exists_unique_antitone <;> assumption)
end
