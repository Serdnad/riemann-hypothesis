module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle057
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle061
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle062
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.IneInf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.UfFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ConstOfChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FrameClassOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GaussianFieldRangeEqKerQuarticChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPtOfIsPtHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle012
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle049
import GroundTheory.ProfiniteCohomology.ClassFormations.Corestriction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle012

@[expose] public section

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Af
open UpperTheory.V.Published
structure HypothesesH' : Prop extends toClassicalTheorems : _root_.UpperTheory.V.Af.Hypotheses' where
  descU : Z.Desc.DescWeak
  cyc : Z.Bc.CycC
  cyc2 : Z.Bc.Desc2
  quat : DefQuatExists
  ssR : CuspSemisimpleReal
def AutBridgeAlt : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)),
    (∀ [IsTotallyReal F], IsAut ι r ↔ IsAutR ι r) ∧
    (∀ [_root_.NumberField.IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π) ∧
    ∀ [IsCMField F], _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r → IsAut ι r
section Ver
variable {F L Ω : Type} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]
  {C : Type} [CommGroup C]
end Ver
section Compat
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
end Compat
end UpperTheory.V.Af
end
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
private theorem under_cPl {K : Type} [Field K] [NumberField K] [IsCMField K] (w : HeightOneSpectrum (𝓞 K)) :
    (cPl w).under (𝓞 ℚ) = w.under (𝓞 ℚ) := by
  have e : (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj K).toRingEquiv) :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  change x ∈ (cPl w).asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) ↔ x ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
  have e2 : RingOfIntegers.mapRingEquiv (IsCMField.complexConj K).toRingEquiv (algebraMap (𝓞 ℚ) (𝓞 K) x) =
      algebraMap (𝓞 ℚ) (𝓞 K) x :=
    RingOfIntegers.ext (map_ratCast (IsCMField.complexConj K) (x : ℚ))
  rw [e, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, e2]
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Z.Bc.polarization_k_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → PolK := by
  intro hP K _ _ _ hK n hn l _ Ω _ _ _ _ _ ι r wt θ P hθ hd hC
  have h5 : NormGal := UpperTheory.galois_norm_compatibility_of_frobenius_restriction UpperTheory.frobenius_power_compatibility (UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility)
  have h8 : PolOfSat := UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse
  haveI : IsScalarTower ℚ (maximalRealSubfield K) Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  haveI : IsGalois ℚ K := inferInstance
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans ℚ K Ω⟩
  have hθ' : IsCycWt l (wt + ((n : ℤ) - 1))
      (θ.comp (res ℚ Ω (maximalRealSubfield K)) * cycBar (maximalRealSubfield K) Ω l ^ ((n : ℤ) - 1)) := by
    obtain ⟨M, χ, hM, hχ, rfl⟩ := hθ
    refine ⟨M, χ.comp (res ℚ Ω (maximalRealSubfield K)), hM, fun s hs => hχ _ hs, ?_⟩
    rw [zpow_add, mul_right_comm]
    rfl
  obtain ⟨hc, χ, art, a, ha⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic hP.litN.aut.art _ Ω l ι _ _ hθ'
  have hL : IsLAdicCharOf ι χ _ := ⟨hc, art, a, ha⟩
  obtain ⟨χ', μ', hL', hN, hres, hs⟩ := UpperTheory.heckeChar_sign_fixed K Ω hK l ι χ _ hL n
  have hres' : μ'.comp (res (maximalRealSubfield K) Ω K) = θ.comp (res ℚ Ω K) * cycBar K Ω l ^ ((n : ℤ) - 1) :=
    hres.trans rfl
  refine ⟨χ', μ', ⟨hs, h8 hP.litN.aut.js.1 hP.litN.aut.gk K n hn P _ ?_⟩, hL', hres'⟩
  have hd' : DualTw (r.comp (res ℚ Ω K)) (θ.comp (res ℚ Ω K)) := let ⟨Q, hQ⟩ := hd; ⟨Q, fun s => hQ _⟩
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hI := UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic UpperTheory.frobenius_conj_of_galois_conjugate_places UpperTheory.hecke_eigenvalue_basic_properties ℚ K Ω l ι n r _ hC
  filter_upwards [h5 K Ω l ι χ' μ' hL', hI, hC.2, hl] with w ⟨hu, he⟩ h3 ⟨B₁, hB₁, hF⟩ hw
  obtain ⟨B, hB, hB'⟩ := h3 (cPl w) (under_cPl w)
  obtain rfl := hB.unique hB₁
  rw [hres'] at he
  exact ⟨hu, B, B, hB, hB', UpperTheory.frobenius_eigenvalues_dual K Ω l ι n _ _ hd' w hw B _ hF he⟩
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.Ga
private theorem cyc_eq_of_pow {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal)
    (h : IsPlaceOver A w) {σ : G L Ω} {q : ℕ}
    (hσ : ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) :
    (cycBar L Ω l σ : Qbar l) = (q : Qbar l) := by
  have h1 : ((cycZ L Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (q : ℤ_[l]) :=
    PadicInt.ext_of_toZModPow.mp (cycZ_toZModPow_eq hl h hσ)
  simp [cycBar, h1]
end UpperTheory.V.Z.Sym.Ga
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Z.Sym.Ga.cyc_char_eq_abs_pow_and_norm_pow_deg_away_l :
    _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ s : Weil h, ι (Ga.ep l (s : G L Ω)) = (absPow (w.adicCompletion L) 1 (a s) : ℂ) ∧ ι (Ga.ep l (s : G L Ω)) = ((normV w : ℕ) : ℂ) ^ deg s := by
  intro _ L Ω _ _ _ _ _ l _ ι w hl A h a ha s
  have hfrob : (cycBar L Ω l ((frob h : Weil h) : G L Ω) : Qbar l) = ((normV w : ℕ) : Qbar l) :=
    Ga.cyc_eq_of_pow hl h (isFrob_frob (h := h)).2
  set t : Weil h := s * (frob h) ^ (-deg s) with ht
  have hdt : deg t = 0 := by
    rw [ht, deg_mul, deg_zpow, deg_frob]
    ring
  have hI : (t : G L Ω) ∈ Ine (F := L) A :=
    actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hdt))
  have hine : (cycBar L Ω l (t : G L Ω) : Qbar l) = 1 := by
    have := Ga.cyc_eq_of_pow (σ := (t : G L Ω)) (q := 1) hl h (fun x hx => by simpa using hI.2 x hx)
    simpa using this
  have hs : s = t * (frob h) ^ (deg s) := by
    rw [ht, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hε : Ga.ep l (s : G L Ω) = ((normV w : ℕ) : Qbar l) ^ deg s := by
    show (cycBar L Ω l (s : G L Ω) : Qbar l) = _
    conv_lhs => rw [hs]
    rw [Subgroup.coe_mul, map_mul, Units.val_mul, hine, one_mul, Subgroup.coe_zpow, map_zpow,
      Units.val_zpow_eq_zpow_val, hfrob]
  have hq : ι (Ga.ep l (s : G L Ω)) = ((normV w : ℕ) : ℂ) ^ deg s := by
    rw [hε, map_zpow₀, map_natCast]
  refine ⟨?_, hq⟩
  have := DFunLike.congr_fun (ha.absPow_comp 1) s
  rw [Complex.ofReal_one] at this
  rw [hq, ← MonoidHom.comp_apply, this, GlobalTheory.WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val]
  simp
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem regElt_place {Ω : Type} [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  have hI : Ideal.span {((p : ℕ) : (Int.castRingHom Ω).range)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨_, c, rfl⟩, hc⟩
    have h1 : ((p : ℕ) : Ω) * ((c : ℤ) : Ω) = 1 := congrArg Subtype.val hc
    have h2 : ((p : ℕ) : ℤ) * c = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
    exact hp.one_lt.ne' (by exact_mod_cast h3)
  obtain ⟨A, -, hA⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨A, A.mem_nonunits_iff.1 (hA ⟨((p : ℕ) : (Int.castRingHom Ω).range), Ideal.mem_span_singleton_self _, by simp⟩)⟩
private theorem regElt_zpow_ne {G : Type} [Group G] (e : G) (he : ¬ IsOfFinOrder e) (n : ℤ) (hn : 0 < n) : e ^ n ≠ 1 := by
  intro h
  refine he (isOfFinOrder_iff_pow_eq_one.2 ⟨n.toNat, by omega, ?_⟩)
  rw [← zpow_natCast, Int.toNat_of_nonneg hn.le, h]
private theorem regElt_key {K : Type} [Field K] (e x : Kˣ) (m k : ℕ) (hm : 2 ≤ m) (hk : 0 < k)
    (hx : x ^ k = (e ^ (m : ℤ)) ^ k) (he : ¬ IsOfFinOrder e) :
    ¬ IsOfFinOrder x ∧ ∀ i : ℤ, |i| ≤ 2 →
      ((x : K) + ((x⁻¹ : Kˣ) : K)) ^ 2 - 2 ≠ (e : K) ^ i + (e : K) ^ (-i) := by
  have hsq : ∀ j : ℤ, |j| ≤ 2 → x ^ 2 ≠ e ^ j := by
    intro j hj h
    have hj' := (abs_le.1 hj).2
    have hpos : 0 < (2 * (m : ℤ) - j) * (k : ℤ) := by
      have : (0 : ℤ) < k := by exact_mod_cast hk
      have : (2 : ℤ) ≤ m := by exact_mod_cast hm
      apply mul_pos <;> omega
    refine regElt_zpow_ne e he _ hpos ?_
    have h1 : (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k = (e ^ j) ^ k := by
      rw [← hx, ← h, ← pow_add, ← pow_mul, two_mul]
    have h2 : e ^ ((2 * (m : ℤ) - j) * (k : ℤ)) = (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k * ((e ^ j) ^ k)⁻¹ := by
      simp only [← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    rw [h2, h1, mul_inv_cancel]
  refine ⟨fun hf => ?_, fun i hi h => ?_⟩
  · obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    have hpos : 0 < (m : ℤ) * k * n := by
      have a : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
      have b : (0 : ℤ) < k := by exact_mod_cast hk
      have c : (0 : ℤ) < n := by exact_mod_cast hn
      positivity
    refine regElt_zpow_ne e he _ hpos ?_
    rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← hx, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  · have hx0 : (x : K) ≠ 0 := x.ne_zero
    have hE0 : ((e : K) ^ i) ≠ 0 := zpow_ne_zero _ e.ne_zero
    have hz : ((x : K) ^ 2 - (e : K) ^ i) * ((x : K) ^ 2 - ((e : K) ^ i)⁻¹) = 0 := by
      rw [Units.val_inv_eq_inv_val, zpow_neg] at h
      field_simp at h ⊢
      linear_combination (exp := 1) h
    rcases mul_eq_zero.1 hz with h0 | h0
    · refine hsq i hi (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
      exact sub_eq_zero.1 h0
    · refine hsq (-i) (by rwa [abs_neg]) (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, zpow_neg]
      exact sub_eq_zero.1 h0
theorem UpperTheory.V.Z.Sym.Ga.exists_regular_elt_in_open_subgroup_infinite_order :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)), _root_.UpperTheory.V.Z.Sym.AdInAlt ι M m r → ∀ H : Subgroup (G L Ω), IsOpen (H : Set (G L Ω)) → ∃ s ∈ H, s ∉ Ga.Bad r ∧ ∃ a b : (Qbar l)ˣ, ¬ IsOfFinOrder (a / b) ∧ (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l)) := by
  intro L Ω _ _ _ _ _ _ l _ ι M m r hr H hH
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨A, hA⟩ := regElt_place (Ω := Ω) l (Fact.out)
  obtain ⟨b0, k, κ, hk, ⟨g, hg⟩, hκ⟩ := hr.above A hA
  obtain ⟨s, hsH, hsI, hinf⟩ := UpperTheory.V.Z.Sym.Ga.ineInf L Ω l A hA H hH
  let t : ↥(Dec (F := L) A) := ⟨s, Ine_le_Dec A hsI⟩
  obtain ⟨h0, h1⟩ := hκ t hsI
  have hcp : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C ((κ 0 t : (Qbar l)ˣ) : Qbar l)) * (X - C ((κ 1 t : (Qbar l)ˣ) : Qbar l)) := by
    have e : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
        (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj g _
    rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (hg t).1 i j hij), Fin.prod_univ_two]
    have e0 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((κ 0 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 0
    have e1 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = ((κ 1 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 1
    rw [e0, e1]
  have hx : (κ 0 t / κ 1 t) ^ k = (cycBar L Ω l s ^ (m : ℤ)) ^ k := by
    rw [div_pow, h0, h1, zpow_add, mul_pow]
    exact mul_div_cancel_left _ _
  have key := regElt_key (cycBar L Ω l s) (κ 0 t / κ 1 t) m k hr.gap hk hx hinf
  refine ⟨s, hsH, ?_, κ 0 t, κ 1 t, key.1, hcp⟩
  rintro ⟨i, hi, hb⟩
  have huf := (UpperTheory.V.Z.Sym.Ga.ufFacts _ (r s)).1 _ _ hcp
  rw [huf] at hb
  exact key.2 i hi hb
end
end
end

section




section
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete
  UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
private theorem tw_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (χ : Γ →* kˣ)
    (h : Af.RepIso r r') : Af.RepIso (Af.tw r χ) (Af.tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul, Matrix.mul_smul,
    Matrix.smul_mul]
private theorem conj_left {G R : Type} [Group G] [CommRing R]
    (r : G →* GG (m := 3) (R := R)) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  have e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by
    rw [map_inv]; rfl
  rw [e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
    SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]
open Matrix in
private theorem matIrr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ} {U : Subgroup G}
    {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R)
    (e : ∀ g ∈ U, a g = ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * a' g * h) (H : MatIrr U a) :
    MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj h e H
private theorem tri_of_char {O G A : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [Group G]
    [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra O A] (h2 : IsUnit (2 : O))
    (h0 : ∀ a ∈ maximalIdeal O, algebraMap O A a = 0) {η : G →* ℤˣ} {Ψ : G →* Oˣ} {c g₁ : G} (hM : Marks η Ψ c g₁)
    {r : G →* GG (m := 3) (R := A)} (hr : UnitaryThreeInertia.Red η Ψ r) (hN : Normalised c g₁ r)
    (U : Subgroup G) (hU : U.FiniteIndex)
    (hch : ∀ g ∈ U, η g = 1 → (r g).mat.charpoly = (((r0 η Ψ g).mat).map (algebraMap O A)).charpoly) :
    Upper η r ∨ Lower η r := by
  letI : Algebra (ResidueField O) A := (Ideal.Quotient.lift _ (algebraMap O A) h0).toAlgebra
  let Φ : G →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp Ψ
  have e : ∀ g, ((r0 η Φ g).mat).map (algebraMap (ResidueField O) A) = ((r0 η Ψ g).mat).map (algebraMap O A) := by
    intro g
    rw [GG.mat, GG.mat, unitaryThreeReflection_left, unitaryThreeReflection_left, tor_val, tor_val, Matrix.diagonal_map (map_zero _),
      Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    rw [show Φ g ^ wt1 i = Units.map (residue O).toMonoidHom (Ψ g ^ wt1 i) from
      (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) _).symm]
    rfl
  refine (constOfChar G (ResidueField O) A ?_ η Φ c g₁ ⟨hM.csq, hM.ηc, ?_, hM.ηg, ?_⟩ r hr.mult
    (fun g => ?_) hN U hU fun g hg hη => ?_).1
  · simpa [map_ofNat] using (h2.map (residue O)).ne_zero
  · show Units.map _ (Ψ c) = 1
    rw [hM.Ψc, map_one]
  · have := hM.Ψg.map (residue O)
    rwa [map_sub, map_pow, map_one] at this
  · rw [e]; exact hr.red g
  · rw [e]; exact hch g hg hη
theorem UpperTheory.V.Pr.symmetric_cube_theorem_of_endomorphisms_alt :
    _root_.UpperTheory.V.Pr.HostEndAlt → _root_.UpperTheory.V.Aut.ThmS6Core_s := by
  intro H K _ _ _ hK Ω _ _ _ l _ ι c N _ e ψ o₁ hd S A F hF
  obtain ⟨σ, hσ, hc⟩ := hF.cc
  have hv : (A F.vl).valuation (l : Ω) < 1 := by simpa using (hF.isOver F.vl (l : 𝓞 ℚ)).2 hF.vl
  obtain ⟨g₁, hM, ⟨U, hU, hfin⟩, haut⟩ := H K hK Ω l ι c N e ψ o₁ hd σ hσ (A F.vl) hv
  have hη : ∀ g, F.η (toGS Ω _ g) = UnitaryThreeInertia.eta4 Ω g := fun g => by rw [← hF.η, hF.π]; rfl
  have hΨ : ∀ g, F.Ψ (toGS Ω _ g) = Chr.Psi l e (Chr.dirG ℚ Ω ψ) g := fun g => by rw [← hF.Ψ, hF.π]; rfl
  rw [hF.π] at hc
  have hg : F.Marked (toGS Ω _ g₁) := ⟨(hη g₁).trans hM.ηg, by rw [hΨ]; exact hM.Ψg⟩
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hcl := isClosed_NS Ω (S : Set UnitaryThreeInertia.Pl)
  haveI : CompactSpace (UnitaryThreeInertia.Gam Ω S) := inferInstance
  haveI : T2Space (UnitaryThreeInertia.Gam Ω S) := inferInstance
  haveI : TotallyDisconnectedSpace (UnitaryThreeInertia.Gam Ω S) := totDisc_quot _ hcl
  have hOk := UnitaryThreeInertia.hostFrame_ok Ω c e ψ o₁ hd S A F hF
  have hsurj : ∀ x : UnitaryThreeInertia.Gam Ω S, ∃ s, toGS Ω _ s = x := fun x => QuotientGroup.mk_surjective x
  refine ⟨_, hg, fun R _ _ _ u hu => ?_⟩
  have hM2 : Module.Finite c.O (UnitaryThreeInertia.wpart c.O u 0) := by
    refine UnitaryThreeInertia.universal_diagonal_of_triangular_points F hOk (UnitaryThreeInertia.frame_class_one Ω c e ψ o₁ hd S A F hF) _ hg u hu fun B _ _ hB h0 r hr => ?_
    haveI := hB.toIsDomain
    haveI := hB.toIsDiscreteValuationRing
    have ho := ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g₁ hc r hr
    refine (tri_of_char hOk.two h0 hM ho.red ho.norm U hU (hfin B h0 _ ho)).imp (fun h g hg => ?_) fun h g hg => ?_
    · obtain ⟨s, rfl⟩ := hsurj g
      exact h s ((hη s).symm.trans hg)
    · obtain ⟨s, rfl⟩ := hsurj g
      exact h s ((hη s).symm.trans hg)
  refine ⟨hM2, fun ξ r h1 h2 => ?_⟩
  have hz : F.IsCharZeroPt _ r := UnitaryThreeInertia.isCharZeroPt_of_isPtHom (l := l) F hOk _ hg u hu hM2 ξ r h1
  have hirr := UnitaryThreeInertia.matIrr_open Ω c e ψ o₁ hd S A F hF _ hg r hz h2
  obtain ⟨B, _, _, t, r', hr', ht⟩ := hz
  have ho := ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g₁ hc r' hr'
  have hm : ∀ s, (r (toGS Ω _ s)).right = UnitaryThreeInertia.eta4 Ω s := fun s =>
    ((h1 _).1.trans (hu.pt.mult _)).trans (hη s)
  have hl : ∀ s ∈ (UnitaryThreeInertia.eta4 Ω).ker, (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _)) s).left =
      tor _ t * (r (toGS Ω _ s)).left * (tor _ t)⁻¹ := fun s hs => by
    rw [← conj_left r _ _ ((hm s).trans hs), ← ht]
    rfl
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra K Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom.toAlgebra
  have hker : ∀ s : G K Ω, Base.galEmb ℚ K Ω s ∈ (UnitaryThreeInertia.eta4 Ω).ker := fun s => by
    rw [← (UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1]
    exact ⟨s, rfl⟩
  let j : G K Ω →* (UnitaryThreeInertia.eta4 Ω).ker := (Base.galEmb ℚ K Ω).codRestrict _ hker
  let ρ : G K Ω →* GL (Fin 3) (Qbar l) := (glPart (UnitaryThreeInertia.eta4 Ω) (r.comp (toGS Ω _)) hm).comp j
  let ρ' : G K Ω →* GL (Fin 3) (Qbar l) :=
    (glPart (UnitaryThreeInertia.eta4 Ω) (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _))) ho.red.mult).comp j
  have hiso : Af.RepIso ρ ρ' := ⟨tor _ t, fun s => hl _ (hker s)⟩
  have key := haut B _ ho (fun V hV hVη => matIrr_conj (tor _ t) (fun s hs => by
    rw [mats, GG.mat, GG.mat, hl s (hVη hs), ← Units.val_mul, ← Units.val_mul]
    congr 1
    group) (hirr V hV hVη)) ρ' fun s => rfl
  refine ⟨inferInstance, inferInstance, ρ, fun s => rfl, ?_⟩
  rw [zpow_neg_one]
  exact _root_.UpperTheory.GalN.V.autCsd_iso_alt (tw_iso _ hiso.symm') key
end
end

section




section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp
namespace P_spTop
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end P_spTop
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
theorem step_spTop_alt (G : Grp k n) : G.Step_spTop_alt := by
  intro hLat hUniq hCount hLift hTw hRes hPiEta hOrd hPiSub hSupp hCusp hProd hTen L V _ _ π hπs hπi Y iY mY τ hτs hτi hτd hsub
  have hc : ∀ a, ∃ μ' : Fin (G.d a) → kˣ →* ℂˣ,
      (∀ j, IsSmoothChar (μ' j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ' j u = G.μ a u) ∧
        IsCuspSupport (τ a) (fun _ => 1) (fun j => detRep (Fin 1) (μ' j)) :=
    fun a => hCusp L.loc k (G.d a) (Y a) (τ a) (hτs a) (hτi a) (G.μ a) (G.smooth a) (hτd a)
  choose ν hν hνc using hc
  have hνs : ∀ a j, IsSmoothChar (ν a j) := fun a j => (hν a j).1
  have hνr : ∀ a j, res (ν a j) = res (G.μ a) := fun a j => P_spTop.res_eq (hν a j).2
  have htw := fun a => hTw Y τ a (hτs a) (hτi a) (hτd a)
  have hPi : (multiProd G.e (G.twD τ)).IsIrreducible :=
    hProd hCusp L.loc k G.s n G.d G.hd Y (G.twD τ) (fun a => (htw a).1) (fun a => (htw a).2.1) G.μ G.smooth
      (fun a => (htw a).2.2) (fun b c hbc => P_spTop.exists_unit_ne (G.dist b c hbc))
  have hπI := hSupp hOrd L V π hπs hπi Y τ hτs hτi ν hνs hνc hsub
  have hPI := hPiSub hOrd L Y τ hτs hτi ν hνs hνc hPi
  obtain ⟨hfd, hle⟩ := hCount L (G.cOf ν) (P_spTop.isSmoothChar_cOf G ν hνs) (hRes ν hνr)
  have hπη : G.HasEtaVec (jacU G.e π) := by
    obtain ⟨v, hv0, hv⟩ := hTen k G.s G.d Y τ G.μ hτd
    refine hLift _ _ (jacU G.e π) (piTensor τ) (isSmooth_jacU G.e hπs) hsub ⟨v, hv0, fun m hm => ?_⟩
    have hm' := hm
    rw [leviK, Subgroup.mem_pi] at hm'
    exact hv m fun a => hm' a (Set.mem_univ a)
  have hPη := hPiEta hLift Y τ hτs hτd
  obtain ⟨e⟩ := hUniq hLat _ (prinSeries (G.cOf ν)) (P_spTop.isSmooth_prinSeries _) hfd hle _ _ π
    (multiProd G.e (G.twD τ)) hπi hPi hπI hPI hπη hPη
  exact ⟨Y, iY, mY, G.twD τ, fun a => (htw a).1, fun a => (htw a).2.1, fun a => (htw a).2.2, ⟨e⟩⟩
end UpperTheory.TNZ.Grp
end
end
end
