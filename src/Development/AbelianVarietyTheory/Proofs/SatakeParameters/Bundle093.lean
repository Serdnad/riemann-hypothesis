module

public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle002
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle005
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle038
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle021
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle089
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle067
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle083
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.Bundle008
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Proof.ColumnStabilizerTrivialLocal

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n n' : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem typePrimesLarge_iff (D : D7) :
    UnipotentLevelStabilisers.TypePrimesLarge D ↔ ∀ i, 2 * D.R.f * D.R.k < D.host.g i - 1 :=
  forall_congr' fun i => by omega

theorem gBig_of_large (h : UnipotentLevelStabilisers.TypePrimesLarge D) : Formalism.MainNotions.StandardLattice.GBig D :=
  ⟨0, (typePrimesLarge_iff D).mp h 0⟩

variable {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)

end GlobalTheory.Proof.ColumnStabilizerTrivialLocal
end
end

section

open GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.compactSpace_maximalCompact_unitary_infinite : ∀ (E : Type) [Field E] (a : ℕ), CompactSpace (Kinf E a) := by
  first | exact @GlobalTheory.KinfCompactness.compactSpace_Kinf | exact GlobalTheory.KinfCompactness.compactSpace_Kinf | (intros; apply GlobalTheory.KinfCompactness.compactSpace_Kinf <;> assumption)
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.exists_localTranslation_comp_commuting_operator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : GlobalTheory.CuspRep.Op E a), ∃ (g : GL (Fin a) (w.adicCompletion E)) (T : Module.End ℂ π.V), (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T := by
  first | exact @GlobalTheory.LocFactor.exists_locRep_comp | exact GlobalTheory.LocFactor.exists_locRep_comp | (intros; apply GlobalTheory.LocFactor.exists_locRep_comp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module

theorem _root_.GlobalTheory.T.charpoly_weilDeligne_potSemistable_enlarge_coefficients : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) → ∀ σ : ↥(Weil h), WD.charPol (wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) σ = WD.charPol (wdPst P ι Bw h hj (Bw.repE L₁ r₁)) σ := by
  first | exact @GlobalTheory.Pst.EnlargeCoeff.charPol_wdPst_enlarge | exact GlobalTheory.Pst.EnlargeCoeff.charPol_wdPst_enlarge | (intros; apply GlobalTheory.Pst.EnlargeCoeff.charPol_wdPst_enlarge <;> assumption)
end

section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeFin

section ValLemmas
variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem val_eq_one_of_sub_one (v : Valuation K Γ) {a : K} {ε : Γ} (hε : ε < 1)
    (ha : v (a - 1) ≤ ε) : v a = 1 := by
  have e : a = 1 + (a - 1) := by ring
  rw [e, Valuation.map_one_add_of_lt v (lt_of_le_of_lt ha hε)]

theorem mul_sub_one_le (v : Valuation K Γ) {a b : K} {ε : Γ} (hε : ε < 1)
    (ha : v (a - 1) ≤ ε) (hb : v (b - 1) ≤ ε) : v (a * b - 1) ≤ ε := by
  have e : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [e]
  refine le_trans (Valuation.map_add v _ _) (max_le ?_ ha)
  rw [map_mul, val_eq_one_of_sub_one v hε ha, one_mul]; exact hb

theorem inv_sub_one_le (v : Valuation K Γ) {a : K} {ε : Γ} (hε : ε < 1)
    (ha : v (a - 1) ≤ ε) : v (a⁻¹ - 1) ≤ ε := by
  have h1 := val_eq_one_of_sub_one v hε ha
  have ha0 : a ≠ 0 := by rintro rfl; simp at h1
  have e : a⁻¹ - 1 = -(a - 1) * a⁻¹ := by field_simp; ring
  rw [e, map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, mul_one]; exact ha

end ValLemmas
end GlobalTheory.HeckeFin

namespace GlobalTheory.HeckeFin

theorem val_coe_sub_one (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (v.adicCompletion E) a - 1) = v.valuation E (a - 1) := by
  rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a - 1)

theorem trivAt_of_degOne_cofinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → (∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1) → ∀ w, TrivAt χ w := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg hinf w x
  classical
  obtain ⟨hunr, hloc, hfac⟩ := GlobalTheory.T.continuous_ideleChar_local_factorization E χ hχ.1
  choose nf hnf using hloc
  have hU := Filter.eventually_cofinite.mp hunr
  have hX := Filter.eventually_cofinite.mp hdeg
  set S : Finset (HeightOneSpectrum (𝓞 E)) := hU.toFinset ∪ hX.toFinset ∪ {w} with hS
  have hSu : ∀ v ∉ S, UnrAt χ v := by
    intro v hv; by_contra h
    exact hv (by simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inl h))
  have hSd : ∀ v ∉ S, DegOne F v → TrivAt χ v := by
    intro v hv; by_contra h
    exact hv (by simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inr h))
  have hwS : w ∈ S := by simp [hS]
  obtain ⟨θ, D, hD0, hθ⟩ := GlobalTheory.T.exists_denom_mul_mem_span_one_gen_of_finrank_two F E (Algebra.IsQuadraticExtension.finrank_eq_two F E)
  set ι := algebraMap (𝓞 F) (𝓞 E) with hι
  have hιinj : Function.Injective ι := by
    first
    | exact FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
    | exact NoZeroSMulDivisors.algebraMap_injective (𝓞 F) (𝓞 E)
  set m : Ideal (𝓞 F) := Ideal.span {D} * Ideal.comap ι (∏ Q ∈ S, Q.asIdeal) with hm
  have hm0 : m ≠ ⊥ := by
    have hP : (∏ Q ∈ S, Q.asIdeal) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
      intro Q _; rw [Ideal.zero_eq_bot]; exact Q.ne_bot
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hC : Ideal.comap ι (∏ Q ∈ S, Q.asIdeal) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral a)
    have hD : Ideal.span {D} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    rw [hm, ← Ideal.zero_eq_bot]
    exact mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot])
  have hmD : m ≤ Ideal.span {D} := Ideal.mul_le_left
  have hmS : ∀ Q ∈ S, m ≤ Q.asIdeal.comap ι := fun Q hQ =>
    le_trans Ideal.mul_le_right (Ideal.comap_mono (by rw [← Finset.mul_prod_erase S (fun Q => Q.asIdeal) hQ]; exact Ideal.mul_le_left))
  have hfin : {P : HeightOneSpectrum (𝓞 E) | m ≤ P.asIdeal.comap ι}.Finite := by
    have h0 : m.map ι ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hιinj]; exact hm0
    refine (Ideal.finite_factors h0).subset ?_
    intro P hP
    simp only [Set.mem_setOf_eq] at hP ⊢
    rw [Ideal.dvd_iff_le]; exact Ideal.map_le_iff_le_comap.mpr hP
  set S' := hfin.toFinset with hS'
  have memS' : ∀ P, P ∈ S' ↔ m ≤ P.asIdeal.comap ι := by intro P; simp [hS']
  have hwS' : w ∈ S' := (memS' w).2 (hmS w hwS)
  have hSS' : ∀ v ∉ S', v ∉ S := fun v hv h => hv ((memS' v).2 (hmS v h))
  set n : ℕ := S'.sup nf + 1 with hn
  set ε : WithZero (Multiplicative ℤ) := WithZero.exp (-(n:ℤ)) with hεdef
  have hε : ε < 1 := by rw [hεdef, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hεv : ∀ v ∈ S', ε ≤ WithZero.exp (-(nf v : ℤ)) := by
    intro v hv; rw [hεdef, WithZero.exp_le_exp]; have := Finset.le_sup (f := nf) hv; omega
  obtain ⟨y, hy0, hyw, hyv⟩ := GlobalTheory.T.exists_weak_approx_unit_finite_place E S' w x n
  obtain ⟨y1, y2, hy2, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have hy2' : y2 ≠ 0 := nonZeroDivisors.ne_zero hy2
  have hy1' : y1 ≠ 0 := by rintro rfl; simp at hy0
  have hDι : ι D ≠ 0 := by
    intro h; apply hD0; apply hιinj; rw [h, map_zero]
  have hc1 : ι D * y1 ≠ 0 := mul_ne_zero hDι hy1'
  have hc2 : ι D * y2 ≠ 0 := mul_ne_zero hDι hy2'
  choose Nf hNf using fun (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) (hc : c ≠ 0) => GlobalTheory.T.exists_pow_valuation_div_sub_one_le_of_congr E v c hc n
  set N : ℕ := S'.sup (fun v => Nf v _ hc1 ⊔ Nf v _ hc2) with hN
  obtain ⟨k1, hk1, hk1P⟩ := GlobalTheory.T.exists_congr_mod_pow_residueDegreeOne_factors F E θ D hθ m hm0 hmD y1 N
  obtain ⟨k2, hk2, hk2P⟩ := GlobalTheory.T.exists_congr_mod_pow_residueDegreeOne_factors F E θ D hθ m hm0 hmD y2 N
  have hmem : ∀ v ∈ S', ∀ (k c : 𝓞 E), k - c ∈ Ideal.map ι (m ^ N) → ∀ M ≤ N, k - c ∈ v.asIdeal ^ M := by
    intro v hv k c h M hM
    have h1 : Ideal.map ι (m ^ N) ≤ v.asIdeal ^ N := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr ((memS' v).1 hv)) N
    exact Ideal.pow_le_pow_right hM (h1 h)
  have hcl1 : ∀ v ∈ S', v.valuation E ((k1 : E) / ((ι D * y1 : 𝓞 E) : E) - 1) ≤ ε := fun v hv =>
    hNf v _ hc1 k1 (hmem v hv _ _ hk1 _ (le_trans le_sup_left (Finset.le_sup (f := fun v => Nf v _ hc1 ⊔ Nf v _ hc2) hv)))
  have hcl2 : ∀ v ∈ S', v.valuation E ((k2 : E) / ((ι D * y2 : 𝓞 E) : E) - 1) ≤ ε := fun v hv =>
    hNf v _ hc2 k2 (hmem v hv _ _ hk2 _ (le_trans le_sup_right (Finset.le_sup (f := fun v => Nf v _ hc1 ⊔ Nf v _ hc2) hv)))
  have hk1' : (k1 : E) ≠ 0 := by
    intro h; have := hcl1 w hwS'; rw [h, zero_div, zero_sub, Valuation.map_neg, map_one] at this
    exact absurd hε (not_lt.mpr this)
  have hk2' : (k2 : E) ≠ 0 := by
    intro h; have := hcl2 w hwS'; rw [h, zero_div, zero_sub, Valuation.map_neg, map_one] at this
    exact absurd hε (not_lt.mpr this)
  have ha : ∀ z : 𝓞 E, algebraMap (𝓞 E) E z = (z : E) := fun z => rfl
  have hDE : ((ι D : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hDι
  have hy1E : (y1 : E) ≠ 0 := by exact_mod_cast hy1'
  have hy2E : (y2 : E) ≠ 0 := by exact_mod_cast hy2'
  set kk : E := (k1 : E) / (k2 : E) with hkk
  have hkk0 : kk ≠ 0 := div_ne_zero hk1' hk2'
  have hkey : kk = ((k1 : E) / ((ι D * y1 : 𝓞 E) : E)) * ((k2 : E) / ((ι D * y2 : 𝓞 E) : E))⁻¹ *
      (algebraMap (𝓞 E) E y1 / algebraMap (𝓞 E) E y2) := by
    rw [ha, ha, hkk]; push_cast; field_simp
  have hv1 : ∀ v ∈ S', v ≠ w → v.valuation E (kk - 1) ≤ ε := by
    intro v hv hvw
    rw [hkey]
    exact GlobalTheory.HeckeFin.mul_sub_one_le _ hε (GlobalTheory.HeckeFin.mul_sub_one_le _ hε (hcl1 v hv)
      (GlobalTheory.HeckeFin.inv_sub_one_le _ hε (hcl2 v hv))) (hyv v hv hvw)
  have hvw : Valued.v (algebraMap E (w.adicCompletion E) kk *
      ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ ε := by
    have e : algebraMap E (w.adicCompletion E) kk * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        algebraMap E (w.adicCompletion E) (((k1 : E) / ((ι D * y1 : 𝓞 E) : E)) * ((k2 : E) / ((ι D * y2 : 𝓞 E) : E))⁻¹) *
        (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E y1 / algebraMap (𝓞 E) E y2) *
          ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E)) := by
      rw [hkey, map_mul, mul_assoc]
    rw [e]
    refine GlobalTheory.HeckeFin.mul_sub_one_le _ hε ?_ hyw
    rw [val_coe_sub_one]
    exact GlobalTheory.HeckeFin.mul_sub_one_le _ hε (hcl1 w hwS') (GlobalTheory.HeckeFin.inv_sub_one_le _ hε (hcl2 w hwS'))
  set kU : Eˣ := Units.mk0 kk hkk0 with hkU
  have hcoe : ∀ v : HeightOneSpectrum (𝓞 E), ((finPart E v (diagUnits E kU) : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
      algebraMap E (v.adicCompletion E) kk := fun v => rfl
  have hout : ∀ v ∉ S', χ (localIdele E v (finPart E v (diagUnits E kU))) = 1 := by
    intro v hv
    have hvS := hSS' v hv
    have hmv : ¬ m ≤ v.asIdeal.comap ι := fun h => hv ((memS' v).2 h)
    by_cases h1 : k1 ∈ v.asIdeal
    · exact hSd v hvS (hk1P v hmv h1) _
    by_cases h2 : k2 ∈ v.asIdeal
    · exact hSd v hvS (hk2P v hmv h2) _
    apply hSu v hvS
    rw [hcoe, show Valued.v (algebraMap E (v.adicCompletion E) kk) = v.valuation E kk from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v kk, hkk, map_div₀]
    have e1 : ∀ k : 𝓞 E, k ∉ v.asIdeal → v.valuation E (k : E) = 1 := by
      intro k hk
      refine le_antisymm (v.valuation_le_one k) ?_
      rw [← not_lt]; intro hlt; exact hk ((v.valuation_lt_one_iff_mem k).mp hlt)
    rw [e1 k1 h1, e1 k2 h2, div_one]
  have hprod := hfac (diagUnits E kU) S' hout
  rw [hχ.2 kU, hinf, one_mul, Finset.prod_eq_single w] at hprod
  · set z : (w.adicCompletion E)ˣ := (finPart E w (diagUnits E kU))⁻¹ * x with hz
    have hzv : χ (localIdele E w z) = 1 := by
      apply hnf w z
      refine le_trans ?_ (hεv w hwS')
      have e : (z : w.adicCompletion E) = (algebraMap E (w.adicCompletion E) kk *
          ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E))⁻¹ := by
        rw [hz, Units.val_mul, Units.val_inv_eq_inv_val, hcoe, Units.val_inv_eq_inv_val, mul_inv, inv_inv]
      rw [e]; exact GlobalTheory.HeckeFin.inv_sub_one_le _ hε hvw
    have hx : x = finPart E w (diagUnits E kU) * z := by rw [hz, mul_inv_cancel_left]
    show χ (localIdele E w x) = 1
    rw [hx, map_mul, map_mul, ← hprod, hzv, one_mul]
  · intro v hv hvw
    apply hnf v
    rw [hcoe]; refine le_trans ?_ (hεv v hv)
    rw [val_coe_sub_one]; exact hv1 v hv hvw
  · intro h; exact absurd hwS' h

end GlobalTheory.HeckeFin
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.absIrr_distinct_constituents_after_extension : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GlobalTheory.SplitCoef.OSplitAt D i → GoodR D.nd i r → ∀ (K' : Type) [Field K'] (f : Kf D.nd i →+* K'), (∀ x W₁ W₂, IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ → IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ W₂) → ∀ x, AbsIrrDistinct (repK D.nd i r x) := by
  first | exact @GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct | exact GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct | (intros; apply GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowSizeClosing

theorem rowSize_of_unitarySphericalComponent :
    ∀ (D : D7), GlobalTheory.RowSatakeBound.UnitarySphericalComponent D.nd D.naut → GlobalTheory.RowCopy.RowSize D :=
  fun D h => by
    intro i σ hσ w hw hu α hα
    have hb := GlobalTheory.RowSatakeBound.rowSize_of_component D.nd D.naut h i σ hσ w hw hu α hα
    simpa only [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hb

end GlobalTheory.RowSizeClosing
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_thick_iff : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → ∀ i, (pageWord L j ε τ φ).thick i ↔ Thick D.host (letter τ φ i) := by
  intro D L C j ε τ φ hR i
  obtain ⟨hlo, -⟩ := bHat_window L C hR
  obtain ⟨hwM, hwle⟩ := GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR
  have hR' := hR
  obtain ⟨hC, hw, ht, hwb, -, hb⟩ := hR'
  obtain ⟨c, hc⟩ := D.R.t_odd
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ L.sc.b' := by linarith
  have h1 : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := by nlinarith
  have hdiv : (D.R.t + 1) / 2 = c + 1 := by omega
  have hdivZ : ((D.R.t : ℤ) + 1) / 2 = (c : ℤ) + 1 := by omega
  have htc : (D.R.t : ℝ) = 2 * c + 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ L.sc.b by linarith)
  have hle := Nat.le_ceil L.sc.b
  have hsub : c + 1 ≤ ⌈L.sc.b⌉₊ := by
    have : ((c + 1 : ℕ) : ℝ) ≤ (⌈L.sc.b⌉₊ : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hbH : bHat L + (c + 1) = ⌈L.sc.b⌉₊ := by
    unfold bHat
    rw [hdiv]
    omega
  have hfl := Nat.lt_floor_add_one L.etaSz
  have hη : etaHat L = ⌊L.etaSz⌋₊ + D.R.t + 2 := rfl
  have hsz : ((pageWord L j ε τ φ).sz i = ⌊(hcAt D (letter τ φ i)).e j⌋ + ((c : ℤ) + 1) ∧
        pos ε (letter τ φ i) = true) ∨
      ((pageWord L j ε τ φ).sz i = ⌊(hcAt D (letter τ φ i)).e j⌋ - ((c : ℤ) + 1) ∧
        pos ε (letter τ φ i) = false) := by
    show szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) = _ ∧ _ ∨
      szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) = _ ∧ _
    unfold szT
    cases pos ε (letter τ φ i) <;> simp [hdivZ]
  have hbW : (pageWord L j ε τ φ).b = bHat L := rfl
  have hηW : (pageWord L j ε τ φ).η = etaHat L := rfl
  unfold WordData.thick
  rw [hbW, hηW, hη]
  generalize hE : ⌊(hcAt D (letter τ φ i)).e j⌋ = E at hsz
  constructor
  · rintro ⟨ha, hz⟩
    by_contra hnT
    have hEw : E ≤ (wMax D : ℤ) := hE ▸ hwle _ j hnT
    have hlt2 : ((wMax D + (c + 1) : ℕ) : ℝ) < (bHat L : ℝ) := by
      push_cast
      rw [htc] at hlo ht
      linarith
    have hlt3 : wMax D + (c + 1) < bHat L := by exact_mod_cast hlt2
    omega
  · intro hT
    obtain ⟨hA, hB⟩ := GlobalTheory.T.floor_size_bounds_at_thick_embedding L _ j hT
    rw [hE] at hA hB
    have hBE : ((⌈L.sc.b⌉₊ : ℤ)) ≤ E := by
      have : ((⌈L.sc.b⌉₊ : ℤ) : ℝ) < ((E + 1 : ℤ) : ℝ) := by push_cast; linarith
      have := Int.cast_lt.mp this
      omega
    have hEB : E < (⌈L.sc.b⌉₊ : ℤ) + (⌊L.etaSz⌋₊ : ℤ) + 2 := by
      have : ((E : ℤ) : ℝ) < (((⌈L.sc.b⌉₊ : ℤ) + (⌊L.etaSz⌋₊ : ℤ) + 2 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp this
    omega

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (wHat D : ℝ) = wMax D + ((D.R.t : ℝ) + 1) / 2 ∧ (wHat D : ℝ) + (L.etaSz + D.R.t + 2) ≤ 2 * L.sc.b' ∧ (wHat D : ℝ) + sHat L + etaHat L + 1 ≤ 2 * L.sc.b' := by
  first | exact @GlobalTheory.HTW.wHat_le | exact GlobalTheory.HTW.wHat_le | (intros; apply GlobalTheory.HTW.wHat_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.residualRankPartExists_of_jointCondition : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | exact GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | (intros; apply GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OrbitPair

open MvPowerSeries

theorem expS_neg_sum_bivariate_pair_integral : ∀ {p : ℕ} [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) {n' : ℕ} [NeZero n'] (om om' : Fin (n' / 2) → ℂ_[p]) (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p]) (t : ZMod n' → MvPowerSeries (Fin (n' / 2) ⊕ Fin (n' / 2)) ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), MvPowerSeries.constantCoeff b0 = 0 → MvPowerSeries.constantCoeff bv = 0 → (∀ s, MvPowerSeries.constantCoeff (t s) = 0) → (∀ r, Formalism.MainNotions.GL3Theta.IntegralW (x r) ∧ MvPowerSeries.constantCoeff (x r) = 0) → (∀ s, MvPowerSeries.subst t (GlobalTheory.ThStr.laS p n' s) = GlobalTheory.ThBe0.zOm σ om om' s) → (∀ s, MvPowerSeries.subst x (t s) = MvPowerSeries.X s) → Formalism.MainNotions.GL3Theta.SimeqW (MvPowerSeries.subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv) (∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r))) → ∃ V : MvPowerSeries (ZMod n') ℂ_[p], Formalism.MainNotions.GL3Theta.IntegralW V ∧ product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(MvPowerSeries.subst (GlobalTheory.ThStr.laS p n') bv)) := by
  intro p _ σ n' _ om om' b0 bv t x _hb0 hbv ht hx hlaS htx hsim
  classical
  have hxS : HasSubst x := hasSubst_of_constantCoeff_zero fun r => (hx r).2
  have htS : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have hzcc : ∀ s : ZMod n', constantCoeff (GlobalTheory.ThBe0.zOm (d := n') σ om om' s) = 0 := by
    intro s
    rw [← hlaS s]
    exact constantCoeff_subst_eq_zero htS ht (GlobalTheory.BeProps.constantCoeff_laS s)
  have hzS : HasSubst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) := hasSubst_of_constantCoeff_zero hzcc
  have hzOm : ∀ s : ZMod n', subst x (GlobalTheory.ThBe0.zOm (d := n') σ om om' s) = GlobalTheory.ThStr.laS p n' s := by
    intro s
    rw [← hlaS s, subst_comp_subst_apply htS hxS]
    have : (fun r => subst x (t r)) = (X : ZMod n' → MvPowerSeries (ZMod n') ℂ_[p]) := funext htx
    rw [this, subst_self]
    rfl
  have hFx : subst x (subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv) = subst (GlobalTheory.ThStr.laS p n') bv := by
    rw [subst_comp_subst_apply hzS hxS]
    congr 1
    funext s
    exact hzOm s
  have hGx : subst x (∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r))) =
      ∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)) := by

    rw [← coe_substAlgHom hxS, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [coe_substAlgHom hxS, GlobalTheory.ThBe0.Inhab.subst_powerSeriesEvalTwoGroups hxS (GlobalTheory.ThBe0.Inhab.cc_lg _) (GlobalTheory.ThBe0.Inhab.cc_lg _)]
    simp only [GlobalTheory.ThBe0.lg]
    rw [GlobalTheory.ThBe0.Inhab.subst_psubst hxS (constantCoeff_X _), GlobalTheory.ThBe0.Inhab.subst_psubst hxS (constantCoeff_X _),
      subst_X hxS, subst_X hxS]
  obtain ⟨hD0, hDint⟩ := hsim
  set F := subst (fun s : ZMod n' => GlobalTheory.ThBe0.zOm σ om om' s) bv with hF
  set G := ∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (GlobalTheory.ThBe0.lg (Sum.inl r)) (GlobalTheory.ThBe0.lg (Sum.inr r)) with hG
  have ccL : constantCoeff (subst (GlobalTheory.ThStr.laS p n') bv) = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun s => GlobalTheory.BeProps.constantCoeff_laS s)
      (fun s => GlobalTheory.BeProps.constantCoeff_laS s) hbv
  have ccD : constantCoeff (subst x (F - G)) = 0 := constantCoeff_subst_eq_zero hxS (fun r => (hx r).2) hD0
  have hneg : -(subst x G) = subst x (F - G) + -(subst (GlobalTheory.ThStr.laS p n') bv) := by
    rw [subst_sub hxS, hFx]
    ring
  refine ⟨subst x (Formalism.MainNotions.TaylorLogMetric.expMv (F - G)), ?_, ?_⟩
  · exact GlobalTheory.SubringSeries.subst_mem (A := Formalism.MainNotions.GL3Theta.Wp p) hxS (fun r => (hx r).1) hDint
  · rw [← hGx, hneg]
    show PowerSeries.subst _ (PowerSeries.exp ℂ_[p]) = _ * PowerSeries.subst _ (PowerSeries.exp ℂ_[p])
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add ccD (by rw [map_neg, ccL, neg_zero]), GlobalTheory.BeProps.expMv_eq_subst hD0,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp x (fun r => (hx r).2) hD0]

end GlobalTheory.OrbitPair
end
end
