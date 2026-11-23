module

import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle196
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle200
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle197
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle095
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle093
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

namespace GlobalTheory.HeightOnePrimeMembership

open NumberField

theorem exists_heightOne_mem (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : Nat.Prime p) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers E),
      (p : RingOfIntegers E) ∈ w.asIdeal := by
  apply UpperTheory.Ram.exists_place_over <;> assumption

end GlobalTheory.HeightOnePrimeMembership
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.weil_deligne_induction_principle : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (S : WD h → Prop), (∀ x y, S x → S y → S (x.lpSum y)) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → S x → S y) → (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ), (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) → ∀ x, S x := by
  first | exact @GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite | exact GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite | (intros; apply GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.weil_deligne_of_finite_image : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (G : Type) [Group G] [Finite G] (π : Weil h →* G), IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} → ∀ (n : ℕ) (R : Representation ℂ G (Fin n → ℂ)) (μ : Weil h →* ℂˣ), IsSmooth μ → ∃ b : WDRep h (Fin n → ℂ), ∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ) := by
  first | exact @GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist | exact GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist | (intros; apply GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist <;> assumption)
end

section

open GlobalTheory.BI GlobalTheory.BrauerZero

theorem _root_.GlobalTheory.T.inducedClassFunctionFromSubgroup_trans : ∀ {G : Type} [Group G] [Finite G] (K A : Subgroup G), K ≤ A → ∀ (ψ : K → ℂ), ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ := by
  first | exact @GlobalTheory.BrauerZero.ind_ind_of_le | exact GlobalTheory.BrauerZero.ind_ind_of_le | (intros; apply GlobalTheory.BrauerZero.ind_ind_of_le <;> assumption)
end

section

open IsDedekindDomain NumberField
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntegralPullback

open Filter Topology ValuativeRel

theorem valued_le_one_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) (z : v.adicCompletion F)
    (hz : Valued.v (c z) ≤ 1) : Valued.v z ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at h
  have hcz : c z ≠ 0 := (map_ne_zero c).mpr hz0

  have hinv : Valued.v z⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h
  have ht : Tendsto (fun n : ℕ => (c z⁻¹) ^ n) atTop (𝓝 0) := by
    have := (hc.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hinv)
    simpa [Function.comp_def, map_pow] using this

  have h1 : 1 ≤ Valued.v (c z⁻¹) := by
    rw [map_inv₀]
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (c z)⁻¹ * Valued.v (c z) := by
          rw [← map_mul, inv_mul_cancel₀ hcz, map_one]
      _ ≤ Valued.v (c z)⁻¹ * 1 := by gcongr
      _ = Valued.v (c z)⁻¹ := mul_one _
  have hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion E) :=
    Valued.mem_nhds_zero.mpr ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨n, hn⟩ := (ht.eventually_mem hU).exists
  have hn' : Valued.v ((c z⁻¹) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact absurd hn' (not_lt.mpr (one_le_pow₀ h1))

theorem mem_integer_iff {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    (z : w.adicCompletion E) :
    z ∈ (valuation (w.adicCompletion E)).integer ↔ Valued.v z ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff (valuation (w.adicCompletion E))]
  show Valued.v z ≤ Valued.v 1 ↔ _
  rw [map_one]

private theorem mem_KO_of_integral_entries' {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} (A : GL (Fin n) (v.adicCompletion F))
    (h1 : ∀ i j, (A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      (valuation (v.adicCompletion F)).integer)
    (h2 : ∀ i j, ((A⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ (valuation (v.adicCompletion F)).integer) :
    A ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) := by

  let P : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer :=
    Matrix.of fun i j => ⟨_, h1 i j⟩
  let Q : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer :=
    Matrix.of fun i j => ⟨_, h2 i j⟩
  let f := algebraMap (valuation (v.adicCompletion F)).integer (v.adicCompletion F)
  have hP : P.map f = (A : Matrix (Fin n) (Fin n) _) := by
    ext i j
    simp only [P, f, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_ofSubsemiring_apply]
  have hQ : Q.map f = ((A⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
    ext i j
    simp only [Q, f, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_ofSubsemiring_apply]
  have inj : ∀ X Y : Matrix (Fin n) (Fin n) (valuation (v.adicCompletion F)).integer,
      X.map f = Y.map f → X = Y := by
    intro X Y h
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hPQ : P * Q = 1 := inj _ _ (by
    rw [Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), hP, hQ]
    exact A.mul_inv)
  have hQP : Q * P = 1 := inj _ _ (by
    rw [Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), hP, hQ]
    exact A.inv_mul)
  unfold GlobalTheory.SplitWeil.KO
  refine MonoidHom.mem_range.mpr ⟨⟨P, Q, hPQ, hQP⟩, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrFun (congrFun hP i) j

private theorem entry_mem_integer_of_map_mem_KO {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) {n : ℕ}
    (M : GL (Fin n) (v.adicCompletion F))
    (hM : Matrix.GeneralLinearGroup.map c.toRingHom M ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n))
    (i j : Fin n) :
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      (valuation (v.adicCompletion F)).integer := by
  unfold GlobalTheory.SplitWeil.KO at hM
  obtain ⟨C, hC⟩ := MonoidHom.mem_range.mp hM
  rw [GlobalTheory.IntegralPullback.mem_integer_iff]
  apply valued_le_one_of_map c hc
  rw [← GlobalTheory.IntegralPullback.mem_integer_iff]
  have hij := congrArg (fun g : GL (Fin n) (w.adicCompletion E) =>
    (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) hC
  simp only [Matrix.GeneralLinearGroup.map_apply] at hij
  have : c ((M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) =
      ((C : Matrix (Fin n) (Fin n) (valuation (w.adicCompletion E)).integer) i j :
        w.adicCompletion E) := hij.symm
  rw [this]
  exact ((C : Matrix (Fin n) (Fin n) (valuation (w.adicCompletion E)).integer) i j).2

theorem mem_KO_of_map : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (c : v.adicCompletion F ≃+* w.adicCompletion E), Continuous c → ∀ {n : ℕ} (A : GL (Fin n) (v.adicCompletion F)), Matrix.GeneralLinearGroup.map c.toRingHom A ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) → A ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) := by
  intro F E _ _ _ _ v w c hc n A hA
  have hAinv : Matrix.GeneralLinearGroup.map c.toRingHom A⁻¹ ∈
      GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
    rw [map_inv]
    exact inv_mem hA
  exact mem_KO_of_integral_entries' A (entry_mem_integer_of_map_mem_KO c hc A hA) (entry_mem_integer_of_map_mem_KO c hc A⁻¹ hAinv)

end GlobalTheory.IntegralPullback
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.isPseudoCharacter_of_approximatedByTraces : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (T : Γ → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), PolyApprox T (trc '' C) → IsPsChar a T := by
  first | exact @GlobalTheory.PsChar.isPsChar_of_polyApprox_trc | exact GlobalTheory.PsChar.isPsChar_of_polyApprox_trc | (intros; apply GlobalTheory.PsChar.isPsChar_of_polyApprox_trc <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbTest

theorem eta_eq_of_norm_eq {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  unfold eta
  by_cases hx : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [if_pos hx, if_pos (h ▸ hx)]
  · rw [if_neg hx, if_neg (h ▸ hx)]

theorem isLocallyConstant_eta_comp {X F : Type} [TopologicalSpace X] [NormedField F] [IsUltrametricDist F]
    (h : X → F) (hc : Continuous h) (h0 : ∀ x, h x ≠ 0) : IsLocallyConstant (fun x => eta (h x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : 0 < ‖h x‖ := norm_pos_iff.mpr (h0 x)
  have hev : ∀ᶠ y in 𝓝 x, dist (h y) (h x) < ‖h x‖ := (hc.tendsto x) (Metric.ball_mem_nhds _ hx)
  filter_upwards [hev] with y hy
  apply eta_eq_of_norm_eq
  rw [dist_eq_norm] at hy
  have hy' : ‖h x - h y‖ < ‖h x‖ := by rwa [norm_sub_rev]
  have e1 : ‖h y‖ ≤ max ‖h y - h x‖ ‖h x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h y - h x) (h x)
  have e2 : ‖h x‖ ≤ max ‖h x - h y‖ ‖h y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h x - h y) (h y)
  apply le_antisymm
  · exact e1.trans (max_le hy.le le_rfl)
  · rcases le_total ‖h x - h y‖ ‖h y‖ with hh | hh
    · exact e2.trans (max_le hh le_rfl)
    · exact absurd (e2.trans (max_le le_rfl hh)) (not_le.mpr hy')

theorem continuous_act {r : ℕ} {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] (Y : Gl r k) :
    Continuous (fun g : GL (Fin r) k => act g Y) := by
  unfold act
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const))
  · exact (Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv
  · exact Units.continuous_val.matrix_mulVec continuous_const
  · exact continuous_const.matrix_vecMul Units.continuous_coe_inv

theorem actU_mul {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g h : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : actU (g * h) X = actU g (actU h X) := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  · simp only [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem continuous_actU {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [ContinuousStar E] (X : Hn r F E) :
    Continuous (fun g : Matrix.unitaryGroup (Fin r) E => actU g X) := by
  unfold actU
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
  · exact (continuous_subtype_val.matrix_mul continuous_const).matrix_mul continuous_subtype_val.star
  · exact continuous_subtype_val.matrix_mulVec continuous_const

end GlobalTheory.JR.OrbTest

namespace GlobalTheory.JR.OrbTest

theorem isTest_orbG_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f' : Gl r F → ℂ) (hf : IsTest f') (Y : Gl r F)
    (hY : Delta (inv Y) ≠ 0) :
    IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y)) := by
  haveI : IsUltrametricDist F := Unram.ultraF (E := E)
  obtain ⟨-, hL1b, hL1c, hL1d, hL1e⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r
  obtain ⟨hL6a, hL6b⟩ := GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det F r
  obtain ⟨-, -, -, hL4⟩ := GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper F E r
  have hC : (Cm Y).det ≠ 0 := by
    intro h0; apply hY; rw [Delta, ← hL1c Y, Matrix.det_mul, h0, zero_mul]
  have hld : (fun g : GL (Fin r) F => lastDet (act g Y)) = fun g =>
      (-1) ^ r * ((Cm Y).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) := by
    funext g; rw [hL6a, hL6b, Matrix.det_mul]
  refine ⟨?_, ?_⟩
  · refine IsLocallyConstant.comp₂ (hf.1.comp_continuous (continuous_act Y)) ?_ (fun a b => a * b)
    show IsLocallyConstant (fun g : GL (Fin r) F => eta (lastDet (act g Y)))
    refine isLocallyConstant_eta_comp (fun g : GL (Fin r) F => lastDet (act g Y)) ?_ ?_
    · rw [hld]
      exact continuous_const.mul (continuous_const.mul Units.continuous_coe_inv.matrix_det)
    · intro g
      rw [show lastDet (act g Y) = _ from congrFun hld g]
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hC ?_)
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (g⁻¹).isUnit).ne_zero
  · have ha : Delta (inv (sec (inv Y))) ≠ 0 := by rw [hL1b]; exact hY
    obtain ⟨g₀, ⟨hg₀, -⟩, -⟩ := hL1e (sec (inv Y)) Y ha (hL1b _).symm
    have hS : IsCompact {h : GL (Fin r) F | act h (sec (inv Y)) ∈ tsupport f'} := by
      have := hL4 (tsupport f') {inv Y} hf.2 isCompact_singleton (by rintro b rfl; exact hY)
      convert this.image continuous_fst using 1
      ext h; constructor
      · intro hh; exact ⟨(h, inv Y), ⟨rfl, hh⟩, rfl⟩
      · rintro ⟨⟨h', a'⟩, ⟨ha', hc⟩, rfl⟩
        simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
    have hK : IsCompact {g : GL (Fin r) F | act g Y ∈ tsupport f'} := by
      have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
      convert this using 1
      ext g; simp [Homeomorph.coe_mulRight, hL1d, hg₀]
    refine HasCompactSupport.intro' hK ((isClosed_tsupport f').preimage (continuous_act Y)) ?_
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    simp only [image_eq_zero_of_notMem_tsupport hg, zero_mul]

theorem isTest_orbU_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f : Hn r F E → ℂ) (hf : IsTest f) (a : Inv r F)
    (X : Hn r F E) (ha : Delta a ≠ 0) (hX : HasInv X a) :
    IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  haveI : ContinuousStar E := ⟨by
    have : Continuous (starAddEquiv : E ≃+ E) :=
      AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1
        (fun x => by rw [starAddEquiv_apply, Unram.norm_star (F := F), one_mul])
    exact this⟩
  obtain ⟨-, -, hL5c, -⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨-, hL5iv⟩ := GlobalTheory.T.invariant_image_openClosed_local_sections F E r a ha
  obtain ⟨Ω, s, -, -, haΩ, -, hs, hprop⟩ := hL5iv ⟨X, hX⟩
  obtain ⟨g₀, hg₀, -⟩ := hL5c (s a) X a ha (hs a haΩ).2 hX
  refine ⟨hf.1.comp_continuous (continuous_actU X), ?_⟩
  have hS : IsCompact {h : Matrix.unitaryGroup (Fin r) E | actU h (s a) ∈ tsupport f} := by
    have h1 := (hprop (tsupport f) hf.2).inter_right (isClosed_univ.prod (isClosed_singleton (x := a)))
    convert h1.image continuous_fst using 1
    ext h; constructor
    · intro hh; exact ⟨(h, a), ⟨⟨haΩ, hh⟩, Set.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨h', a'⟩, ⟨⟨-, hc⟩, -, ha'⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
  have hK : IsCompact {g : Matrix.unitaryGroup (Fin r) E | actU g X ∈ tsupport f} := by
    have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
    convert this using 1
    ext g; simp [Homeomorph.coe_mulRight, actU_mul, hg₀]
  refine HasCompactSupport.intro' hK ((isClosed_tsupport f).preimage (continuous_actU X)) ?_
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  exact image_eq_zero_of_notMem_tsupport hg

end GlobalTheory.JR.OrbTest


open GlobalTheory.JR.OrbTest in
theorem GlobalTheory.JR.orb_integrand_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ Y : Gl r F, Delta (inv Y) ≠ 0 → IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y))) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a : Inv r F) (X : Hn r F E), Delta a ≠ 0 → HasInv X a → IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  intro F E _ _ _ _ _ r _
  exact ⟨fun f' hf Y hY => isTest_orbG_integrand F E r f' hf Y hY,
    fun f hf a X ha hX => isTest_orbU_integrand F E r f hf a X ha hX⟩
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.frobenius_polydisc_windows_surjective_bounds_zero : WinThm := by
  first | exact @GlobalTheory.PMonE.winThm | exact GlobalTheory.PMonE.winThm | (intros; apply GlobalTheory.PMonE.winThm <;> assumption)
end

section

open Formalism.MainNotions.N GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ e : R, IsIdempotentElem e → (∃ m : ℕ, m ≤ d ∧ T e = m) ∧ (T e = 0 → ∀ y : R, T (e * y) = 0) := by
  first | exact @GlobalTheory.PsChar.isPsChar_idempotent | exact GlobalTheory.PsChar.isPsChar_idempotent | (intros; apply GlobalTheory.PsChar.isPsChar_idempotent <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_compact_preimage_norm_centralizer_hermitian : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) := by
  first | exact @GlobalTheory.NormSec.normsec | exact GlobalTheory.NormSec.normsec | (intros; apply GlobalTheory.NormSec.normsec <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitLemma_residually_unipotent_via_cayley : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ, algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 → (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧ Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent | exact GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent | (intros; apply GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.HypJ

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) →
    ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧
      ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  have hH : μK.IsAddHaarMeasure := hsd.1
  have hT := GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport F E A ψ hψ μK hH φ' hφ
  refine ⟨⟨?_, fun z s g => GlobalTheory.T.jHyp_unipotent_torus_equivariance F E A μK hH ψ φ' z s g⟩, ?_⟩
  · obtain ⟨U, hU, hk⟩ := GlobalTheory.T.test_function_locally_invariant A.K _ hT
    refine ⟨U, hU, fun g k hkU => ?_⟩
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have := hk k hkU (t * g 1 0) (t * g 1 1)
    simp only at this
    have e1 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 =
        g 1 0 * k 0 0 + g 1 1 * k 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have e2 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 =
        g 1 0 * k 0 1 + g 1 1 * k 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [e1, e2]
    rw [← this]; congr 2 <;> ring
  · intro h
    have key : ∀ c u, A.tilde μK ψ (A.fourK μK ψ φ') c u = A.tilde μK ψ φ' (-u) c := by
      intro c u
      have hG := GlobalTheory.TestFn.slice_test _ hT c
      have := hsd.2 _ hG u
      rw [← this]
      unfold Et.tilde fourB
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [GlobalTheory.T.fourierEtaleK_eq_integral_partialFourier F E A ψ hψ μK hH φ' hφ b c]
      unfold fourB Et.tilde Et.kerK
      rw [mul_comm u b]
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [key]
    congr 2
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]

end GlobalTheory.JR.HypJ
end
