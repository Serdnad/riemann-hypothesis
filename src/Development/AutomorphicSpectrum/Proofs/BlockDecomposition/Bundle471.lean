module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import GroundTheory.GlobalFields.Adele.Bundle003
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharactersDeRhamJumpZero
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.LocFinType
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerKernelPullbackJacquet
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle441
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle442
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle443
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff
public import GroundTheory.GlobalFields.Adele.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.AnnLattice

variable {E : Type} [Field E] [NumberField E]

theorem sLoc_mul (w : Pl E) (t : w.adicCompletion E) (z : Af E) :
    sLoc E w t * z = sLoc E w (t * pLoc E w z) := by
  classical
  refine FiniteAdeleRing.ext _ fun v => ?_
  change (Pi.single w t : ∀ v : Pl E, v.adicCompletion E) v * pLoc E v z =
    (Pi.single w (t * pLoc E w z) : ∀ v : Pl E, v.adicCompletion E) v
  by_cases h : v = w
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem val_int_le_one (u : Pl E) (d : 𝓞 E) :
    Valued.v (algebraMap E (u.adicCompletion E) (algebraMap (𝓞 E) E d)) ≤ 1 := by
  rw [Formalism.UG.P.levelaf_valued_algebraMap]
  exact u.valuation_le_one d

theorem exists_int_small (S : Finset (Pl E)) (c : Pl E → WithZero (Multiplicative ℤ))
    (hc : ∀ w ∈ S, c w ≠ 0) :
    ∃ D : 𝓞 E, D ≠ 0 ∧ ∀ w ∈ S, Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E D)) ≤ c w := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert w S hw ih =>
    obtain ⟨D, hD0, hD⟩ := ih fun u hu => hc u (Finset.mem_insert_of_mem hu)
    obtain ⟨x, hxw, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hlt : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E x)) < 1 := by
      rw [Formalism.UG.P.levelaf_valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hxw
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hlt (Units.mk0 _ (hc w (Finset.mem_insert_self _ _)))
    refine ⟨D * x ^ n, mul_ne_zero hD0 (pow_ne_zero _ hx0), fun u hu => ?_⟩
    simp only [map_mul, map_pow]
    rcases Finset.mem_insert.1 hu with rfl | hu
    · calc _ ≤ 1 * _ := mul_le_mul' (val_int_le_one u D) le_rfl
        _ = _ := one_mul _
        _ ≤ c u := hn.le
    · calc _ ≤ c u * 1 := mul_le_mul' (hD u hu) (pow_le_one' (val_int_le_one u x) n)
        _ = c u := mul_one _

theorem one_le_exp_mul {b : WithZero (Multiplicative ℤ)} (h : 1 < b) : 1 ≤ WithZero.exp (-1 : ℤ) * b := by
  have hb0 : b ≠ 0 := (zero_lt_one.trans h).ne'
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, b = WithZero.exp n := ⟨_, (WithZero.exp_log hb0).symm⟩
  rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  omega

variable {ψ : AddChar (Ad E) ℂ}

theorem val_le_one_of_cond {w : Pl E} (hw : Cond ψ w) {L : Set (Af E)}
    (hL : ∀ t ∈ Formalism.UG.Ov E w, sLoc E w t ∈ L) {z : Af E}
    (hz : ∀ a ∈ L, ψ (sFin E (a * z)) = 1) : Valued.v (pLoc E w z) ≤ 1 := by
  by_contra hcon
  have h1 : 1 < Valued.v (pLoc E w z) := not_le.1 hcon
  obtain ⟨-, ϖ, y, hϖ, hy1, hy⟩ := hw
  have hz0 : Valued.v (pLoc E w z) ≠ 0 := (zero_lt_one.trans h1).ne'
  have hzw : pLoc E w z ≠ 0 := (map_ne_zero _).1 hz0
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hd : 1 ≤ Valued.v ϖ * Valued.v (pLoc E w z) := by
    rw [hϖ']
    exact one_le_exp_mul h1
  have hyv : Valued.v (ϖ * y) ≤ 1 := hy1
  rw [map_mul] at hyv
  have hle : Valued.v y ≤ Valued.v (pLoc E w z) := by
    calc Valued.v y = 1 * Valued.v y := (one_mul _).symm
      _ ≤ (Valued.v ϖ * Valued.v (pLoc E w z)) * Valued.v y := mul_le_mul' hd le_rfl
      _ = (Valued.v ϖ * Valued.v y) * Valued.v (pLoc E w z) := mul_right_comm _ _ _
      _ ≤ 1 * Valued.v (pLoc E w z) := mul_le_mul' hyv le_rfl
      _ = _ := one_mul _
  have ht : y / pLoc E w z ∈ Formalism.UG.Ov E w := by
    change Valued.v (y / pLoc E w z) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ hle zero_le'
  have h2 := hz _ (hL _ ht)
  rw [sLoc_mul, div_mul_cancel₀ _ hzw] at h2
  exact hy h2

theorem exists_val_bound (hψ : StdPsi ψ) (w : Pl E) {L : Set (Af E)} {N : Set (w.adicCompletion E)} (hN : N ∈ 𝓝 0)
    (hL : ∀ t ∈ N, sLoc E w t ∈ L) :
    ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ ∀ z : Af E, (∀ a ∈ L, ψ (sFin E (a * z)) = 1) →
      ∀ d : w.adicCompletion E, Valued.v d ≤ c → Valued.v (d * pLoc E w z) ≤ 1 := by
  obtain ⟨y, hy⟩ := hψ.loc w
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (by simp)
  have hY : Valued.v y ≠ 0 := (map_ne_zero _).2 hy0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hN
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]; exact (map_ne_zero _).2 γ.ne_zero
  refine ⟨g / Valued.v y, div_ne_zero hg0 hY, fun z hz d hd => ?_⟩
  by_contra hcon
  have h1 : 1 < Valued.v (d * pLoc E w z) := not_le.1 hcon
  rw [map_mul] at h1
  have hb0 : Valued.v (pLoc E w z) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact not_lt_of_ge zero_le' h1
  have hzw : pLoc E w z ≠ 0 := (map_ne_zero _).1 hb0
  have hYpos : 0 < Valued.v y := zero_lt_iff.2 hY
  have hbpos : 0 < Valued.v (pLoc E w z) := zero_lt_iff.2 hb0
  have hdY : Valued.v d * Valued.v y ≤ g := (le_div_iff₀ hYpos).1 hd
  have ht : y / pLoc E w z ∈ N := by
    refine hγ ?_
    change (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict (y / pLoc E w z) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, map_div₀, ← hg, div_lt_iff₀ hbpos]
    calc Valued.v y = 1 * Valued.v y := (one_mul _).symm
      _ < (Valued.v d * Valued.v (pLoc E w z)) * Valued.v y := mul_lt_mul_of_pos_right h1 hYpos
      _ = (Valued.v d * Valued.v y) * Valued.v (pLoc E w z) := mul_right_comm _ _ _
      _ ≤ g * Valued.v (pLoc E w z) := mul_le_mul' hdY le_rfl
  have h2 := hz _ (hL _ ht)
  rw [sLoc_mul, div_mul_cancel₀ _ hzw] at h2
  exact hy h2

theorem exists_isCompact_annihilator : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ},
    StdPsi ψ → ∀ (S : Finset (Pl E)), (∀ w, w ∉ S → Cond ψ w) → ∀ (L : Set (Af E)),
    (∀ w, w ∉ S → ∀ t ∈ Formalism.UG.Ov E w, sLoc E w t ∈ L) →
    (∀ w ∈ S, ∃ N ∈ 𝓝 (0 : w.adicCompletion E), ∀ t ∈ N, sLoc E w t ∈ L) →
    ∃ C : Set (Af E), IsCompact C ∧ ∀ z : Af E, (∀ a ∈ L, ψ (sFin E (a * z)) = 1) → z ∈ C := by
  intro E _ _ _ ψ hψ S hS L hoff hon
  classical
  have hloc : ∀ w : Pl E, ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ (w ∈ S → ∀ z : Af E,
      (∀ a ∈ L, ψ (sFin E (a * z)) = 1) → ∀ d : w.adicCompletion E, Valued.v d ≤ c →
        Valued.v (d * pLoc E w z) ≤ 1) := fun w => by
    by_cases hw : w ∈ S
    · obtain ⟨N, hN, hNL⟩ := hon w hw
      obtain ⟨c, hc0, hc⟩ := exists_val_bound hψ w hN hNL
      exact ⟨c, hc0, fun _ => hc⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hw⟩
  choose c hc0 hc using hloc
  obtain ⟨D, hD0, hD⟩ := exists_int_small S c fun w _ => hc0 w
  have he : algebraMap (𝓞 E) E D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hD0
  refine ⟨(fun y => algebraMap E (Af E) (algebraMap (𝓞 E) E D)⁻¹ * y) ''
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)),
    (GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id), fun z hz => ?_⟩
  refine ⟨algebraMap E (Af E) (algebraMap (𝓞 E) E D) * z, ?_, ?_⟩
  · refine SetLike.mem_coe.2 (GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => ?_)
    have e : (algebraMap E (Af E) (algebraMap (𝓞 E) E D) * z) w =
        algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E D) * pLoc E w z := rfl
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hw : w ∈ S
    · exact hc w hw z hz _ (hD w hw)
    · rw [map_mul]
      calc _ ≤ 1 * 1 := mul_le_mul' (val_int_le_one w D) (val_le_one_of_cond (hS w hw) (hoff w hw) hz)
        _ = 1 := one_mul 1
  · change algebraMap E (Af E) (algebraMap (𝓞 E) E D)⁻¹ * (algebraMap E (Af E) (algebraMap (𝓞 E) E D) * z) = z
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one, one_mul]

end GlobalTheory.CompanionTheory.AnnLattice

end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

theorem _root_.GlobalTheory.T.local_character_induced_agree : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A) →* (↥LL'.1)ˣ),
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) → (∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1) →
      ∀ V : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω), IsOpen (V : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) →
      (∀ σ : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A), (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ∈ V → (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A → ψ σ = 1) →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ 0 := by
  first | exact @GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia | exact GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia | (intros; apply GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia <;> assumption)
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeakHolo

open _root_.Metric Set Filter _root_.Topology Complex Real

theorem taylor_two {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {s₀ : ℂ} {r M : ℝ}
    (hr : 0 < r) (hb : closedBall s₀ (3 * r) ⊆ U) (hM : ∀ z ∈ closedBall s₀ (3 * r), ‖f z‖ ≤ M) {η : ℂ}
    (hη : ‖η‖ ≤ r) : ‖f (s₀ + η) - f s₀ - η * deriv f s₀‖ ≤ M / r ^ 2 * ‖η‖ ^ 2 := by
  have hdf : DifferentiableOn ℂ (deriv f) U :=
    ((hf.analyticOnNhd hU).deriv_of_isOpen hU).differentiableOn
  have h1 : ∀ z ∈ closedBall s₀ (2 * r), ‖deriv f z‖ ≤ M / r := by
    intro z hz
    have hsub : closedBall z r ⊆ closedBall s₀ (3 * r) := by
      refine closedBall_subset_closedBall' ?_
      have := mem_closedBall.1 hz
      linarith
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr (hf.diffContOnCl_ball (hsub.trans hb))
      fun w hw => hM w (hsub (sphere_subset_closedBall hw))
  have h2 : ∀ z ∈ closedBall s₀ r, ‖deriv (deriv f) z‖ ≤ M / r / r := by
    intro z hz
    have hsub : closedBall z r ⊆ closedBall s₀ (2 * r) := by
      refine closedBall_subset_closedBall' ?_
      have := mem_closedBall.1 hz
      linarith
    have hsub' : closedBall s₀ (2 * r) ⊆ closedBall s₀ (3 * r) :=
      closedBall_subset_closedBall (by linarith)
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (hdf.diffContOnCl_ball ((hsub.trans hsub').trans hb))
      fun w hw => h1 w (hsub (sphere_subset_closedBall hw))
  have hin : ∀ z ∈ closedBall s₀ r, z ∈ U := fun z hz =>
    hb (closedBall_subset_closedBall (by linarith) hz)
  have hc : s₀ ∈ closedBall s₀ r := mem_closedBall_self hr.le
  have h3 : ∀ z ∈ closedBall s₀ r, ‖deriv f z - deriv f s₀‖ ≤ M / r / r * ‖z - s₀‖ := fun z hz =>
    (convex_closedBall s₀ r).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (hdf y (hin y hy)).differentiableAt (hU.mem_nhds (hin y hy))) h2 hc hz
  have hMn : 0 ≤ M := (norm_nonneg _).trans (hM s₀ (mem_closedBall_self (by positivity)))
  have hs : closedBall s₀ ‖η‖ ⊆ closedBall s₀ r := closedBall_subset_closedBall hη
  have h4 := (convex_closedBall s₀ ‖η‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => f z - z * deriv f s₀) (f' := fun z => deriv f z - deriv f s₀) (C := M / r / r * ‖η‖)
    (fun z hz => by
      have a := ((hf z (hin z (hs hz))).differentiableAt (hU.mem_nhds (hin z (hs hz)))).hasDerivAt
      have b := (hasDerivAt_id z).mul_const (deriv f s₀)
      have c : HasDerivAt (fun z => f z - z * deriv f s₀) (deriv f z - 1 * deriv f s₀) z := a.sub b
      rw [one_mul] at c
      exact c.hasDerivWithinAt)
    (fun z hz => (h3 z (hs hz)).trans (by
      have := mem_closedBall_iff_norm.1 hz
      gcongr))
    (mem_closedBall_self (norm_nonneg η)) (x := s₀) (y := s₀ + η) (by simp [mem_closedBall_iff_norm])
  have e : f (s₀ + η) - f s₀ - η * deriv f s₀ =
      (f (s₀ + η) - (s₀ + η) * deriv f s₀) - (f s₀ - s₀ * deriv f s₀) := by ring
  rw [e]
  refine h4.trans (le_of_eq ?_)
  simp only [add_sub_cancel_left]
  field_simp

theorem deriv_circle {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hf : DiffContOnCl ℂ f (ball c r)) :
    deriv f c = (2 * π * I)⁻¹ * ∮ z in C(c, r), (1 / (z - c) ^ 2) • f z := by
  have := hf.circleIntegral_one_div_sub_center_pow_smul hr 1
  simp only [zero_add, Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, div_one, iteratedDeriv_one] at this
  rw [this, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by simp [pi_ne_zero]), one_mul]

theorem continuous_deriv_family {X : Type*} [TopologicalSpace X] {w : ℂ → X → ℂ} {S : Set ℂ} {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : closedBall s₀ r ⊆ S) (hd : ∀ x, DifferentiableOn ℂ (fun s => w s x) S)
    (hc : ContinuousOn (fun y : ℂ × X => w y.1 y.2) (S ×ˢ Set.univ)) :
    Continuous fun x => deriv (fun s => w s x) s₀ := by
  have e : (fun x => deriv (fun s => w s x) s₀) = fun x => (2 * π * I : ℂ)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap s₀ r) θ •
        ((1 / (circleMap s₀ r θ - s₀) ^ 2) • w (circleMap s₀ r θ) x) := by
    funext x
    rw [deriv_circle hr ((hd x).diffContOnCl_ball hb)]
    rfl
  rw [e]
  refine continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _)
  have hA : Continuous fun θ : ℝ => deriv (circleMap s₀ r) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hB : Continuous fun θ : ℝ => (1 / (circleMap s₀ r θ - s₀) ^ 2 : ℂ) :=
    continuous_const.div (((continuous_circleMap s₀ r).sub continuous_const).pow 2) fun θ =>
      pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hr.ne'))
  have hC : Continuous fun p : X × ℝ => w (circleMap s₀ r p.2) p.1 :=
    hc.comp_continuous (((continuous_circleMap s₀ r).comp continuous_snd).prodMk continuous_fst)
      fun p => ⟨hb (circleMap_mem_closedBall s₀ hr.le p.2), mem_univ _⟩
  exact (hA.comp continuous_snd).smul ((hB.comp continuous_snd).smul hC)

theorem form_scale {X : Type*} {V : Submodule ℂ (X → ℂ)} (μ : V →ₗ[ℂ] ℂ) {b : X → ℝ} {K : ℝ}
    (hK : ∀ f : V, (∀ x, ‖f.1 x‖ ≤ b x) → ‖μ f‖ ≤ K) (f : V) {l : ℝ} (hl : 0 < l)
    (hf : ∀ x, ‖f.1 x‖ ≤ l * b x) : ‖μ f‖ ≤ K * l := by
  have h := hK (((l⁻¹ : ℝ) : ℂ) • f) fun x => by
    have e : ‖(((l⁻¹ : ℝ) : ℂ) • f).1 x‖ = l⁻¹ * ‖f.1 x‖ := by
      simp [abs_of_pos hl]
    rw [e, inv_mul_le_iff₀ hl]
    exact hf x
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl),
    inv_mul_le_iff₀ hl] at h
  linarith

theorem differentiableOn_form {X : Type*} [TopologicalSpace X] {h : X → ℝ} (hh : ∀ x, 0 ≤ h x)
    {V : Submodule ℂ (X → ℂ)}
    (hV : ∀ (g : X → ℂ) (A : ℝ) (N : ℕ), Continuous g → (∀ x, ‖g x‖ ≤ A * h x ^ N) → g ∈ V)
    (μ : V →ₗ[ℂ] ℂ) (hμ : ∀ N : ℕ, ∃ C : ℝ, ∀ f : V, (∀ x, ‖f.1 x‖ ≤ h x ^ N) → ‖μ f‖ ≤ C)
    (v : ℂ → V) {S : Set ℂ} (hS : IsOpen S)
    (hd : ∀ x, DifferentiableOn ℂ (fun s => (v s).1 x) S)
    (hc : ContinuousOn (fun y : ℂ × X => (v y.1).1 y.2) (S ×ˢ Set.univ))
    (hb : ∀ Q : Set ℂ, Q ⊆ S → IsCompact Q → ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Q, ∀ x, ‖(v s).1 x‖ ≤ C * h x ^ N) :
    DifferentiableOn ℂ (fun s => μ (v s)) S := by
  intro s₀ hs₀
  obtain ⟨R, hR, hRS⟩ := nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hs₀)
  obtain ⟨C, N, hCN⟩ := hb _ hRS (isCompact_closedBall s₀ R)
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ R = 3 * r := ⟨R / 3, by positivity, by ring⟩
  have hsub : closedBall s₀ r ⊆ closedBall s₀ (3 * r) := closedBall_subset_closedBall (by linarith)
  let d : X → ℂ := fun x => deriv (fun s => (v s).1 x) s₀
  have dc : Continuous d := continuous_deriv_family (w := fun s => (v s).1) hr (hsub.trans hRS) hd hc
  have dB : ∀ x, ‖d x‖ ≤ C / r * h x ^ N := fun x => by
    have := norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun s => (v s).1 x) (c := s₀) hr
      ((hd x).diffContOnCl_ball (hsub.trans hRS)) (C := C * h x ^ N)
      fun z hz => hCN z (hsub (sphere_subset_closedBall hz)) x
    calc ‖d x‖ ≤ C * h x ^ N / r := this
      _ = C / r * h x ^ N := by ring
  let D : V := ⟨d, hV d _ N dc dB⟩
  obtain ⟨K, hK⟩ := hμ N
  set B : ℝ := |C| / r ^ 2 + 1 with hB
  have hBpos : 0 < B := by positivity
  have key : ∀ η : ℂ, ‖η‖ < r →
      ‖μ (v (s₀ + η)) - μ (v s₀) - η • μ D‖ ≤ K * B * ‖η ^ 2‖ := by
    intro η hη
    by_cases h0 : η = 0
    · simp [h0]
    have hηp : 0 < ‖η‖ := norm_pos_iff.2 h0
    have e : μ (v (s₀ + η)) - μ (v s₀) - η • μ D = μ (v (s₀ + η) - v s₀ - η • D) := by
      simp only [map_sub, map_smul]
    rw [e, norm_pow, mul_assoc]
    refine form_scale μ hK _ (by positivity) fun x => ?_
    have t := taylor_two hS (hd x) hr hRS (fun z hz => hCN z hz x) hη.le
    have hp : 0 ≤ h x ^ N := pow_nonneg (hh x) N
    have e2 : (v (s₀ + η) - v s₀ - η • D).1 x =
        (v (s₀ + η)).1 x - (v s₀).1 x - η * deriv (fun s => (v s).1 x) s₀ := rfl
    rw [e2]
    refine t.trans ?_
    have : C * h x ^ N / r ^ 2 * ‖η‖ ^ 2 = (C / r ^ 2) * (‖η‖ ^ 2 * h x ^ N) := by ring
    rw [this, show B * ‖η‖ ^ 2 * h x ^ N = B * (‖η‖ ^ 2 * h x ^ N) by ring]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hB]
    have : C / r ^ 2 ≤ |C| / r ^ 2 := by gcongr; exact le_abs_self C
    linarith
  have hO : (fun η : ℂ => μ (v (s₀ + η)) - μ (v s₀) - η • μ D) =O[𝓝 0] fun η => η ^ 2 :=
    Asymptotics.IsBigO.of_bound (K * B) (Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) hr)
      fun η hη => key η (by simpa using hη))
  exact (hasDerivAt_iff_isLittleO_nhds_zero.2
    (hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two))).differentiableAt.differentiableWithinAt

end GlobalTheory.CompanionTheory.WeakHolo

namespace GlobalTheory.CompanionTheory.WeakHolo

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem mem_modFun {g : G2 σ Y → ℂ} {A : ℝ} {N : ℕ} (hg : Continuous g)
    (hA : ∀ x, ‖g x‖ ≤ A * (ht2 x : ℝ) ^ N) : g ∈ modFun σ Y := by
  have hp : 0 < |A| + 1 := by positivity
  have hq : (((|A| + 1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1 : ((((|A| + 1 : ℝ)) : ℂ)⁻¹ • g) ∈ modFun σ Y := by
    refine Submodule.subset_span ⟨hg.const_smul _, N, fun x => ?_⟩
    have hh : 0 ≤ (ht2 x : ℝ) ^ N := by positivity
    rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
      inv_mul_le_iff₀ hp]
    refine (hA x).trans (mul_le_mul_of_nonneg_right ?_ hh)
    linarith [le_abs_self A]
  have := (modFun σ Y).smul_mem (((|A| + 1 : ℝ)) : ℂ) h1
  rwa [smul_inv_smul₀ hq] at this

theorem wholo_growForms (v : ℂ → modFun σ Y) {S : Set ℂ} (hS : IsOpen S)
    (hd : ∀ x, DifferentiableOn ℂ (fun s => (v s).1 x) S)
    (hc : ContinuousOn (fun y : ℂ × G2 σ Y => (v y.1).1 y.2) (S ×ˢ Set.univ))
    (hb : ∀ Q : Set ℂ, Q ⊆ S → IsCompact Q → ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Q, ∀ x, ‖(v s).1 x‖ ≤ C * (ht2 x : ℝ) ^ N) :
    WHolo {μ | IsGrowForm μ} v S := fun μ hμ =>
  differentiableOn_form (h := fun x : G2 σ Y => (ht2 x : ℝ)) (fun x => NNReal.coe_nonneg _)
    (fun _ _ _ hg hA => mem_modFun hg hA) μ hμ v hS hd hc hb

end GlobalTheory.CompanionTheory.WeakHolo

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

theorem _root_.GlobalTheory.T.whittaker_kernel_pullback_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    (whitKer ψ ![n, j + 1] (jac (stdBlocks ![n, j + 1] hd) π)).comap
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks ![n, j + 1] hd)) 1)) =
      twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.DerComap.whitKer_jac_comap_eq_twKer_derUnip | exact GlobalTheory.CompanionTheory.BZNuPair.DerComap.whitKer_jac_comap_eq_twKer_derUnip | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.DerComap.whitKer_jac_comap_eq_twKer_derUnip <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitian_scalar_sequence_tends_zero : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r : ℕ, ∃ e : ℕ → Mx D r r, (∀ n, e n ∈ hermA D r) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ (n : ℕ) (ρ : D.what₂.Tau), compAt θ ρ (e n) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitian_character_continuous_unit : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ β : PositivityTheory.GramSchwartzFunctions.HermE D n, Continuous (fun b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n => ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) ∧ ∀ b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n, ‖ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar | exact GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar | (intros; apply GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar <;> assumption)
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eisenstein_rational_points : PositivityTheory.GramSchwartzFunctions.EC.RatPts := by
  first | exact @GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn | exact GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn | (intros; apply GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn <;> assumption)
end
