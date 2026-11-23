module

public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.ArtinA
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1264
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle776
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import GroundTheory.PAdicHodge.Bundle004
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem fubini_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (fouH σ ψ db τ) db → (∀ z, ∫ y, fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∫ y, fouH σ ψ db τ y * (starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∂dx := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ dx hdx db hdb Φ hΦ τ hτ hinv T hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, hTr, -, hB, hCl, hG⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  have : LocallyCompactSpace (HermR (AF F) σ n) := (hCl n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR (AF F) σ n) :=
    (hCl n).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have := hdx.1
  have := hdb.1
  have : SFinite dx := inferInstance
  have : SFinite db := inferInstance
  set Th := fouH σ ψ db τ with hTh
  set S : HermR (AF F) σ n := hermOf (AF F) σ T hT with hS
  obtain ⟨hψc, hψn, -⟩ := hψ

  have hstar : ∀ (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E),
      algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x)) =
      pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x) := by
    intro y x
    simp only [pairHerm, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rfl
  have hchi : ∀ y : HermR (AF F) σ n, chiT σ ψ T y = ψ (-pairHerm (AF F) σ n y S) := by
    intro y
    have e : Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) =
        ∑ a, ∑ b, (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b *
          (S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) b a := by
      rw [Matrix.trace_mul_comm]
      rfl
    rw [chiT, e]
    rfl
  have hsub : ∀ y z w : HermR (AF F) σ n,
      pairHerm (AF F) σ n y z + -pairHerm (AF F) σ n y w = pairHerm (AF F) σ n y (z - w) := by
    intro y z w
    simp only [pairHerm, AddSubgroup.coe_sub, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, map_sub]
    ring
  have hpc : Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
      pairHerm (AF F) σ n z.1 (gramH hCM hJ (AF F) z.2 - S) := by
    have hg : Continuous (gramR (AF F) σ J : (Fin n → Fin M → AF F ⊗[F] E) → _) := hG n M J
    show Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
      algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (∑ a, ∑ b, (z.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b *
          (gramR (AF F) σ J z.2 b a - (S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) b a))
    refine continuous_const.mul (hTr.comp (continuous_finsetSum _ fun a _ =>
      continuous_finsetSum _ fun b _ => ?_))
    exact ((continuous_subtype_val.comp continuous_fst).matrix_elem a b).mul
      (((hg.comp continuous_snd).matrix_elem b a).sub continuous_const)
  have hint : Integrable (Function.uncurry fun (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E) =>
      Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S)))) (db.prod dx) := by
    have h0 : Integrable (fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) => Th z.1 * Φ z.2)
        (db.prod dx) := hτ.mul_prod hΦ
    have hc : Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
        ψ (pairHerm (AF F) σ n z.1 (gramH hCM hJ (AF F) z.2 - S)) := hψc.comp hpc
    refine h0.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have := h0.aestronglyMeasurable.mul hc.aestronglyMeasurable
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
    · simp only [Function.uncurry, norm_mul, hψn, mul_one, le_refl]
  have hL : ∀ y, Th y * (starN σ J ψ dx Φ y * chiT σ ψ T y) =
      ∫ x, Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S))) ∂dx := by
    intro y
    rw [integral_const_mul, starN, ← integral_mul_const, hchi]
    congr 2
    funext x
    rw [hstar, mul_assoc, ← AddChar.map_add_eq_mul, hsub]
  have hR : ∀ x, ∫ y, Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S))) ∂db =
      Φ x * τ (S - gramH hCM hJ (AF F) x) := by
    intro x
    have := hinv (gramH hCM hJ (AF F) x - S)
    rw [neg_sub] at this
    rw [← this, ← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hL]
  rw [integral_integral_swap hint]
  simp_rw [hR]

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

section

noncomputable section
open NumberField IsDedekindDomain
open Neutral.B1 hiding IsPlaceOver
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.ArtinMapUniq

open PositivityTheory.FamInh

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem exists_ideal_ramificationIdx (L : Type) [Field L] [NumberField L] [Algebra E L] :
    ∃ 𝔡 : Ideal (𝓞 E), 𝔡 ≠ ⊥ ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 L)),
      ¬ v.asIdeal ∣ 𝔡 → w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 E) = 1 := by
  refine ⟨(differentIdeal (𝓞 E) (𝓞 L)).under (𝓞 E), ?_, fun v w hv hl => ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (differentIdeal_ne_bot (A := 𝓞 E) (B := 𝓞 L))
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  · have hnd : ¬ w.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 L) := fun hd => hv (Ideal.dvd_iff_le.2 (by
      rw [hl.over]
      exact Ideal.comap_mono (Ideal.dvd_iff_le.1 hd)))
    exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

theorem res_unif_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') (L : IntermediateField E Ω) [FiniteDimensional E L]
    [IsAbelianGalois E L] (v : HeightOneSpectrum (𝓞 E)) {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) (w : HeightOneSpectrum (𝓞 L)) (hw : IsPlaceOver A w)
    [w.asIdeal.LiesOver v.asIdeal] (hr : w.asIdeal.ramificationIdx (𝓞 E) = 1)
    {x : (v.adicCompletion E)ˣ} (hx : IsUnifAt v x) :
    res L (art (localIdele E v x)) = res L (art' (localIdele E v x)) := by
  obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
  obtain ⟨σ', hσ', e'⟩ := (ha'.frob v A hA _).mp ⟨x, hx, rfl⟩
  have h := (res_isArithFrobAt hw hσ).mul_inv_mem_inertia (res_isArithFrobAt hw hσ')
  rw [(inertia_eq_bot_iff v w).2 hr, Subgroup.mem_bot, mul_inv_eq_one] at h
  rw [← e, ← e', map_inv, map_inv, map_inv, map_inv, res_toAb, res_toAb, h]

theorem res_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') (L : IntermediateField E Ω) [FiniteDimensional E L]
    [IsAbelianGalois E L] (x : Ideles E) : res L (art x) = res L (art' x) := by
  have := isAlgClosure_top L
  letI : CommGroup (L ≃ₐ[E] L) :=
    { (inferInstance : Group (L ≃ₐ[E] L)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := L ≃ₐ[E] L)).comm a b }
  have : T2Space (L ≃ₐ[E] L) := krullTopology_t2
  have : IsTopologicalGroup (L ≃ₐ[E] L) := inferInstance
  let f : Ideles E →* (L ≃ₐ[E] L) := (res L).comp art
  let f' : Ideles E →* (L ≃ₐ[E] L) := (res L).comp art'
  have hf : Continuous f := (continuous_res L).comp ha.quot.continuous
  have hf' : Continuous f' := (continuous_res L).comp ha'.quot.continuous
  have hk : ∀ b : Ideles E →* Gab E Ω, IsGlobalArtin b → ∀ k, b (diagUnits E k) = 1 := fun b hb k => by
    have hk : diagUnits E k ∈ b.ker := by
      rw [hb.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact MonoidHom.mem_ker.mp hk
  obtain ⟨𝔡, h𝔡, hun⟩ := exists_ideal_ramificationIdx (E := E) L
  have hψ := GlobalTheory.FrobDense.eq_one_of_away (f * f'⁻¹) (hf.mul hf'.inv) (fun k => by
      simp [f, f', hk _ ha k, hk _ ha' k]) (Ideal.finite_factors (I := 𝔡) h𝔡).toFinset fun v hv => by
    refine GlobalTheory.FrobDense.eq_one_of_unif ((f * f'⁻¹).comp (localIdele E v)) fun y hy => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨w, hw, hwv⟩ := exists_place_between (L := L) hA
    have hv' : ¬ v.asIdeal ∣ 𝔡 := by simpa using hv
    have e := res_unif_eq ha ha' L v hA w hw (hun v w hv' hwv) hy
    simp [f, f', e]
  have := DFunLike.congr_fun hψ x
  simpa [f, f', mul_inv_eq_one] using this

theorem eq_inv_arithmetic_artin_map : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → art = (PositivityTheory.FamInh.art0 E Ω)⁻¹ := by
  intro E Ω _ _ _ _ _ art ha
  ext x
  have ha0 : IsGlobalArtin (art0 E Ω)⁻¹ := by
    refine ⟨(Homeomorph.inv (Gab E Ω)).isOpenQuotientMap.comp (isOpenQuotientMap_art0 E Ω),
      ?_, ?_, ?_, ?_⟩
    · rw [← ker_art0 E Ω]
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
    · intro v A hA g
      simp only [MonoidHom.inv_apply, inv_eq_iff_eq_inv]
      rw [art0_unit_iff hA, Subgroup.inv_mem_iff]
      rfl
    · intro v A hA g
      simp only [MonoidHom.inv_apply, map_inv, inv_eq_iff_eq_inv]
      exact art0_unif_iff hA _
    · intro v A hA
      rw [← closure_range_eq hA]
      congr 1
      ext g
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x⁻¹, by simp⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x⁻¹, by simp⟩
  have h : art x * ((art0 E Ω)⁻¹ x)⁻¹ ∈ (⊥ : Subgroup (Gab E Ω)) :=
    mem_of_forall_res (H := ⊥) isClosed_singleton fun L _ _ _ => by
      rw [map_mul, map_inv, res_eq ha ha0 L x, mul_inv_cancel]
  rwa [Subgroup.mem_bot, mul_inv_eq_one] at h

end GlobalTheory.CompanionTheory.ArtinMapUniq
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelAssemblyLI

open GlobalTheory.CompanionTheory.SiegelAssembly

theorem weilSiegelFormula_of_chapters_LI : GlobalTheory.Published.WeilThetaConvergence → GlobalTheory.Published.WeilEisensteinSiegelConvergence →
    PullSchLI → EisCells → ThetaOrbits → BigCell → GlobalTheory.Published.WeilSiegelFormula := by
  intro hTh hES hP hE hT hB D n V hn h2n ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω ν hν Φ
  haveI := hν
  have hw : 2 * Formalism.MainNotions.SchurIrreducible.wittIdx V ≤ V.rank := two_mul_wittIdx_le_rank V
  have hSet : HidaSetting D n V ψ χ θ μ ω := ⟨hn, h2n, hψ, hχ, hη, hθ, ⟨𝓕, hμ⟩, hω⟩
  have hconv := hES D n V hn h2n ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω Φ
  choose μr 𝓕r hμr using fun r => GlobalTheory.MixModel.exists_isCovolOne D V.rank r
  choose c hc using fun U : Submodule D.host.E (Fin n → D.host.E) => exists_isRowBasis U
  have hEis := hE D n V ψ χ θ μ ω hSet Φ hconv μr (fun r => ⟨𝓕r r, hμr r⟩) c hc
  have hfib : ∀ U : Submodule D.host.E (Fin n → D.host.E),
      HasSum (fun b : HermE D (Module.finrank D.host.E U) => J ψ V (μr _) (pull (c U) Φ.1) b)
        (Ifr V ν (pull (c U) Φ.1)) := by
    intro U
    have hr : Module.finrank D.host.E U ≤ n := by
      have := Submodule.finrank_le U
      simpa using this
    have hpull := hP D θ hθ V.rank _ n (c U) (hc U).1 Φ.1 Φ.2
    have habs : GlobalTheory.SiegelFormula.absThetaInt V ν (pull (c U) Φ.1) < ⊤ := by
      rcases Nat.eq_zero_or_pos (Module.finrank D.host.E U) with h0 | hpos
      · exact absThetaInt_lt_top_of_eq_zero V ν h0 _
      · exact hTh D _ V hpos (Or.inr (by omega)) θ hθ ν hν ⟨_, hpull⟩
    exact hB D _ V (by omega) ψ hψ θ hθ (μr _) (𝓕r _) (hμr _) ν hν _ hpull habs
      (hEis.summable.sigma_factor U)
  exact (hEis.sigma hfib).unique
    (hT D n V θ hθ ν hν Φ (hTh D n V hn (Or.inr (by omega)) θ hθ ν hν Φ) c hc)

end GlobalTheory.CompanionTheory.SiegelAssemblyLI
end
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.JoinInfProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def infOf (τ : E →+* ℂ) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) : Multiset ℂ :=
  if h : ∃ m, HasInfCharGL x.2 τ m then h.choose else 0

theorem infOf_eq {τ : E →+* ℂ} {x : Σ M : ℕ, Submodule ℂ (Sm E M)} (h0 : x.2 ≠ ⊥) {m : Multiset ℂ}
    (h : HasInfCharGL x.2 τ m) : infOf τ x = m := by
  have hex : ∃ m, HasInfCharGL x.2 τ m := ⟨m, h⟩
  unfold infOf
  rw [dite_eq_left hex]
  exact GlobalTheory.BcSpehProof.hasInfCharGL_unique h0 hex.choose_spec h

theorem sum_m {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : ∑ i, P.m i τ = ((parts P).map (infOf τ)).sum := by
  rw [PositivityTheory.Rg.BcB.F.RS.parts, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (infOf_eq (P.discrete i).ne_bot (P.inf i τ)).symm

theorem infOf_twPart {n : ℕ} (P : Pre E n) (χ : HChar E) (τ : E →+* ℂ) (i : Fin P.c) :
    infOf τ (twPart χ ⟨P.N i, P.V i⟩) = (P.m i τ).map (· + expo χ τ) := by
  have hne : Submodule.map ((GlobalTheory.CuspRep.mulChi (P.N i) χ : Sm E (P.N i) ≃ₗ[ℂ] Sm E (P.N i)) :
      Sm E (P.N i) →ₗ[ℂ] Sm E (P.N i)) (P.V i) ≠ ⊥ := by
    intro hb
    exact (P.discrete i).ne_bot (Submodule.map_eq_bot_iff.1 hb)
  exact infOf_eq hne (GlobalTheory.BCT.TwistDisc.hasInfCharGL_map (P.inf i τ) χ)

theorem sum_tw {n : ℕ} (P : Pre E n) (χ : HChar E) (τ : E →+* ℂ) :
    (((parts P).map (twPart χ)).map (infOf τ)).sum = (∑ i, P.m i τ).map (· + expo χ τ) := by
  rw [PositivityTheory.Rg.BcB.F.RS.parts, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
  have hmap : ∀ s : Finset (Fin P.c), (∑ i ∈ s, P.m i τ).map (· + expo χ τ) =
      ∑ i ∈ s, (P.m i τ).map (· + expo χ τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add (f := _), ih]
  rw [hmap Finset.univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact infOf_twPart P χ τ i

end GlobalTheory.CompanionTheory.JoinInfProof

theorem GlobalTheory.CompanionTheory.JoinInfProof.joinInf : PositivityTheory.Rg.BcB.F.RS.JoinInf := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pb D hJ τ
  rw [sum_m D τ, hJ, List.map_append, List.sum_append, sum_tw Pa χ₁ τ, sum_tw Pb χ₂ τ]

end
end

section

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.TreeInfSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

inductive ListInf (τ : E →+* ℂ) : List (Σ M : ℕ, Submodule ℂ (Sm E M)) → Multiset ℂ → Prop
  | nil : ListInf τ [] 0
  | cons {x : Σ M : ℕ, Submodule ℂ (Sm E M)} {l : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {m₀ m' : Multiset ℂ} :
      HasInfCharGL x.2 τ m₀ → ListInf τ l m' → ListInf τ (x :: l) (m₀ + m')

theorem ListInf.split (τ : E →+* ℂ) (l₁ l₂ : List (Σ M : ℕ, Submodule ℂ (Sm E M))) (m : Multiset ℂ)
    (h : ListInf τ (l₁ ++ l₂) m) : ∃ m₁ m₂, ListInf τ l₁ m₁ ∧ ListInf τ l₂ m₂ ∧ m = m₁ + m₂ := by
  induction l₁ generalizing m with
  | nil => exact ⟨0, m, .nil, h, by simp⟩
  | cons x l ih =>
    have h' : ListInf τ (x :: (l ++ l₂)) m := h
    cases h' with
    | cons h₀ h' =>
      obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := ih _ h'
      exact ⟨_, m₂, .cons h₀ h₁, h₂, by rw [add_assoc]⟩

theorem listInf_ofFn (τ : E →+* ℂ) {c : ℕ} (N : Fin c → ℕ) (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (m : Fin c → Multiset ℂ) (h : ∀ i, HasInfCharGL (V i) τ (m i)) :
    ListInf τ (List.ofFn fun i => (⟨N i, V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) (∑ i, m i) := by
  induction c with
  | zero => simpa using ListInf.nil
  | succ c ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    exact .cons (h 0) (ih (fun i => N i.succ) (fun i => V i.succ) (fun i => m i.succ) (fun i => h i.succ))

theorem hasInfCharGL_rank_zero (V : Submodule ℂ (Sm E 0)) (τ : E →+* ℂ) : HasInfCharGL V τ 0 := by
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

theorem infOf_of_listInf (τ : E →+* ℂ) {N : ℕ} (t : Tr E N) (hg : t.Good) (hu : t.Untw) (m : Multiset ℂ)
    (h : ListInf τ (t.leafList.filter fun x => 0 < x.1) m) : t.InfOf τ m := by
  induction t generalizing m with
  | @leaf M V z =>
    rcases hg with ⟨rfl, rfl, rfl⟩ | ⟨hM, -, -⟩
    · have h' : ListInf τ [] m := by simpa [Tr.leafList] using h
      cases h'
      exact ⟨0, hasInfCharGL_rank_zero _ τ, by simp⟩
    · have hz : z = 0 := hu z (by simp [Tr.twists])
      subst hz
      have h' : ListInf τ [(⟨M, V⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))] m := by
        simpa [Tr.leafList, hM] using h
      cases h' with
      | cons h₀ h₁ =>
        cases h₁
        exact ⟨_, h₀, by simp⟩
  | node t₁ t₂ ih₁ ih₂ =>
    have hu₁ : t₁.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    have hu₂ : t₂.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    have h' := h
    simp only [Tr.leafList, List.filter_append] at h'
    obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := ListInf.split τ _ _ m h'
    exact ⟨m₁, m₂, ih₁ hg.1 hu₁ m₁ h₁, ih₂ hg.2 hu₂ m₂ h₂, rfl⟩

theorem treeInf : PositivityTheory.Rg.BcB.F.RS.TreeInf := by
  intro hT E _ _ _ N t P τ m hg hu hp h0 hm
  have h1 := listInf_ofFn τ P.N P.V (fun i => P.m i τ) (fun i => P.inf i τ)
  have hp' : (List.ofFn fun i => (⟨P.N i, P.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) =
      t.leafList.filter fun x => 0 < x.1 := hp
  rw [hp'] at h1
  exact GlobalTheory.BcSpehProof.hasInfCharGL_unique h0 (hT E N t τ _ (infOf_of_listInf τ t hg hu _ h1)) hm

end GlobalTheory.CompanionTheory.TreeInfSum

end
end
